// Tuned m-CFA for Scheme (m = 1) in Flix's first-class Datalog — a
// performance rewrite of ../flix/mcfa.flix (verified-correct faithful port of
// Appendix A of:
//   Davis Ross Silverman, Yihao Sun, Kristopher Micinski, Thomas Gilray.
//   "So You Want To Analyze Scheme Programs With Datalog?"
//   Scheme and Functional Programming Workshop, 2021.
//
// SAME facts, SAME `report()` output, SAME relation cardinalities as
// mcfa.flix. What's different is purely how the rule bodies are shaped, and
// it is the identical rewrite ../src/tuned.rs ("delta-friendly"/"tuned" Ascent
// port) applies to the faithful Ascent port, adapted to Flix. Two problems
// in mcfa.flix's rule set, both invisible in the *semantics* but expensive in
// semi-naive evaluation:
//
//  1. **Multi-head duplication.** Soufflé (and the paper) write rules with
//     several heads sharing one body, e.g. E-Call produces state_e, a new
//     stored_kont row, AND a flow_ee edge from a single 3-atom join. Flix (like
//     the faithful Ascent port) has no multi-head rules, so mcfa.flix turned
//     each into 3-4 *separate* Flix rules that each independently re-join the
//     same body — the same `StateE ⋈ Call ⋈ PeekCtx` join gets computed 3
//     times per semi-naive iteration instead of once. The fix: materialize the
//     body join ONCE into an intermediate "redex" relation (e.g. `AppRedex`),
//     then derive every head from it via a trivial single-atom-body rule.
//     Where the body itself is a 3-atom join reached through a large
//     recursively-growing relation (state_e / stored_val / state_a), we also
//     split it into binary joins first — the exact same "reader index"
//     relations tuned.rs introduces (`app_state`, `let_state`, `callcc_state`,
//     `var_read`, `copy_edge` there; `AppState`, `LetState`, `CallccState`,
//     `VarRead`, `CopyEdge` here) — so no single rule ever re-scans a 3-way
//     join from scratch.
//
//  2. **The functional-predicate workaround was a per-match scan.** mcfa.flix
//     documents a confirmed Flix 0.75.1 bug: a variable bound by `let x =
//     f(v)` is not properly join-constrained when later used as an ARGUMENT of
//     a subsequent body atom (it matches every row, not just the one
//     consistent with `x`). mcfa.flix's A-Call/A-C/cc worked around this by
//     binding a FRESH variable from the next atom and comparing with an `if`
//     guard — which still means Souffle-style destructuring effectively
//     re-derives "is this state_a a closure?" and does a guarded scan of ALL
//     of `Lambda` per match. Since the *other* direction of the bug (a
//     destructured variable used only in a rule's HEAD) is safe — mcfa.flix's
//     own A-C/ccKont rules already rely on exactly this — we instead
//     materialize two small shadow relations once, up front:
//         AClosure(v, elam, ctxclo) :- StateA(v, _), let (elam, ctxclo) = closureParts(v).
//         AKont(v, k)               :- StateA(v, _), let k = kontParts(v).
//     Every value that ever reaches KontFn's `func` column or a callcc
//     operand was itself produced by some StateA rule, so these two relations
//     cover every destructuring need in the whole rule set. A-Call and A-C/cc
//     then become ordinary, fully-positive, indexed joins against `AClosure`/
//     `AKont` — no `let`-inside-a-multi-atom-body pattern (and hence no bug
//     workaround, and no per-match `Lambda` scan) is needed anywhere below.
//
// Paper semantics preserved exactly (checked rule-by-rule against mcfa.flix):
// A-Call's kont-operator branch still requires `pos == 0` (now a literal `0`
// selecting rows out of the shared `FnState` reader index instead of out of
// `KontFn` directly), and A-C/cc's closure-operand branch still binds
// parameter 0 to `VKont(ak)` where `ak` is the address the value arrived at.
//
// `rules()` is split into three `def`s (`rulesFreevarInject`, `rulesE`,
// `rulesA`) rather than one, for the same reason mcfa.flix pulled `rules()`
// out of `main` in the first place: this rule set has roughly twice as many
// individual Flix rules (each simpler) as the faithful port, and one JVM
// method holding it all plus the driver would overflow the 64KB
// method-bytecode limit ("Method too large").

type alias Sym = String // expression/name ids
type alias Ctx = String // m = 1: the context IS a binding-site expression id ("" = empty)

enum AddrK with Eq, Order, ToString {
    case KAddr(Sym, Ctx)
}

enum Value with Eq, Order, ToString {
    case VNum(Int64)
    case VBool(String)
    case VKont(AddrK)
    case VClosure(Sym, Ctx)
    case VPrim(Sym, Value, Value)
}

// ===================== Value-shape helpers =====================

/// Truthy per the paper: everything except the boolean `#f` and (per the
/// A-IfT Soufflé disjunction, which omits `PrimVal`) partially-applied
/// primitives.
def isTruthy(v: Value): Bool = match v {
    case Value.VBool(b)        => b == "#t"
    case Value.VPrim(_, _, _)  => false
    case _                     => true
}

/// A value's closure parts, or no rows if it isn't a closure. Unlike
/// mcfa.flix's `closurePartsCC`/`closurePartsFn`, this has exactly one call
/// site (`AClosure`, below) and its destructured output is used ONLY in that
/// rule's head — the safe direction of the Flix 0.75.1 functional-predicate
/// bug (see the header comment) — so no fresh-variable/`if`-guard workaround
/// is needed here.
def closureParts(v: Value): Vector[(Sym, Ctx)] = match v {
    case Value.VClosure(e, c) => Vector#{(e, c)}
    case _                    => Vector#{}
}

/// A value's continuation address, or no rows if it isn't a continuation.
/// Same safety argument as `closureParts`.
def kontParts(v: Value): Vector[AddrK] = match v {
    case Value.VKont(k) => Vector#{k}
    case _              => Vector#{}
}

// ===================== Fact-file parsing (unchanged from mcfa.flix) =====

def bugRow(name: String, line: String): a = bug!("mcfa_tuned: bad row in ${name}.facts: '${line}'")

def loadRaw(dir: String, name: String): List[String] \ Fs.FileRead.FileRead =
    match Fs.FileRead.readLines("${dir}/${name}.facts") {
        case Ok(ls)  => List.filter(l -> String.length(l) > 0, ls)
        case Err(_)  => Nil
    }

def splitTab(line: String): List[String] = String.splitOn(substr = "\t", line)

def toI32(s: String): Int32 = match Int32.fromString(s) {
    case Some(i) => i
    case None    => bug!("mcfa_tuned: bad int32: '${s}'")
}

def toI64(s: String): Int64 = match Int64.fromString(s) {
    case Some(i) => i
    case None    => bug!("mcfa_tuned: bad int64: '${s}'")
}

def load1(dir: String, name: String): List[String] \ Fs.FileRead.FileRead =
    loadRaw(dir, name)

def load2(dir: String, name: String): List[(String, String)] \ Fs.FileRead.FileRead =
    List.map(l -> match splitTab(l) {
        case a :: b :: Nil => (a, b)
        case _             => bugRow(name, l)
    }, loadRaw(dir, name))

def load2i(dir: String, name: String): List[(String, Int64)] \ Fs.FileRead.FileRead =
    List.map(l -> match splitTab(l) {
        case a :: b :: Nil => (a, toI64(b))
        case _             => bugRow(name, l)
    }, loadRaw(dir, name))

def load3(dir: String, name: String): List[(String, String, String)] \ Fs.FileRead.FileRead =
    List.map(l -> match splitTab(l) {
        case a :: b :: c :: Nil => (a, b, c)
        case _                  => bugRow(name, l)
    }, loadRaw(dir, name))

/// For lambda_arg_list / call_arg_list: (list-id, position:Int32, name-or-expr-id).
def load3mid(dir: String, name: String): List[(String, Int32, String)] \ Fs.FileRead.FileRead =
    List.map(l -> match splitTab(l) {
        case a :: b :: c :: Nil => (a, toI32(b), c)
        case _                  => bugRow(name, l)
    }, loadRaw(dir, name))

def load4(dir: String, name: String): List[(String, String, String, String)] \ Fs.FileRead.FileRead =
    List.map(l -> match splitTab(l) {
        case a :: b :: c :: d :: Nil => (a, b, c, d)
        case _                       => bugRow(name, l)
    }, loadRaw(dir, name))

// ===================== the analysis rule set =====================
//
// One shared schema alias for every relation used anywhere below (EDB, the
// same derived relations mcfa.flix reports, and the new intermediate "redex"
// / reader-index relations this file introduces). Every `rules*` def and
// `report` below is ascribed this exact alias, so `<+>` between them and
// `solve`/`query` against the result all just work on one concrete row type
// instead of needing separate open-row plumbing per def.
type alias McfaSchema = #{
    // ----- EDB (14), same names/arities as mcfa.flix -----
    Bool(Sym, Sym), Call(Sym, Sym, Sym), CallArgList(Sym, Int32, Sym), Callcc(Sym, Sym),
    If(Sym, Sym, Sym, Sym), Lambda(Sym, Sym, Sym), LambdaArgList(Sym, Int32, Sym),
    Let(Sym, Sym, Sym), LetList(Sym, Sym, Sym), Num(Sym, Int64), PrimCall(Sym, Sym, Sym),
    Setb(Sym, Sym, Sym), TopExp(Sym), Var(Sym, Sym),

    // ----- derived relations kept identical to mcfa.flix (21); these (plus
    // the 14 EDB relations above) are exactly what `report` prints -----
    CopyCtx(Ctx, Ctx, Sym), FlowAA(Value, Value), FlowAE(Value, Sym), FlowEA(Sym, Value),
    FlowEE(Sym, Sym), Freevar(Sym, Sym), IsParam(Sym, Sym),
    KontArg(AddrK, Sym, Ctx, Ctx, AddrK), KontCallcc(AddrK, Ctx, AddrK),
    KontFn(AddrK, Value, Int32, Ctx, AddrK), KontIf(AddrK, Sym, Sym, Ctx, AddrK),
    KontLet(AddrK, Sym, Ctx, Sym, Ctx, AddrK), KontMt(AddrK),
    KontPrim1(AddrK, Sym, Sym, Ctx, AddrK), KontPrim2(AddrK, Sym, Value, AddrK),
    KontSet(AddrK, Sym, Ctx, AddrK), LetBound(Sym, Sym),
    PeekCtx(Sym, Ctx, Ctx), StateA(Value, AddrK), StateE(Sym, Ctx, AddrK),
    StoredVal(Sym, Ctx, Value),

    // ----- new intermediate relations: NOT printed by `report`, exist only to
    // materialize a rule body once so every head reads it with a single atom
    // (see header comment, problem 1) -----
    IfRedex(Sym, Sym, Sym, Sym, Ctx, AddrK),
    SetRedex(Sym, Sym, Sym, Ctx, AddrK),
    CallccState(Sym, Sym, Ctx, AddrK), CallccRedex(Sym, Sym, Ctx, Ctx, AddrK),
    AppState(Sym, Sym, Sym, Ctx, AddrK), AppRedex(Sym, Sym, Sym, Ctx, Ctx, AddrK),
    LetState(Sym, Sym, Sym, Sym, Ctx, AddrK), LetRedex(Sym, Sym, Sym, Sym, Ctx, Ctx, AddrK),
    PrimState(Sym, Sym, Sym, Ctx, AddrK), PrimRedex(Sym, Sym, Sym, Sym, Ctx, AddrK),
    NumRedex(Sym, Int64, AddrK), BoolRedex(Sym, Sym, AddrK), LambdaAtomRedex(Sym, Ctx, AddrK),
    VarRead(Sym, Ctx, Sym, AddrK), VarRedex(Sym, Sym, Ctx, AddrK, Value),
    CopyEdge(Sym, Ctx, Ctx),
    IfTRedex(Sym, Ctx, AddrK), IfFRedex(Sym, Ctx, AddrK),
    // shadow decomposition relations (problem 2)
    AClosure(Value, Sym, Ctx), AKont(Value, AddrK),
    FnState(Value, AddrK, Value, Int32, Ctx, AddrK),
    FnClosureRedex(Value, Sym, Ctx, Int32, Ctx, AddrK),
    FnBodyRedex(Value, Sym, Ctx, AddrK, Ctx, Sym, Sym),
    FnKontRedex(Value, AddrK),
    CallccKontJoin(Value, AddrK, Ctx, AddrK),
    CCClosureRedex(AddrK, Sym, Ctx, Ctx, AddrK),
    CCBodyRedex(AddrK, Ctx, AddrK, Sym, Sym, Ctx, Sym),
    CCKontOpRedex(AddrK, AddrK),
    ArState(Value, AddrK, Sym, Ctx, Ctx, AddrK), ArRedex(Value, Ctx, Ctx, AddrK, Int32, Sym),
    LetKontRedex(Value, Sym, Ctx, Sym, Ctx, AddrK),
    Prim1Redex(Value, Sym, Sym, Ctx, AddrK), Prim2Redex(Value, Sym, Value, AddrK),
    SetKontRedex(Value, Sym, Ctx, AddrK)
}

/// Freevar (unchanged from mcfa.flix — not part of this tuning), injection,
/// peek_ctx, and the flat-closure copy-across-context-boundary rule (split
/// into a binary join via `CopyEdge`, exactly tuned.rs's `copy_edge`).
def rulesFreevarInject(): McfaSchema = #{
    // ----- freevar (negation projected first: no wildcards allowed in `not`) -----
    IsParam(vars, x)  :- LambdaArgList(vars, _, x).
    LetBound(l, x)    :- LetList(l, x, _).

    Freevar(x, e) :- Var(e, x).
    Freevar(x, e) :- Lambda(e, vars, body), Freevar(x, body), not IsParam(vars, x).
    Freevar(x, e) :- Call(e, func, _), Freevar(x, func).
    Freevar(x, e) :- Call(e, _, args), Freevar(x, args).
    Freevar(x, e) :- PrimCall(e, _, args), Freevar(x, args).
    Freevar(x, e) :- CallArgList(e, _, arg), Freevar(x, arg).
    Freevar(x, e) :- If(e, eguard, _, _), Freevar(x, eguard).
    Freevar(x, e) :- If(e, _, et, _), Freevar(x, et).
    Freevar(x, e) :- If(e, _, _, ef), Freevar(x, ef).
    Freevar(y, e) :- Setb(e, _, ev), Freevar(y, ev).
    Freevar(x, e) :- Callcc(e, ev), Freevar(x, ev).
    Freevar(x, e) :- Let(e, binds, _), Freevar(x, binds).
    Freevar(x, e) :- Let(e, _, body), Freevar(x, body).
    Freevar(x, e) :- LetList(e, _, bind), Freevar(x, bind), not LetBound(e, x).

    // ----- injection (top_exp -> the initial state) -----
    StateE(e, "", AddrK.KAddr(e, "")) :- TopExp(e).
    PeekCtx(e, "", e)                 :- TopExp(e).
    KontMt(AddrK.KAddr(e, ""))        :- TopExp(e).

    // ----- peek_ctx: one rule per expression form that introduces a new context -----
    PeekCtx(e, ctx, e) :- StateE(e, ctx, _), Callcc(e, _).
    PeekCtx(e, ctx, e) :- StateE(e, ctx, _), Call(e, _, _).
    PeekCtx(e, ctx, e) :- StateE(e, ctx, _), Let(e, _, _).
    PeekCtx(e, ctx, e) :- StateE(e, ctx, _), Lambda(e, _, _).

    // ----- flat-closure copy of free variables across a context boundary,
    // split into a binary join via CopyEdge (tuned.rs's copy_edge) -----
    CopyEdge(fv, fromCtx, to)   :- CopyCtx(fromCtx, to, e), Freevar(fv, e).
    StoredVal(fv, to, v)       :- CopyEdge(fv, fromCtx, to), StoredVal(fv, fromCtx, v).
}

/// E-If / E-C/cc / E-Set! / E-Call / E-Let / E-Prim, and atomic evaluation
/// (Num/Bool/Lambda/Var). Each rule body is materialized ONCE into a "redex"
/// relation (splitting 3-atom joins into binary joins first, à la tuned.rs's
/// `app_state`/`let_state`/`callcc_state`/`var_read`), then every head reads
/// that redex with a single-atom body.
def rulesE(): McfaSchema = #{
    // ----- E-If -----
    IfRedex(e, eguard, et, ef, ctx, ak) :- StateE(e, ctx, ak), If(e, eguard, et, ef).
    StateE(eguard, ctx, AddrK.KAddr(eguard, ctx))     :- IfRedex(e, eguard, et, ef, ctx, ak).
    KontIf(AddrK.KAddr(eguard, ctx), et, ef, ctx, ak) :- IfRedex(e, eguard, et, ef, ctx, ak).
    FlowEE(e, eguard)                                 :- IfRedex(e, eguard, et, ef, ctx, ak).

    // ----- E-C/cc, split so the peek_ctx join is binary -----
    CallccState(e, elam, ctx, ak) :- StateE(e, ctx, ak), Callcc(e, elam).
    CallccRedex(e, elam, ctx, ectx, ak) :- CallccState(e, elam, ctx, ak), PeekCtx(e, ctx, ectx).
    StateE(elam, ctx, AddrK.KAddr(elam, ctx))    :- CallccRedex(e, elam, ctx, ectx, ak).
    KontCallcc(AddrK.KAddr(elam, ctx), ectx, ak) :- CallccRedex(e, elam, ctx, ectx, ak).
    FlowEE(e, elam)                              :- CallccRedex(e, elam, ctx, ectx, ak).

    // ----- E-Set! -----
    SetRedex(e, x, esetto, ctx, ak) :- StateE(e, ctx, ak), Setb(e, x, esetto).
    StateE(esetto, ctx, AddrK.KAddr(esetto, ctx)) :- SetRedex(e, x, esetto, ctx, ak).
    KontSet(AddrK.KAddr(esetto, ctx), x, ctx, ak) :- SetRedex(e, x, esetto, ctx, ak).
    FlowEE(e, esetto)                             :- SetRedex(e, x, esetto, ctx, ak).

    // ----- E-Call, split so the peek_ctx join is binary -----
    AppState(e, efunc, eargs, ctx, ak) :- StateE(e, ctx, ak), Call(e, efunc, eargs).
    AppRedex(e, efunc, eargs, ctx, ectx, ak) :- AppState(e, efunc, eargs, ctx, ak), PeekCtx(e, ctx, ectx).
    StateE(efunc, ctx, AddrK.KAddr(efunc, ctx))            :- AppRedex(e, efunc, eargs, ctx, ectx, ak).
    KontArg(AddrK.KAddr(efunc, ctx), eargs, ctx, ectx, ak) :- AppRedex(e, efunc, eargs, ctx, ectx, ak).
    FlowEE(e, efunc)                                       :- AppRedex(e, efunc, eargs, ctx, ectx, ak).

    // ----- E-Let, split so the peek_ctx join is binary -----
    LetState(e, x, ebnd, ebody, ctx, ak) :- StateE(e, ctx, ak), Let(e, ll, ebody), LetList(ll, x, ebnd).
    LetRedex(e, x, ebnd, ebody, ctx, ectx, ak) :- LetState(e, x, ebnd, ebody, ctx, ak), PeekCtx(e, ctx, ectx).
    StateE(ebnd, ctx, AddrK.KAddr(ebnd, ctx))                 :- LetRedex(e, x, ebnd, ebody, ctx, ectx, ak).
    KontLet(AddrK.KAddr(ebnd, ctx), x, ectx, ebody, ectx, ak) :- LetRedex(e, x, ebnd, ebody, ctx, ectx, ak).
    CopyCtx(ctx, ectx, e)                                     :- LetRedex(e, x, ebnd, ebody, ctx, ectx, ak).
    FlowEE(e, ebnd)                                           :- LetRedex(e, x, ebnd, ebody, ctx, ectx, ak).

    // ----- E-Prim -----
    PrimState(e, op, pl, ctx, ak) :- StateE(e, ctx, ak), PrimCall(e, op, pl).
    PrimRedex(e, op, earg0, earg1, ctx, ak) :-
        PrimState(e, op, pl, ctx, ak), CallArgList(pl, 0, earg0), CallArgList(pl, 1, earg1).
    StateE(earg0, ctx, AddrK.KAddr(earg0, ctx))          :- PrimRedex(e, op, earg0, earg1, ctx, ak).
    KontPrim1(AddrK.KAddr(earg0, ctx), op, earg1, ctx, ak) :- PrimRedex(e, op, earg0, earg1, ctx, ak).
    FlowEE(e, earg0)                                     :- PrimRedex(e, op, earg0, earg1, ctx, ak).

    // ----- Atomic evaluation: Num / Bool / Lambda -----
    NumRedex(e, n, ak) :- StateE(e, _, ak), Num(e, n).
    StateA(Value.VNum(n), ak)     :- NumRedex(e, n, ak).
    FlowEA(e, Value.VNum(n))      :- NumRedex(e, n, ak).

    BoolRedex(e, b, ak) :- StateE(e, _, ak), Bool(e, b).
    StateA(Value.VBool(b), ak)    :- BoolRedex(e, b, ak).
    FlowEA(e, Value.VBool(b))     :- BoolRedex(e, b, ak).

    LambdaAtomRedex(e, ctx, ak) :- StateE(e, ctx, ak), Lambda(e, _, _).
    StateA(Value.VClosure(e, ctx), ak) :- LambdaAtomRedex(e, ctx, ak).
    FlowEA(e, Value.VClosure(e, ctx))  :- LambdaAtomRedex(e, ctx, ak).

    // Atomic evaluation: Var, split into a binary join via VarRead
    // (tuned.rs's var_read).
    VarRead(x, ctx, e, ak) :- StateE(e, ctx, ak), Var(e, x).
    VarRedex(e, x, ctx, ak, v) :- VarRead(x, ctx, e, ak), StoredVal(x, ctx, v).
    StateA(v, ak) :- VarRedex(e, x, ctx, ak, v).
    FlowEA(e, v)  :- VarRedex(e, x, ctx, ak, v).
}

/// A-If, A-Ar, A-Call (both operator forms), A-C/cc (both operand forms),
/// A-Let, A-Prim1, A-Prim2, A-Set!. Same "materialize the body once" fix as
/// `rulesE`, plus the `AClosure`/`AKont` shadow relations that replace the
/// guarded functional-predicate destructuring problem 2 in the header
/// comment describes.
def rulesA(): McfaSchema = #{
    // ----- shadow decomposition relations: cover every place a StateA value
    // is later matched as a closure (KontFn's func column, A-Call) or as a
    // continuation (a callcc operand, A-C/cc) -- see header comment. -----
    AClosure(v, elam, ctxclo) :- StateA(v, _), let (elam, ctxclo) = closureParts(v).
    AKont(v, k)               :- StateA(v, _), let k = kontParts(v).

    // ----- A-IfT (truthy = anything but #f and a partially-applied prim) -----
    IfTRedex(et, ctxk, nak) :- StateA(v, ak), KontIf(ak, et, ef, ctxk, nak), if (isTruthy(v)).
    StateE(et, ctxk, nak)          :- IfTRedex(et, ctxk, nak).
    FlowAE(Value.VBool("#t"), et)  :- IfTRedex(et, ctxk, nak).

    // ----- A-IfF -----
    IfFRedex(ef, ctxk, nak) :- StateA(v, ak), KontIf(ak, et, ef, ctxk, nak), if (v == Value.VBool("#f")).
    StateE(ef, ctxk, nak)          :- IfFRedex(ef, ctxk, nak).
    FlowAE(Value.VBool("#f"), ef)  :- IfFRedex(ef, ctxk, nak).

    // ----- A-Ar (already a simple indexed join; still fix multi-head dup) -----
    ArState(v, ak, eargs, ctx, ectx, nak) :- StateA(v, ak), KontArg(ak, eargs, ctx, ectx, nak).
    ArRedex(v, ctx, ectx, nak, pos, earg) :- ArState(v, ak, eargs, ctx, ectx, nak), CallArgList(eargs, pos, earg).
    StateE(earg, ctx, AddrK.KAddr(earg, ctx))            :- ArRedex(v, ctx, ectx, nak, pos, earg).
    KontFn(AddrK.KAddr(earg, ctx), v, pos, ectx, nak)    :- ArRedex(v, ctx, ectx, nak, pos, earg).
    FlowAE(v, earg)                                      :- ArRedex(v, ctx, ectx, nak, pos, earg).

    // ----- A-Call (closure operand): all-positive indexed joins via AClosure,
    // no functional-predicate bug workaround needed -----
    FnState(v, ak, func, pos, ectx, nak) :- StateA(v, ak), KontFn(ak, func, pos, ectx, nak).
    FnClosureRedex(v, elam, ctxclo, pos, ectx, nak) :-
        FnState(v, ak, func, pos, ectx, nak), AClosure(func, elam, ctxclo).
    FnBodyRedex(v, ebody, ectx, nak, ctxclo, elam, x) :-
        FnClosureRedex(v, elam, ctxclo, pos, ectx, nak), Lambda(elam, params, ebody), LambdaArgList(params, pos, x).
    StateE(ebody, ectx, nak)          :- FnBodyRedex(v, ebody, ectx, nak, ctxclo, elam, x).
    StoredVal(x, ectx, v)             :- FnBodyRedex(v, ebody, ectx, nak, ctxclo, elam, x).
    CopyCtx(ctxclo, ectx, elam)       :- FnBodyRedex(v, ebody, ectx, nak, ctxclo, elam, x).
    FlowAE(v, ebody)                  :- FnBodyRedex(v, ebody, ectx, nak, ctxclo, elam, x).

    // ----- A-Call (continuation as operator): requires pos == 0, selected
    // as a literal out of the shared FnState reader index -----
    FnKontRedex(v, callccKont) :- FnState(v, ak, func, 0, ectx, nak), AKont(func, callccKont).
    StateA(v, callccKont) :- FnKontRedex(v, callccKont).
    FlowAA(v, v)          :- FnKontRedex(v, callccKont).

    // ----- A-C/cc (closure operand): param 0 binds to VKont(ak), where ak is
    // the address the value arrived at -- via AClosure, no bug workaround -----
    CallccKontJoin(v, ak, ectx, nak) :- StateA(v, ak), KontCallcc(ak, ectx, nak).
    CCClosureRedex(ak, elam, ctxclo, ectx, nak) :- CallccKontJoin(v, ak, ectx, nak), AClosure(v, elam, ctxclo).
    CCBodyRedex(ak, ectx, nak, ebody, x, ctxclo, elam) :-
        CCClosureRedex(ak, elam, ctxclo, ectx, nak), Lambda(elam, params, ebody), LambdaArgList(params, 0, x).
    StateE(ebody, ectx, nak)                             :- CCBodyRedex(ak, ectx, nak, ebody, x, ctxclo, elam).
    StoredVal(x, ectx, Value.VKont(ak))                  :- CCBodyRedex(ak, ectx, nak, ebody, x, ctxclo, elam).
    CopyCtx(ctxclo, ectx, elam)                          :- CCBodyRedex(ak, ectx, nak, ebody, x, ctxclo, elam).
    FlowAE(Value.VClosure(elam, ctxclo), ebody)          :- CCBodyRedex(ak, ectx, nak, ebody, x, ctxclo, elam).

    // ----- A-C/ccKont (continuation operand): shares CallccKontJoin with the
    // closure-operand branch above (same body, computed once) -----
    CCKontOpRedex(ak, bk) :- CallccKontJoin(v, ak, ectx, nak), AKont(v, bk).
    StateA(Value.VKont(bk), ak)              :- CCKontOpRedex(ak, bk).
    FlowAA(Value.VKont(bk), Value.VKont(ak)) :- CCKontOpRedex(ak, bk).

    // ----- A-Let -----
    LetKontRedex(v, x, xctx, ebody, ctx, nak) :- StateA(v, ak), KontLet(ak, x, xctx, ebody, ctx, nak).
    StateE(ebody, ctx, nak) :- LetKontRedex(v, x, xctx, ebody, ctx, nak).
    StoredVal(x, xctx, v)   :- LetKontRedex(v, x, xctx, ebody, ctx, nak).
    FlowAE(v, ebody)        :- LetKontRedex(v, x, xctx, ebody, ctx, nak).

    // ----- A-Prim1 -----
    Prim1Redex(v, op, earg1, ctx, nak) :- StateA(v, ak), KontPrim1(ak, op, earg1, ctx, nak).
    StateE(earg1, ctx, AddrK.KAddr(earg1, ctx))    :- Prim1Redex(v, op, earg1, ctx, nak).
    KontPrim2(AddrK.KAddr(earg1, ctx), op, v, nak) :- Prim1Redex(v, op, earg1, ctx, nak).
    FlowAE(v, earg1)                                :- Prim1Redex(v, op, earg1, ctx, nak).

    // ----- A-Prim2 -----
    Prim2Redex(v2, op, v1, nak) :- StateA(v2, ak), KontPrim2(ak, op, v1, nak).
    StateA(Value.VPrim(op, v1, v2), nak)  :- Prim2Redex(v2, op, v1, nak).
    FlowAA(v2, Value.VPrim(op, v1, v2))   :- Prim2Redex(v2, op, v1, nak).

    // ----- A-Set! -----
    SetKontRedex(v, x, xctx, nak) :- StateA(v, ak), KontSet(ak, x, xctx, nak).
    StateA(Value.VNum(-42i64), nak)       :- SetKontRedex(v, x, xctx, nak).
    StoredVal(x, xctx, v)                 :- SetKontRedex(v, x, xctx, nak).
    FlowAA(v, Value.VNum(-42i64))         :- SetKontRedex(v, x, xctx, nak).
}

// ===================== reporting =====================
//
// Identical to mcfa.flix's `report`: same relations queried, same lines
// printed, same `stored_kont` sum over the 9 Kont* relations. The new
// intermediate/redex relations are declared in `McfaSchema` (so this
// function can accept a solved `McfaSchema` model) but never queried here —
// they are not part of the analysis's observable output.
def report(model1: McfaSchema): Unit \ IO = {
    let stateE  = query model1 select (e, c, ak) from StateE(e, c, ak);
    let stateA  = query model1 select (v, ak) from StateA(v, ak);
    let storedV = query model1 select (x, c, v) from StoredVal(x, c, v);

    // NOTE: each query below selects EVERY column of its relation, not just
    // `ak` — the same address legitimately carries several distinct
    // continuations (that's the whole point of a finite m-CFA abstraction),
    // so projecting away the other columns would silently deduplicate
    // genuinely-distinct rows and undercount `stored_kont`.
    let kMt     = query model1 select ak from KontMt(ak);
    let kArg    = query model1 select (ak, args, ctx, ectx, nak) from KontArg(ak, args, ctx, ectx, nak);
    let kFn     = query model1 select (ak, func, pos, ectx, nak) from KontFn(ak, func, pos, ectx, nak);
    let kSet    = query model1 select (ak, x, xctx, nak) from KontSet(ak, x, xctx, nak);
    let kIf     = query model1 select (ak, et, ef, ctxk, nak) from KontIf(ak, et, ef, ctxk, nak);
    let kCallcc = query model1 select (ak, ectx, nak) from KontCallcc(ak, ectx, nak);
    let kLet    = query model1 select (ak, x, xctx, ebody, ctx, nak) from KontLet(ak, x, xctx, ebody, ctx, nak);
    let kPrim1  = query model1 select (ak, op, e2, ctx, nak) from KontPrim1(ak, op, e2, ctx, nak);
    let kPrim2  = query model1 select (ak, op, v1, nak) from KontPrim2(ak, op, v1, nak);

    let flowEE  = query model1 select (e1, e2) from FlowEE(e1, e2);
    let flowEA  = query model1 select (e1, v) from FlowEA(e1, v);
    let flowAE  = query model1 select (v, e2) from FlowAE(v, e2);
    let flowAA  = query model1 select (v1, v2) from FlowAA(v1, v2);
    let peekCtx = query model1 select (e, c1, c2) from PeekCtx(e, c1, c2);
    let copyCtx = query model1 select (c1, c2, e) from CopyCtx(c1, c2, e);
    let fv      = query model1 select (x, e) from Freevar(x, e);

    let storedKont =
        Vector.length(kMt) + Vector.length(kArg) + Vector.length(kFn) + Vector.length(kSet) +
        Vector.length(kIf) + Vector.length(kCallcc) + Vector.length(kLet) +
        Vector.length(kPrim1) + Vector.length(kPrim2);

    println("state_e ${Vector.length(stateE)}");
    println("state_a ${Vector.length(stateA)}");
    println("stored_val ${Vector.length(storedV)}");
    println("stored_kont ${storedKont}");
    println("flow_ee ${Vector.length(flowEE)}");
    println("flow_ea ${Vector.length(flowEA)}");
    println("flow_ae ${Vector.length(flowAE)}");
    println("flow_aa ${Vector.length(flowAA)}");
    println("peek_ctx ${Vector.length(peekCtx)}");
    println("copy_ctx ${Vector.length(copyCtx)}");
    println("freevar ${Vector.length(fv)}")
}

// ===================== main =====================

pub def main(): Unit \ {IO, Fs.FileRead.FileRead, Time.Clock.Clock, Sys.Env.Env} = {
    let cliArgs = Sys.Env.getArgs();
    let dir = match cliArgs {
        case d :: _ => d
        case Nil    => bug!("usage: mcfa_tuned.flix -- FACTS_DIR")
    };

    let topExp     = load1(dir, "top_exp");
    let lambda     = load3(dir, "lambda");
    let lambdaArgL = load3mid(dir, "lambda_arg_list");
    let primCall   = load3(dir, "prim_call");
    let call       = load3(dir, "call");
    let callArgL   = load3mid(dir, "call_arg_list");
    let var_       = load2(dir, "var");
    let num_       = load2i(dir, "num");
    let bool_      = load2(dir, "bool");
    let if_        = load4(dir, "if");
    let setb_      = load3(dir, "setb");
    let callcc_    = load2(dir, "callcc");
    let let_       = load3(dir, "let");
    let letList    = load3(dir, "let_list");

    let edb = inject topExp, lambda, lambdaArgL, primCall, call, callArgL, var_, num_, bool_, if_, setb_, callcc_, let_, letList
        into TopExp/1, Lambda/3, LambdaArgList/3, PrimCall/3, Call/3, CallArgList/3,
             Var/2, Num/2, Bool/2, If/4, Setb/3, Callcc/2, Let/3, LetList/3;

    let program = edb <+> rulesFreevarInject() <+> rulesE() <+> rulesA();

    // Timing note (copied verbatim from mcfa.flix): `solve` is pure, so the
    // optimizer may common up or sink repeated `solve program` calls, or —
    // subtler — inline a let-bound solve used at exactly one query call site
    // and evaluate only the strata that query's predicate depends on (an EDB
    // predicate like TopExp forces ~nothing). Each timed solve below is
    // therefore (a) forced by TWO queries against distinct predicates spanning
    // the derived strata, and (b) run on a distinguishable program value so
    // two solves cannot be merged into one.
    let t0 = Time.Clock.currentTime(Time.TimeUnit.Nanoseconds);
    let model1 = solve program;
    let force1 = query model1 select e from TopExp(e);
    let t1 = Time.Clock.currentTime(Time.TimeUnit.Nanoseconds);
    println("solve1 ${(t1 - t0) / 1_000_000i64} (top=${Vector.length(force1)})");

    // Warm-JIT second solve: merge in a dummy fact so this is a different
    // program value than the one above (defeats common-subexpression reuse),
    // and use the model TWICE so the pure `solve` cannot be inlined into a
    // single `query` — an inlined query solves only the strata its selected
    // predicate needs (forcing through EDB `TopExp` measures ~nothing, and
    // even a derived relation would prune the flow_* strata).
    let t2 = Time.Clock.currentTime(Time.TimeUnit.Nanoseconds);
    let model2 = solve (program <+> #{ TopExp("warmup-dummy"). });
    let force2a = query model2 select (e, c, ak) from StateE(e, c, ak);
    let force2b = query model2 select (v1, v2) from FlowAA(v1, v2);
    let t3 = Time.Clock.currentTime(Time.TimeUnit.Nanoseconds);
    println("solve2 ${(t3 - t2) / 1_000_000i64} (state_e=${Vector.length(force2a)}, flow_aa=${Vector.length(force2b)})");

    report(model1)
}
