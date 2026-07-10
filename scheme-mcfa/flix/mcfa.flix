// m-CFA for Scheme (m = 1) in Flix's first-class Datalog — a port of
// Appendix A of:
//   Davis Ross Silverman, Yihao Sun, Kristopher Micinski, Thomas Gilray.
//   "So You Want To Analyze Scheme Programs With Datalog?"
//   Scheme and Functional Programming Workshop, 2021.
//
// This follows ../souffle/mcfa.dl rule-for-rule (see also ../src/tuned.rs and
// ../egglog/mcfa.egg, other ports of the identical fixpoint). Differences
// forced by Flix:
//
//  * Datalog rule bodies may only mention variables, wildcards, and
//    primitive constants (no enum/tuple destructuring), so the continuation
//    store `stored_kont(ak, kont)` — where `kont` is a tagged union in the
//    paper — is split into one relation per `Kont` variant, keyed by
//    address (KontMt, KontArg, KontFn, ...). Likewise the flat value store
//    `stored_val(VAddress(x, ctx), v)` becomes `StoredVal(x, ctx, v)` with
//    the address flattened into columns (same trick as ../src/tuned.rs).
//  * Values that must be pattern-matched inside a rule body (e.g. "is this
//    state_a a closure?") are destructured via *functional predicates*
//    (`let (a, b) = f(v)` where `f` returns a `Vector` — zero rows filters
//    the rule out, matching Soufflé's implicit type-tag tests).
//  * Soufflé's `;` body disjunctions become one Flix rule per disjunct, or a
//    guard (`if (...)`) when the disjunction is really a truthiness test.
//  * `freevar` is computed in-language (unlike the egglog port, which
//    precomputes it): the two negated Soufflé atoms are projected into
//    helper relations first (`IsParam`, `LetBound`) since Flix negation
//    forbids wildcards in the negated atom.
//
// The rule set is spliced directly into `main` (rather than factored into
// its own top-level `def`) so that its ~30-predicate row-polymorphic schema
// type can be inferred rather than spelled out by hand.

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

// ===================== Value-shape helpers (for functional predicates) =====

/// Truthy per the paper: everything except the boolean `#f` and (per the
/// A-IfT Soufflé disjunction, which omits `PrimVal`) partially-applied
/// primitives.
def isTruthy(v: Value): Bool = match v {
    case Value.VBool(b)        => b == "#t"
    case Value.VPrim(_, _, _)  => false
    case _                     => true
}

/// `state_a`'s value is a closure: yields its (expr, ctx) pair, or no rows.
///
/// NOTE ON A CONFIRMED FLIX 0.75.1 BUG: a variable bound by a functional
/// predicate (`let x = f(v)` / `let (a, b) = f(v)`), when later used as an
/// ARGUMENT of a subsequent positive body atom, is not properly
/// join-constrained — that atom matches against EVERY one of its rows, not
/// just the one(s) consistent with the destructured value (minimal repro:
/// `A(v, k), let x = f(v), B(x, y)` returns a `y` for every row of `B`,
/// not just the one whose key equals `x`). The two call sites below
/// (`closurePartsCC` for A-C/cc, `closurePartsFn` for A-Call) are affected
/// because their output ("elam") is later used as `Lambda(elam, ...)`'s
/// key column; the workaround (applied at the call sites, not here) is to
/// bind a FRESH variable from that atom and compare it against the
/// destructured one with an explicit `if` guard instead of unifying via
/// argument position. `kontPartsCC`/`kontPartsFn` are unaffected because
/// their output is only ever used in rule HEADS, never as a later atom's
/// argument. Duplicating this logic per call site (rather than sharing one
/// `closureParts`/`kontParts`) is NOT required for correctness — it was an
/// earlier (wrong) guess at the cause and is kept only because it is
/// harmless and slightly clarifies which rule each helper belongs to.
def closurePartsCC(v: Value): Vector[(Sym, Ctx)] = match v {
    case Value.VClosure(e, c) => Vector#{(e, c)}
    case _                    => Vector#{}
}

def closurePartsFn(v: Value): Vector[(Sym, Ctx)] = match v {
    case Value.VClosure(e, c) => Vector#{(e, c)}
    case _                    => Vector#{}
}

/// `state_a`'s value is a continuation: yields its address, or no rows.
def kontPartsCC(v: Value): Vector[AddrK] = match v {
    case Value.VKont(k) => Vector#{k}
    case _              => Vector#{}
}

def kontPartsFn(v: Value): Vector[AddrK] = match v {
    case Value.VKont(k) => Vector#{k}
    case _              => Vector#{}
}

// ===================== Fact-file parsing =====================

def bugRow(name: String, line: String): a = bug!("mcfa: bad row in ${name}.facts: '${line}'")

def loadRaw(dir: String, name: String): List[String] \ Fs.FileRead.FileRead =
    match Fs.FileRead.readLines("${dir}/${name}.facts") {
        case Ok(ls)  => List.filter(l -> String.length(l) > 0, ls)
        case Err(_)  => Nil
    }

def splitTab(line: String): List[String] = String.splitOn(substr = "\t", line)

def toI32(s: String): Int32 = match Int32.fromString(s) {
    case Some(i) => i
    case None    => bug!("mcfa: bad int32: '${s}'")
}

def toI64(s: String): Int64 = match Int64.fromString(s) {
    case Some(i) => i
    case None    => bug!("mcfa: bad int64: '${s}'")
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
// Factored into its own top-level `def` (with the full row-polymorphic
// schema spelled out) rather than inlined into `main`: a single JVM method
// containing the whole ruleset plus all the driver code overflows the JVM's
// 64KB method-bytecode limit ("Method too large").

def rules(): #{
    Bool(Sym, Sym), Call(Sym, Sym, Sym), CallArgList(Sym, Int32, Sym), Callcc(Sym, Sym),
    CopyCtx(Ctx, Ctx, Sym), FlowAA(Value, Value), FlowAE(Value, Sym), FlowEA(Sym, Value),
    FlowEE(Sym, Sym), Freevar(Sym, Sym), If(Sym, Sym, Sym, Sym), IsParam(Sym, Sym),
    KontArg(AddrK, Sym, Ctx, Ctx, AddrK), KontCallcc(AddrK, Ctx, AddrK),
    KontFn(AddrK, Value, Int32, Ctx, AddrK), KontIf(AddrK, Sym, Sym, Ctx, AddrK),
    KontLet(AddrK, Sym, Ctx, Sym, Ctx, AddrK), KontMt(AddrK),
    KontPrim1(AddrK, Sym, Sym, Ctx, AddrK), KontPrim2(AddrK, Sym, Value, AddrK),
    KontSet(AddrK, Sym, Ctx, AddrK), Lambda(Sym, Sym, Sym), LambdaArgList(Sym, Int32, Sym),
    Let(Sym, Sym, Sym), LetBound(Sym, Sym), LetList(Sym, Sym, Sym), Num(Sym, Int64),
    PeekCtx(Sym, Ctx, Ctx), PrimCall(Sym, Sym, Sym), Setb(Sym, Sym, Sym),
    StateA(Value, AddrK), StateE(Sym, Ctx, AddrK), StoredVal(Sym, Ctx, Value), TopExp(Sym), Var(Sym, Sym)
} = #{
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

        // ----- flat-closure copy of free variables across a context boundary -----
        StoredVal(fv, to, v) :- CopyCtx(fromCtx, to, e), Freevar(fv, e), StoredVal(fv, fromCtx, v).

        // ----- E-If -----
        StateE(eguard, ctx, AddrK.KAddr(eguard, ctx)) :- StateE(e, ctx, ak), If(e, eguard, et, ef).
        KontIf(AddrK.KAddr(eguard, ctx), et, ef, ctx, ak) :- StateE(e, ctx, ak), If(e, eguard, et, ef).
        FlowEE(e, eguard) :- StateE(e, ctx, ak), If(e, eguard, et, ef).

        // ----- E-C/cc -----
        StateE(elam, ctx, AddrK.KAddr(elam, ctx)) :- StateE(e, ctx, ak), Callcc(e, elam), PeekCtx(e, ctx, ectx).
        KontCallcc(AddrK.KAddr(elam, ctx), ectx, ak) :- StateE(e, ctx, ak), Callcc(e, elam), PeekCtx(e, ctx, ectx).
        FlowEE(e, elam) :- StateE(e, ctx, ak), Callcc(e, elam), PeekCtx(e, ctx, ectx).

        // ----- E-Set! -----
        StateE(esetto, ctx, AddrK.KAddr(esetto, ctx)) :- StateE(e, ctx, ak), Setb(e, x, esetto).
        KontSet(AddrK.KAddr(esetto, ctx), x, ctx, ak) :- StateE(e, ctx, ak), Setb(e, x, esetto).
        FlowEE(e, esetto) :- StateE(e, ctx, ak), Setb(e, x, esetto).

        // ----- E-Call -----
        StateE(efunc, ctx, AddrK.KAddr(efunc, ctx)) :- StateE(e, ctx, ak), Call(e, efunc, eargs), PeekCtx(e, ctx, ectx).
        KontArg(AddrK.KAddr(efunc, ctx), eargs, ctx, ectx, ak) :- StateE(e, ctx, ak), Call(e, efunc, eargs), PeekCtx(e, ctx, ectx).
        FlowEE(e, efunc) :- StateE(e, ctx, ak), Call(e, efunc, eargs), PeekCtx(e, ctx, ectx).

        // ----- E-Let -----
        StateE(ebnd, ctx, AddrK.KAddr(ebnd, ctx)) :-
            StateE(e, ctx, ak), Let(e, ll, ebody), LetList(ll, x, ebnd), PeekCtx(e, ctx, ectx).
        KontLet(AddrK.KAddr(ebnd, ctx), x, ectx, ebody, ectx, ak) :-
            StateE(e, ctx, ak), Let(e, ll, ebody), LetList(ll, x, ebnd), PeekCtx(e, ctx, ectx).
        CopyCtx(ctx, ectx, e) :-
            StateE(e, ctx, ak), Let(e, ll, ebody), LetList(ll, x, ebnd), PeekCtx(e, ctx, ectx).
        FlowEE(e, ebnd) :-
            StateE(e, ctx, ak), Let(e, ll, ebody), LetList(ll, x, ebnd), PeekCtx(e, ctx, ectx).

        // ----- E-Prim -----
        StateE(earg0, ctx, AddrK.KAddr(earg0, ctx)) :-
            StateE(e, ctx, ak), PrimCall(e, op, pl), CallArgList(pl, 0, earg0), CallArgList(pl, 1, earg1).
        KontPrim1(AddrK.KAddr(earg0, ctx), op, earg1, ctx, ak) :-
            StateE(e, ctx, ak), PrimCall(e, op, pl), CallArgList(pl, 0, earg0), CallArgList(pl, 1, earg1).
        FlowEE(e, earg0) :-
            StateE(e, ctx, ak), PrimCall(e, op, pl), CallArgList(pl, 0, earg0), CallArgList(pl, 1, earg1).

        // ----- Atomic evaluation -----
        StateA(Value.VNum(n), ak) :- StateE(e, _, ak), Num(e, n).
        FlowEA(e, Value.VNum(n)) :- StateE(e, _, ak), Num(e, n).

        StateA(Value.VBool(b), ak) :- StateE(e, _, ak), Bool(e, b).
        FlowEA(e, Value.VBool(b)) :- StateE(e, _, ak), Bool(e, b).

        StateA(Value.VClosure(e, ctx), ak) :- StateE(e, ctx, ak), Lambda(e, _, _).
        FlowEA(e, Value.VClosure(e, ctx)) :- StateE(e, ctx, ak), Lambda(e, _, _).

        StateA(v, ak) :- StateE(e, ctx, ak), Var(e, x), StoredVal(x, ctx, v).
        FlowEA(e, v)  :- StateE(e, ctx, ak), Var(e, x), StoredVal(x, ctx, v).

        // ----- A-IfT (truthy = anything but #f and a partially-applied prim) -----
        StateE(et, ctxk, nak) :- StateA(v, ak), KontIf(ak, et, ef, ctxk, nak), if (isTruthy(v)).
        FlowAE(Value.VBool("#t"), et) :- StateA(v, ak), KontIf(ak, et, ef, ctxk, nak), if (isTruthy(v)).

        // ----- A-IfF -----
        StateE(ef, ctxk, nak) :- StateA(v, ak), KontIf(ak, et, ef, ctxk, nak), if (v == Value.VBool("#f")).
        FlowAE(Value.VBool("#f"), ef) :- StateA(v, ak), KontIf(ak, et, ef, ctxk, nak), if (v == Value.VBool("#f")).

        // ----- A-C/cc (closure operand) -----
        //
        // NOTE ON A FLIX 0.75.1 BUG: a variable bound by a functional
        // predicate (`let x = f(...)` / `let (a, b) = f(...)`) is NOT
        // properly join-constrained when later reused as an ARGUMENT of a
        // subsequent body atom — that atom matches as if the variable were
        // still free, silently returning extra, wrong rows (confirmed with a
        // minimal repro: `A(v), let x = f(v), B(x, y)` returns a row for
        // EVERY row of `B`, not just the one whose first column equals `x`).
        // Using the destructured variable only in the *head*, or in a guard
        // (`if (x == x0)`) after binding a FRESH variable `x0` from the atom
        // instead, both work correctly. So below, `Lambda`/`LambdaArgList`
        // are joined via a fresh `elamCC0`/`elamFn0` compared with `if`,
        // never via `elamCC`/`elamFn` used directly as an atom argument.
        StateE(ebodyCC, ectxCC, nakCC) :-
            StateA(vCC, akCC), KontCallcc(akCC, ectxCC, nakCC),
            let (elamCC, ctxcloCC) = closurePartsCC(vCC),
            Lambda(elamCC0, paramsCC, ebodyCC), if (elamCC0 == elamCC),
            LambdaArgList(paramsCC, 0, xCC).
        StoredVal(xCC, ectxCC, Value.VKont(akCC)) :-
            StateA(vCC, akCC), KontCallcc(akCC, ectxCC, nakCC),
            let (elamCC, ctxcloCC) = closurePartsCC(vCC),
            Lambda(elamCC0, paramsCC, ebodyCC), if (elamCC0 == elamCC),
            LambdaArgList(paramsCC, 0, xCC).
        CopyCtx(ctxcloCC, ectxCC, elamCC) :-
            StateA(vCC, akCC), KontCallcc(akCC, ectxCC, nakCC),
            let (elamCC, ctxcloCC) = closurePartsCC(vCC),
            Lambda(elamCC0, paramsCC, ebodyCC), if (elamCC0 == elamCC),
            LambdaArgList(paramsCC, 0, xCC).
        FlowAE(Value.VClosure(elamCC, ctxcloCC), ebodyCC) :-
            StateA(vCC, akCC), KontCallcc(akCC, ectxCC, nakCC),
            let (elamCC, ctxcloCC) = closurePartsCC(vCC),
            Lambda(elamCC0, paramsCC, ebodyCC), if (elamCC0 == elamCC),
            LambdaArgList(paramsCC, 0, xCC).

        // ----- A-C/ccKont (continuation operand) -----
        // (bkK is only used in the head here, so no workaround is needed.)
        StateA(Value.VKont(akK), bkK) :- StateA(vK, akK), KontCallcc(akK, _ectxCCu, _nakCCu), let bkK = kontPartsCC(vK).
        FlowAA(Value.VKont(bkK), Value.VKont(akK)) :- StateA(vK, akK), KontCallcc(akK, _ectxCCu2, _nakCCu2), let bkK = kontPartsCC(vK).

        // ----- A-Ar -----
        StateE(earg, ctx, AddrK.KAddr(earg, ctx)) :-
            StateA(v, ak), KontArg(ak, eargs, ctx, ectx, nak), CallArgList(eargs, pos, earg).
        KontFn(AddrK.KAddr(earg, ctx), v, pos, ectx, nak) :-
            StateA(v, ak), KontArg(ak, eargs, ctx, ectx, nak), CallArgList(eargs, pos, earg).
        FlowAE(v, earg) :-
            StateA(v, ak), KontArg(ak, eargs, ctx, ectx, nak), CallArgList(eargs, pos, earg).

        // ----- A-Call (closure operator) -----
        StateE(ebodyFn, ectxFn, nakFn) :-
            StateA(vFn, akFn), KontFn(akFn, funcFn, posFn, ectxFn, nakFn),
            let (elamFn, ctxcloFn) = closurePartsFn(funcFn),
            Lambda(elamFn0, paramsFn, ebodyFn), if (elamFn0 == elamFn),
            LambdaArgList(paramsFn, posFn, xFn).
        StoredVal(xFn, ectxFn, vFn) :-
            StateA(vFn, akFn), KontFn(akFn, funcFn, posFn, ectxFn, nakFn),
            let (elamFn, ctxcloFn) = closurePartsFn(funcFn),
            Lambda(elamFn0, paramsFn, ebodyFn), if (elamFn0 == elamFn),
            LambdaArgList(paramsFn, posFn, xFn).
        CopyCtx(ctxcloFn, ectxFn, elamFn) :-
            StateA(vFn, akFn), KontFn(akFn, funcFn, posFn, ectxFn, nakFn),
            let (elamFn, ctxcloFn) = closurePartsFn(funcFn),
            Lambda(elamFn0, paramsFn, ebodyFn), if (elamFn0 == elamFn),
            LambdaArgList(paramsFn, posFn, xFn).
        FlowAE(vFn, ebodyFn) :-
            StateA(vFn, akFn), KontFn(akFn, funcFn, posFn, ectxFn, nakFn),
            let (elamFn, ctxcloFn) = closurePartsFn(funcFn),
            Lambda(elamFn0, paramsFn, ebodyFn), if (elamFn0 == elamFn),
            LambdaArgList(paramsFn, posFn, xFn).

        // ----- A-Call (continuation as operator) -----
        // (callccKontCk is only used in the head here, so no workaround is needed.)
        StateA(vCk, callccKontCk) :- StateA(vCk, akCk), KontFn(akCk, funcCk, 0, _ectxCku, _nakCku), let callccKontCk = kontPartsFn(funcCk).
        FlowAA(vCk, vCk) :- StateA(vCk, akCk), KontFn(akCk, funcCk, 0, _ectxCku2, _nakCku2), let callccKontCk = kontPartsFn(funcCk).

        // ----- A-Let -----
        StateE(ebody, ctx, nak) :- StateA(v, ak), KontLet(ak, x, xctx, ebody, ctx, nak).
        StoredVal(x, xctx, v)   :- StateA(v, ak), KontLet(ak, x, xctx, ebody, ctx, nak).
        FlowAE(v, ebody)        :- StateA(v, ak), KontLet(ak, x, xctx, ebody, ctx, nak).

        // ----- A-Prim1 -----
        StateE(earg1, ctx, AddrK.KAddr(earg1, ctx)) :- StateA(v, ak), KontPrim1(ak, op, earg1, ctx, nak).
        KontPrim2(AddrK.KAddr(earg1, ctx), op, v, nak) :- StateA(v, ak), KontPrim1(ak, op, earg1, ctx, nak).
        FlowAE(v, earg1) :- StateA(v, ak), KontPrim1(ak, op, earg1, ctx, nak).

        // ----- A-Prim2 -----
        StateA(Value.VPrim(op, v1, v2), nak) :- StateA(v2, ak), KontPrim2(ak, op, v1, nak).
        FlowAA(v2, Value.VPrim(op, v1, v2))  :- StateA(v2, ak), KontPrim2(ak, op, v1, nak).

        // ----- A-Set! -----
        StateA(Value.VNum(-42i64), nak) :- StateA(v, ak), KontSet(ak, x, xctx, nak).
        StoredVal(x, xctx, v)           :- StateA(v, ak), KontSet(ak, x, xctx, nak).
        FlowAA(v, Value.VNum(-42i64))   :- StateA(v, ak), KontSet(ak, x, xctx, nak).
    }

// ===================== reporting =====================
//
// Also factored out of `main` for the same JVM-method-size reason as `rules`.

def report(model1: #{
    Bool(Sym, Sym), Call(Sym, Sym, Sym), CallArgList(Sym, Int32, Sym), Callcc(Sym, Sym),
    CopyCtx(Ctx, Ctx, Sym), FlowAA(Value, Value), FlowAE(Value, Sym), FlowEA(Sym, Value),
    FlowEE(Sym, Sym), Freevar(Sym, Sym), If(Sym, Sym, Sym, Sym), IsParam(Sym, Sym),
    KontArg(AddrK, Sym, Ctx, Ctx, AddrK), KontCallcc(AddrK, Ctx, AddrK),
    KontFn(AddrK, Value, Int32, Ctx, AddrK), KontIf(AddrK, Sym, Sym, Ctx, AddrK),
    KontLet(AddrK, Sym, Ctx, Sym, Ctx, AddrK), KontMt(AddrK),
    KontPrim1(AddrK, Sym, Sym, Ctx, AddrK), KontPrim2(AddrK, Sym, Value, AddrK),
    KontSet(AddrK, Sym, Ctx, AddrK), Lambda(Sym, Sym, Sym), LambdaArgList(Sym, Int32, Sym),
    Let(Sym, Sym, Sym), LetBound(Sym, Sym), LetList(Sym, Sym, Sym), Num(Sym, Int64),
    PeekCtx(Sym, Ctx, Ctx), PrimCall(Sym, Sym, Sym), Setb(Sym, Sym, Sym),
    StateA(Value, AddrK), StateE(Sym, Ctx, AddrK), StoredVal(Sym, Ctx, Value), TopExp(Sym), Var(Sym, Sym)
}): Unit \ IO = {
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
        case Nil    => bug!("usage: mcfa.flix -- FACTS_DIR")
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

    let program = edb <+> rules();

    // Timing note: `solve` is pure, so the optimizer may common up or sink
    // repeated `solve program` calls — a naive t0/solve/t1 sandwich can print
    // 0 ms while the work actually happens at the first query. Each timed
    // solve below is therefore (a) immediately *forced* by a query whose
    // result is printed, and (b) run on a distinguishable program value so
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
