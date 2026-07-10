//! Lowering of the [`Ast`] into the flat "extensional database" (EDB) of input
//! facts consumed by the analysis. These relations mirror the `.input`
//! relations declared in Appendix A of the paper.
//!
//! The same [`Facts`] can be loaded into the ascent program (see
//! [`crate::Facts::into_program`]) or written out as Soufflé `.facts` files
//! (see [`Facts::write_souffle`]) so that the original Soufflé program can be
//! run on an equivalent input.

use std::fs;
use std::io::{self, Write};
use std::path::Path;

use crate::ast::{Ast, Sym};

/// Flat input facts. Field names match the Soufflé `.decl` relations.
#[derive(Default, Clone)]
pub struct Facts {
   pub top_exp: Vec<(Sym,)>,
   pub lambda: Vec<(Sym, Sym, Sym)>,          // Id, Vars, BodyId
   pub lambda_arg_list: Vec<(Sym, i64, Sym)>, // Vars, Pos, X
   pub prim: Vec<(Sym, Sym)>,                 // Id, OpName (declared but unused by the rules)
   pub prim_call: Vec<(Sym, Sym, Sym)>,       // Id, PrimId, Args
   pub call: Vec<(Sym, Sym, Sym)>,            // Id, FuncId, Args
   pub call_arg_list: Vec<(Sym, i64, Sym)>,   // Args, Pos, X
   pub var: Vec<(Sym, Sym)>,                  // Id, MetaName
   pub num: Vec<(Sym, i64)>,                  // Id, v
   pub boolean: Vec<(Sym, Sym)>,              // Id, v  (Soufflé relation `bool`)
   pub quotation: Vec<(Sym, Sym)>,            // Id, Expr (declared but unused)
   pub if_: Vec<(Sym, Sym, Sym, Sym)>,        // Id, Guard, True, False
   pub setb: Vec<(Sym, Sym, Sym)>,            // Id, Var, Expr
   pub callcc: Vec<(Sym, Sym)>,               // Id, Expr
   pub let_: Vec<(Sym, Sym, Sym)>,            // Id, BindList, Body
   pub let_list: Vec<(Sym, Sym, Sym)>,        // BindList, X, EId
}

/// Assigns a unique id to every AST node and emits the corresponding facts.
struct Builder {
   facts: Facts,
   counter: usize,
}

impl Builder {
   fn new() -> Self { Builder { facts: Facts::default(), counter: 0 } }

   fn fresh(&mut self, prefix: &str) -> Sym {
      let id = format!("{prefix}{}", self.counter);
      self.counter += 1;
      Arc::from(id.as_str())
   }

   /// Lower an expression, returning its assigned id.
   fn build(&mut self, e: &Ast) -> Sym {
      match e {
         Ast::Var(name) => {
            let id = self.fresh("e");
            self.facts.var.push((id.clone(), name.clone()));
            id
         }
         Ast::Num(n) => {
            let id = self.fresh("e");
            self.facts.num.push((id.clone(), *n));
            id
         }
         Ast::Bool(b) => {
            let id = self.fresh("e");
            self.facts.boolean.push((id.clone(), Arc::from(if *b { "#t" } else { "#f" })));
            id
         }
         Ast::Lam(params, body) => {
            let id = self.fresh("e");
            let body_id = self.build(body);
            let vars_id = self.fresh("p");
            for (pos, p) in params.iter().enumerate() {
               self.facts.lambda_arg_list.push((vars_id.clone(), pos as i64, p.clone()));
            }
            self.facts.lambda.push((id.clone(), vars_id, body_id));
            id
         }
         Ast::App(func, args) => {
            let id = self.fresh("e");
            let func_id = self.build(func);
            let args_id = self.fresh("a");
            for (pos, arg) in args.iter().enumerate() {
               let arg_id = self.build(arg);
               self.facts.call_arg_list.push((args_id.clone(), pos as i64, arg_id));
            }
            self.facts.call.push((id.clone(), func_id, args_id));
            id
         }
         Ast::If(g, t, f) => {
            let id = self.fresh("e");
            let gid = self.build(g);
            let tid = self.build(t);
            let fid = self.build(f);
            self.facts.if_.push((id.clone(), gid, tid, fid));
            id
         }
         Ast::Let(binds, body) => {
            let id = self.fresh("e");
            let body_id = self.build(body);
            let binds_id = self.fresh("l");
            for (name, be) in binds {
               let be_id = self.build(be);
               self.facts.let_list.push((binds_id.clone(), name.clone(), be_id));
            }
            self.facts.let_.push((id.clone(), binds_id, body_id));
            id
         }
         Ast::Set(name, e) => {
            let id = self.fresh("e");
            let eid = self.build(e);
            self.facts.setb.push((id.clone(), name.clone(), eid));
            id
         }
         Ast::Callcc(e) => {
            let id = self.fresh("e");
            let eid = self.build(e);
            self.facts.callcc.push((id.clone(), eid));
            id
         }
         Ast::Prim(op, e0, e1) => {
            let id = self.fresh("e");
            let e0id = self.build(e0);
            let e1id = self.build(e1);
            let args_id = self.fresh("a");
            self.facts.call_arg_list.push((args_id.clone(), 0, e0id));
            self.facts.call_arg_list.push((args_id.clone(), 1, e1id));
            self.facts.prim_call.push((id.clone(), op.clone(), args_id));
            id
         }
      }
   }
}

use std::sync::Arc;

impl Facts {
   /// Lower an AST into input facts, marking the root as `top_exp`.
   pub fn from_ast(root: &Ast) -> Facts {
      let mut b = Builder::new();
      let root_id = b.build(root);
      b.facts.top_exp.push((root_id,));
      b.facts
   }

   /// Total number of input facts (a rough measure of program size).
   pub fn len(&self) -> usize {
      self.top_exp.len()
         + self.lambda.len()
         + self.lambda_arg_list.len()
         + self.prim_call.len()
         + self.call.len()
         + self.call_arg_list.len()
         + self.var.len()
         + self.num.len()
         + self.boolean.len()
         + self.if_.len()
         + self.setb.len()
         + self.callcc.len()
         + self.let_.len()
         + self.let_list.len()
   }

   pub fn is_empty(&self) -> bool { self.len() == 0 }

   /// Write the facts as Soufflé `.facts` (tab-separated) files into `dir`,
   /// using the Soufflé relation names from Appendix A.
   pub fn write_souffle(&self, dir: &Path) -> io::Result<()> {
      fs::create_dir_all(dir)?;

      fn write_rows<R>(dir: &Path, name: &str, rows: &[R], fmt: impl Fn(&R) -> String) -> io::Result<()> {
         let mut f = fs::File::create(dir.join(format!("{name}.facts")))?;
         for r in rows {
            f.write_all(fmt(r).as_bytes())?;
            f.write_all(b"\n")?;
         }
         Ok(())
      }

      write_rows(dir, "top_exp", &self.top_exp, |(a,)| a.to_string())?;
      write_rows(dir, "lambda", &self.lambda, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "lambda_arg_list", &self.lambda_arg_list, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "prim", &self.prim, |(a, b)| format!("{a}\t{b}"))?;
      write_rows(dir, "prim_call", &self.prim_call, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "call", &self.call, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "call_arg_list", &self.call_arg_list, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "var", &self.var, |(a, b)| format!("{a}\t{b}"))?;
      write_rows(dir, "num", &self.num, |(a, b)| format!("{a}\t{b}"))?;
      write_rows(dir, "bool", &self.boolean, |(a, b)| format!("{a}\t{b}"))?;
      write_rows(dir, "quotation", &self.quotation, |(a, b)| format!("{a}\t{b}"))?;
      write_rows(dir, "if", &self.if_, |(a, b, c, d)| format!("{a}\t{b}\t{c}\t{d}"))?;
      write_rows(dir, "setb", &self.setb, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "callcc", &self.callcc, |(a, b)| format!("{a}\t{b}"))?;
      write_rows(dir, "let", &self.let_, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      write_rows(dir, "let_list", &self.let_list, |(a, b, c)| format!("{a}\t{b}\t{c}"))?;
      Ok(())
   }
}
