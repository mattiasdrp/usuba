open Utils

type ident = Ident.t

type expr =
  | Const of int * Usuba_AST.typ option
  | ExpVar of Usuba_AST.var
  | Tuple of expr list
  | Not of expr
  | Log of Usuba_AST.log_op * expr * expr
  | Arith of Usuba_AST.arith_op * expr * expr
  | Shift of Usuba_AST.shift_op * expr * Usuba_AST.arith_expr
(*| Shuffle of var * int list
  | Bitmask of expr * arith_expr
  | Pack of expr * expr * typ option
  | Fun of ident * expr list
  | Fun_v of ident * arith_expr * expr list *)

type deq_i =
  | Eqn of Usuba_AST.var list * expr * bool
(*| Loop of {
      id : ident;
      start : arith_expr;
      stop : arith_expr;
      body : deq list;
      opts : stmt_opt list;
    } *)

and deq = { content : deq_i; orig : (ident * deq_i) list }

type def_i =
  | Single of Usuba_AST.p * deq list

type def = { id : ident; p_in : Usuba_AST.p; p_out : Usuba_AST.p; opt : Usuba_AST.def_opt list; node : def_i }

let rec ast_to_es = function
  | Usuba_AST.Const (i, t) -> Const(i, t)
  | Usuba_AST.ExpVar v -> ExpVar v
  | Usuba_AST.Tuple el -> Tuple (List.map ast_to_es el)
  | Usuba_AST.Not e -> Not(ast_to_es e)
  | Usuba_AST.Log (op, e1, e2) -> Log(op, ast_to_es e1, ast_to_es e2)
  | Usuba_AST.Arith (op, e1, e2) -> Arith(op, ast_to_es e1, ast_to_es e2)
  | Usuba_AST.Shift (op, e1, e2) -> Shift(op, ast_to_es e1, e2)
(*| Shuffle (var, il) -> 
  | Bitmask (e, ae) ->
  | Pack (e1, e2, o) -> 
  | Fun (id, el) -> 
  | Fun_v (id, ae, el) -> *)
  | _ -> failwith "ast_to_es"

let rec es_to_ast = function
  | Const(i,t) ->  Usuba_AST.Const(i,t)
  | ExpVar v -> Usuba_AST.ExpVar v 
  | Tuple el -> Usuba_AST.Tuple(List.map es_to_ast el)
  | Not e -> Usuba_AST.Not(es_to_ast e)
  | Log(op,e1,e2) -> Usuba_AST.Log(op, es_to_ast e1, es_to_ast e2) 
  | Arith(op, e1, e2) -> Usuba_AST.Arith(op, es_to_ast e1, es_to_ast e2)
  | Shift(op, e1, e2) -> Usuba_AST.Shift(op, es_to_ast e1, e2) 

let eqAst_to_eqEs = function 
    | Usuba_AST.Eqn(v,e,b) -> Eqn(v, ast_to_es e, b)
    | _ -> failwith "eqAst_to_eqEs"

let eqEs_to_eqAst = function 
    | Eqn(v,e,b) -> Usuba_AST.Eqn(v, es_to_ast e, b)

let deq_ast_to_es (v : Usuba_AST.deq) = {
    content = eqAst_to_eqEs v.content;
    orig = List.map (fun (i,d) -> (i, eqAst_to_eqEs d)) v.orig
}

let deq_es_to_ast (v : deq) : Usuba_AST.deq = {
    content = eqEs_to_eqAst v.content;
    orig = List.map (fun (i,d) -> (i, eqEs_to_eqAst d)) v.orig
}

let rec fold_deqs (env_var : Usuba_AST.typ Ident.Hashtbl.t) (deqs : Usuba_AST.deq list) : deq list =
    List.map deq_ast_to_es deqs

let def_ast_to_es = function 
    | Usuba_AST.Single(p,dl) -> Single(p, List.map deq_ast_to_es dl)
    | _ -> failwith "def_ast_to_es"

let def_es_to_ast = function
    | Single(p,dl) -> Usuba_AST.Single(p, List.map deq_es_to_ast dl)


let fold_def (def : Usuba_AST.def) : Usuba_AST.def =
    { def with Usuba_AST.node = def_es_to_ast (def_ast_to_es def.node) }

let run _ prog _ : Usuba_AST.prog = { Usuba_AST.nodes = List.map fold_def prog.Usuba_AST.nodes }
let as_pass = (run, "ES", 0)