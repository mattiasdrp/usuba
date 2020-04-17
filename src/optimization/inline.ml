(* ************************************************************************** *)
(*                                  INLINING                                  *)
(*                                                                            *)
(* I see two ways of doing inlining:                                          *)
(*   - iterating through the nodes' bodies, and inlining functions calls as   *)
(*      they appear.                                                          *)
(*   - iterating through the nodes, and for each nodes, inline every call     *)
(*      made to it by parcouring the other nodes' bodies.                     *)
(* I chose the latter; not sure what more efficient though.                   *)
(* ************************************************************************** *)


open Usuba_AST
open Basic_utils
open Utils
open Pass_runner

(* This module checks if a node _must_ be inlined and if so, returns
   it. For now, a node must be inlined if it uses shifts of sizes
   depending on the parameters. *)
module Must_inline = struct
  let rec contains_in (env_in:(ident,bool) Hashtbl.t) (ae:arith_expr) : bool =
    match ae with
    | Const_e _   -> false
    | Var_e v     -> Hashtbl.mem env_in v
    | Op_e(_,x,y) -> (contains_in env_in x) || (contains_in env_in y)

  (* |e| is a variable that is being shifted. Need to check if it's a
  tuple, or it's dir is Bitslice. *)
  (* TODO: this should be done somewhere else / some other way. *)
  let must_inline_shift (env_var:(ident,typ) Hashtbl.t)
                        (env_in:(ident,bool) Hashtbl.t)
                        (e:expr) (ae:arith_expr) : bool =
    (contains_in env_in ae) &&
      match e with
      | Tuple l -> true
      | _       ->
         (* Note that at this point, there is a chance that we are
         bitslicing but Monomorphize hasn't ran already. In this case,
         this will return false, but we don't care, as later call to
         this module will work correctly. *)
         get_normed_expr_dir env_var e = Bslice

  let rec must_inline_expr (env_var:(ident,typ) Hashtbl.t)
                           (env_in:(ident,bool) Hashtbl.t)
                           (e:expr) : bool =
    match e with
    | Const _        -> false
    | ExpVar _       -> false
    | Tuple l        -> List.exists (must_inline_expr env_var env_in) l
    | Not e'         -> must_inline_expr env_var env_in e'
    | Shift(_,e',ae) -> (must_inline_expr env_var env_in e') ||
                          (must_inline_shift env_var env_in e' ae)
    | Log(_,x,y)     -> (must_inline_expr env_var env_in x) ||
                          (must_inline_expr env_var env_in y)
    | Shuffle _      -> false
    | Arith(_,x,y)   -> (must_inline_expr env_var env_in x) ||
                          (must_inline_expr env_var env_in y)
    | Fun(_,l)       -> List.exists (must_inline_expr env_var env_in) l
    | Fun_v(_,_,l)   -> List.exists (must_inline_expr env_var env_in) l

  let rec must_inline_deqs (env_var:(ident,typ) Hashtbl.t)
                           (env_in:(ident,bool) Hashtbl.t)
                           (deqs:deq list) : bool =
    List.exists (fun d -> match d.content with
                  | Eqn(_,e,_) -> must_inline_expr env_var env_in e
                  | Loop(_,_,_,dl,_) -> must_inline_deqs env_var env_in dl) deqs

  let must_inline_def (def:def) : bool =
    match def.node with
    | Single(vars,body) ->
       let env_var = build_env_var def.p_in def.p_out vars in
       let env_in  = Hashtbl.create 10 in
       List.iter (fun vd -> Hashtbl.add env_in vd.vd_id true) def.p_in;
       must_inline_deqs env_var env_in body
    | _ -> false

  let must_inline (prog:prog) : def option =
    List.find_opt must_inline_def prog.nodes
end

let gen_iterator =
  let cpt = ref 0 in
  fun id ->
    incr cpt;
    fresh_ident (Printf.sprintf "%s%d" id.name !cpt)

let rec update_aexpr_idx (it_env:(var,var) Hashtbl.t)
                         (ae:arith_expr) : arith_expr =
  match ae with
  | Const_e _ -> ae
  | Var_e id  -> (match Hashtbl.find_opt it_env (Var id) with
                  | Some (Var v) -> Var_e v
                  | _ -> Var_e id)
  | Op_e(op,x,y) -> Op_e(op,update_aexpr_idx it_env x,update_aexpr_idx it_env y)

let rec update_in_var (it_env:(var,var) Hashtbl.t)
                      (v:var) : var =
  match v with
  | Var _ -> v
  | Index(v',ae) -> Index(update_in_var it_env v',update_aexpr_idx it_env ae)
  | _ -> assert false

let rec  update_var_to_var (it_env:(var,var) Hashtbl.t)
                      (var_env : (var,var) Hashtbl.t)
                      (v:var) : var =
  let v = update_in_var it_env v in
  match Hashtbl.find_opt it_env v with
  | Some v' -> v'
  | None ->
     match Hashtbl.find_opt var_env v with
     | Some v' -> v'
     | None -> match v with
               | Var _ -> Printf.fprintf stderr "Fail: %s\n" (Usuba_print.var_to_str v);
                          assert false
               | Index(v',ae) -> Index(update_var_to_var it_env var_env v',ae)
               | _ -> assert false

let rec update_var_to_expr (it_env:(var,var) Hashtbl.t)
                           (var_env : (var,var) Hashtbl.t)
                           (expr_env: (var,expr) Hashtbl.t)
                           (v:var) : expr =
  match Hashtbl.find_opt it_env v with
  | Some v' -> ExpVar v'
  | None ->
     match Hashtbl.find_opt expr_env v with
     | Some e -> e
     | None ->
        match Hashtbl.find_opt var_env v with
        | Some v' -> ExpVar v'
        | None ->
           match v with
           | Var id -> assert false
           | Index(v',ae) ->
              begin
                match update_var_to_expr it_env var_env expr_env v' with
                | ExpVar v'' -> ExpVar(Index(v'',update_aexpr it_env var_env expr_env ae))
                | _ -> assert false
              end
           | _ -> assert false

and expr_to_aexpr (e:expr) : arith_expr =
  match e with
  | Const(c,_) -> Const_e c
  | ExpVar(Var v) -> Var_e v
  | Arith(op,x,y) -> Op_e(op,expr_to_aexpr x,expr_to_aexpr y)
  | _ -> assert false

(* TODO: this is quite messy, as we are mixing aexpr and expr ... *)
and update_aexpr(it_env:(var,var) Hashtbl.t)
                (var_env : (var,var) Hashtbl.t)
                (expr_env: (var,expr) Hashtbl.t)
                (ae:arith_expr) : arith_expr =
  let rec_call = update_aexpr it_env var_env expr_env in
  match ae with
  | Const_e _ -> ae
  | Var_e v -> expr_to_aexpr (update_var_to_expr it_env var_env expr_env (Var v))
  | Op_e(op,x,y) -> Op_e(op,rec_call x, rec_call y)

(* Convert variables names inside an expression *)
let rec update_expr (it_env:(var,var) Hashtbl.t)
                    (var_env : (var,var) Hashtbl.t)
                    (expr_env: (var,expr) Hashtbl.t)
                    (e:expr) : expr =
  let rec_call = update_expr it_env var_env expr_env in
  match e with
  | Const _ -> e
  | ExpVar v -> update_var_to_expr it_env var_env expr_env v
  | Shuffle(v,l) -> begin match update_var_to_expr it_env var_env expr_env v with
                          | ExpVar v' -> Shuffle(v',l)
                          | _ -> assert false end

     (*( match Hashtbl.find_opt expr_env v with
                      | Some (ExpVar v) -> Shuffle(v,l)
                      | None -> Shuffle(Hashtbl.find var_env v,l)
                      | _ -> assert false)*)
  | Tuple l -> Tuple (List.map rec_call l)
  | Not e -> Not (rec_call e)
  (* TODO: Should do something with 'ae' *)
  | Shift(op,e,ae) -> Shift(op,rec_call e,update_aexpr it_env var_env expr_env ae)
  | Log(op,x,y) -> Log(op,rec_call x,rec_call y)
  | Arith(op,x,y) -> Arith(op,rec_call x,rec_call y)
  | Fun(f,l) -> Fun(f,List.map rec_call l)
  | _ -> print_endline (Usuba_print.expr_to_str e);
         assert false

(* Convert the variable names, and update deq's orig with |f| (since
   those deqs are being inlined from |f| into another node). *)
let rec update_vars_and_deqs (it_env:(var,var) Hashtbl.t)
                    (var_env : (var,var) Hashtbl.t)
                    (expr_env: (var,expr) Hashtbl.t)
                    (f:ident)
                    (body:deq list) : deq list =
  List.map (
      fun d -> {
        orig = (f,d.content) :: d.orig;
        content =
          match d.content with
          | Eqn(lhs,e,sync) -> Eqn( List.map (update_var_to_var it_env var_env) lhs,
                                    update_expr it_env var_env expr_env e, sync )
          | Loop(i,ei,ef,dl,opts) ->
             let i' = gen_iterator i in
             Hashtbl.add it_env (Var i) (Var i');
             let updated = Loop(i',ei,ef,update_vars_and_deqs it_env var_env
                                                              expr_env f dl,opts) in
             Hashtbl.remove it_env (Var i);
             updated }
    ) body


(* Inline a specific call (defined by lhs & args) *)
let inline_call (to_inl:def) (args:expr list) (lhs:var list) (cpt:int) :
      p * deq list =
  (* Define a name conversion function *)
  let conv_name (id:ident) : ident =
    { id with name = Printf.sprintf "%s_%d_%s" to_inl.id.name cpt id.name } in

  (* Extract body, vars, params and name of the node to inline *)
  let (vars_inl,body_inl) = match to_inl.node with
    | Single(vars,body) -> vars, body
    | _ -> assert false in
  let p_in  = to_inl.p_in  in
  let p_out = to_inl.p_out in

  (* alpha-conversion environments *)
  let var_env = Hashtbl.create 100 in
  let expr_env = Hashtbl.create 100 in
  (* p_out replaced by the lhs *)
  List.iter2 ( fun vd v -> Hashtbl.add var_env (Var vd.vd_id) v ) p_out lhs;
  (* p_in replaced by the expressions of arguments *)
  List.iter2 ( fun vd e -> Hashtbl.add expr_env (Var vd.vd_id) e) p_in args;
  (* Create a list containing the new variables names *)
  let vars = List.map (fun vd -> { vd with vd_id = conv_name vd.vd_id;
                                           vd_orig = (to_inl.id,vd) :: vd.vd_orig}) vars_inl in
  (* nodes variables alpha-converted *)
  List.iter2 ( fun vd vd' ->
               Hashtbl.add var_env (Var vd.vd_id) (Var vd'.vd_id)) vars_inl vars;

  vars, update_vars_and_deqs (Hashtbl.create 10) var_env expr_env to_inl.id body_inl


(* Inline all the calls to "to_inl" in a given node
   (desribed by its variables and body "vars,body") *)
let rec inline_in_node (deqs:deq list) (to_inl:def) : p * deq list =
  let f_inl = to_inl.id.name in
  (* maintain a counter for variables alpha-conversion *)
  let cpt   = ref 0 in

  let (vars,deqs) =
    (* Unpack the list bellow into a single list of vars and
       a list of deqs *)
    List.split
      (* Find the calls to f_inl, and inline them.
       This will introduce new variables, which is
       why maps returns a (p * deq list) list. *)
      ( List.map (
            fun eqn -> match eqn.content with
                       | Eqn(lhs,Fun(f,l),_) when f.name = f_inl ->
                          incr cpt;
                          inline_call to_inl l lhs !cpt
                       | Eqn _ -> [], [eqn]
                       | Loop(i,ei,ef,dl,opts) ->
                          let (vars, deqs) = inline_in_node dl to_inl in
                          vars, [ { eqn with content = Loop(i,ei,ef,deqs,opts) } ]
          ) deqs ) in
  List.flatten vars, List.flatten deqs


(* Perform the inlining of node "to_inline" at every call point *)
(* And removes the node from the program *)
let do_inline (prog:prog) (to_inline:def) : prog =

  { nodes =
      List.filter (fun def -> def.id <> to_inline.id) @@
        List.map (fun def ->
                  match def.node with
                  | Single(vars,body) ->
                     let (vars',body') = inline_in_node body to_inline in
                     { def with node = Single(vars @ vars',body') }
                  | _ -> def) prog.nodes }


(* Heuristically decides (ie returns true of false) if |def| should be
   inlined or not. *)
let should_inline_heuristic (def:def) : bool =

  (* |is_full_assign| returns true if |deqs| only contains assignments *)
  let rec is_full_assign (deqs:deq list) : bool =
    List.for_all (fun deq ->
                  match deq.content with
                  | Eqn(_,ExpVar _,_) -> true
                  | Loop(_,_,_,dl,_) -> is_full_assign dl
                  | _ -> false) deqs in

  if (List.length def.p_in) + (List.length def.p_out) > 8 then
    (* More than 8 parameters -> will need to be passed on the stack
       -> inlining *)
    true
  else if is_single def.node && is_full_assign (get_body def.node) then
    (* Node only contains assignments -> it's a permutation of some
       kind -> inlining *)
    true
  else
    false

(* Returns true if def doesn't contain any function call,
   or if those calls are to functions that are not going
   to be inlined *)
let rec is_call_free env inlined conf (def:def) : bool =
  let rec deq_call_free (deq:deq) : bool =
    match deq.content with
    | Eqn(_,Fun(f,_),_) ->
       if f.name = "refresh" then true
       else not (can_inline env inlined conf (Hashtbl.find env f.name))
    | Eqn _ -> true
    | Loop(_,_,_,dl,_) -> List.for_all deq_call_free dl in
  match def.node with
  | Single(_,body) -> List.for_all deq_call_free body
  | _ -> false

(* Returns true if the node can be inlined now. ie:
    - is not already inlined
    - it doesn't have the attribute "no_inline"
       (and "inline_all" isn't set to true)
    - it doesn't contain any function call, or
    - every function call it contains is to a node that should not be inlined
    - the heuristic decides that this node is worth being inlined *)
and can_inline env inlined conf (node:def) : bool =
  if Hashtbl.find inlined node.id.name then
    false (* Already inlined *)
  else if conf.light_inline then
    is_inline node (* Only inline if node is marked as "_inline" *)
  else if conf.inline_all then
    true (* All nodes are inlined if -inline-all is active *)
  else if is_call_free env inlined conf node then
    (* Node doesn't contain any function call that should be inlined
       -> heuristically deciding to inline it or not *)
    should_inline_heuristic node
  else
    false

(* Inlines only the functions that must be inlined. For now, those are
   functions that use tuple shifts with a shift size depending on a
   parameter *)
let rec vital_inline (prog:prog) (conf:config) : prog =
  match Must_inline.must_inline prog with
  | None      -> prog
  | Some node ->
     try vital_inline (do_inline prog node) conf with
       _ -> prog (* Program not normalized -> can't inline now *)


(* Inline every node that should be and hasn't already been
   (inlined contains the status of each node: inlined or not) *)
let rec _inline (prog:prog) (conf:config) inlined : prog =

  (* A list of every node, needed for "is_call_free" *)
  let env = Hashtbl.create 20 in
  List.iter (fun x -> Hashtbl.add env x.id.name x) prog.nodes;

  (* If there is a node that can be inlined *)
  if List.exists (can_inline env inlined conf) prog.nodes then
    (* find the node to inline *)
    let to_inline = List.find (can_inline env inlined conf) prog.nodes in
    (* inline it *)
    let prog' = do_inline prog to_inline in
    (* add it to the hash of inlined nodes *)
    Hashtbl.replace inlined to_inline.id.name true;
    (* continue inlining *)
    _inline prog' conf inlined
  else
    (* inlining is done, return the prog *)
    prog


(* Main inlining function. _inline actually does most of the job *)
let run _ (prog:prog) (conf:config) : prog =
  if conf.no_inline then prog
  else
    (* Hashtbl containing the inlining status of each node:
     false if it is not already inlined, true if it is *)
    let inlined = Hashtbl.create 20 in
    List.iter (fun x -> Hashtbl.add inlined x.id.name false) prog.nodes;
    (* The last node is the entry point, it wouldn't make sense to try inline it *)
    Hashtbl.replace inlined (last prog.nodes).id.name true;

    (* And now, perform the inlining *)
    _inline prog conf inlined


let run_with_cont (runner:pass_runner) (prog:prog) (conf:config) nexts : prog =
  if not conf.bench_inline then
    runner#run_modules_guard nexts (run runner prog conf)
  else
    (assert conf.bench_inline;
     let fully_inlined = run runner prog { conf with inline_all = true } in
     let no_inlined    = run runner prog { conf with no_inline  = true } in
     let auto_inlined  = run runner prog conf in

     let fully_inlined = runner#run_modules_guard nexts fully_inlined in
     let no_inlined    = runner#run_modules_guard nexts no_inlined in
     let auto_inlined  = runner#run_modules_guard nexts auto_inlined in

     Printf.printf "Benchmarking dat shit...\n";

     let (perfs_full, perfs_no, perfs_auto) =
       list_to_tuple3
         (Perfs.compare_perfs [ fully_inlined; no_inlined; auto_inlined ]) in

     Printf.printf "Benchmarks res: %.2f vs %.2f vs %.2f\n" perfs_full perfs_no perfs_auto;

     if perfs_full < perfs_auto then
       if perfs_full < perfs_no then
         fully_inlined
       else
         no_inlined
     else
       if perfs_no < perfs_auto then
         no_inlined
       else
         auto_inlined)



let as_pass = (run, "Inline")
