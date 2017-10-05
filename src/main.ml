
open Usuba_AST
open Ocaml_gen_naive
open Printf
open Parse_file
open Interp
open Utils

let print_naive_ml (file_in: string) (prog: Usuba_AST.prog) (conf:config) =
  (* Generating OCaml code *)
  let full_name = match (String.split_on_char '.' file_in) with
    | []     -> file_in
    | x :: _ ->  x in
  let path = String.split_on_char '/' full_name in
  let out_name = List.nth path (List.length path - 1) in
  let out = open_out ("tests/ocaml_run/" ^ out_name ^ "_naive.ml") in
  fprintf out "%s" (Ocaml_gen_naive.prog_to_str_ml prog conf);
  close_out out

let print_ortho_ml (file_in: string) (prog: Usuba_AST.prog) (conf:config) =
  (* Generating OCaml code *)
  let full_name = match (String.split_on_char '.' file_in) with
    | []   -> file_in
    | x::_ ->  x in
  let path = String.split_on_char '/' full_name in
  let out_name = List.nth path (List.length path - 1) in
  let out = open_out ("tests/ocaml_run/" ^ out_name ^ "_ortho.ml") in
  fprintf out "%s" (Ocaml_gen_ortho.prog_to_str_ml prog conf);
  close_out out

let print_c (file_in: string) (prog: Usuba_AST.prog) (conf:config) : unit =
  (* Generating C code *)
  let full_name = match (String.split_on_char '.' file_in) with
    | []   -> file_in
    | x::_ ->  x in
  let path = String.split_on_char '/' full_name in
  let out_name = List.nth path (List.length path - 1) in
  let out = open_out ("tests/C/" ^ out_name ^ ".c") in
  let normalized = Normalize.norm_prog prog conf in

  (* Usuba_print.print_prog normalized; *)

  let c_prog = Usuba_to_c.prog_to_c prog normalized conf in
  
  fprintf out "%s" c_prog;
  fprintf out "\n\nint main() { return 0; }";
  close_out out
            
let main () =
  Printexc.record_backtrace true;

  let conf = { inline       = true;
               gen_z3       = false;
               check_tables = true;
               verbose      = 1;
               warnings     = false } in

  if conf.verbose >= 5 then print_conf conf;

  Arg.parse []
            (fun s ->
             let prog = parse_file s in
             if not (Type_checker.is_typed prog) then
               raise (Error "Unsound program");
             if conf.gen_z3 then Gen_z3.verify prog s conf;
             print_c s prog conf ) "Usage"
                 

let () = main ()
