open Usuba_AST

let prog_to_c (orig : prog) (normed : prog) (conf : Config.config)
    (filename : string) : string =
  (* let prog = if conf.interleave > 0 then *)
  (*              Interleave.interleave normed conf *)
  (*            else normed in *)
  GenC_standalone.gen_runtime orig normed conf filename
