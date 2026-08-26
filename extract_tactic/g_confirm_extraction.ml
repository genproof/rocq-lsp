(* Rocq 9.2: Mltop.add_known_module is gone; registration is by the
   findlib name alone (the Tacentries.tactic_extend key below). *)

# 3 "g_confirm_extraction.mlg"
 
open Ltac_plugin
open Stdarg


let () = Tacentries.tactic_extend "coq-lsp.confirm-extraction" "confirm_extraction" ~level:0 
         [(Tacentries.TyML (Tacentries.TyIdent ("confirm_extraction", 
                            Tacentries.TyArg (Extend.TUentry (Genarg.get_arg_tag wit_string), 
                            Tacentries.TyNil)), (fun h ist -> 
# 9 "g_confirm_extraction.mlg"
                                          Confirm_extraction.confirm h 
                                                )))]

