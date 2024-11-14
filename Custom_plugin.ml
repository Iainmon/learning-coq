(* Custom_plugin.ml *)

open Coq
open Pp
open Libnames

let print_custom _loc args =
  let message = match args with
    | [Constr.Annotated _ loc; Constr.Annotated _ msg] -> (* Extract message *)
        (* Extract and process message from AST *)
        "Custom Message: " ^ (extract_message msg)
    | _ -> "Invalid arguments"
  in
  Feedback.msg_info (str message)

let () =
  Vernac.addvernac ("PrintCustom", print_custom)

  