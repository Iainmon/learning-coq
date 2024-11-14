(* let () = print_endline "Hello, World!"
(* let print_custom _loc args =
  let message = match args with
    | [Constr.Annotated _ loc; Constr.Annotated _ msg] -> (* Extract message *)
        (* Extract and process message from AST *)
        "Custom Message: " ^ (extract_message msg)
    | _ -> "Invalid arguments"
  in
  Feedback.msg_info (str message)

let () =
  Vernac.addvernac ("PrintCustom", print_custom) *)

  open Plugin

  let hello_command =
    Plugin.command "hello"
      ~params:None
      ~body:(fun _proof_state ->
        Plugin.log_info "Hello, Coq!";
        Plugin.return ())
  
  let () =
    Plugin.register_plugin ~name:"my_plugin" ~version:"1.0" ();
    Plugin.add_command hello_command
 *)
 open Plugin

 let hello_command =
   Plugin.command "hello"
     ~params:None
     ~body:(fun _proof_state ->
       Plugin.log_info "Hello, Coq!";
       Plugin.return ())
 
 let () =
   Plugin.register_plugin ~name:"my_plugin" ~version:"1.0" ();
   Plugin.add_command hello_command
 