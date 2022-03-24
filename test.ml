let chan = open_in "test.mml"
let lexbuf = Lexing.from_channel chan

let prog = Parser.expr Lexer.token lexbuf
let t = Typecheck.typecheck_exp_full prog
(*let s = Print.string_of_expr prog
let _ = Printf.printf "%s\n" s *)
         (*
let _ = Typecheck.typecheck_exp Context.empty_ctx prog
let v = Interp.eval_expr (Interp.unannot_expr prog)
let _ = Print.pprint_value Format.std_formatter v
let _ = Format.pp_print_newline Format.std_formatter ()
          *)
