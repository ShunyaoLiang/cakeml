(*
  Produces an sexp print-out of the bootstrap translated compiler
  definition for the 64-bit version of the compiler.
*)
open preamble compiler64ProgTheory astToSexprLib

val _ = new_theory"sexprBootstrap64";

val filename = "cake-sexpr-64"

val _ = ((write_ast_to_file filename) o rhs o concl) compiler64_prog_def;

val _ = export_theory();
