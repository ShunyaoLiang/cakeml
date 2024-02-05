val prog = ``
  (Dec (strlit "x") (Const 14w)
    Skip)
``;
val empty_context = ``
  <| locals_memory := {(FEMPTY, \w. Word 0w)} ;
     be            := T ;
     base_addr     := 0w ;
     ffi           := the_value |>
``;
EVAL ``working_set ^prog ^empty_context``;
