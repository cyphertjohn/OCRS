type subscript = SAdd of string * int
  | SSVar of string
  ;;

let subscript_order a b =
  match (a, b) with
  | (SSVar a_str, SSVar b_str) ->
      String.compare a_str b_str
  | (SSVar a_str, SAdd (b_str, b_index)) ->
      if a_str <> b_str then String.compare a_str b_str
      else (-1)
  | (SAdd (a_str, a_index), SSVar b_str) ->
      if a_str <> b_str then String.compare a_str b_str
      else 1
  | (SAdd (a_str, a_index), SAdd (b_str, b_index)) ->
      if a_str <> b_str then String.compare a_str b_str
      else compare a_index b_index
  ;;
