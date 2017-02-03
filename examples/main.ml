let _ = print_endline "To solve a recurrence enter in a recurrence relation followed by a comma and the input variable." in
let _ = print_endline "Output variables are identified by preceding an undercore." in
let _ = print_endline "Example input: y_{n+1} = y_n + n, n" in
let _ = print_endline "" in


let rec repl str = 
  if str = "" then print_endline "Goodbye!"
  else
    let _ = Solve_rec.solve_rec_str str in
    let _ = print_endline "" in
    let _ = print_string "Enter a recurrence: " in
    let str1 = read_line () in
    repl str1
  in
  
let _ = print_string "Enter a recurrence: " in
let str = read_line () in
repl str
