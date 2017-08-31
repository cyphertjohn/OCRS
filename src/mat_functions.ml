open Type_def

let remove_row_column row column matrix = 
  let size = Array.length matrix in
  let answer = ref [] in
  let _ = 
    for i = 0 to size - 1 do
      if i <> row then
        (let row = ref [] in
        let _ =
          for j = 0 to size - 1 do
            if j <> column then row := !row @ [matrix.(i).(j)]
          done in
        answer := !answer @ [!row])
    done in
  let res = !answer in
  let lis_of_arrays = List.map Array.of_list res in
  Array.of_list lis_of_arrays
  ;;

let rec determinant matrix = 
  if (Array.length matrix) = 2 then
    Op_simplifications.op_automatic_simplify (OpMinus (OpTimes (matrix.(0).(0), matrix.(1).(1)), OpTimes (matrix.(0).(1), matrix.(1).(0))))
  else if (Array.length matrix) = 1 then Op_simplifications.op_automatic_simplify matrix.(0).(0)
  else if (Array.length matrix) = 0 then failwith "Determinant of empty matrix"
  else
    (let sum_list = ref [] in
    let top_row = Array.get matrix 0 in
    let _ = 
      for i = 0 to (Array.length top_row) - 1 do
        let _ = if i mod 2 <> 0 then (Array.set top_row i (Op_simplifications.op_automatic_simplify (OpTimes(OpRational(Mpq.init_set_si (-1) 1), top_row.(i))))) in
        sum_list := !sum_list @ [OpTimes(top_row.(i), determinant (remove_row_column 0 i matrix))]
      done in
    Op_simplifications.op_automatic_simplify (OpSum !sum_list))

let get_matrix_of_cofactors matrix = 
  let size = Array.length matrix in
  let answer = ref [] in
  let _ = 
    for i = 0 to size - 1 do
      let row = ref [] in
      let _ = 
        for j = 0 to size - 1 do
          if (i + j) mod 2 <> 0 then
            row := !row @ [Op_simplifications.op_automatic_simplify (OpTimes(OpRational (Mpq.init_set_si (-1) 1), determinant (remove_row_column i j matrix)))]
          else
            row := !row @ [determinant (remove_row_column i j matrix)]
        done in
      answer := !answer @ [!row]
    done in
  let res = !answer in
  let lis_of_arrays = List.map Array.of_list res in
  Array.of_list lis_of_arrays
  ;;


let dot_product a b = 
  if Array.length a <> Array.length b then failwith "dot_product of vectors of unequal length"
  else
    (
    let a_lis = Array.to_list a in
    let b_lis = Array.to_list b in
    let sum_lis = List.map2 (fun x y -> OpTimes(x, y)) a_lis b_lis in
    Op_simplifications.op_automatic_simplify (OpSum sum_lis)
    )
  ;;

let matrix_times_vector matrix vector = 
  let result_vector = Array.make (Array.length matrix) (OpRational (Mpq.init_set_si 0 1)) in
  let _ = 
    for i = 0 to (Array.length matrix) - 1 do
      Array.set result_vector i (dot_product (Array.get matrix i) vector)
    done in
  result_vector
  ;;


let multiply_scalar_through matrix scalar =
  let size_n = Array.length matrix in 
  let size_m = Array.length (matrix.(0)) in
  let answer = Array.make_matrix size_n size_m (OpRational (Mpq.init_set_si 0 1)) in
  let _ = 
    for i = 0 to size_n - 1 do
      for j = 0 to size_m - 1 do
        answer.(i).(j) <- (Op_simplifications.op_automatic_simplify (OpTimes (scalar, matrix.(i).(j))))
      done
    done in
  answer
  ;;

let multiply_scalar_through_vector vector scalar = 
  Array.map (fun x -> (Op_simplifications.op_automatic_simplify (OpTimes (scalar, x)))) vector
  ;;


let invert_matrix matrix = 
  let scalar = OpPow(determinant matrix, OpRational (Mpq.init_set_si (-1) 1)) in
  let cofactor_transpose_matrix = Mat_helpers.transpose_matrix (get_matrix_of_cofactors matrix) in
  multiply_scalar_through cofactor_transpose_matrix scalar
  ;;


let sub_vectors a b =
  if (Array.length a) <> (Array.length b) then failwith "Adding vectors of different length"
  else
    (
    let a_lis = Array.to_list a in
    let b_lis = Array.to_list b in
    let answer_list = List.map2 (fun x y -> Op_simplifications.op_automatic_simplify (OpMinus(x, y))) a_lis b_lis in
    Array.of_list answer_list
    )
  ;;

let sub_matrix a b =
  if (Array.length a) <> (Array.length b) || (Array.length (a.(0)) <> Array.length (b.(0))) then
    failwith "Matrices have different dimensions"
  else
    (
    let a_lis = Array.to_list (Array.map Array.to_list a) in
    let b_lis = Array.to_list (Array.map Array.to_list b) in
    let answer_list = List.map2 (fun x y -> (List.map2 (fun w z -> Op_simplifications.op_automatic_simplify (OpMinus(w, z))) x y)) a_lis b_lis in
    Array.of_list (List.map Array.of_list answer_list)
    )
  ;;



let add_vectors a b = 
  if (Array.length a) <> (Array.length b) then failwith "Adding vectors of different length"
  else
    (
    let a_lis = Array.to_list a in
    let b_lis = Array.to_list b in
    let answer_list = List.map2 (fun x y -> Op_simplifications.op_automatic_simplify (Op_transforms.make_rat_expr (OpPlus(x, y)))) a_lis b_lis in
    Array.of_list answer_list
    )
  ;;

let add_matrix a b =
  if (Array.length a) <> (Array.length b) || (Array.length (a.(0)) <> Array.length (b.(0))) then
    failwith "Matrices have different dimensions"
  else
    (
    let a_lis = Array.to_list (Array.map Array.to_list a) in
    let b_lis = Array.to_list (Array.map Array.to_list b) in
    let answer_list = List.map2 (fun x y -> (List.map2 (fun w z -> Op_simplifications.op_automatic_simplify (Op_transforms.make_rat_expr (OpPlus (w, z)))) x y)) a_lis b_lis in
    Array.of_list (List.map Array.of_list answer_list)
    )
  ;;


let get_block_matrix mat = 
  let size = Array.length mat in
  let sub_size = if (size mod 2) = 0 then size/2 else size/2 + 1 in
  let mat_1_1 = Array.make_matrix sub_size sub_size (OpRational (Mpq.init_set_si 0 1 )) in
  let mat_1_2 = Array.make_matrix sub_size sub_size (OpRational (Mpq.init_set_si 0 1 )) in
  let mat_2_1 = Array.make_matrix sub_size sub_size (OpRational (Mpq.init_set_si 0 1 )) in
  let mat_2_2 = Array.make_matrix sub_size sub_size (OpRational (Mpq.init_set_si 0 1 )) in
  let _ = 
    for i = 0 to size - 1 do
      for j = 0 to size - 1 do
        if i < sub_size then (
          if j < sub_size then mat_1_1.(i).(j) <- (mat.(i).(j))
          else mat_1_2.(i).(j-sub_size) <- (mat.(i).(j))
        ) else (
          if j < sub_size then mat_2_1.(i-sub_size).(j) <- (mat.(i).(j))
          else mat_2_2.(i-sub_size).(j-sub_size) <- (mat.(i).(j))
        )
      done
    done in
  (mat_1_1, mat_1_2, mat_2_1, mat_2_2)
  ;;

let unblockify mat_1_1 mat_1_2 mat_2_1 mat_2_2 size = 
  let block_size = Array.length mat_1_1 in
  let answer = Array.make_matrix size size (mat_1_1.(0).(0)) in
  let _ = 
    for i = 0 to size - 1 do
      for j = 0 to size - 1 do
        if i < block_size then (
          if j < block_size then answer.(i).(j) <- (mat_1_1.(i).(j))
          else answer.(i).(j) <- (mat_1_2.(i).(j-block_size))
        ) else (
          if j < block_size then answer.(i).(j) <- (mat_2_1.(i-block_size).(j))
          else answer.(i).(j) <- (mat_2_2.(i-block_size).(j-block_size))
        )
      done
    done in
  answer
  ;;



let rec matrix_mult_square a b =
  let size_a = Array.length a in
  let size_b = Array.length b in
  if size_a <> size_b then failwith "this function only multiplies square matrices"
  else if size_a = 1 then ( 
    let answer = Array.make_matrix 1 1 (a.(0).(0)) in
    let _ = answer.(0).(0) <- (Op_simplifications.op_automatic_simplify (OpTimes(a.(0).(0), b.(0).(0)))) in
    answer
  ) else (
    let (a_1_1, a_1_2, a_2_1, a_2_2) = get_block_matrix a in
    let (b_1_1, b_1_2, b_2_1, b_2_2) = get_block_matrix b in
    let c_1_1 = add_matrix (matrix_mult_square a_1_1 b_1_1) (matrix_mult_square a_1_2 b_2_1) in
    let c_1_2 = add_matrix (matrix_mult_square a_1_1 b_1_2) (matrix_mult_square a_1_2 b_2_2) in
    let c_2_1 = add_matrix (matrix_mult_square a_2_1 b_1_1) (matrix_mult_square a_2_2 b_2_1) in
    let c_2_2 = add_matrix (matrix_mult_square a_2_1 b_1_2) (matrix_mult_square a_2_2 b_2_2) in
    unblockify c_1_1 c_1_2 c_2_1 c_2_2 size_a)
  ;;


let matrix_mult a b = 
  let n_a = Array.length a in
  let m_a = Array.length (a.(0)) in
  let m_b = Array.length b in
  let q_b = Array.length (b.(0)) in
  let _ = if m_a <> m_b then failwith "Incompatible matrix multiplication" in
  let make_square_mat mat size n m = 
    let res = Array.make_matrix size size (Op_simplifications.op_automatic_simplify (OpTimes(mat.(0).(0), OpRational (Mpq.init_set_si 0 1)))) in
    let _ = 
      for i = 0 to n - 1 do
        for j = 0 to m - 1 do
          res.(i).(j) <- (mat.(i).(j))
        done
      done in
    res in
  let block_size = max (max n_a m_a) q_b in
  let block_a = make_square_mat a block_size n_a m_a in
  let block_b = make_square_mat b block_size m_b q_b in
  let block_c = matrix_mult_square block_a block_b in
  let answer = Array.make_matrix n_a q_b block_c.(0).(0) in
  let _ = 
    for i = 0 to n_a - 1 do
      for j = 0 to q_b - 1 do 
        answer.(i).(j) <- block_c.(i).(j)
      done
    done in
  answer
  ;;


let part_matrix mat =
  let size = Array.length mat in
  let a_size = if (size mod 2) = 0 then size/2 else size/2 + 1 in
  let a = Array.make_matrix a_size a_size mat.(0).(0) in
  let b = Array.make_matrix a_size (size-a_size) mat.(0).(0) in
  let c = Array.make_matrix (size-a_size) a_size mat.(0).(0) in
  let d = Array.make_matrix (size-a_size) (size-a_size) mat.(0).(0) in
  let _ =
    for i = 0 to size - 1 do
      for j = 0 to size - 1 do
        if i < a_size then (
          if j < a_size then a.(i).(j) <- (mat.(i).(j))
          else b.(i).(j-a_size) <- (mat.(i).(j))
        ) else (
          if j < a_size then c.(i-a_size).(j) <- (mat.(i).(j))
          else d.(i-a_size).(j-a_size) <- (mat.(i).(j))
        )
      done
    done in
  (a, b, c, d)
  ;;


let unpart_matrix a b c d = 
  let a_size = Array.length a in
  let res_size_n = a_size + (Array.length c) in
  let res_size_m = a_size + (Array.length b.(0)) in
  let res = Array.make_matrix res_size_n res_size_m a.(0).(0) in
  let _ =
    for i = 0 to res_size_n - 1 do
      for j = 0 to res_size_m - 1 do
        if i < a_size then (
          if j < a_size then res.(i).(j) <- a.(i).(j)
          else res.(i).(j) <- b.(i).(j-a_size)
        ) else (
          if j < a_size then res.(i).(j) <- c.(i-a_size).(j)
          else res.(i).(j) <- d.(i-a_size).(j-a_size)
        )
      done
    done in
  res
  ;;


let rec invert_matrix_fast matrix =
  let size = Array.length matrix in
  if size = 1 then Array.make_matrix 1 1 (Op_simplifications.op_automatic_simplify (OpPow(matrix.(0).(0), OpRational (Mpq.init_set_si (-1) 1))))
  else (
    let (a, b, c, d) = part_matrix matrix in
    let a_inv = invert_matrix_fast a in
    let c_a_inv = matrix_mult c a_inv in
    let a_inv_b = matrix_mult a_inv b in
    let schur = sub_matrix d (matrix_mult c_a_inv b) in
    let schur_inv = invert_matrix_fast schur in
    let a_inv_b_schur_inv = matrix_mult a_inv_b schur_inv in
    let inv_mat_1_1 = add_matrix a_inv (matrix_mult a_inv_b_schur_inv c_a_inv) in
    let minus_inv_mat_1_2 = Array.map Array.copy a_inv_b_schur_inv in
    let minus_inv_mat_2_1 = matrix_mult schur_inv c_a_inv in
    let inv_mat_1_2 = multiply_scalar_through minus_inv_mat_1_2 (OpRational (Mpq.init_set_si (-1) 1 )) in
    let inv_mat_2_1 = multiply_scalar_through minus_inv_mat_2_1 (OpRational (Mpq.init_set_si (-1) 1 )) in
    unpart_matrix inv_mat_1_1 inv_mat_1_2 inv_mat_2_1 schur_inv
  )
  ;;

