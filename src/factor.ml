open Type_def

let irem a p = 
  let ans = Mpz.init () in
  let _ = Mpz.gmod ans a p in
  ans
  ;;

let mpz_sub a b = 
  let ans = Mpz.init () in
  let _ = Mpz.sub ans a b in
  ans
  ;;

let mpz_mul a b = 
  let ans = Mpz.init () in
  let _ = Mpz.mul ans a b in
  ans
  ;;

let multiplicative_inverse_p t p = 
  let ans = Mpz.init () in
  let p_minus_2 = Mpz.init () in
  let _ = Mpz.sub_ui p_minus_2 p 2 in
  let _ = Mpz.powm ans t p_minus_2 p in
  ans
  ;;

let divide_p a b p = 
  let b_inv = multiplicative_inverse_p b p in
  irem (mpz_mul a b_inv) p
  ;;


let poly_to_z_p poly p = 
  match poly with
  | OpSum sum_list ->
    let aux term = 
    (match term with
    | OpProduct [OpRational coef; Q] ->
      let temp = Mpz.init () in
      let _ = Mpq.get_z temp coef in
      OpProduct [OpRational (Mpq.init_set_z (irem temp p)); Q]
    | OpProduct [OpRational coef; OpPow(Q, exp)] ->
      let temp = Mpz.init () in
      let _ = Mpq.get_z temp coef in
      OpProduct [OpRational (Mpq.init_set_z (irem temp p)); OpPow(Q, exp)]
    | Q -> Q
    | OpPow(Q, exp) -> OpPow(Q, exp)
    | OpRational coef ->
      let temp = Mpz.init () in
      let _ = Mpq.get_z temp coef in
      OpRational (Mpq.init_set_z (irem temp p))
    | _ -> failwith "input wasn't an integer polynomial"
    ) in
    OpSum (List.map aux sum_list)
  | OpProduct [OpRational coef; Q] ->
    let temp = Mpz.init () in
    let _ = Mpq.get_z temp coef in
    OpProduct [OpRational (Mpq.init_set_z (irem temp p)); Q]
  | OpProduct [OpRational coef; OpPow(Q, exp)] ->
    let temp = Mpz.init () in
    let _ = Mpq.get_z temp coef in
    OpProduct [OpRational (Mpq.init_set_z (irem temp p)); OpPow(Q, exp)]
  | Q -> Q
  | OpPow(Q, exp) -> OpPow(Q, exp)
  | OpRational coef ->
    let temp = Mpz.init () in
    let _ = Mpq.get_z temp coef in
    OpRational (Mpq.init_set_z (irem temp p))
  | _ -> failwith "input wasn't a polynomial"
  ;;


let sym_rep b m = 
  let new_b = irem b m in
  let pivot = Mpz.init () in
  let _ = Mpz.fdiv_q pivot m (Mpz.init_set_si 2) in
  if (Mpz.cmp new_b pivot) <= 0 then new_b
  else (
    let res = Mpz.init() in
    let _ = Mpz.sub res new_b m in
    res
  )
  ;;


let poly_to_z_sym_p poly p =
  match poly with
  | OpSum sum_list ->
    let aux term =
    (match term with
    | OpProduct [OpRational coef; Q] ->
      let temp = Mpz.init () in
      let _ = Mpq.get_z temp coef in
      OpProduct [OpRational (Mpq.init_set_z (sym_rep temp p)); Q]
    | OpProduct [OpRational coef; OpPow(Q, exp)] ->
      let temp = Mpz.init () in
      let _ = Mpq.get_z temp coef in
      OpProduct [OpRational (Mpq.init_set_z (sym_rep temp p)); OpPow(Q, exp)]
    | Q -> Q
    | OpPow(Q, exp) -> OpPow(Q, exp)
    | OpRational coef ->
      let temp = Mpz.init () in
      let _ = Mpq.get_z temp coef in
      OpRational (Mpq.init_set_z (sym_rep temp p))
    | _ -> failwith "input wasn't an integer polynomial"
    ) in
    OpSum (List.map aux sum_list)
  | OpProduct [OpRational coef; Q] ->
    let temp = Mpz.init () in
    let _ = Mpq.get_z temp coef in
    OpProduct [OpRational (Mpq.init_set_z (sym_rep temp p)); Q]
  | OpProduct [OpRational coef; OpPow(Q, exp)] ->
    let temp = Mpz.init () in
    let _ = Mpq.get_z temp coef in
    OpProduct [OpRational (Mpq.init_set_z (sym_rep temp p)); OpPow(Q, exp)]
  | Q -> Q
  | OpPow(Q, exp) -> OpPow(Q, exp)
  | OpRational coef ->
    let temp = Mpz.init () in
    let _ = Mpq.get_z temp coef in
    OpRational (Mpq.init_set_z (sym_rep temp p))
  | _ -> failwith "input wasn't a polynomial"
  ;;


let get_mpz_of_rat_expr expr =
  match expr with
  | OpRational rat ->
    let res = Mpz.init () in
    let _ = Mpq.get_z res rat in
    res
  | _ -> failwith "poly_div_p polynomial not in Z"
  ;;

let poly_div_p u v p =
  let x = Op_transforms.degree u in
  let y = Op_transforms.degree v in
  let n = snd y in
  let lcv = get_mpz_of_rat_expr (fst y) in
  let rec aux acc m r =
    let is_zero expr =
      match expr with
      | OpRational rat when (Mpq.cmp_si rat 0 1)=0 -> true
      | _ -> false in
    if (Mpq.cmp m n)<0 || (is_zero r) then (acc, r)
    else (
      let lcr = get_mpz_of_rat_expr (fst (Op_transforms.degree r)) in
      let s = divide_p lcr lcv p in
      let new_acc = Op_simplifications.op_automatic_simplify (OpSum[acc; OpProduct[OpRational (Mpq.init_set_z s); OpPow(Q, OpMinus(OpRational m, OpRational n))]]) in
      let new_r = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpMinus(OpMinus(r, OpProduct[OpRational (Mpq.init_set_z lcr); OpPow(Q, OpRational m)]), OpProduct[OpMinus(v, OpProduct[OpRational (Mpq.init_set_z lcv);OpPow(Q, OpRational n)]);OpRational (Mpq.init_set_z s);OpPow(Q, OpMinus(OpRational m, OpRational n))])))) in
      let new_r_p = Op_simplifications.op_automatic_simplify (poly_to_z_p new_r p) in
      let new_acc_p = Op_simplifications.op_automatic_simplify (poly_to_z_p new_acc p) in
      let new_m = snd (Op_transforms.degree new_r_p) in
      aux new_acc_p new_m new_r_p ) in
  aux (OpRational (Mpq.init_set_si 0 1)) (snd x) u
  ;;

let poly_gcd_p u v p =
  if (op_expr_order (Op_simplifications.op_automatic_simplify (poly_to_z_p u p)) (OpRational (Mpq.init_set_si 0 1))) = 0 && (op_expr_order (Op_simplifications.op_automatic_simplify (poly_to_z_p v p)) (OpRational (Mpq.init_set_si 0 1))) = 0 then (OpRational (Mpq.init_set_si 0 1))
  else (
    let rec aux little_u little_v = 
      if (op_expr_order (Op_simplifications.op_automatic_simplify (poly_to_z_p little_v p)) (OpRational (Mpq.init_set_si 0 1))) = 0 then (
        let new_coef = divide_p (Mpz.init_set_si 1) (get_mpz_of_rat_expr (fst (Op_transforms.degree little_u))) p in
        Op_simplifications.op_automatic_simplify (poly_to_z_p (Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpProduct [OpRational (Mpq.init_set_z new_coef); little_u])))) p)
      ) else (
        let r = snd (poly_div_p little_u little_v p) in
        let new_u = little_v in
        let new_v = r in
        aux new_u new_v
      )
    in
    aux u v
  )
  ;;



(* n has to be less than max int *)
let auxiliary_basis r n p =
  let big_p = Array.make n (-1) in
  let s = ref [] in
  let _ = 
    for j = 0 to n - 1 do
      let i = ref 0 in
      let pivot_found = ref false in
      let _ = 
        while (not !pivot_found) && (!i < n) do
          if (Mpz.cmp_si (r.(!i).(j)) 0) <> 0 && big_p.(!i) = (-1) then pivot_found := true
          else i := !i + 1
        done in
      if !pivot_found then (
        let _ = big_p.(!i) <- j in
        let a = multiplicative_inverse_p (r.(!i).(j)) p in
        let _ = 
          for l = 0 to n - 1 do
            r.(!i).(l) <- (irem (mpz_mul a (r.(!i).(l))) p)
          done in 
        for k = 0 to n - 1 do
          if k <> !i then (
            let f = r.(k).(j) in
            for l = 0 to n - 1 do
              r.(k).(l) <- (irem (mpz_sub (r.(k).(l)) (mpz_mul f (r.(!i).(l)))) p)
            done
          )
        done
      ) else if (not !pivot_found) then (
        let little_s = ref (OpPow (Q, OpRational (Mpq.init_set_si j 1))) in
        let _ = 
          for l = 0 to j - 1 do
            let e = ref (-1) in
            let _ = (i := 0) in
            let _ = 
              while !e = (-1) && !i < n do
                if big_p.(!i) = l then e := !i
                else i := !i + 1
              done in
            if !e >= 0  then (
              let neg_val = Mpz.init () in
              let _ = Mpz.neg neg_val (r.(!e).(j)) in
              let c = irem neg_val p in
              little_s := OpPlus(!little_s, OpTimes(OpRational(Mpq.init_set_z c), OpPow(Q, OpRational (Mpq.init_set_si l 1))))
            )
          done in
        s := (Op_simplifications.op_automatic_simplify !little_s) :: !s
      )
    done in
  List.rev !s
  ;;


let find_factors u big_s p =
  let r = List.length big_s in
  let factors = ref [u] in
  let finished = ref false in
  let _ = 
    for k = 1 to (r - 1) do
      if (not !finished) then (
        let b = List.nth big_s k in
        let old_factors = ref !factors in
        for i = 0 to (List.length !old_factors) - 1 do
          if (not !finished) then (
            let w = ref (List.nth !old_factors i) in
            let j = ref 0 in
            while (Mpz.cmp_si p !j) > 0 do
              let g = poly_gcd_p (Op_simplifications.op_automatic_simplify (poly_to_z_p (Op_simplifications.op_automatic_simplify (OpMinus (b, OpRational (Mpq.init_set_si !j 1)))) p)) !w p in
              if (op_expr_order g (OpRational (Mpq.init_set_si 1 1))) = 0 then j := !j + 1
              else if (op_expr_order g !w) = 0 then j := (Mpz.get_int p)
              else (
                let _ = (factors := List.filter (fun x -> (op_expr_order !w x) <> 0) !factors) in
                let q = fst (poly_div_p !w g p) in
                let _ = factors := !factors @ [g; q] in
                if List.length !factors = r then (let _ = finished := true in (j := Mpz.get_int p))
                else (let _ = j := !j + 1 in w := q)
              )
            done
          )
        done
      )
    done in
  !factors
  ;;


let get_coef_array_of_poly expr length =
  let res = Array.make length (Mpz.init_set_si 0) in
  let _ = (match expr with
    | OpRational rat -> 
      let coef = Mpz.init () in
      let _ = Mpq.get_z coef rat in
      res.(0) <- coef
    | Q -> res.(1) <- (Mpz.init_set_si 1)
    | OpPow (Q, OpRational rat) ->
      let deg = Mpz.init () in
      let _ = Mpq.get_z deg rat in
      res.(Mpz.get_int deg) <- (Mpz.init_set_si 1)
    | OpProduct [OpRational coef; OpPow (Q, OpRational exp)] ->
      let deg_z = Mpz.init () in
      let coef_z = Mpz.init () in
      let _ = Mpq.get_z coef_z coef in
      let _ = Mpq.get_z deg_z exp in
      res.(Mpz.get_int deg_z) <- coef_z
    | OpProduct [OpRational coef; Q] ->
      let coef_z = Mpz.init () in
      let _ = Mpq.get_z coef_z coef in
      res.(1) <- coef_z
    | OpSum sum_list ->
      let get_pos_and_coef_of_term term = 
        (match term with
        | OpRational rat ->
          let coef = Mpz.init () in
          let _ = Mpq.get_z coef rat in
          (coef, 0)
        | Q -> (Mpz.init_set_si 1, 1)
        | OpProduct [OpRational coef; Q] ->
          let coef_z = Mpz.init () in
          let _ = Mpq.get_z coef_z coef in
          (coef_z, 1)
        | OpPow (Q, OpRational rat) ->
          let deg = Mpz.init () in
          let _ = Mpq.get_z deg rat in
          (Mpz.init_set_si 1, Mpz.get_int deg)
        | OpProduct [OpRational coef; OpPow (Q, OpRational exp)] ->
          let deg_z = Mpz.init () in
          let coef_z = Mpz.init () in
          let _ = Mpq.get_z coef_z coef in
          let _ = Mpq.get_z deg_z exp in
          (coef_z, Mpz.get_int deg_z)
        | _ -> failwith "Input wasn't a polynomial")
      in
      let coef_loc_pair = List.map get_pos_and_coef_of_term sum_list in
      List.iter (fun x -> res.(snd x) <- fst x) coef_loc_pair
    | _ -> failwith "Input wasn't a modular polynomial"
  ) in
  res
  ;;


let r_matrix u n p = 
  let rec get_remainder_polys acc iter = 
    if iter >= n then List.rev acc
    else (
      let exp = Mpz.init () in
      let _ = Mpz.mul_si exp p iter in
      let rem = snd (poly_div_p (Op_simplifications.op_automatic_simplify (OpPow (Q, OpRational (Mpq.init_set_z exp)))) u p) in
      get_remainder_polys ((get_coef_array_of_poly rem n) :: acc) (iter + 1)
    )
  in
  let lis_of_arrs = get_remainder_polys [] 0 in
  let result = Mat_helpers.transpose_matrix (Array.of_list lis_of_arrs) in
  let _ = 
    for i = 0 to (n-1) do result.(i).(i) <- irem (mpz_sub result.(i).(i) (Mpz.init_set_si 1)) p done in
  result
  ;;

let berlekamp_factor u p = 
  let num = Mpz.init () in
  let _ = Mpq.get_num num (snd (Op_transforms.degree u)) in
  let n = Mpz.get_int num in
  if n = 0 || n = 1 then [u]
  else (
    let r = r_matrix u n p in
    let s = auxiliary_basis r n p in
    if List.length s = 1 then [u]
    else find_factors u s p
  )
  ;;


let square_free_factor_rat u = 
  if (op_expr_order u (OpRational (Mpq.init_set_si 0 1))) = 0 then u
  else (
    let c = fst (Op_transforms.degree u) in
    let big_u = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide (u, c)))) in
    let p = ref (OpRational (Mpq.init_set_si 1 1)) in
    let r = ref (List.nth (Op_transforms.extended_euclidean big_u (Op_transforms.polynomial_derivative_q big_u)) 0) in
    let f = ref (fst (Op_transforms.polynomial_division big_u !r)) in
    let j = ref 1 in
    let _ = 
      while (op_expr_order !r (OpRational (Mpq.init_set_si 1 1))) <> 0 do
        let g = List.nth (Op_transforms.extended_euclidean !r !f) 0 in
        let s = fst (Op_transforms.polynomial_division !f g) in
        let _ = p := Op_simplifications.op_automatic_simplify (OpTimes(!p, OpPow(s, OpRational (Mpq.init_set_si !j 1)))) in
        let _ = r := fst (Op_transforms.polynomial_division !r g) in
        let _ = f := g in
        j := !j + 1
      done
    in
    let _ = p := Op_simplifications.op_automatic_simplify (OpTimes(!p, OpPow(!f, OpRational (Mpq.init_set_si !j 1)))) in
    Op_simplifications.op_automatic_simplify (OpTimes(c, !p))
  )
  ;;


let content poly = 
  let deg = int_of_string (Mpq.to_string (snd (Op_transforms.degree poly))) in
  let coefs = List.filter (fun x -> (Mpz.cmp_si x 0) <> 0) (Array.to_list (get_coef_array_of_poly poly (deg+1))) in
  List.fold_left (fun a b -> 
                   let res = Mpz.init () in
                   let _ = Mpz.gcd res a b in res) (List.nth coefs 0) coefs
  ;;

let pp poly = 
  let cont = content poly in
  let sign = 
    let lc = fst (Op_transforms.degree poly) in
    (match lc with
      | OpRational rat when (Mpq.cmp_si rat 0 1) < 0 -> OpRational (Mpq.init_set_si (-1) 1)
      | OpRational rat when (Mpq.cmp_si rat 0 1) > 0 -> OpRational (Mpq.init_set_si 1 1)
      | _ -> failwith "we should never get here"
    )
  in
  Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(sign, OpDivide (poly, OpRational (Mpq.init_set_z cont))))))
  ;;



let pseudo_division u v =
  let old_m = Mpz.get_int (get_mpz_of_rat_expr (OpRational (snd (Op_transforms.degree u)))) in
  let n = Mpz.get_int (get_mpz_of_rat_expr (OpRational (snd (Op_transforms.degree v)))) in
  let delta = max (old_m - n + 1) 0 in
  let lcv = fst (Op_transforms.degree v) in 
  let rec aux p s m sigma = 
    if m < n then (
      let q = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(OpPow(lcv, OpRational (Mpq.init_set_si (delta - sigma) 1)), p)))) in
      let r = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(OpPow(lcv, OpRational (Mpq.init_set_si (delta - sigma) 1)), s)))) in
      (q, r)
    ) else (
      let lcs = fst (Op_transforms.degree s) in
      let new_p = Op_simplifications.op_automatic_simplify (OpPlus(OpTimes(lcv,p), OpTimes(lcs,OpPow(Q, OpRational (Mpq.init_set_si (m-n) 1))))) in
      let new_s = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpMinus(OpTimes(lcv, s), OpTimes(OpTimes(lcs, v), OpPow(Q, OpRational (Mpq.init_set_si (m-n) 1))))))) in
      let new_m = Mpz.get_int (get_mpz_of_rat_expr (OpRational (snd (Op_transforms.degree new_s)))) in
      if m = 0 && n = 0 then aux new_p new_s (-1) (sigma + 1)
      else aux new_p new_s new_m (sigma + 1)
    )
  in
  aux (OpRational (Mpq.init_set_si 0 1)) u old_m 0
  ;;


let poly_gcd_z u v = 
  let cont_u = content u in
  let cont_v = content v in
  let d = Mpz.init() in
  let _ = Mpz.gcd d cont_u cont_v in
  let pp_u_old = pp u in
  let pp_v_old = pp v in
  let rec aux pp_u pp_v =
    if (Type_def.op_expr_order pp_v (OpRational (Mpq.init_set_si 0 1))) = 0 then pp (Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(OpRational (Mpq.init_set_z d), pp_u)))))
    else (
      let r = snd (pseudo_division pp_u pp_v) in
      let pp_r = 
        if (Type_def.op_expr_order r (OpRational (Mpq.init_set_si 0 1))) = 0 then OpRational (Mpq.init_set_si 0 1)
        else (
          pp r
        ) in
      aux pp_v pp_r
    )
  in
  aux pp_u_old pp_v_old
  ;;


let square_free_factor_z u =
  if (op_expr_order u (OpRational (Mpq.init_set_si 0 1))) = 0 then u
  else (
    let lc = fst (Op_transforms.degree u) in
    let cont = content u in
    let c = if (Mpz.cmp_si (get_mpz_of_rat_expr lc) 0) < 0 then Op_simplifications.op_automatic_simplify (OpTimes (OpRational (Mpq.init_set_si (-1) 1), OpRational (Mpq.init_set_z cont)))
      else OpRational (Mpq.init_set_z cont) in
    let big_u = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide (u, c)))) in
    let p = ref (OpRational (Mpq.init_set_si 1 1)) in
    let r = ref (poly_gcd_z big_u (Op_transforms.polynomial_derivative_q big_u)) in
    let f = ref (fst (Op_transforms.polynomial_division big_u !r)) in
    let j = ref 1 in
    let _ =
      while (op_expr_order !r (OpRational (Mpq.init_set_si 1 1))) <> 0 do
        let g = poly_gcd_z !r !f in
        let s = fst (Op_transforms.polynomial_division !f g) in
        let _ = p := Op_simplifications.op_automatic_simplify (OpTimes(!p, OpPow(s, OpRational (Mpq.init_set_si !j 1)))) in
        let _ = r := fst (Op_transforms.polynomial_division !r g) in
        let _ = f := g in
        j := !j + 1
      done
    in
    let _ = p := Op_simplifications.op_automatic_simplify (OpTimes(!p, OpPow(!f, OpRational (Mpq.init_set_si !j 1)))) in
    Op_simplifications.op_automatic_simplify (OpTimes(c, !p))
  )
  ;;



let res old_u old_v =
  let rec aux u v = 
    let m = snd (Op_transforms.degree u) in
    let n = snd (Op_transforms.degree v) in
    if (Mpq.cmp_si n 0 1) = 0 then Op_simplifications.op_automatic_simplify (OpPow(v, OpRational m))
    else (
      let r = snd (Op_transforms.polynomial_division u v) in
      if (Type_def.op_expr_order r (OpRational (Mpq.init_set_si 0 1))) = 0 then OpRational (Mpq.init_set_si 0 1)
      else (
        let s = snd (Op_transforms.degree r) in
        let l = fst (Op_transforms.degree v) in
        let m_times_n = Mpq.init() in
        let m_minus_s = Mpq.init() in
        let _ = Mpq.mul m_times_n m n in
        let _ = Mpq.sub m_minus_s m s in
        Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpProduct[OpPow(OpRational (Mpq.init_set_si (-1) 1), OpRational m_times_n);OpPow(l, OpRational m_minus_s);aux v r])))
      )
    ) in
  get_mpz_of_rat_expr (aux old_u old_v)
  ;;



let find_prime u = 
  let u_prime = Op_transforms.polynomial_derivative_q u in
  let resultant = res u u_prime in
  let two = Mpz.init_set_si 2 in
  let rec aux prime =
    if not (Mpz.divisible_p resultant prime) then prime
    else (
      let next_prime = Mpz.init() in
      let _ = Mpz.nextprime next_prime prime in
      aux next_prime
    ) in
  aux two
  ;;


let poly_height u = 
  let (_, deg) = Op_transforms.degree u in
  let deg_z = Mpz.init() in
  let _ = Mpq.get_num deg_z deg in
  let coef_arr = get_coef_array_of_poly u ((Mpz.get_int deg_z) + 1) in
  let max_abs_z a b = 
    let a_abs = Mpz.init() in
    let b_abs = Mpz.init() in
    let _ = Mpz.abs a_abs a in
    let _ = Mpz.abs b_abs b in
    if Mpz.cmp a_abs b_abs > 0 then a_abs
    else b_abs
  in
  Array.fold_left max_abs_z (Mpz.init_set_si 0) coef_arr
  ;;


let find_k u p = 
  let (_, deg) = Op_transforms.degree u in
  let deg_z = Mpz.init() in
  let _ = Mpq.get_num deg_z deg in
  let n = Mpz.get_int deg_z in
  let two_to_n_plus_1 = Mpz.init() in
  let _ = Mpz.ui_pow_ui two_to_n_plus_1 2 (n+1) in
  let sqrt_n_plus_1 = snd (Mpfr.init_set_si (n+1) Mpfr.Near) in
  let _ = Mpfr.sqrt sqrt_n_plus_1 sqrt_n_plus_1 Mpfr.Near in
  let height = poly_height u in
  let temp = Mpz.init () in
  let _ = Mpz.mul temp two_to_n_plus_1 height in
  let two_b = Mpfr.init () in
  let _ = Mpfr.mul two_b sqrt_n_plus_1 (Mpfr.of_mpz temp Mpfr.Near) Mpfr.Near in
  let log_two_b = Mpfr.init () in
  let log_p = Mpfr.init () in
  let _ = Mpfr.log log_two_b two_b Mpfr.Near in
  let _ = Mpfr.log log_p (snd (Mpfr.init_set_z p Mpfr.Near)) Mpfr.Near in
  let _ = Mpfr.div log_two_b log_two_b log_p Mpfr.Near in
  let _ = Mpfr.ceil log_two_b log_two_b in 
  let result = Mpz.init () in
  let _ = Mpfr.get_z result log_two_b Mpfr.Near in
  result
  ;;



let euclidean_algorithm_p u v p =
  match (u, v) with
  | (OpRational rat1, OpRational rat2) when (Mpq.cmp_si rat1 0 1)=0 && (Mpq.cmp_si rat2 0 1)=0 ->
    [OpRational (Mpq.init_set_si 0 1); OpRational (Mpq.init_set_si 0 1); OpRational (Mpq.init_set_si 0 1)]
  | _ ->
    let rec aux u v app ap bpp bp =
      (match v with
      | OpRational rat when (Mpq.cmp_si rat 0 1)=0 -> [u; app; bpp;]
      | _ ->
        let division_result = poly_div_p u v p in
        let a = Op_simplifications.op_automatic_simplify (OpMinus (app, OpTimes(fst division_result, ap))) in
        let b = Op_simplifications.op_automatic_simplify (OpMinus (bpp, OpTimes(fst division_result, bp))) in
        let new_app = ap in
        let new_ap = a in
        let new_bpp = bp in
        let new_bp = b in
        let new_u = v in
        let new_v = snd division_result in
        aux new_u new_v new_app new_ap new_bpp new_bp) in
      let aux_result = aux u v (OpRational (Mpq.init_set_si 1 1)) (OpRational (Mpq.init_set_si 0 1)) (OpRational (Mpq.init_set_si 0 1)) (OpRational (Mpq.init_set_si 1 1)) in
      let c = get_mpz_of_rat_expr (fst (Op_transforms.degree (List.nth aux_result 0))) in
      let c_inv = multiplicative_inverse_p c p in
      let app_res = poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(List.nth aux_result 1, OpRational (Mpq.init_set_z c_inv))))) p in
      let bpp_res = poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(List.nth aux_result 2, OpRational (Mpq.init_set_z c_inv))))) p in
      let u_res = poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(List.nth aux_result 0, OpRational (Mpq.init_set_z c_inv))))) p in
      [Op_simplifications.op_automatic_simplify u_res; Op_simplifications.op_automatic_simplify app_res; Op_simplifications.op_automatic_simplify bpp_res]
  ;;


let gen_extend_sigma_p v p =
  let g = List.map (fun x -> Op_simplifications.op_automatic_simplify (poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpProduct (List.filter (fun y -> Type_def.op_expr_order x y <> 0) v)))) p)) v in 
  let len = List.length g in
  if len = 2 then (
    let res = euclidean_algorithm_p (List.nth g 0) (List.nth g 1) p in
    List.tl res
  ) else (
    let rec aux acc gcd remaining_lis = 
      (match remaining_lis with
      | [] -> acc
      | hd :: tl -> 
        let euc_res = euclidean_algorithm_p gcd hd p in
        let app = List.nth euc_res 1 in
        let bpp = List.nth euc_res 2 in
        let expand_in_sym_p el op = 
          Op_simplifications.op_automatic_simplify (poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(el, op)))) p)
        in
        let new_acc = (List.map (fun x -> expand_in_sym_p x app) acc) @ [bpp] in
        aux new_acc (List.nth euc_res 0) (List.tl remaining_lis))
    in
    let first_res = euclidean_algorithm_p (List.nth g 0) (List.nth g 1) p in
    aux [List.nth first_res 1; List.nth first_res 2] (List.nth first_res 0) (List.tl (List.tl g))
  )
  ;;


let gen_extend_r_p v g f p =
  let rem_mul sigma v =
    let num = Op_simplifications.op_automatic_simplify (poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpTimes(f, sigma)))) p) in
    poly_to_z_sym_p (snd (poly_div_p num v p)) p
  in
  List.map2 rem_mul g v
  ;;


let rec comb big_s m =
  if (List.length big_s) = m then [big_s]
  else if m = 0 then [[]]
  else (
    let x = List.hd big_s in
    let big_t = List.tl big_s in
    let big_d = comb big_t (m-1) in
    let big_e = List.map (fun a -> x :: a) big_d in
    big_e @ (comb big_t m)
  )
  ;;


let clean_up big_c t =
  List.filter (fun x -> not (List.exists (fun a -> List.exists (fun b -> Type_def.op_expr_order a b = 0) t) x)) big_c
  ;;


let true_factors u l p k =
  let big_u = ref u in
  let big_l = ref l in
  let factors = ref [] in
  let m = ref 1 in
  let _ = 
    while !m <= (List.length l)/2 do
      let big_c = ref (comb !big_l !m) in
      let _ =
        while (List.length !big_c) <> 0 do
          let t = List.nth !big_c 0 in
          let big_t = Op_simplifications.op_automatic_simplify (OpProduct t) in
          let p_to_k = Mpz.init () in
          let _ = Mpz.pow_ui p_to_k p k in
          let big_t = Op_simplifications.op_automatic_simplify (poly_to_z_sym_p (Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (big_t))) p_to_k) in
          let big_d = Op_transforms.polynomial_division !big_u big_t in
          if (Type_def.op_expr_order (snd big_d) (OpRational (Mpq.init_set_si 0 1))) = 0 then (
            let _ = factors := !factors @ [big_t] in
            let _ = big_u := (fst big_d) in
            let _ = big_l := (List.filter (fun x -> List.for_all (fun y -> Type_def.op_expr_order x y <> 0) t) !big_l) in
            big_c := clean_up !big_c t
          ) else big_c := List.tl !big_c
        done 
      in
      m := !m + 1
    done
  in
  if (Type_def.op_expr_order !big_u (OpRational (Mpq.init_set_si 1 1))) <> 0 then !factors @ [!big_u]
  else !factors
  ;;

let hensel_lift u big_s p old_k = 
  let k = Mpz.get_int old_k in
  if k = 1 then true_factors u big_s p k
  else (
    let big_v = big_s in
    let big_g = gen_extend_sigma_p big_v p in
    let rec aux v j = 
      if j > k then true_factors u v p k
      else (
        let v_p = Op_transforms.algebraic_expand (OpProduct v) in
        let big_e = Op_simplifications.op_automatic_simplify (OpMinus(u, v_p)) in
        if (Type_def.op_expr_order big_e (OpRational (Mpq.init_set_si 0 1))) = 0 then v
        else (
          let p_to_j = Mpz.init () in
          let p_to_j_minus_1 = Mpz.init () in
          let _ = Mpz.pow_ui p_to_j p j in
          let _ = Mpz.pow_ui p_to_j_minus_1 p (j-1) in
          let big_f = Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpDivide(poly_to_z_sym_p big_e p_to_j, OpRational (Mpq.init_set_z p_to_j_minus_1)))) in
          let big_r = gen_extend_r_p v big_g big_f p in
          let v_new = List.map2 (fun a b -> Op_transforms.algebraic_expand (Op_simplifications.op_automatic_simplify (OpPlus(a, OpTimes(OpRational (Mpq.init_set_z p_to_j_minus_1), b))))) v big_r in
          aux v_new (j+1)
        )
      )
    in
    aux big_v 2
  )
  ;;


let irreducible_factor u =
  let (l, n) = Op_transforms.degree u in
  if (Mpq.cmp_si n 0 1) <= 0 then u
  else (
    let n_minus_1 = Mpq.init() in
    let _ = Mpq.sub n_minus_1 n (Mpq.init_set_si 1 1) in
    let v = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (Op_transforms.substitute (OpTimes(OpPow(l, OpRational n_minus_1), u)) Q (OpDivide (Q, l)))) in
    let p = find_prime v in
    let big_s = berlekamp_factor (poly_to_z_p v p) p in
    if (List.length big_s) = 1 then u
    else (
      let k = find_k v p in
      let big_w = hensel_lift v (List.map (fun x -> poly_to_z_sym_p x p) big_s) p k in
      let big_w = List.map (fun x -> Op_transforms.substitute x Q (Op_simplifications.op_automatic_simplify (OpTimes(l, Q)))) big_w in
      let res = Op_simplifications.op_automatic_simplify (OpProduct (List.map (fun x -> Op_transforms.algebraic_expand (OpDivide (x, OpRational (Mpq.init_set_z (content x))))) big_w)) in
      res
    )
  )
  ;;



let factor_z u = 
  let square_free = square_free_factor_z u in
  let factor_square_free fact = 
    (match fact with
    | OpPow (poly, exp) -> OpPow (irreducible_factor poly, exp)
    | _ -> irreducible_factor fact) in
  (match square_free with
  | OpProduct prod_list -> Op_simplifications.op_automatic_simplify (OpProduct (List.map factor_square_free prod_list))
  | _ -> factor_square_free square_free
  )
  ;;


let find_big_m u = 
  let rec get_coef poly_q acc =
    if (Type_def.op_expr_order poly_q (OpRational (Mpq.init_set_si 0 1))) = 0 then acc
    else ( 
      let (lc, deg) = Op_transforms.degree poly_q in
      let denom = 
        (match lc with
        | OpRational rat ->
          let denominator = Mpz.init() in
          let _ = Mpq.get_den denominator rat in
          denominator
        | _ -> failwith "input wasn't a polynomial"
        )
      in
      let new_poly = Op_simplifications.op_automatic_simplify (OpMinus (poly_q, OpTimes(lc, OpPow (Q, OpRational deg)))) in
      get_coef new_poly (denom :: acc)
    )
  in
  let lcm a b =
    let res = Mpz.init () in
    let _ = Mpz.lcm res a b in
    res
  in
  List.fold_left lcm (Mpz.init_set_si 1) (get_coef u [])
  ;;


let factor_q u = 
  let big_m = find_big_m u in
  let v = Op_simplifications.op_automatic_simplify (Op_transforms.algebraic_expand (OpTimes(OpRational (Mpq.init_set_z big_m), u))) in
  let cont_v = content v in
  let pp_v = pp v in
  let sign_v = if (Type_def.op_expr_order (fst (Op_transforms.degree u)) (OpRational (Mpq.init_set_si 0 1))) < 0 then OpRational (Mpq.init_set_si (-1) 1) else OpRational (Mpq.init_set_si 1 1) in
  let v_fact = factor_z pp_v in
  Op_simplifications.op_automatic_simplify (OpTimes(OpDivide(OpTimes(OpRational (Mpq.init_set_z cont_v), sign_v), OpRational (Mpq.init_set_z big_m)), v_fact))
  
  ;;
