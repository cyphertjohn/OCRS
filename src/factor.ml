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


let poly_div_p u v p =
  let get_mpz_of_rat_expr expr = 
    (match expr with
    | OpRational rat -> 
      let res = Mpz.init () in
      let _ = Mpq.get_z res rat in
      res
    | _ -> failwith "poly_div_p polynomial not in Z"
    )
  in
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


let poly_div_p u v p = 

  ;;

let poly_gcd_p u v p =

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
        let little_s = ref (OpPow (Q, OpRational (Mpq.init_set_z j 1))) in
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
              little_s := Op_simplifications.op_automatic_simplify (OpPlus(!little_s, OpTimes(OpRational(Mpq.init_set_z c), OpPow(Q, OpRational (Mpq.init_set_si l 1)))))
            )
          done in
        s := !little_s :: !s
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
        for i = 0 to (List.length old_factors) - 1 do
          if (not !finished) then (
            let w = ref (List.nth !old_factors i) in
            let j = ref 0 in
            while (Mpz.cmp_si p j) > 0 do
              let g = poly_gcd_p (Op_simplifications.op_automatic_simplify (OpMinus (b, OpRational (Mpq.init_set_si !j 1)))) !w p in
              if (op_expr_order g (OpRational (Mpq.init_set_si 1))) = 0 then j := !j + 1
              else if (op_expr_order g !w) = 0 then j := (Mpz.get_int p)
              else (
                let _ = (factors := List.filter (fun x -> (op_expr_order !w x) <> 0) !factors) in
                let q = List.nth (poly_div_p !w g p) 0 in
                let _ = factors := !factors @ [g; q] in
                if List.length !factors = r then (let _ = finished := true in (j := Mpq.get_int p))
                else (let j := !j + 1 in w := q)
              )
            done
          )
        done
      )
    done in
  !factors
  ;;

(*
let berlekamp_factor u p = 
  let n = Op_transforms.degree u in
  if n = 0 || n = 1 then u
  else (
    let r = r_matrix u n p in
    let s = auxiliary_basis r n p in
    if List.length s = 1 then u
    else find_factors u s p
  )
*)
