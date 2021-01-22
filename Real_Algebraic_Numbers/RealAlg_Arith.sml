structure RealAlg_Arith : sig
  
  val alg_add: int list*((int*int)*(int*int)) -> int list*((int*int)*(int*int)) 
    -> int list*((int*int)*((int*int)*((int*int) option)));
    
  val alg_mult: int list*((int*int)*(int*int)) -> int list*((int*int)*(int*int)) 
    -> int list*((int*int)*((int*int)*((int*int) option)));

  val alg_minus: int list*((int*int)*(int*int)) -> int list*((int*int)*(int*int)) 
    -> int list*((int*int)*((int*int)*((int*int) option)));
    
  val alg_inverse: int list*((int*int)*(int*int))
    -> (int*int)*(int*int);
end = struct
 
exception Undefined

val lcm = (fn (x,y) => zz_lcm x y);
                   
fun poly_scale p = foldl lcm 1 (map (Useful.snd o Rat.quotient_of_rat o Useful.fst) p);

(*convert a univariate polynomial with rational coefficients to a list of ints by multiplying each 
  coefficient with a common scalar*)
local
open Algebra;

(*assume p is in canonical form (ordered in descending order w.r.t. m_lt)*)
fun univ_p_toRatList (p : poly) =
    let 
      val deg = p_deg p;
      fun f p d =
	      if d > deg then [] else
	      if p = [] then Rat.zero :: (f p (d+1)) else
	        let 
	          val ((c, pp) :: ms) = p
	          val mono_deg = m_deg (c,pp) 
	        in
	          if mono_deg = d then 
	            (c :: (f ms (d+1)))
	          else (* mono_deg > d *) 
	            Rat.zero :: (f p (d+1))
	        end
	  in
	    f (List.rev p) 0
    end;

in

fun to_int_list p= 
  let
    val scale = poly_scale p;
    val rat_list= univ_p_toRatList p
  in
    map ((fn (n,m) =>n*(scale div m)) o Rat.quotient_of_rat) rat_list
  end

end;


local
  fun poly_of_int_list' nil _ = nil
    | poly_of_int_list' (x::xs) n = 
      if x=0 then 
        poly_of_int_list' xs (n+1) 
      else 
        (Rat.rat_of_int x,[(0,n)])::poly_of_int_list' xs (n+1)
in
  fun poly_of_int_list xs = poly_of_int_list' xs 0;
end
 
fun to_alg (p,((lb1,lb2),(ub1,ub2))) = RealAlg.mk_real_alg (poly_of_int_list p) 
    (Rat.rat_of_quotient (lb1,lb2)) (Rat.rat_of_quotient (ub1,ub2));

fun of_alg (p,r1,r2,r3) = 
  let
    val f = Rat.quotient_of_rat
  in
    (to_int_list p,(f r1,(f r2,Option.map f r3)))
  end



fun alg_add alg1 alg2 = (of_alg o RealAlg.add) (to_alg alg1 NONE,to_alg alg2 NONE)

fun alg_mult alg1 alg2 = (of_alg o RealAlg.mult) (to_alg alg1 NONE,to_alg alg2 NONE)

fun alg_minus alg1 alg2 = (of_alg o RealAlg.minus) (to_alg alg1 NONE,to_alg alg2 NONE)

fun alg_inverse alg1 = (let val (_,((lb1,lb2),(ub1,ub2))) = alg1 in ((ub2,ub1),(lb2,lb1)) end)

end; (*end struct*)
