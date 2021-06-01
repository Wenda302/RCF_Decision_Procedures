(* 
    Author:     Wenda Li, University of Cambridge
*)


signature UNIV_RCF =
sig
  val univ_rcf_cert : Proof.context -> term -> int -> tactic;
  val univ_rcf : Proof.context -> int -> tactic;

end

structure Univ_RCF: UNIV_RCF =
struct

(*
val holds = Code_Runtime.static_holds_conv {ctxt = @{context},
    consts = [           
     @{const_name HOL.Trueprop},
     @{const_name Set.insert},
     @{const_name Set.bot_set_inst.bot_set},
     @{const_name Nat.Suc},
     @{const_name List.list_all},
     @{const_name Option.equal_option_inst.equal_option},
     @{const_name Rat.uminus_rat_inst.uminus_rat},
     @{const_name Rat.of_int},
     @{const_name Rat.divide_rat_inst.divide_rat},
     @{const_name Rat.one_rat_inst.one_rat},
     @{const_name Real.uminus_real_inst.uminus_real},
     @{const_name Real.divide_real_inst.divide_real},
     @{const_name Polynomial.zero_poly_inst.zero_poly},
     @{const_name Polynomial.pCons},
     @{const_name Poly_Maps.of_int_poly},
     @{const_name RealAlg.int_poly},
     @{const_name RCF_Decision_Proc.contain_all_roots},
     @{const_name RCF_Decision_Proc.alg_rat_list_conv},
     @{const_name RCF_Decision_Proc.valid_list},
     @{const_name RCF_Decision_Proc.var_bound},
     @{const_name RCF_Decision_Proc.qf_form2_interp_core},
     @{const_name RCF_Decision_Proc.mk_samples},
     @{const_name RCF_Decision_Proc.qf_form2.Disj},
     @{const_name RCF_Decision_Proc.qf_form2.Conj},
     @{const_name RCF_Decision_Proc.qf_form2.Zero},
     @{const_name RCF_Decision_Proc.qf_form2.Neg},
     @{const_name RCF_Decision_Proc.qf_form2.Pos},
     @{const_name RCF_Decision_Proc.norm_num2.Pol},
     @{const_name RCF_Decision_Proc.ordered_reps},
     @{const_name RCF_Decision_Proc.code_inst}
    ]};
*)

(*
fun extract_answer (existential:bool) ctxt output = let 
  (*extract the witness for exitential cases*)
  val ex_p1= Scan.repeat (Scan.unless (Scan.this_string "with witness") 
    (Scan.one Symbol.not_eof)) |-- (Scan.this_string "with witness");
  val ex_p2= Scan.repeat (Scan.unless (Scan.this_string ".\n") 
    (Scan.one Symbol.not_eof));
  val ex_p3 = ex_p1 |-- ex_p2;

  val all_p1 = Scan.repeat (Scan.unless (Scan.this_string "[Begin univariate CAD sampling]") 
    (Scan.one Symbol.not_eof)) |-- (Scan.this_string "[Begin univariate CAD sampling]");
  val all_p2 = Scan.repeat (Scan.permissive all_p1);
  val all_p3= all_p2 |-- Scan.repeat (Scan.unless (Scan.this_string "-- [End univariate CAD sampling]") 
      (Scan.one Symbol.not_eof >> (fn x => case x of "\n" => "" | _ => x)));
  val all_p4= Scan.permissive all_p3 || (fn x => ([],x)) ;
  val all_samples="[" ^ (output |> Symbol.explode |> 
        (if existential then ex_p3 else all_p4) |> #1 |> implode) ^ "]";
  fun get_roots (x::xs) = let
      fun get_roots' [] = []
        | get_roots' (y1::_::ys) = y1 :: get_roots' ys 
    in if existential then x::xs else get_roots' xs end|
      get_roots [] = [] ;
  in  all_samples |> Syntax.parse_term ctxt |>  Syntax.check_term ctxt |> HOLogic.dest_list |> get_roots 
    |> HOLogic.mk_list @{typ "alg_float"}  end;

fun dest_list (Const ("List.list.Nil", _)) = []
  | dest_list (Const ("List.list.Cons", _) $ t $ u) = t :: dest_list u
  | dest_list t = raise TERM ("dest_list", [t]);
*)

fun int_to_str n = ((signed_string_of_int o snd o HOLogic.dest_number) n);

fun rat_to_str (Const ("Rings.divide_class.divide", _) $ t $ u) = 
  (int_to_str t) ^ "/" ^ (int_to_str u)
   | rat_to_str (Const ("Groups.uminus_class.uminus", _) $ t) = "-"^rat_to_str t
   | rat_to_str n = int_to_str n;

fun poly_to_str p = let
  fun term_to_str t exp = (case t of
    Const ("Groups.zero_class.zero", _) => ""|
    _ => (rat_to_str t)^ "*" ^ "x" ^ "^" ^ (string_of_int exp));
  fun poly_to_str' (Const ("Polynomial.pCons", _) $ t $ (Const ("Groups.zero_class.zero", _))) exp
      = term_to_str t exp
    | poly_to_str' (Const ("Polynomial.pCons", _) $ t $ u) exp 
      = let val str = term_to_str t exp in 
          ((if str="" then "" else str ^ " + ") ^ poly_to_str' u (exp+1)) 
        end
    | poly_to_str' t _ = raise TERM ("poly_to_str", [t]);
  in poly_to_str' p 0 end;

(*
fun norm_num2_to_str (Const ("Univ_RCF_Reification.norm_num2.Pol", _ ) 
      $ ((Const ("RealAlg_Imp.int_poly", _) $ t)) $ _) =poly_to_str t
   | norm_num2_to_str (Const ("Univ_RCF_Reification.norm_num2.Const", _ ) $ t ) = rat_to_str t
   | norm_num2_to_str t= 
      let val _ = @{print} t in raise TERM ("norm_num2_to_str",[t]) end;
*)

fun norm_num2_to_str (Const ("Univ_RCF_Reification.norm_num2.Pol", _ ) 
      $ (t) $ _) =poly_to_str t
   | norm_num2_to_str (Const ("Univ_RCF_Reification.norm_num2.Const", _ ) $ t ) = rat_to_str t
   | norm_num2_to_str t= 
      let val _ = @{print} t in raise TERM ("norm_num2_to_str",[t]) end;


fun qf_form_to_str (Const ("Univ_RCF_Reification.qf_form2.Disj", _ ) $ t $ u) =
     "(" ^ qf_form_to_str t ^ "||" ^ qf_form_to_str u ^ ")"
    | qf_form_to_str (Const ("Univ_RCF_Reification.qf_form2.Conj", _ ) $ t $ u) =
     "(" ^ qf_form_to_str t ^ "&&" ^ qf_form_to_str u ^ ")"
    | qf_form_to_str (Const ("Univ_RCF_Reification.qf_form2.Neg", _ ) $ t ) =
     "!(" ^ qf_form_to_str t ^ ")"
    | qf_form_to_str (Const ("Univ_RCF_Reification.qf_form2.Pos", _ ) $ t ) =
     "(" ^ norm_num2_to_str t ^ ">0)"
    | qf_form_to_str (Const ("Univ_RCF_Reification.qf_form2.Zero", _ ) $ t ) =
     "(" ^ norm_num2_to_str t ^ "==0)"
    | qf_form_to_str t = raise TERM ("qf_form_to_str",[t]);

(*
fun norm_form_to_str (Const ("RCF_Decision_Proc.norm_form.AllQ", _ ) $ t) =
    "![X]:" ^ (norm_form_to_str t)
    | norm_form_to_str (Const ("RCF_Decision_Proc.norm_form.ExQ", _ ) $ t) =
    "?[X]:" ^ (norm_form_to_str t)
    | norm_form_to_str (Const ("RCF_Decision_Proc.norm_form.QF", _ ) $ t) =
      qf_form_to_str t
    | norm_form_to_str t = raise TERM ("norm_form_to_str",[t]) ;
;
*)

(*norm_form2 \<Rightarrow> (poly) list*)

fun extract_polys (Const ("Univ_RCF_Reification.norm_form2.AllQ", _) $ t) = extract_polys t 
  | extract_polys (Const ("Univ_RCF_Reification.norm_form2.ExQ", _) $ t) = extract_polys t
  | extract_polys (Const ("Univ_RCF_Reification.norm_form2.QF", _) $ t) = extract_polys t 
  | extract_polys (Const ("Univ_RCF_Reification.qf_form2.Disj", _) $ t $ u) 
      = extract_polys t @ extract_polys u
  | extract_polys (Const ("Univ_RCF_Reification.qf_form2.Conj", _) $ t $ u) 
      = extract_polys t @ extract_polys u
  | extract_polys (Const ("Univ_RCF_Reification.qf_form2.Pos", _) $ t) = extract_polys t 
  | extract_polys (Const ("Univ_RCF_Reification.qf_form2.Zero", _) $ t) = extract_polys t 
  | extract_polys (Const ("Univ_RCF_Reification.qf_form2.Neg", _) $ t) = extract_polys t 
  | extract_polys (Const ("Univ_RCF_Reification.norm_num2.Pol", _) $ t $ _) = extract_polys t
  | extract_polys t = [t];

(* 
  | extract_polys (Const ("RealAlg_Imp.int_poly", _) $ t) = [t];
*)

fun runMathematica extential ctxt formula =
  (if extential then 
     let 
        val qf_str= (case formula of 
            (Const ("Univ_RCF_Reification.norm_form2.ExQ", _) 
              $ (Const ("Univ_RCF_Reification.norm_form2.QF", _) $ t)) => qf_form_to_str t);
        val cmd="getInstance["^qf_str^"]//FullForm";
        val _ = writeln ("Command to Mathematica: "^cmd );
        val result = execute_MathKernel_print cmd;
        val _ = writeln ("Mathematica returns: "^result );
      in Syntax.read_term ctxt result end
    else 
      let val cmd = "isolateRoots[{"^(String.concatWith "," (map poly_to_str (extract_polys formula)))
                      ^"}]//FullForm";
          val _ = writeln ("Command to Mathematica: "^cmd );
          val result = execute_MathKernel_print cmd;
      in Syntax.read_term ctxt result end);


fun output_line cert =
  "To repeat this proof with a certificate use this command:\n" ^
    Active.sendback_markup_command ("apply (univ_rcf_cert \"" ^ cert ^ "\")");

(*
fun run_metitarski (existential:bool) ctxt term = let
    val tmp_path = File.tmp_path (Path.basic ("rcf_input" ^ serial_string ()));
    val formula = norm_form_to_str term;
    val tptp = "fof(tmp,conjecture," ^ formula ^ "). \n include('Axioms/general.ax')."
    val _ = File.write tmp_path tptp;
    val (output,msg) = Isabelle_System.bash_output ("$METITARSKI_HOME/metit --tptp $METITARSKI_HOME/tptp --univ_cert_rcf " 
    ^ (File.shell_path tmp_path));
    (*val (output,msg) = Isabelle_System.bash_output ("~/Programs/metitarski/metit --tptp /home/wl302/Programs/metitarski/tptp --univ_cert_rcf " 
    ^ (File.shell_path tmp_path));*)
    val _ = if msg <>0 then error ("metitarski fails:" ^ output)  else ();
  in extract_answer existential ctxt output end;
*)

fun existential_case_tac ctxt pt =  
    resolve0_tac [(infer_instantiate' ctxt    
    [SOME (pt |> HOLogic.dest_list |> hd |> 
        (fn x => Thm.cterm_of ctxt (@{term alg_rat_aux_conv} $ x)))] 
    @{thm ExQ_intro_code})] 1
  (* Already eliminated in @{thm ExQ_intro_code}
    THEN
    (*Because computation_check does not support abstraction (e.g. "let ... in ...")
      we need to unofold Let_def first. It would be good to have this step eliminated
      in the future.*)
    let val _ = writeln "bbb" in
    Local_Defs.unfold_tac ctxt [@{thm Let_def}] end
  *)
  THEN 
    CONVERSION (rcf_holds ctxt) 1 
  THEN 
    let val _ = writeln "ccc" in
    resolve0_tac [TrueI] 1 end;

fun universal_case_tac ctxt roots = 
    resolve0_tac [(infer_instantiate' ctxt
        [NONE,NONE,SOME (Thm.cterm_of ctxt (@{term alg_rat_list_conv} $ roots))] @{thm allQ_intro_code})]
    1
   THEN 
      simp_tac ctxt 1
   (* Already eliminated in @{thm ExQ_intro_code}
   THEN
    (*Because computation_check does not support abstraction (e.g. "let ... in ...")
      we need to unofold Let_def first. It would be good to have this step eliminated
      in the future.*)
    Local_Defs.unfold_tac ctxt [@{thm Let_def}] 
    *)
   THEN 
      (CONVERSION (rcf_holds ctxt) THEN' (resolve0_tac [TrueI])) 1 
    ;

fun univ_rcf_cert ctxt (cert:term) =
  let val cert' = case cert of @{term "[]"} => @{term "[]:: alg_rat_aux list"} | _ => cert
  in 
    Reflection.default_reflection_tac 
      ctxt   
      @{thms norm_form2_correct} 
      @{thms num_interp_eqs form_interp.simps} 
      NONE 
    THEN' 
      efficient_norm_tac ctxt
    THEN'
      CSUBGOAL (fn (ctrm,i) => 
        let (*val _ = cert' |> HOLogic.dest_list |> hd 
                |> (fn x => Thm.cterm_of ctxt (@{term alg_rat_aux_conv} $ x))
                |> Thm.term_of
                |> Syntax.string_of_term ctxt |> writeln;
             *)
             val _ = @{print} ctrm
          in
        (case (ctrm |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.term_of) of
          Const ("Univ_RCF_Reification.norm_form2.ExQ",_) $ _ => existential_case_tac ctxt cert'  
         | Const ("Univ_RCF_Reification.norm_form2.AllQ",_) $ _ => universal_case_tac ctxt cert' 
        )
        end
        )
  end

fun univ_rcf ctxt  =
    Reflection.default_reflection_tac 
      ctxt   
      @{thms norm_form2_correct} 
      @{thms num_interp_eqs form_interp.simps} 
      NONE 
  THEN' 
    efficient_norm_tac ctxt
  THEN'
    CSUBGOAL (fn (p, i) =>
      let 
        val formula = p |> Thm.dest_arg |> Thm.dest_arg1 |> Thm.term_of;
        val existential = (case formula of 
          Const ("Univ_RCF_Reification.norm_form2.ExQ",_) $ _ =>  true 
         | Const ("Univ_RCF_Reification.norm_form2.AllQ",_) $ _ => false) ;
        (*val _ = writeln "Porting the following formula to MetiTarski:";*)
        (*val _ = formula |> norm_form_to_str |> writeln; *)
        val cert = runMathematica existential ctxt formula;
        (*val cert = (case term_of (Thm.dest_arg p) of 
          (Const ("RCF_Decision_Proc.norm_form_interp", _) $ t $ _) 
            => run_metitarski ctxt t)*)
        val _ = Syntax.pretty_term ctxt cert |> Pretty.string_of |> output_line |> warning;
      in if existential then existential_case_tac ctxt cert else universal_case_tac ctxt cert end);

end;
