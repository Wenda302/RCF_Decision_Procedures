(* Interface between MetiTarski and Mathematica's MathKernel *)
(* adapted from Grant Passmore's code*)

signature Mathematica =
sig
  

(*MATH_KERNEL should point to an executable of Mathematica Kernel*)
val execute_and_print: string -> string;


end


structure Mathematica :> Mathematica =
struct


exception Mathematica_Error of string;

val mathematica_used = ref false;

val mk_hc_bin = "/usr/groups/mathematica/9.0/bin/MathKernel";
val use_mk_hc_bin = ref false; (* <- Should be false when building MT binaries *)

val mk_proc = ref (NONE : ((TextIO.instream, TextIO.outstream) Unix.proc
                           * TextIO.instream * TextIO.outstream) option);


fun matches class c =
    List.exists (fn x => x = c) (explode class);

(* Some basic lexical classes: Note that '>' is a special white-space
    char for Mathematica's FullForm output mode. *)

val white_space = matches " \t\n\r>"; 
val num = matches "0123456789.";
val alpha_num = 
    matches "abcdefghijklmnopqrstuvwxyz_ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

(* Datatype for Mathematica expressions we support *)

datatype m_tm = Int of int
              | Var of string
              | Plus of m_tm list
              | Times of m_tm list
              | Power of m_tm * int
              | Rational of int * int
              | Sin of m_tm
              | Cos of m_tm
              | Sinh of m_tm
              | Cosh of m_tm
              | Abs of m_tm
              | Log of m_tm
              | Tan of m_tm
              | Sqrt of m_tm
              | CubeRoot of m_tm
              | ArcTan of m_tm
              | ArcSin of m_tm
              | ArcCos of m_tm
              | Exp of m_tm
              | UnaryMinus of m_tm
              | Function of m_tm list
              | Slot of int
              | List of m_tm list;

datatype m_fm = Tm of m_tm | True | False | Aborted;

(* Exception for non-parsing *)

exception MATHEMATICA_PARSING of string;

(* Given a list of token strings, construct a parse tree for
    Mathematica terms using the method of recursive descent. *)

fun parse_m_tm_lst l =
    case l of
        "[" :: r =>
        (case parse_m_tm_lst r of
             (tm_lst, "]" :: s) => (tm_lst, s)
           | (_, s :: s') => raise MATHEMATICA_PARSING ("bad term list: " ^ s)
           | _ => raise MATHEMATICA_PARSING "bad term list")
      | _ => case parse_m_tm' l of
                 (tm, r) =>
                 if (hd r) = "," then
                     let val (tm_lst, r) = parse_m_tm_lst (tl r) in
                         ([tm] @ tm_lst, r)
                     end
                 else ([tm], r)

and parse_m_tm' l =
    case l of
        [] => raise MATHEMATICA_PARSING "expected non-empty token list"
      | "Plus" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                           (Plus tm_lst, s)
                       end
      | "Times" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                            (Times tm_lst, s)
                        end
      | "Function" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                            (Function tm_lst, s)
                        end
      | "Slot" :: r => let val (slot_lst, s) = parse_m_tm_lst r in
                           case slot_lst of
                               [Int slot_id] => (Slot slot_id, s)
                             | _ => raise MATHEMATICA_PARSING "bad Slot[_]"
                       end
      | "Power" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                            case tm_lst of
                                [x, Int y] => (Power (x, y), s)
                              | _ => raise MATHEMATICA_PARSING "bad Power[_]"
                        end
      | "Rational" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                               case tm_lst of
                                   [Int x, Int y] => (Rational (x, y), s)
                                 | _ => raise MATHEMATICA_PARSING "bad Rational[_]"
                           end
      | "List" :: r => let val (tm_lst, s) = parse_m_tm_lst r in
                           (List tm_lst, s)
                       end
      | "-" :: r =>
        (case Int.fromString (hd r) of
             SOME i => (Int (~ i), (tl r))
           | NONE => raise MATHEMATICA_PARSING "expected int")
      | x :: r =>
        (case Int.fromString x of
             SOME i => (Int i, r)
           | NONE =>
             if List.all alpha_num (explode x) then (Var x, r)
             else raise MATHEMATICA_PARSING ("bad expression: " ^ (String.concatWith " " l)));

(* Parse a lex'd representation of a Mathematica FullForm term into
   our internal m_tm syntax tree. *)

fun parse_m_tm l = let val (x, y) = parse_m_tm' l in x end;

fun m_tm_to_str t =
    let val int_to_str = (fn i => if i >= 0 then Int.toString i
                                 else "-" ^ Int.toString (~i))
    in case t of
           Rational (p, 1) => int_to_str p
         | Rational (p, q) => "Rational[" ^ int_to_str p ^ "," ^ int_to_str q ^ "]"
         | Int i => int_to_str i
         | Var s => s
         | Plus [x, y] => "Plus[" ^ m_tm_to_str x ^ "," ^ m_tm_to_str y ^ "]"
         | Times [x, y] => "Times[" ^ m_tm_to_str x ^ "," ^ m_tm_to_str y ^ "]"
         | Power (x, y) => "Power[" ^ m_tm_to_str x ^ "," ^ int_to_str y ^ "]"
         | UnaryMinus x => "Times[-1," ^ m_tm_to_str x ^ "]"
         | Sin x => "Sin[" ^ m_tm_to_str x ^ "]"
         | Cos x => "Cos[" ^ m_tm_to_str x ^ "]"
         | Sinh x => "Sinh[" ^ m_tm_to_str x ^ "]"
         | Cosh x => "Cosh[" ^ m_tm_to_str x ^ "]"
         | Abs x => "Abs[" ^ m_tm_to_str x ^ "]"
         | Log x => "Log[" ^ m_tm_to_str x ^ "]"
         | Tan x => "Tan[" ^ m_tm_to_str x ^ "]"
         | Sqrt x => "Sqrt[" ^ m_tm_to_str x ^ "]"
         | CubeRoot x => "CubeRoot[" ^ m_tm_to_str x ^ "]"
         | ArcTan x => "ArcTan[" ^ m_tm_to_str x ^ "]"
         | ArcSin x => "ArcSin[" ^ m_tm_to_str x ^ "]"
         | ArcCos x => "ArcCos[" ^ m_tm_to_str x ^ "]"
         | Exp x => "Exp[" ^ m_tm_to_str x ^ "]"
         | List xs => "List["^ (String.concatWith "," (map m_tm_to_str xs)) ^ "]"
         | Function xs => "Function["^ (String.concatWith "," (map m_tm_to_str xs)) ^ "]"
         | Slot i => "Slot[" ^ int_to_str i ^ "]"
         (* | RootIntervals x => "RootIntervals[{" ^ m_tm_to_str x ^ "}]" *)
         | _ => raise MATHEMATICA_PARSING "cannot convert Mathematica tm to string"
    end;

(* Parse a lex'd repesentation of a Mathematica FullForm formula *)

fun parse_m_fm l =
    case l of
        [] => raise MATHEMATICA_PARSING "expected non-empty token list"
      | ["True"] => True
      | ["False"] => False
      | ["$", "Aborted"] => Aborted
      | _ => Tm (parse_m_tm l);

(* Given a list of characters S, snag the longest leading subsequence
   S' of S of a given lex class, returning a pair : string * char list
   (str(S'), rest), s.t. S' @ String.implode(rest) = S. *)

fun lex_snag p cl =
    case cl of
	c :: cs => if p c then
		       let val (s', rest) = lex_snag p cs in
			   (Char.toString(c) ^ s', rest)
		       end
		   else ("", cl)
      | _ => ("", cl);

(* Lex: Map a list of chars into a list of token strings *)

fun lex cl =
    let val (_, cl') = lex_snag white_space cl in
	case cl' of
	    c :: cs => let val p = if alpha_num c then alpha_num
				   else (fn x => false) in
			   let val (tok_str, rest) = lex_snag p cs in
			       (Char.toString(c) ^ tok_str) :: lex rest
			   end
		       end
	  | _ => []
    end;


fun update_mk_is new_is =
    case !mk_proc of
        SOME m => let val (a, b, c) = m in
                      mk_proc := SOME (a, new_is, c)
                  end
      | NONE => ();

fun string_of_signal s =
    if s = Posix.Signal.hup then "Hangup"
    else if s = Posix.Signal.ill then "Illegal instruction"
    else if s = Posix.Signal.int then "Interrupt"
    else if s = Posix.Signal.kill then "Kill"
    else if s = Posix.Signal.segv then "Segmentation violation"
    else if s = Posix.Signal.bus then "Bus error"
    else "signalled " ^ SysWord.toString (Posix.Signal.toWord s);

local open Unix
in
fun stringOfStatus W_EXITED = "exited"
  | stringOfStatus (W_EXITSTATUS w) = "exit " ^ Word8.toString w
  | stringOfStatus (W_SIGNALED s) = string_of_signal s
  | stringOfStatus (W_STOPPED w) = "stopped";
end;

(* Signal: subprocess cpu time limit exceeded *)

(* Close MathKernel process *)

fun mk_close ignore_outcome =
    case !mk_proc of
        SOME (proc, instr, outstr) =>
        let
            (* TODO: Consider first trying to quit nicely with Quit[] *)
            val _ = Unix.kill (proc, Posix.Signal.kill)
            val status = Unix.fromStatus (Unix.reap proc)
        in
            (if ignore_outcome orelse status = Unix.W_EXITED
                orelse status = Unix.W_SIGNALED 9 then 
                (println("MathKernel has been closed.");
                ())
             else (*if status = Unix.W_SIGNALED sigxcpu
             then print "Processor time limit exceeded for Mathematica\n"
             else*) print ("****ERROR: exit status = " ^ stringOfStatus status ^ "\n");
             mk_proc := NONE)
        end
      | NONE => ();

fun mk_is () =
    case !mk_proc of
        SOME (_, y, _) => SOME y
      | NONE => NONE;

fun mk_os () =
    case !mk_proc of
        SOME (_, _, z) => SOME z
      | NONE => NONE;


fun stream_strings_until_prompt is prompt_str acc =
    case mk_is() of
        SOME is => (case TextIO.inputLine is of
                        NONE => raise Mathematica_Error "Mathematica has unexpectedly terminated - NB this may be an OS timeout - "
                      | SOME line =>
                        (*(Useful.chatting 4 andalso Useful.chat ("MathKernel: " ^ line);*)
                         (print ("MathKernel: " ^ line); 
                         if String.isSubstring prompt_str line
                         then  List.rev acc
                         else stream_strings_until_prompt is prompt_str (line :: acc)))
      | NONE => raise Mathematica_Error "No MathKernel process yet spawned.";

fun mk_writeln (s) =
    case mk_os() of
        SOME os => TextIO.output (os, (s ^ "\n"))
      | NONE => raise Mathematica_Error "No MathKernel process spawned.";

fun mk_result_tokens () =
    case mk_is() of
        SOME is =>
        let val s = stream_strings_until_prompt is "InMT>" []
            val s' = String.concat s
            (* val _ = print ("Read: " ^ s' ^ "\n") *)
            val l = lex (explode s')
        in SOME l end
      | NONE => NONE;

(* Send a command string to MK and parse back the result.
   We use the m_fm parser, so this works for also QE results. *)

fun m_fm_of_mk_exec_str s =
    let val _ = mk_writeln s
    in
        case mk_result_tokens() of
            SOME l => SOME (parse_m_fm l)
          | NONE => NONE
    end;


val root_iso_code =
" isolateRoots[polys_]:=Module[{sortedRoots,sortedRootsEx,minDiff,expr,floatbound}, \n \
\ (*{lb,ub}=floatbound[r,d] s.t. lb and ub are binary rationals, r-d<lb<r, and r<ub<r+d*) \
\ floatbound[r_,d_]:=With[ {n=Power[2,Ceiling[Log[2,1/d]]]}, \
\ {Floor[n*r]/n,Ceiling[n*r]/n}]; \

\ expr=Or@@((#==0)&/@ polys); \
\ sortedRoots = DeleteDuplicates[SortBy[RootReduce /@ (x /. SemialgebraicComponentInstances[expr, x]), N]];\
\ (*sortedRoots=Union[x /. SemialgebraicComponentInstances[expr,x]];*) \
\ (*sortedRootsEx=Sort[Append[sortedRoots,0],Less];*) \

\ (*minDiff calculates a suitable size for isolation interval such that those intervals don't overlap and exclude 0*) \
\ minDiff=Min[(#[[2]]-#[[1]])& /@ Transpose[{Drop[N /@ sortedRoots,-1],Drop[N /@ sortedRoots,1]}]]; \
\ \
\ (If [# \\[Element] Algebraics, \
\ If[# \\[Element]Rationals,{MinimalPolynomial[#],floatbound[#,minDiff/2]},{MinimalPolynomial[#],IsolatingInterval[#,minDiff]}],#])&/@ sortedRoots \
\ ] \n"

(*
val root_iso_code =
    "isolateRoots[polys_] :=    \n \
\Module[{sortedRoots, sortedRootsEx, minDiff, expr},   \n \
\   expr = Or @@ ((# == 0) & /@ polys);   \n \
\   sortedRoots =    \n \
\    Sort[x /. SemialgebraicComponentInstances[expr, x], Less];   \n \
\   sortedRootsEx = Sort[Append[sortedRoots, 0], Less];   \n \
\   (* minDiff calculates a suitable size for isolation interval such    \n \
\       that those intervals don't overlap and exclude 0 *)   \n \
\   minDiff =   \n \
\    Min[(#[[2]] - #[[1]]) & /@   \n \
\      Transpose[{Drop[N /@ sortedRootsEx, -1],   \n \
\        Drop[N /@ sortedRootsEx, 1]}]];   \n \
\    (If [# \\[Element] Algebraics, {MinimalPolynomial[#],   \n \
\        IsolatingInterval[#, minDiff]}, #]) & /@ sortedRoots   \n \
\   ]\n";
*)

val get_instance_code =
"getInstance[fm_] := \
 \ With[{xs = x /. FindInstance[fm, {x}], minDiff = 0.1}, \
 \ (*{lb,ub}=floatbound[r,d] s.t.lb and ub are binary rationals,r-d<lb< \
 \ r,and r<ub<r+d*) \
 \ floatbound[r_, d_] := \
 \ With[{n = Power[2, Ceiling[Log[2, 1/d]]]}, {Floor[n*r]/n, Ceiling[n*r]/n}];\
 \ (If[# \\[Element] Algebraics, \
 \      If[# \\[Element] Rationals, {MinimalPolynomial[#], \ 
 \       floatbound[#, minDiff/2]}, {MinimalPolynomial[#], \
 \      IsolatingInterval[#, minDiff]}], #]) & /@ xs] \n"


(* A simple handshaking function.  This should be run immediately
   after opening up an MK process.  It just does a simple check to
   make sure the MK is being responsive, and crucially gets the system
   into a state so that all strings read from it will begin with
   "\nOut[...]//FullForm=" and end with "\n\nIn[...]:= ", with the
   '...' being numbers. *)

fun mk_handshake () =
    ((* print ("\n" ^ (mk_opt_str (!mk_active_options)) ^ "\n"); *)
     mk_writeln ("InitTime = TimeUsed[]");

     (* mk_writeln ("FullForm[1+1]");
      block_until_read "FullForm= 2\n\nIn[4]:= " *)

     (* We need to install into Mathematica's runtime Wenda Li's
        polynomial real root isolation code *)
        
     mk_writeln (root_iso_code);
     mk_writeln (get_instance_code);

     (*** Setup our custom Mathematica REPL so we can use line-based I/O ***)
     mk_writeln ("While[True, NV = Input[\"InMT>\\n\"]; Print[NV]; If[NV == Quit, Quit[]]]"));

(* Open a MathKernel process and setup the global mk_proc with I/O streams *)

fun mk_open() = case !mk_proc of
    SOME pio => pio
  | NONE =>
    let val mk_bin_str =
              if !use_mk_hc_bin then mk_hc_bin
              else case OS.Process.getEnv"MATH_KERNEL" of
                  NONE => raise Mathematica_Error
                              ("Environment variable MATH_KERNEL must " ^
                               "point to Mathematica MathKernel binary")
                | SOME s => s
        val proc = Unix.execute(mk_bin_str, ["-noinit"]) : (TextIO.instream, TextIO.outstream) Unix.proc
        val (instr, outstr) = Unix.streamsOf proc
        (* val (instr', outstr') = (TextIO.getInstream instr, TextIO.getOutstream outstr) *)
    in
        mk_proc := SOME (proc, instr, outstr);
        println ("Starting to handshake with MathKernel.");
        mk_handshake();
        println ("Finish handshaking with MathKernel.");
        mathematica_used := true;
        stream_strings_until_prompt instr "InMT>" [];
        println ("MathKernel starts.");
        (* ^^^ This ignored all characters in stream until our custom REPL prompt is read. *)
        (proc, instr, outstr)
    end;


(* A private Mathematica-module version of the RealAlg type,
   used only for printing purposes. *)

type m_real_alg = Algebra.poly * Rat.rat * Rat.rat;

(* Convert, e.g.,

     [Plus [Int ~2, Power (Slot 1, 2)]]

   into

     -2 + x^2.

   * We let Slot[k] represent x_[k-1], i.e.,

     val p_x = [(Rat.one, [(0, 1)])] : poly;

 *)

local open Algebra Rat in

fun rat_of_m_numeric_tm q =
    case q of
        Int n => Rat.rat_of_int n
      | Rational (a,b) =>  Rat.rat_of_quotient (a,b)
      | _ => raise MATHEMATICA_PARSING "Bad root interval endpoint"

fun poly_pow (p, n) =
    if n < 0 then raise MATHEMATICA_PARSING "Pow with negative expt"
    else if n = 0 then p_one
    else p_mult(p, (poly_pow(p, n-1)))

fun poly_of_m_fun (m : m_tm) =
    case m of
        Int n => poly_of_rat (rat_of_int n)
      | Rational (a,b) => poly_of_rat (Rat.rat_of_quotient (a,b))
      | UnaryMinus p => p_neg(poly_of_m_fun p)
      | Plus ps =>
        let val m_ps = List.map poly_of_m_fun ps
        in
            List.foldr p_sum p_zero m_ps
        end
      | Times ps =>
        let val m_ps = List.map poly_of_m_fun ps
        in
            List.foldr p_mult p_one m_ps
        end
      | Power (p, n) =>
        let val m_p = poly_of_m_fun p
        in
            poly_pow (m_p, n)
        end
      | Slot n => [(Rat.one, [(n-1, 1)])] (* : poly *)
      | _ => raise MATHEMATICA_PARSING "Bad polynomial in Mathematica real_alg"

end;


(* Construct m_real_algs from a Mathematica representation *)
(* Example:

  let val tm =
    List
      [Function [Plus [Int ~2, Power (Slot 1, 2)]],
       List [Rational (~725, 512), Rational (~181, 128)]]
  in
   mra_of_tm tm
  end;

*)

fun mra_of_m_tm m =
    case m of
        List([(Function [f]),
              List([q1, q2])])
        => (poly_of_m_fun f,
            rat_of_m_numeric_tm q1,
            rat_of_m_numeric_tm q2)
      | _ => raise MATHEMATICA_PARSING "Bad Mathematica real_alg"

(* Example:

let val tm =
 List
    [List
      [Function [Plus [Int ~2, Power (Slot 1, 2)]],
       List [Rational (~725, 512), Rational (~181, 128)]],
     List
      [Function
        [Plus
          [Int ~1, Times [Int ~4, Slot 1], Times [Int 3, Power (Slot 1, 2)],
           Times [Int ~2, Int 1], Power (Slot 1, 4)]],
       List [Rational (~55, 256), Rational (~27, 128)]],
     List [Function [Plus [Int ~1, Slot 1]], List [Int 1, Int 1]],
     List
      [Function [Plus [Int ~2, Power (Slot 1, 2)]],
       List [Rational (181, 128), Rational (725, 512)]],
     List
      [Function [Plus [Int ~1, Times [Slot 1, Slot 1], Int 3]],
       List [Rational (113, 64), Rational (905, 512)]]]
  in
    mras_of_m_tm tm
 end;

*)

fun mras_of_m_tm (m : m_tm) =
    case m of
        List tms => map mra_of_m_tm tms
      | _ => raise MATHEMATICA_PARSING "Bad list of real_algs"

(* Isabelle/HOL style string representation *)

fun mra_toIsabelleString (r : m_real_alg) =
    case r of
        (p, l, u) => if l = u then ("RAT (" ^ (Rat.toString l) ^ ")")
                     else ("ALG [:" ^ (Algebra.univ_p_toString p) ^
                           ":] (" ^ (Rat.toString l) ^ ") (" ^
                           (Rat.toString u) ^ ")") ;

fun execute_and_print str =
  (let
    val _ = mk_open ();
    val rts = case m_fm_of_mk_exec_str str of
            SOME (Tm m_tm) => mras_of_m_tm m_tm
          | SOME _ => raise MATHEMATICA_PARSING "Term expected"
          | NONE => raise MATHEMATICA_PARSING "NONE";
    val r_str = String.concatWith "," (map mra_toIsabelleString rts);
    val _ = mk_close true
  in
    "["^r_str^"]" end);

end ; 
      