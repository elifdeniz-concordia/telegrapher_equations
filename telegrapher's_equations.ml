(* ===============================================================*)
(*                                                                *)
(*         Formalization of Telegrapher's Equations               *)
(*                                                                *)
(*        (c) Copyright, Elif Deniz* & Adnan Rashid*              *)
(*                                                                *)
(*                   *Hardware Verification Group,                *)
(*         Department of Electrical and Computer Engineering      *)
(*                        Concordia University                    *) 
(*                        Montreal, Canada                        *)
(*                                                                *)
(*                                                                *)
(*                                                                *)
(*           Contact:   *<e_deniz@encs.concordia.ca>              *) 
(*                     **<rashid@encs.concordia.ca>               *)
(*                                                                *)
(* ============================================================== *)

(*===================== Theories to load==========================*)

needs "Multivariate/cauchy.ml";;
needs "Multivariate/cvectors.ml";;

(*=================================================================*)
(*                 Some Useful Theorems                            *)
(*=================================================================*)

let ccot = new_definition `ccot z = ccos z / csin z`;;

let CSQRT_MINUS = prove (
`Re ii = &0 /\ &0 <= Im ii  ==> csqrt (--Cx(&1)) = ii`,

 REPEAT DISCH_TAC THEN ASSERT_TAC `csqrt (ii pow 2) = ii`
 THENL [MATCH_MP_TAC POW_2_CSQRT THEN ASM_SIMP_TAC[]; ALL_TAC]
 THEN ASSERT_TAC `ii pow 2 = --Cx(&1)`
  THENL [REWRITE_TAC[COMPLEX_POW_II_2]; ALL_TAC]
  THEN ASM_MESON_TAC[]);;


let LEMMA_RE_ALT = prove (
`!z. Im z = &0
   ==>  Cx (Re z) = z`,

REPEAT STRIP_TAC THEN 
 ONCE_REWRITE_TAC [COMPLEX_EXPAND] THEN
 REWRITE_TAC [GSYM COMPLEX_TRAD] THEN 
  SIMP_TAC [RE_CX] THEN SIMP_TAC[COMPLEX_EQ] THEN
  CONJ_TAC THEN
   SIMP_TAC[RE;IM;IM_CX] THEN ASM_REWRITE_TAC[]);;

let COSH = prove (
`(cexp (--x) + cexp (x)) / Cx (&2) = ccos(ii * x)`,
  REWRITE_TAC[ccos; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`]);;


let COSH_INV = prove(`
    (inv(cexp x) + cexp (x)) / Cx (&2) = ccos(ii * x)`,

REWRITE_TAC[ccos; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`] THEN
REWRITE_TAC[GSYM CEXP_NEG]);;

let SINH = prove (
    `(cexp (x) - cexp (--x)) / Cx (&2) = --ii * csin(ii * x) `,

REWRITE_TAC[csin; COMPLEX_RING `--ii * ii * z = z /\ ii * ii * z = --z`]
 THEN REWRITE_TAC[CEXP_NEG; GSYM CX_EXP; GSYM CX_INV; CX_SUB; CX_DIV] THEN
  CONV_TAC COMPLEX_FIELD);;

let tanh = new_definition
 `tanh x = ((cexp x - cexp (--x)) / Cx (&2)) / ((cexp (--x) + cexp x) / Cx (&2))`;;

let TANH = prove (`tanh x = --ii * csin (ii * x) / ccos (ii * x)`,

REWRITE_TAC[tanh] THEN
ASM_REWRITE_TAC[SINH;COSH] THEN
SIMPLE_COMPLEX_ARITH_TAC);;

let MINUS_II_EXP = prove (`
         --ii = cexp (ii * --(Cx (pi) / Cx(&2)))`,

   REPEAT STRIP_TAC THEN REWRITE_TAC[CEXP_EULER]
     THEN ASM_SIMP_TAC[] THEN SIMP_TAC[CX_NEG;GSYM CX_DIV;CCOS_NEG;CSIN_NEG]
       THEN ASSERT_TAC `ccos (Cx (pi / &2)) = Cx (cos (pi / &2))`
     THENL [SIMP_TAC [CX_COS];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
     THEN SIMP_TAC[COS_PI2;COMPLEX_ADD_LID] THEN
       ASSERT_TAC `csin (Cx (pi / &2)) = Cx (sin (pi / &2))`
     THENL [SIMP_TAC [CX_SIN];ALL_TAC]
      THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[SIN_PI2]
        THEN CONV_TAC COMPLEX_RING);;


let II_EXP = prove (`
     Cx(&1) / (cexp (ii * --(Cx (pi) / Cx(&2)))) = cexp ((ii * (Cx (pi) / Cx(&2))))`,

    ASSERT_TAC `Cx (&1) = cexp (Cx (&0))` THEN SIMP_TAC[GSYM CEXP_0] THEN
         ASM_SIMP_TAC[] THEN
          SIMP_TAC[GSYM CEXP_SUB] THEN SIMP_TAC[COMPLEX_SUB_LZERO] THEN
   REWRITE_TAC[COMPLEX_FIELD `--(ii * --(Cx pi / Cx (&2))) = --(--(Cx pi / Cx (&2)) * ii)`] THEN
    SIMP_TAC[COMPLEX_FIELD `--(--(Cx pi / Cx (&2)) * ii) = (Cx pi / Cx (&2)) * ii`] THEN
     SIMP_TAC[COMPLEX_MUL_SYM]);;

(*==================== Some Custom Tactics ===============================*)

let SHORT_TAC =  BINOP_TAC THEN BINOP_TAC THEN SIMP_TAC[] THEN
                 SIMP_TAC[COMPLEX_FIELD `t = Cx (Re t) <=> Cx (Re t) = t`]
                 THEN  MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[]
                 THEN BINOP_TAC THEN SIMP_TAC[] THEN
                 SIMP_TAC[COMPLEX_FIELD `z = Cx (Re z) <=> Cx (Re z) = z`]
		 THEN MATCH_MP_TAC LEMMA_RE_ALT
		 THEN ASM_SIMP_TAC[];;
    
let EQ_DIFF_SIMP = BINOP_TAC THEN REWRITE_TAC[CX_MUL]
                   THEN BINOP_TAC THEN SIMP_TAC[]
		   THEN MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[]
		   THEN SIMP_TAC[CX_MUL] THEN BINOP_TAC
		   THEN SIMP_TAC[] THEN MATCH_MP_TAC LEMMA_RE_ALT
		   THEN ASM_SIMP_TAC[];;


(*===========================================================================*)
(*                               Section 4.1                                 *)
(*         Formalization of Telegrapher's Equations in Time Domain           *)
(*===========================================================================*)

(*===========================================================================*)
(*                             Definition 4.1                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                Telegrapher's Equation for Voltage                         *)
(*---------------------------------------------------------------------------*)

let telegraph_equation_voltage = new_definition
`telegraph_equation_voltage V II R L z t <=> 
   (complex_derivative (\z. V z t) z) = 
           -- (Cx L * complex_derivative (\t. II z t) t) - Cx R * (II z t)`;;

(*===========================================================================*)
(*                           Definition 4.2                                  *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                Telegrapher's Equation for Current                         *)
(*---------------------------------------------------------------------------*)

let telegraph_equation_current = new_definition
`telegraph_equation_current V II G C z t <=> 
  (complex_derivative (\z. II z t) z) = 
    -- (Cx C * complex_derivative (\t. V z t) t) - Cx G * (V z t)`;;


(*===========================================================================*)
(*                             Definition 4.3                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*               New Data-Type for Transmission Line Constants               *)
(*---------------------------------------------------------------------------*)

new_type_abbrev ("R",`:real`);;
new_type_abbrev ("L",`:real`);;
new_type_abbrev ("G",`:real`);;
new_type_abbrev ("C",`:real`);;

new_type_abbrev ("trans_line_const",`:R # L # G # C`);;


(*===========================================================================*)
(*                             Definition 4.4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                       Wave Equation for Voltage                           *)
(*---------------------------------------------------------------------------*)

let wave_voltage_equation = new_definition `
     wave_voltage_equation V ((R,L,G,C):trans_line_const) z t <=>
      higher_complex_derivative 2  (\z. V z t) z - Cx L * Cx C *
       (higher_complex_derivative 2  (\t. V z t) t) =
         (Cx R * Cx C + Cx G * Cx L) * (complex_derivative (\t. V z t) t) +
	                                             Cx R * Cx G * (V z t)`;;

(*===========================================================================*)
(*                             Definition 4.5                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                       Wave Equation for Current                           *)
(*---------------------------------------------------------------------------*)

let wave_current_equation = new_definition `
     wave_current_equation II ((R,L,G,C):trans_line_const) z t = 
      higher_complex_derivative 2  (\z. II z t) z - Cx L * Cx C *
       (higher_complex_derivative 2  (\t. II z t) t) =
         (Cx R * Cx C + Cx G * Cx L) * (complex_derivative (\t. II z t) t) +
	                                            Cx R * Cx G * (II z t)`;;

(*===========================================================================*)
(*                               Section 4.2                                 *)
(*         Formalization of Telegrapher's Equations in Phasor Domain         *)
(*===========================================================================*)

(*===========================================================================*)
(*                    Definitions 4.6 and 4.7                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                       Telegrapher's Equation                              *)
(*---------------------------------------------------------------------------*)

let telegraph_voltage = new_definition
`telegraph_voltage V II R L w z = 
      complex_derivative (\z. V (z)) z +
      (Cx R + ii * Cx w * Cx L) * II (z)`;;

let telegraph_equation_phasor_voltage = new_definition
`telegraph_equation_phasor_voltage V II R L w z  <=> 
    telegraph_voltage V II R L w z = Cx (&0)`;;
    
(*===========================================================================*)
(*                     Definitions 4.8 and 4.9                               *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                       Telegrapher's Equation                              *)
(*---------------------------------------------------------------------------*)

let telegraph_current = new_definition
`telegraph_current V II G C w z = 
   complex_derivative (\z. II (z)) z +
   (Cx G + ii * Cx w * Cx C) * V (z)`;;
   
 let telegraph_equation_phasor_current = new_definition
`telegraph_equation_phasor_current V II G C w z  <=> 
   telegraph_current V II G C w z = Cx (&0)`;;

(*============================================================================*)
(*                           Section 4.3                                      *)
(* Relationship between Telegrapher's and Wave Equations in Phasor Domain     *)
(*============================================================================*)

(*===========================================================================*)
(*                         Definition 4.10                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                       Propagation Constant                                *)
(*---------------------------------------------------------------------------*)

let propagation_constant = new_definition `
     propagation_constant ((R,L,G,C):trans_line_const) w
       = csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C))`;;

(*===========================================================================*)
(*                 Definitions 4.11 and 4.12                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                     Wave Equation for Voltage                             *)
(*---------------------------------------------------------------------------*)

let wave_voltage = new_definition `
     wave_voltage V z (tlc:trans_line_const) w =
      higher_complex_derivative 2  (\z. V (z)) z -
        (propagation_constant tlc w) pow 2 * V (z)`;;

let wave_equation_phasor_voltage = new_definition
`wave_equation_phasor_voltage V z (tlc:trans_line_const) w  =
    (wave_voltage V z tlc w = Cx (&0))`;;

(*===========================================================================*)
(*                 Definitions 4.13 and 4.14                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                   Wave Equation for Current                               *)
(*---------------------------------------------------------------------------*)

let wave_current = new_definition `
     wave_current II z tlc w = 
      higher_complex_derivative 2  (\z. II (z)) z -
       (propagation_constant tlc w) pow 2 * II (z)`;;

let wave_equation_phasor_current = new_definition
`wave_equation_phasor_current II z tlc w =
      wave_current II z tlc w = Cx (&0)`;;

(*===========================================================================*)
(*                               Theorem 4.1                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*    Relationship Between Telegrapher's and Wave Equations for Voltage      *)
(*---------------------------------------------------------------------------*)

let TELEGRAPH_WAVE_RELATIONSHIP_1 = prove (
`!V II z R L G C w. 
 let tlc = ((R,L,G,C):trans_line_const) in
 (\z. complex_derivative (\z. V z) z) complex_differentiable at z /\
    II complex_differentiable at z /\ 
	telegraph_current V II G C w z = Cx (&0)
      ==> complex_derivative (\z. telegraph_voltage V II R L w z) z =
                                               wave_voltage V z tlc w`,
 LET_TAC THEN (POP_ASSUM (K ALL_TAC))
 THEN REPEAT STRIP_TAC
  THEN REWRITE_TAC[telegraph_voltage;wave_voltage]
   THEN SIMP_TAC [ARITH_RULE `2 = SUC 1`]
    THEN REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1]
 THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[telegraph_current] THEN DISCH_TAC THEN
   SUBGOAL_THEN `complex_derivative
    (\z. complex_derivative (\z. V z) z + (Cx R + ii * Cx w * Cx L) * II z) z =
     complex_derivative (\z. complex_derivative (\z. V z) z) z + 
      complex_derivative (\z. (Cx R + ii * Cx w * Cx L) * II z) z` ASSUME_TAC THENL
 [MATCH_MP_TAC COMPLEX_DERIVATIVE_ADD THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN
   CONJ_TAC THEN SIMP_TAC[COMPLEX_DIFFERENTIABLE_CONST] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
 ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `complex_derivative (\z. (Cx R + ii * Cx w * Cx L) * II z) z  =
    (Cx R + ii * Cx w * Cx L) * complex_derivative (\z. II z) z` ASSUME_TAC THENL
 [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL THEN
  ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `complex_derivative (\z. II z) z + (Cx G + ii * Cx w * Cx C) * V z = Cx (&0)`
  THEN REWRITE_TAC[COMPLEX_FIELD `complex_derivative (\z. II z) z + (Cx G + ii * Cx w * Cx C) * V z =
   Cx (&0)  <=> complex_derivative (\z. II z) z = --(Cx G + ii * Cx w * Cx C) * V z`]
   THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[ETA_AX]
   THEN SIMP_TAC[ARITH_RULE `SUC 1 = 2`] THEN
   SIMP_TAC[propagation_constant;CSQRT]
   THEN CONV_TAC COMPLEX_FIELD);;
   
(*===========================================================================*)
(*                               Theorem 4.2                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*    Relationship Between Telegrapher's and Wave Equations for Current      *)
(*---------------------------------------------------------------------------*)

let TELEGRAPH_WAVE_RELATIONSHIP_2 = prove (
`!V II z R L G C w. 
 (let tlc = ((R,L,G,C):trans_line_const) in
(\z. complex_derivative (\z. II z) z) complex_differentiable at z /\
     V complex_differentiable at z /\ 
	 telegraph_voltage V II R L w z = Cx (&0)
       ==> complex_derivative (\z. telegraph_current V II G C w z) z =
                                                     wave_current II z tlc w)`,

LET_TAC THEN (POP_ASSUM (K ALL_TAC))
THEN REPEAT STRIP_TAC
 THEN REWRITE_TAC[telegraph_current;wave_current] THEN 
  SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN 
   REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1]
    THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[telegraph_voltage] THEN DISCH_TAC THEN
 SUBGOAL_THEN `complex_derivative (\z. complex_derivative (\z. II z)z +
  (Cx G + ii * Cx w * Cx C) * V z) z = complex_derivative (\z. complex_derivative (\z. II z) z) z +
       complex_derivative (\z. (Cx G + ii * Cx w * Cx C) * V z) z` ASSUME_TAC THENL
[MATCH_MP_TAC COMPLEX_DERIVATIVE_ADD THEN CONJ_TAC THEN ASM_SIMP_TAC[] THEN
 MATCH_MP_TAC COMPLEX_DIFFERENTIABLE_MUL_AT THEN CONJ_TAC
  THEN SIMP_TAC[COMPLEX_DIFFERENTIABLE_CONST] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN ASM_REWRITE_TAC[]
  THEN SUBGOAL_THEN `complex_derivative (\z. (Cx G + ii * Cx w * Cx C) * V z) z  =
   (Cx G + ii * Cx w * Cx C) * complex_derivative (\z. V z) z` ASSUME_TAC THENL
    [REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC COMPLEX_DERIVATIVE_LMUL
    THEN ASM_SIMP_TAC[]; ALL_TAC]
    THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `complex_derivative (\z. V z) z + (Cx R + ii * Cx w * Cx L) * II z = Cx (&0)`
      THEN REWRITE_TAC[COMPLEX_FIELD `complex_derivative (\z. V z) z +
       (Cx R + ii * Cx w * Cx L) * II z = Cx (&0)
         <=> complex_derivative (\z. V z) z = -- (Cx R + ii * Cx w * Cx L) * II z`]
    THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[ETA_AX]
    THEN REWRITE_TAC[ARITH_RULE `SUC 1 = 2`] THEN
    REWRITE_TAC[propagation_constant;CSQRT] THEN
    CONV_TAC COMPLEX_FIELD);;

(*===========================================================================*)
(*                             Section 5.1                                   *)
(*           Verification of the Solutions in Phasor Domain                  *)
(*===========================================================================*)

(*===========================================================================*)
(*                         Definition 5.1                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                       Characteristic Impedance                            *)
(*---------------------------------------------------------------------------*)

let characteristic_impedance = new_definition `
     characteristic_impedance ((R,L,G,C):trans_line_const) w =
	 (let tlc = ((R,L,G,C):trans_line_const) in
      (Cx R + ii * Cx w * Cx L) / propagation_constant tlc w)`;;

(*===========================================================================*)
(*                         Definition 5.2                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                      Wave Solution for Voltage                            *)
(*---------------------------------------------------------------------------*)

let wave_solution_voltage_phasor = new_definition 
`wave_solution_voltage_phasor (V1:complex) (V2:complex) (tlc:trans_line_const) (w:real) (z:complex) =
    V1 * cexp (--(propagation_constant tlc w) * z) +
     V2 * cexp ((propagation_constant tlc w) * z)`;;

(*===========================================================================*)
(*                         Definition 5.3                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                      Wave Solution for Current                            *)
(*---------------------------------------------------------------------------*)

let wave_solution_current_phasor = new_definition 
`wave_solution_current_phasor V1 V2 (tlc:trans_line_const) w z = 
  Cx (&1) / characteristic_impedance tlc w *
    (V1 * cexp (--(propagation_constant tlc w) * z) -
      V2 * cexp ((propagation_constant tlc w) * z))`;;

(*===========================================================================*)
(*                         Lemma 1 of Table 3                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*          First-Order Derivative of General Solution for Voltage           *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_1_ALT = prove (
 `!(V1:complex) (V2:complex) R C L G (w:real) (z:complex).
  complex_derivative (\z. wave_solution_voltage_phasor V1 V2 ((R,L,G,C):trans_line_const) w z) z =
   V1 * (--(propagation_constant (R,L,G,C) w)) * cexp (--(propagation_constant (R,L,G,C) w) * z) +
    V2 * (propagation_constant (R,L,G,C) w) * cexp ((propagation_constant (R,L,G,C) w) * z)`,

 REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  REWRITE_TAC [wave_solution_voltage_phasor;propagation_constant] THEN
   COMPLEX_DIFF_TAC THEN SIMP_TAC[COMPLEX_MUL_RID]);;


let WAVE_VOLTAGE_1 = prove (
 `!(V1:complex) (V2:complex) R C L G (w:real) (z:complex).
  let tlc = ((R,L,G,C):trans_line_const) in 
  complex_derivative (\z. wave_solution_voltage_phasor V1 V2 tlc w z) z =
   V1 * (--(propagation_constant tlc w)) * cexp (--(propagation_constant tlc w) * z) +
    V2 * (propagation_constant tlc w) * cexp ((propagation_constant tlc w) * z)`,

LET_TAC THEN SIMP_TAC[WAVE_VOLTAGE_1_ALT]);;


let WAVE_VOLTAGE_2_ALT = prove (
 `!(V1:complex) (V2:complex) R L G C (w:real) (z:complex).
   complex_derivative (\z. wave_solution_voltage_phasor V1 V2 ((R,L,G,C):trans_line_const) w z)  =
    (\z.  V1 * --(propagation_constant (R,L,G,C) w) * cexp (--(propagation_constant (R,L,G,C) w) * z) +
               V2 * (propagation_constant (R,L,G,C) w) * cexp ((propagation_constant (R,L,G,C) w) * z))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WAVE_VOLTAGE_1_ALT]);;


let WAVE_VOLTAGE_2 = prove (
 `!(V1:complex) (V2:complex) R L G C (w:real) (z:complex).
   let tlc = ((R,L,G,C):trans_line_const) in 
   complex_derivative (\z. wave_solution_voltage_phasor V1 V2 tlc w z)  =
    (\z.  V1 * --(propagation_constant tlc w) * cexp (--(propagation_constant tlc w) * z) +
               V2 * (propagation_constant tlc w) * cexp ((propagation_constant tlc w) * z))`,

LET_TAC THEN SIMP_TAC[WAVE_VOLTAGE_2_ALT]);;

(*---------------------------------------------------------------------------*)
(*           Auxiliary Lemma for Second-Order Derivative of                  *)
(*                    General Solution for Voltage                           *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_3_ALT = prove (
 `!(V1:complex) (V2:complex) R C L G (w:real) (z:complex).
   complex_derivative (\z. V1 *  --(propagation_constant ((R,L,G,C):trans_line_const) w) *
    cexp (--(propagation_constant (R,L,G,C) w) * z) + V2 * (propagation_constant (R,L,G,C) w) *
     cexp ((propagation_constant (R,L,G,C) w) * z)) z =
 V1 * (propagation_constant (R,L,G,C) w) pow 2 * cexp (--(propagation_constant (R,L,G,C) w) * z) +
  V2 * (propagation_constant (R,L,G,C) w) pow 2 * cexp ((propagation_constant (R,L,G,C) w) * z)`,

REPEAT STRIP_TAC THEN PURE_REWRITE_TAC[propagation_constant; CSQRT]
  THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN COMPLEX_DIFF_TAC THEN
   PURE_REWRITE_TAC[COMPLEX_MUL_RID] THEN
    REWRITE_TAC[COMPLEX_FIELD `V1 *
 --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
     cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) = V1 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)`] THEN

 REWRITE_TAC[COMPLEX_FIELD `V1 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
 V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) = V1 *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) +
   V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
    cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)`]

THEN SIMP_TAC[CSQRT]);;

let WAVE_VOLTAGE_3 = prove (
 `!(V1:complex) (V2:complex) R C L G (w:real) (z:complex).
   let tlc = ((R,L,G,C):trans_line_const) in 
   complex_derivative (\z. V1 *  --(propagation_constant tlc w) *
    cexp (--(propagation_constant tlc w) * z) + V2 * (propagation_constant tlc w) *
     cexp ((propagation_constant tlc w) * z)) z =
 V1 * (propagation_constant tlc w) pow 2 * cexp (--(propagation_constant tlc w) * z) +
  V2 * (propagation_constant tlc w) pow 2 * cexp ((propagation_constant tlc w) * z)`,

LET_TAC THEN SIMP_TAC [WAVE_VOLTAGE_3_ALT]);;

(*===========================================================================*)
(*                         Lemma 2 of Table 3                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*            Second-Order Derivative of General Solution for Voltage        *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_4_ALT = prove (
`!(V1:complex) (V2:complex) R L G C (w:real) (z:complex).
  higher_complex_derivative 2 (\z. wave_solution_voltage_phasor V1 V2 ((R,L,G,C):trans_line_const) w z) z =
   V1 * (propagation_constant (R,L,G,C) w) pow 2 * cexp (--(propagation_constant (R,L,G,C) w) * z) +
    V2 * (propagation_constant (R,L,G,C) w) pow 2 * cexp ((propagation_constant (R,L,G,C) w) * z)`,

 SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
  REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1] THEN
   REWRITE_TAC[propagation_constant;CSQRT] THEN SIMP_TAC [ARITH_RULE `SUC 1 = 2`]
    THEN SIMP_TAC[WAVE_VOLTAGE_2_ALT;WAVE_VOLTAGE_3_ALT] THEN SIMP_TAC [propagation_constant;CSQRT]);;


let WAVE_VOLTAGE_4 = prove (
`!(V1:complex) (V2:complex) R L G C (w:real) (z:complex).
   let tlc = ((R,L,G,C):trans_line_const) in 
  higher_complex_derivative 2 (\z. wave_solution_voltage_phasor V1 V2 tlc w z) z =
   V1 * (propagation_constant tlc w) pow 2 * cexp (--(propagation_constant tlc w) * z) +
    V2 * (propagation_constant tlc w) pow 2 * cexp ((propagation_constant tlc w) * z)`,

 LET_TAC THEN SIMP_TAC [WAVE_VOLTAGE_4_ALT]);;

(*===========================================================================*)
(*                               Theorem 5.1                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*               Correctness of the Solution for Voltage                     *)
(*---------------------------------------------------------------------------*)

let WAVE_SOLUTION_VOLTAGE_PHASOR_VERIFIED = prove (
 `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
 (wave_equation_phasor_voltage (\z. wave_solution_voltage_phasor V1 V2 tlc w z) (z) tlc w)`,

LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REWRITE_TAC[wave_equation_phasor_voltage; wave_voltage]
 THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[WAVE_VOLTAGE_4_ALT;wave_solution_voltage_phasor;propagation_constant;CSQRT]
  THEN SIMP_TAC[COMPLEX_FIELD `(   V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C))
    * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G +  ii * Cx w * Cx C)) * z) +
     V2 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) =
   ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
    (V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) *
     (Cx G + ii * Cx w * Cx C)) * z) +  V2 * (cexp (csqrt ((Cx R + ii * Cx w * Cx L) *
   (Cx G + ii * Cx w * Cx C)) * z)))`] THEN
   MESON_TAC[COMPLEX_SUB_0]);;

(*===========================================================================*)
(*                         Lemma 3 of Table 3                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*          First-Order Derivative of General Solution for Current           *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_1_ALT = prove (
 `!V1 V2 R L G C w z. 
 complex_derivative (\z. wave_solution_current_phasor V1 V2 ((R,L,G,C):trans_line_const) w z) z =
    Cx (&1) / characteristic_impedance (R,L,G,C) w *
    (V1 * (--propagation_constant (R,L,G,C) w) * cexp (--(propagation_constant (R,L,G,C) w) * z) -
      V2 * (propagation_constant (R,L,G,C) w) * cexp ((propagation_constant (R,L,G,C) w) * z))`, 

REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
THEN REWRITE_TAC [wave_solution_current_phasor;propagation_constant]
THEN COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_RID]);;


let WAVE_CURRENT_1 = prove (
 `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
 complex_derivative (\z. wave_solution_current_phasor V1 V2 tlc w z) z =
    Cx (&1) / characteristic_impedance tlc w *
    (V1 * (--propagation_constant tlc w) * cexp (--(propagation_constant tlc w) * z) -
      V2 * (propagation_constant tlc w) * cexp ((propagation_constant tlc w) * z))`, 

LET_TAC THEN REWRITE_TAC[WAVE_CURRENT_1_ALT]);;


let WAVE_CURRENT_2_ALT = prove (
 `!V1 V2 R L G C w z. 
 complex_derivative (\z. wave_solution_current_phasor V1 V2 ((R,L,G,C):trans_line_const) w z) =
   (\z. Cx (&1) / characteristic_impedance (R,L,G,C) w  *
    (V1 * (--propagation_constant (R,L,G,C) w) * cexp (--(propagation_constant (R,L,G,C) w) * z) -
      V2 * (propagation_constant (R,L,G,C) w * cexp ((propagation_constant (R,L,G,C) w) * z))))`,

REWRITE_TAC [FUN_EQ_THM] THEN MESON_TAC [WAVE_CURRENT_1_ALT]);;


let WAVE_CURRENT_2 = prove (
 `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in  
 complex_derivative (\z. wave_solution_current_phasor V1 V2 tlc w z) =
   (\z. Cx (&1) / characteristic_impedance tlc w  *
    (V1 * (--propagation_constant tlc w) * cexp (--(propagation_constant tlc w) * z) -
      V2 * (propagation_constant tlc w * cexp ((propagation_constant tlc w) * z))))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_2_ALT]);;

(*---------------------------------------------------------------------------*)
(*             Auxiliary Lemma for Second-Order Derivative of                *)
(*                    General Solution for Current                           *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_3_ALT = prove (
 `!V1 V2 R L G C w z. 
 complex_derivative (\z. Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w *
   (V1 * --propagation_constant (R,L,G,C) w * cexp (--(propagation_constant (R,L,G,C) w) * z) -
     V2 * propagation_constant (R,L,G,C) w * cexp ((propagation_constant (R,L,G,C) w) * z))) z =
      Cx (&1) / characteristic_impedance (R,L,G,C) w *
(V1 * (propagation_constant (R,L,G,C) w) pow 2 * cexp (--(propagation_constant (R,L,G,C) w) * z) -
 V2 * (propagation_constant (R,L,G,C) w) pow 2 * cexp ((propagation_constant (R,L,G,C) w) * z))`,

REPEAT STRIP_TAC THEN REWRITE_TAC[characteristic_impedance] THEN
REPEAT LET_TAC THEN POP_ASSUM MP_TAC THEN
ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [] THEN
DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
    THEN SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((Cx R + ii * Cx w * Cx L) / propagation_constant (R,L,G,C) w) =
      propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L)`]
      THEN REWRITE_TAC[propagation_constant; CSQRT]
      THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
      THEN COMPLEX_DIFF_TAC THEN REWRITE_TAC[COMPLEX_MUL_RID] THEN 
      SIMP_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) *
           (Cx G + ii * Cx w * Cx C)) / (Cx R + ii * Cx w * Cx L) *
      (V1 * --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
             --csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
      cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
       V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
             csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
     cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) =
           csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) / (Cx R + ii * Cx w * Cx L) *
     (V1 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
           csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
    cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
    V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
          csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`]
   THEN  SIMP_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) *
   (Cx G + ii * Cx w * Cx C)) /(Cx R + ii * Cx w * Cx L) *
    (V1 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
    V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
     csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) =
     csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) / (Cx R + ii * Cx w * Cx L) *
  (V1 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
   cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
      V2 * csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) pow 2 *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`] THEN
    SIMP_TAC[CSQRT] THEN
 REWRITE_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) =
   csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) / (Cx R + ii * Cx w * Cx L) *
 (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))`]);;


let WAVE_CURRENT_3 = prove (
 `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
 complex_derivative (\z. Cx (&1) / characteristic_impedance tlc w *
   (V1 * --propagation_constant tlc w * cexp (--(propagation_constant tlc w) * z) -
     V2 * propagation_constant tlc w * cexp ((propagation_constant tlc w) * z))) z =
      Cx (&1) / characteristic_impedance tlc w *
(V1 * (propagation_constant tlc w) pow 2 * cexp (--(propagation_constant tlc w) * z) -
 V2 * (propagation_constant tlc w) pow 2 * cexp ((propagation_constant tlc w) * z))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_3_ALT]);;



(*===========================================================================*)
(*                         Lemma 4 of Table 3                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*          Second-Order Derivative of General Solution for Current          *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_4_ALT = prove (
 `!V1 V2 R L G C w z. 
 higher_complex_derivative 2 (\z. wave_solution_current_phasor V1 V2 ((R,L,G,C):trans_line_const) w z) z =
   Cx (&1) / characteristic_impedance (R,L,G,C) w *
 (V1 * (propagation_constant (R,L,G,C) w) pow 2 * cexp (--(propagation_constant (R,L,G,C) w) * z) -
   V2 * (propagation_constant (R,L,G,C) w) pow 2 * cexp ((propagation_constant (R,L,G,C) w) * z))`,

SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
 REWRITE_TAC [higher_complex_derivative_alt;HIGHER_COMPLEX_DERIVATIVE_1]
  THEN REWRITE_TAC[propagation_constant;CSQRT] THEN
  REWRITE_TAC[WAVE_CURRENT_2_ALT;WAVE_CURRENT_3_ALT] THEN
  SIMP_TAC[propagation_constant;CSQRT] 
   THEN SIMP_TAC [ARITH_RULE `SUC 1 = 2 `] THEN
   SIMP_TAC[CSQRT]);;

let WAVE_CURRENT_4 = prove (
 `!V1 V2 R L G C w z. 
  let tlc = ((R,L,G,C):trans_line_const) in 
 higher_complex_derivative 2 (\z. wave_solution_current_phasor V1 V2 tlc w z) z =
   Cx (&1) / characteristic_impedance tlc w *
 (V1 * (propagation_constant tlc w) pow 2 * cexp (--(propagation_constant tlc w) * z) -
   V2 * (propagation_constant tlc w) pow 2 * cexp ((propagation_constant tlc w) * z))`,

LET_TAC THEN SIMP_TAC [WAVE_CURRENT_4_ALT]);;

(*===========================================================================*)
(*                               Theorem 5.2                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*               Correctness of the Solution for Current                     *)
(*---------------------------------------------------------------------------*)

let WAVE_SOLUTION_CURRENT_PHASOR_VERIFIED = prove (
`!V1 V2 R C L G w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  (wave_equation_phasor_current
    (\z. wave_solution_current_phasor V1 V2 tlc w z) z tlc w)`,

LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REWRITE_TAC[wave_equation_phasor_current; wave_current] THEN
ASM_SIMP_TAC[WAVE_CURRENT_4_ALT] THEN
REWRITE_TAC[wave_solution_current_phasor] THEN
REPEAT STRIP_TAC THEN SIMP_TAC[propagation_constant;CSQRT] 
THEN REWRITE_TAC[COMPLEX_FIELD `csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
   cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
   cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) -
 (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
  csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 *  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z)) =
 Cx (&0) <=> csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) /
 (Cx R + ii * Cx w * Cx L) * (V1 * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
  cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))  =
 (Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) *
 csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) / (Cx R + ii * Cx w * Cx L) *
 (V1 *  cexp (--csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z) -
  V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) * z))
`] THEN CONV_TAC COMPLEX_FIELD);;

(*===========================================================================*)
(*                               Theorem 5.3                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*         General Solution of the Telegrapher's Equation for Voltage        *)
(*---------------------------------------------------------------------------*)

let WAVESOL_FOR_TELEG_VOLTAGE = prove
(`!V1 V2 II V R L G C w z.  
   let tlc = ((R,L,G,C):trans_line_const) in 
    ~(Cx R + ii * Cx w * Cx L = Cx (&0)) /\
     (!z. V z = wave_solution_voltage_phasor V1 V2 tlc w z) /\
     (!z. II z = wave_solution_current_phasor V1 V2 tlc w z)
          ==> telegraph_equation_phasor_voltage V II R L w z`,

LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN REWRITE_TAC[telegraph_equation_phasor_voltage;telegraph_voltage]
         THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[WAVE_VOLTAGE_1_ALT;wave_solution_current_phasor]
 THEN SIMP_TAC [COMPLEX_FIELD `(V1 * --propagation_constant (R,L,G,C) w *
    cexp (--propagation_constant (R,L,G,C) w * z) + V2 * propagation_constant (R,L,G,C) w *
    cexp (propagation_constant (R,L,G,C) w * z)) + (Cx R + ii * Cx w * Cx L) *
   Cx (&1) / characteristic_impedance (R,L,G,C) w *
   (V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
     V2 * cexp (propagation_constant (R,L,G,C) w * z)) = Cx (&0) <=>
   (V1 *  --propagation_constant (R,L,G,C) w * cexp (--propagation_constant (R,L,G,C) w * z) +
  V2 * propagation_constant (R,L,G,C) w * cexp (propagation_constant (R,L,G,C) w * z)) +
 ((Cx R + ii * Cx w * Cx L) * Cx (&1) / characteristic_impedance (R,L,G,C) w) *
 (V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
  V2 * cexp (propagation_constant (R,L,G,C) w * z)) = Cx (&0)`] THEN
 SUBGOAL_THEN `(Cx R + ii * Cx w * Cx L) * Cx (&1) / characteristic_impedance (R,L,G,C) w =
 propagation_constant (R,L,G,C) w` ASSUME_TAC
 THENL [REWRITE_TAC[characteristic_impedance] THEN LET_TAC
 THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC []
 THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
 THEN SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((Cx R + ii * Cx w * Cx L) / propagation_constant (R,L,G,C) w) =
 propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L)`]
 THEN MATCH_MP_TAC COMPLEX_DIV_LMUL THEN ASM_SIMP_TAC[]; ALL_TAC]
 THEN ASM_REWRITE_TAC[] THEN
 REWRITE_TAC[COMPLEX_FIELD `!(a:complex) (b:complex). a + b = Cx(&0) <=> a = --b`]
 THEN SIMP_TAC[COMPLEX_SUB_LDISTRIB] THEN
 REWRITE_TAC[COMPLEX_FIELD `!(a:complex) (b:complex). --(a - b) = --a + b`] THEN
 SIMP_TAC[COMPLEX_FIELD `!(a:complex) (b:complex) (c:complex). --(a * b * c) = --a * b * c`]
 THEN CONV_TAC COMPLEX_FIELD);;

(*===========================================================================*)
(*                               Theorem 5.4                                 *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*         General Solution of the Telegrapher's Equation for Current        *)
(*---------------------------------------------------------------------------*)

let WAVESOL_FOR_TELEG_CURRENT = prove (
`!V1 V2 II V R L G C w z.  
   let tlc = ((R,L,G,C):trans_line_const) in 
~(Cx R + ii * Cx w * Cx L = Cx (&0)) /\
 (!z. V z = wave_solution_voltage_phasor V1 V2 tlc w z) /\
 (!z. II z = wave_solution_current_phasor V1 V2 tlc w z)
==> telegraph_equation_phasor_current V II G C w z`,

LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN
       REWRITE_TAC[telegraph_equation_phasor_current;telegraph_current] THEN
       ASM_REWRITE_TAC[] THEN REWRITE_TAC[WAVE_CURRENT_1_ALT;wave_solution_voltage_phasor]
       THEN SIMP_TAC[COMPLEX_FIELD `!(a:complex) (b:complex). a + b = Cx(&0) <=> a = --b`]
       THEN REWRITE_TAC[characteristic_impedance] THEN LET_TAC
 THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC []
 THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
 THEN SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((Cx R + ii * Cx w * Cx L) / propagation_constant (R,L,G,C) w)
          = propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L)`]
      THEN REWRITE_TAC[COMPLEX_FIELD `propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L) *
 (V1 * --propagation_constant (R,L,G,C) w * cexp (--propagation_constant (R,L,G,C) w * z) -
  V2 * propagation_constant (R,L,G,C) w * cexp (propagation_constant (R,L,G,C) w * z)) = (V1 * --propagation_constant (R,L,G,C) w * cexp (--propagation_constant (R,L,G,C) w * z) - V2 * propagation_constant (R,L,G,C) w *
  cexp (propagation_constant (R,L,G,C) w * z)) * propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L)`]
  THEN REWRITE_TAC[COMPLEX_ADD_LDISTRIB] THEN
  REWRITE_TAC[COMPLEX_FIELD `!(a:complex) (b:complex) (c:complex) (d:complex).
   --(a * b + c * d) = --a * b - c * d`] THEN
   REWRITE_TAC[COMPLEX_FIELD `--(Cx G + ii * Cx w * Cx C) * V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
 (Cx G + ii * Cx w * Cx C) * V2 * cexp (propagation_constant (R,L,G,C) w * z) = (Cx G + ii * Cx w * Cx C) * (--V1 *
 cexp (--propagation_constant (R,L,G,C) w * z) - V2 * cexp (propagation_constant (R,L,G,C) w * z))`]
 THEN SIMP_TAC[COMPLEX_FIELD `propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L) =
       propagation_constant (R,L,G,C) w * Cx(&1) /(Cx R + ii * Cx w * Cx L)`]
 THEN SIMP_TAC[COMPLEX_FIELD `(V1 * --propagation_constant (R,L,G,C) w * cexp (--propagation_constant (R,L,G,C) w * z) -
  V2 * propagation_constant (R,L,G,C) w * cexp (propagation_constant (R,L,G,C) w * z)) * propagation_constant (R,L,G,C) w * Cx (&1) / (Cx R + ii * Cx w * Cx L) = propagation_constant (R,L,G,C) w * (--V1 *
   cexp (--propagation_constant (R,L,G,C) w * z) - V2 * cexp (propagation_constant (R,L,G,C) w * z)) *
    propagation_constant (R,L,G,C) w * Cx (&1) / (Cx R + ii * Cx w * Cx L)`]
    THEN SIMP_TAC[COMPLEX_FIELD `propagation_constant (R,L,G,C) w *
     (--V1 * cexp (--propagation_constant (R,L,G,C) w * z) - V2 * cexp (propagation_constant (R,L,G,C) w * z)) *
     propagation_constant (R,L,G,C) w * Cx (&1) / (Cx R + ii * Cx w * Cx L) =
      (--V1 * cexp (--propagation_constant (R,L,G,C) w * z) - V2 * cexp (propagation_constant (R,L,G,C) w * z)) *
  propagation_constant (R,L,G,C) w * propagation_constant (R,L,G,C) w * Cx (&1) / (Cx R + ii * Cx w * Cx L)`]
  THEN SIMP_TAC[COMPLEX_FIELD `(--V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
  V2 * cexp (propagation_constant (R,L,G,C) w * z)) * propagation_constant (R,L,G,C) w * propagation_constant (R,L,G,C) w * Cx (&1) / (Cx R + ii * Cx w * Cx L) =
   (--V1 * cexp (--propagation_constant (R,L,G,C) w * z) - V2 * cexp (propagation_constant (R,L,G,C) w * z)) *
    propagation_constant (R,L,G,C) w pow 2 * Cx (&1) / (Cx R + ii * Cx w * Cx L)`]
    THEN REWRITE_TAC[propagation_constant;CSQRT]
    THEN REWRITE_TAC[COMPLEX_FIELD `(--V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) *
     (Cx G + ii * Cx w * Cx C)) * z) - V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) *
      (Cx G + ii * Cx w * Cx C)) * z)) * ((Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C)) *
       Cx (&1) / (Cx R + ii * Cx w * Cx L) = (--V1 * cexp (--csqrt ((Cx R + ii * Cx w * Cx L) *
       (Cx G + ii * Cx w * Cx C)) * z) - V2 * cexp (csqrt ((Cx R + ii * Cx w * Cx L) *
       (Cx G + ii * Cx w * Cx C)) * z)) * (Cx G + ii * Cx w * Cx C) * (Cx R + ii * Cx w * Cx L) *
         Cx (&1) / (Cx R + ii * Cx w * Cx L)`]
   THEN ASSERT_TAC `(Cx R + ii * Cx w * Cx L) * Cx (&1) / (Cx R + ii * Cx w * Cx L) =  Cx (&1)`
   THENL [MATCH_MP_TAC COMPLEX_DIV_LMUL THEN ASM_SIMP_TAC[];ALL_TAC]
   THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_RID] THEN CONV_TAC COMPLEX_FIELD);;

(*===========================================================================*)
(*                             Section 5.2                                   *)
(*                    Properties of Transmission Line                        *)
(*===========================================================================*)

(*===========================================================================*)
(*                       Theorem 1 of Table 4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                Attenuation Constant for Lossless Line                     *)
(*---------------------------------------------------------------------------*)

let ATTENUATION_COEFFICIENT_ALT = prove (
    `!R L G C w.  
	&0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
         ==> Re(propagation_constant ((R,L,G,C):trans_line_const) w) = &0`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[propagation_constant]
  THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_ADD_LID] THEN
   REWRITE_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C =
                                   (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`]
 THEN ASSERT_TAC `Cx w * Cx w * Cx L * Cx C * ii pow 2 = Cx (w * w * L * C) * ii pow 2`
 THENL [REWRITE_TAC[CX_MUL] THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN
  ASSERT_TAC `Cx(w * w * L * C) = Cx (w pow 2 * L * C)` THENL
 [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
  ASSERT_TAC `csqrt (Cx (w pow 2 * L * C) * ii pow 2) =
               Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)`
  THENL [MATCH_MP_TAC CSQRT_MUL_LCX THEN MATCH_MP_TAC REAL_LE_MUL
  THEN CONJ_TAC THEN  REWRITE_TAC[REAL_POW_2] THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC THEN
  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN
  ASSERT_TAC `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))` THENL
 [MATCH_MP_TAC CX_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN
  CONJ_TAC THEN REWRITE_TAC[REAL_POW_2]
   THEN  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
     THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC [COMPLEX_POW_II_2]
      THEN ASSERT_TAC `csqrt (--Cx (&1)) = ii` THENL
       [MATCH_MP_TAC CSQRT_MINUS THEN SIMP_TAC[RE_II;IM_II] THEN ASM_REAL_ARITH_TAC; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN
  ASSERT_TAC `Re (csqrt (Cx (w pow 2 * L * C)) * ii) =
               Re (ii * csqrt (Cx (w pow 2 * L * C)))` THENL
 [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]
  THEN REWRITE_TAC[RE_MUL_II] THEN
  ASSERT_TAC `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))` THENL
   [MATCH_MP_TAC CSQRT_CX THEN MATCH_MP_TAC REAL_LE_MUL THEN
    CONJ_TAC THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
     THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[]
      THEN SIMP_TAC[IM_CX] THEN REAL_ARITH_TAC);;

let ATTENUATION_COEFFICIENT = prove (
    `!R L G C w.  
  let tlc = ((R,L,G,C):trans_line_const) in 
	&0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
         ==> Re(propagation_constant tlc w) = &0`,

LET_TAC THEN REWRITE_TAC [ATTENUATION_COEFFICIENT_ALT]);;


(*===========================================================================*)
(*                       Theorem 2 of Table 4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                  Phase Constant for Lossless Line                         *)
(*---------------------------------------------------------------------------*)

let PHASE_COEFFICIENT_ALT = prove (`
      !R L G C w.  
 	  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
          ==> Im(propagation_constant ((R,L,G,C):trans_line_const) w) = w * sqrt(L * C)`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  REWRITE_TAC[propagation_constant] THEN ASM_REWRITE_TAC[] THEN
   REWRITE_TAC[COMPLEX_ADD_LID] THEN
 REWRITE_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C =
  (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`]
  THEN ASSERT_TAC `Cx w * Cx w * Cx L * Cx C * ii pow 2 =
   Cx (w * w * L * C) * ii pow 2` THENL [REWRITE_TAC[CX_MUL]
   THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
 ASSERT_TAC `Cx(w * w * L * C) = Cx (w pow 2 * L * C)` THENL
 [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
   ASSERT_TAC `csqrt (Cx (w pow 2 * L * C) * ii pow 2) =
               Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)` THENL
    [MATCH_MP_TAC CSQRT_MUL_LCX THEN MATCH_MP_TAC REAL_LE_MUL
    THEN CONJ_TAC THEN REWRITE_TAC[REAL_POW_2] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC
  THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN
  ASSERT_TAC `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))`
  THENL [MATCH_MP_TAC CX_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
   REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
   THEN ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
   THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC [COMPLEX_POW_II_2]
   THEN ASSERT_TAC `csqrt (--Cx (&1)) = ii` THENL
   [MATCH_MP_TAC CSQRT_MINUS THEN SIMP_TAC[RE_II;IM_II] THEN ASM_REAL_ARITH_TAC; ALL_TAC]
   THEN ASM_REWRITE_TAC[] THEN
   ASSERT_TAC `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))` THENL
   [MATCH_MP_TAC CSQRT_CX THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THEN
    REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
    THEN ASM_REAL_ARITH_TAC THEN  MATCH_MP_TAC REAL_LE_MUL
    THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[IM_MUL_II] THEN REWRITE_TAC[RE_CX]
    THEN REWRITE_TAC[SQRT_MUL] THEN ASSERT_TAC `sqrt (w pow 2) = w`
    THENL [REWRITE_TAC[REAL_POW_2] THEN REWRITE_TAC[SQRT_MUL] THEN
    REWRITE_TAC[REAL_FIELD `sqrt w * sqrt w = sqrt (w) pow 2`]
     THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC]
      THEN ONCE_ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;


let PHASE_COEFFICIENT = prove (`
      !R L G C w.  
    let tlc = ((R,L,G,C):trans_line_const) in 
 	  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
          ==> Im(propagation_constant tlc w) = w * sqrt(L * C)`,

LET_TAC THEN REWRITE_TAC [PHASE_COEFFICIENT_ALT]);;

(*===========================================================================*)
(*                       Theorem 3 of Table 4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*             Characteristic Impedance for Lossless Line                    *)
(*---------------------------------------------------------------------------*)

let CHARACTERISTIC_IMPEDANCE_LOSSLESS = prove (`
 !R L G C (w:real). 
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\
    R = &0 /\ G = &0 /\ ~(ii * Cx w = Cx (&0)) /\ ~(csqrt (Cx L * Cx C) = Cx (&0)) 
     
       ==> characteristic_impedance tlc w = csqrt(Cx L * Cx C) / Cx C`,

LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN 
 REWRITE_TAC[characteristic_impedance] THEN LET_TAC
 THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC []
 THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
 THEN REWRITE_TAC [propagation_constant] THEN
 ASM_SIMP_TAC[] THEN SIMP_TAC[COMPLEX_ADD_LID] THEN
     SIMP_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C =
                           (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`] THEN 
    SUBGOAL_THEN `Cx w * Cx w * Cx L * Cx C * ii pow 2 = Cx (w * w * L * C) * ii pow 2` ASSUME_TAC
 THENL [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]
 THEN SUBGOAL_THEN `Cx(w * w * L * C) = Cx (w pow 2 * L * C)` ASSUME_TAC
 THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[] THEN
 SUBGOAL_THEN `csqrt (Cx (w pow 2 * L * C) * ii pow 2) = Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)` ASSUME_TAC
 THENL[MATCH_MP_TAC CSQRT_MUL_LCX THEN MATCH_MP_TAC REAL_LE_MUL
           THEN CONJ_TAC THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL THEN
                ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;ALL_TAC]
 THEN ASM_REWRITE_TAC[] THEN
 SUBGOAL_THEN `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))` ASSUME_TAC
         THENL [MATCH_MP_TAC CX_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC
	 THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
         THEN ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;ALL_TAC]
	 THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC [COMPLEX_POW_II_2] THEN
 SUBGOAL_THEN `csqrt (--Cx (&1)) = ii` ASSUME_TAC THENL[MATCH_MP_TAC CSQRT_MINUS THEN SIMP_TAC[RE_II;IM_II] THEN ASM_REAL_ARITH_TAC;ALL_TAC]
 THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN  `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))`ASSUME_TAC
         THENL [MATCH_MP_TAC CSQRT_CX THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC
	 THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
         THEN ASM_REAL_ARITH_TAC THEN  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
	 THEN REWRITE_TAC[ASSUME `csqrt (Cx (w pow 2 * L * C)) = Cx (sqrt (w pow 2 * L * C))`]
	 THEN SUBGOAL_THEN `sqrt (w pow 2 * L * C) = sqrt (w pow 2) * sqrt (L) * sqrt(C)`ASSUME_TAC
	 THENL[SIMP_TAC[SQRT_MUL];ALL_TAC]
	 THEN REWRITE_TAC[ASSUME `sqrt (w pow 2 * L * C) = sqrt (w pow 2) * sqrt L * sqrt C`]
	 THEN SIMP_TAC[CX_MUL] THEN SUBGOAL_THEN `sqrt (w pow 2) = w` ASSUME_TAC
	 THENL[REWRITE_TAC[REAL_POW_2] THEN REWRITE_TAC[SQRT_MUL]
	 THEN REWRITE_TAC[REAL_FIELD `sqrt w * sqrt w = sqrt (w) pow 2`]
         THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[] THEN 
 SIMP_TAC[COMPLEX_FIELD `((Cx w * Cx (sqrt L) * Cx (sqrt C)) * ii) =
                                 (ii * Cx w) * Cx (sqrt L) * Cx (sqrt C)`] THEN
 SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) / ((ii * Cx w) * Cx (sqrt L) * Cx (sqrt C)) =
                     (ii * Cx w * Cx L) * Cx(&1) / ((ii * Cx w) * Cx (sqrt L) * Cx (sqrt C))`] THEN
 SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx (&1) / ((ii * Cx w) * Cx (sqrt L) * Cx (sqrt C)) =
            (ii * Cx w * Cx L) * Cx (&1) / (ii * Cx w) * Cx (&1) / Cx (sqrt L) * Cx (&1) / Cx (sqrt C)`] THEN
 SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx (&1) / (ii * Cx w) * Cx (&1) / Cx (sqrt L) * Cx (&1) / Cx (sqrt C)        = Cx (L) * (ii * Cx w) * Cx (&1) / (ii * Cx w) * Cx (&1) / Cx (sqrt L) * Cx (&1) / Cx (sqrt C)`] THEN 
 ASSERT_TAC `(ii * Cx w) * Cx (&1) / (ii * Cx w) = Cx(&1)`
 THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV THEN  ASM_SIMP_TAC[];ALL_TAC]
 THEN SIMP_TAC[COMPLEX_FIELD `Cx L * (ii * Cx w) * Cx (&1) / (ii * Cx w) * Cx (&1) / Cx (sqrt L) * Cx (&1) / Cx (sqrt C)  = Cx L * ((ii * Cx w) * Cx (&1) / (ii * Cx w)) * Cx (&1) / Cx (sqrt L) * Cx (&1) / Cx (sqrt C)`]
          THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LID] THEN
          REWRITE_TAC[COMPLEX_FIELD `Cx L * Cx (&1) / Cx (sqrt L) * Cx (&1) / Cx (sqrt C) =
	                                                   Cx L / (Cx (sqrt L) * Cx (sqrt C))`]
	  THEN SIMP_TAC[GSYM CX_MUL] THEN SIMP_TAC[GSYM SQRT_MUL] THEN
          ASSERT_TAC `Cx (sqrt (L * C)) = csqrt(Cx L * Cx C)`
 THENL[SIMP_TAC[GSYM CX_MUL] THEN MATCH_MP_TAC CX_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN
 ASM_REAL_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[] THEN 
                  ASSERT_TAC `Cx L / csqrt (Cx L * Cx C) =
		     csqrt (Cx L * Cx C) * (Cx(&1) / csqrt (Cx L * Cx C)) * Cx L / csqrt (Cx L * Cx C)`
          THENL [ASSERT_TAC `csqrt (Cx L * Cx C) * Cx (&1) / csqrt (Cx L * Cx C) = Cx(&1)`
	  THENL [REWRITE_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV
	  THEN ASM_SIMP_TAC[];ALL_TAC] THEN
 SIMP_TAC[COMPLEX_FIELD `csqrt (Cx L * Cx C) * Cx (&1) / csqrt (Cx L * Cx C) * Cx L / csqrt (Cx L * Cx C) =
                             (csqrt (Cx L * Cx C) * Cx (&1) / csqrt (Cx L * Cx C)) * Cx L / csqrt (Cx L * Cx C)`]
              THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LID];ALL_TAC]
	      THEN ONCE_ASM_REWRITE_TAC[] THEN
 SIMP_TAC[COMPLEX_FIELD `csqrt (Cx L * Cx C) * Cx (&1) / csqrt (Cx L * Cx C) *
 Cx L / csqrt (Cx L * Cx C) = csqrt (Cx L * Cx C) * Cx L / (csqrt (Cx L * Cx C) * csqrt (Cx L * Cx C))`]
 THEN SIMP_TAC[COMPLEX_FIELD `csqrt (Cx L * Cx C) * csqrt (Cx L * Cx C) = csqrt (Cx L * Cx C) pow 2`]
 THEN SIMP_TAC[CSQRT] THEN
 SIMP_TAC[COMPLEX_FIELD `csqrt (Cx L * Cx C) * Cx L / (Cx L * Cx C) =
                     csqrt (Cx L * Cx C) * Cx L * Cx(&1) / (Cx L * Cx C)`]
	      THEN REWRITE_TAC[COMPLEX_FIELD `csqrt (Cx L * Cx C) * Cx L * Cx (&1) / (Cx L * Cx C) =
	                            csqrt (Cx L * Cx C) * Cx L * Cx (&1) / (Cx L) * Cx(&1) / (Cx C)`]
	      THEN ASSERT_TAC `Cx L * Cx (&1) / Cx L = Cx(&1)`
	      THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV
	      THEN UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
	      THEN SIMP_TAC[COMPLEX_FIELD `csqrt (Cx L * Cx C) * Cx L * Cx (&1) / Cx L * Cx (&1) / Cx C =
	                                  csqrt (Cx L * Cx C) * (Cx L * Cx (&1) / Cx L) * Cx (&1) / Cx C`]
 THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LID] THEN SIMP_TAC[GSYM CX_MUL]
                             THEN SIMPLE_COMPLEX_ARITH_TAC);;

(*===========================================================================*)
(*                       Theorem 4 of Table 4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*             Attenuation Constant for Distortionless Line                  *)
(*---------------------------------------------------------------------------*)

let ATTENUATIONN_COEFFICIENT_DISTORTIONLESS = prove (
  `!R L G C (w:real).  
   let tlc = ((R,L,G,C):trans_line_const) in 
 &0 < L /\ &0 < R /\ &0 < G /\ R / L = G / C 
                     ==> Re(propagation_constant tlc w) = sqrt(R * G)`,

LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN
REWRITE_TAC[propagation_constant] THEN
      SUBGOAL_THEN `(Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) =
          Cx R * Cx G * (Cx(&1) + (ii * Cx w * Cx L) / Cx R) * (Cx(&1) +
	   (ii * Cx w * Cx C) / Cx G)` ASSUME_TAC THENL 

    [ASSERT_TAC `Cx (&1) = Cx R / Cx R ` THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
    THEN UNDISCH_TAC `&0 < R` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx R / Cx R + (ii * Cx w * Cx L) / Cx R = (Cx R + ii * Cx w * Cx L) / Cx R`]
    THEN ASSERT_TAC `Cx R / Cx R = Cx (&1)` THENL [ASM_SIMP_TAC[];ALL_TAC]
    THEN ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx (&1) = Cx G / Cx G `
    THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
    THEN UNDISCH_TAC `&0 < G` THEN
    SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN REWRITE_TAC[ASSUME `Cx (&1) = Cx G / Cx G`]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx G / Cx G + (ii * Cx w * Cx C) / Cx G =
                                     (Cx G + ii * Cx w * Cx C) / Cx G`] THEN
SIMP_TAC[COMPLEX_FIELD `Cx R * Cx G * (Cx R + ii * Cx w * Cx L) / Cx R * (Cx G + ii * Cx w * Cx C) / Cx G =
   (Cx R * (Cx R + ii * Cx w * Cx L) / Cx R) * (Cx G * (Cx G + ii * Cx w * Cx C) / Cx G)`] THEN

 SUBGOAL_THEN `Cx R * (Cx R + ii * Cx w * Cx L) / Cx R = Cx R + ii * Cx w * Cx L` ASSUME_TAC
         THENL [SIMP_TAC[complex_div] THEN
	 REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex)(c:complex). a * b * c = a * c * b`] THEN

       ASSERT_TAC `Cx R * inv (Cx R) = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_MUL_RINV THEN
       UNDISCH_TAC `&0 < R` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
       THEN SIMP_TAC[COMPLEX_FIELD `Cx R * inv (Cx R) * (Cx R + ii * Cx L * Cx w) =
                      (Cx R * inv (Cx R)) * (Cx R + ii * Cx L * Cx w)`]
       THEN ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID];ALL_TAC] THEN 

REWRITE_TAC[ASSUME `Cx R * (Cx R + ii * Cx w * Cx L) / Cx R = Cx R + ii * Cx w * Cx L`] THEN 

SUBGOAL_THEN `Cx G * (Cx G + ii * Cx w * Cx C) / Cx G = Cx G + ii * Cx w * Cx C` ASSUME_TAC
        THENL [SIMP_TAC[complex_div] THEN
	REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex)(c:complex). a * b * c = a * c * b`]
	THEN ASSERT_TAC `Cx G * inv (Cx G) = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_MUL_RINV THEN
        UNDISCH_TAC `&0 < G` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN 

REWRITE_TAC[COMPLEX_FIELD `Cx G * inv (Cx G) * (Cx G + ii * Cx C * Cx w) =
               (Cx G * inv (Cx G)) * (Cx G + ii * Cx C * Cx w)`] THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID];ALL_TAC] THEN

REWRITE_TAC[ASSUME `Cx G * (Cx G + ii * Cx w * Cx C) / Cx G = Cx G + ii * Cx w * Cx C`];ALL_TAC] THEN 

ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx R = Cx G * Cx L / Cx C` THENL 
[SIMP_TAC[COMPLEX_FIELD `Cx G * Cx L / Cx C = (Cx G / Cx C) * Cx L`]
          THEN ASSERT_TAC `Cx G / Cx C = Cx R / Cx L` THENL 

[SIMP_TAC[GSYM CX_DIV] THEN ASM_SIMP_TAC[];ALL_TAC] THEN  ASM_SIMP_TAC[] THEN 

                ASSERT_TAC `Cx R / Cx L * Cx L = Cx R * (Cx(&1) / Cx L * Cx L)` THENL 
      [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN 

 ASSERT_TAC `Cx (&1) / Cx L * Cx L = Cx(&1)` THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN

  MATCH_MP_TAC COMPLEX_MUL_LINV THEN UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
       THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_RID];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN ASSERT_TAC `Cx G / Cx C = Cx R / Cx L`
       THENL [ASM_SIMP_TAC[] THEN
       REWRITE_TAC[COMPLEX_FIELD `(Cx G * Cx L / Cx C) / Cx L = Cx G / Cx C *  (Cx L /  Cx L)`]
  THEN ASSERT_TAC `Cx L / Cx L = Cx(&1)` THENL  [MATCH_MP_TAC COMPLEX_DIV_REFL THEN
       UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN  SIMP_TAC[COMPLEX_MUL_RID];ALL_TAC] THEN REWRITE_TAC[ASSUME `Cx G / Cx C = Cx R / Cx L`]
       THEN ASSERT_TAC `Cx R / Cx L * Cx L =  Cx R` THENL  [MATCH_MP_TAC COMPLEX_DIV_RMUL THEN
       UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
  THEN SUBGOAL_THEN `(ii * Cx w * Cx L) / (Cx G * Cx L / Cx C) = (ii * Cx w * Cx C) / Cx G` ASSUME_TAC
  THENL [SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) / (Cx G * Cx L / Cx C) =
                   (ii * Cx w * Cx L) * Cx(&1) / (Cx G * Cx L / Cx C)`] THEN
  SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx (&1) / (Cx G * Cx L / Cx C) =
                    (ii * Cx w * Cx L) * Cx (&1) / ((Cx G * Cx L) / Cx C)`] THEN
  SIMP_TAC[COMPLEX_FIELD ` a / (b / c) = a * c / b`] THEN REWRITE_TAC[COMPLEX_MUL_LID]
           THEN REWRITE_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx C / (Cx G * Cx L) =
 	            ii * Cx w * Cx C * Cx L /(Cx L * Cx G)`] THEN
  SIMP_TAC[COMPLEX_FIELD `Cx L / (Cx L * Cx G) = (Cx L * Cx(&1) / Cx L) * (Cx(&1) / Cx G)`] THEN

         ASSERT_TAC `Cx L * Cx (&1) / Cx L = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
           UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 
       REWRITE_TAC[COMPLEX_MUL_LID] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN  SIMP_TAC[GSYM COMPLEX_POW_2] THEN ASSERT_TAC `Cx G * Cx L / Cx C = Cx R`
 THENL  [ASM_SIMP_TAC[];ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 
         REWRITE_TAC[COMPLEX_FIELD `Cx R * Cx G * (Cx (&1) + (ii * Cx w * Cx C) / Cx G) pow 2 =
	       (Cx R * Cx G) * (Cx (&1) + (ii * Cx w * Cx C) / Cx G) pow 2`] THEN
  REWRITE_TAC[GSYM CX_MUL] THEN
   SUBGOAL_THEN `csqrt (Cx (R * G) * (Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2) = Cx (sqrt(R * G)) * csqrt((Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2)` ASSUME_TAC
   THENL [MATCH_MP_TAC CSQRT_MUL_LCX_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
         CONJ_TAC THEN ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
   THEN SUBGOAL_THEN `csqrt ((Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2) =
                            Cx (&1) + (ii * Cx (w * C)) / Cx G` ASSUME_TAC THENL

 [MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[complex_mul;RE_II;IM_II;COMPLEX_MUL_LZERO;REAL_MUL_LZERO;REAL_MUL_LID;REAL_SUB_RZERO;REAL_SUB_LZERO;REAL_ADD_LID;RE_CX;IM_CX;RE_ADD;IM_ADD;RE_CX;IM_CX;REAL_ADD_LID;RE;IM]
       THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 

         SIMP_TAC[COMPLEX_FIELD `Cx (sqrt (R * G)) * (Cx (&1) + (ii * Cx (w * C)) / Cx G) =
	         Cx (sqrt (R * G)) * Cx (&1) + Cx (sqrt (R * G)) * (ii * Cx (w * C)) / Cx G`] THEN
   REWRITE_TAC[COMPLEX_MUL_RID] THEN SIMP_TAC[COMPLEX_FIELD `(ii * Cx (w * C)) / Cx G = ii * Cx (w * C) / Cx G`]
    THEN SIMP_TAC[complex_mul;RE_II;IM_II;REAL_MUL_LZERO;REAL_MUL_LID;REAL_SUB_LZERO;RE_CX;IM_CX;REAL_MUL_LZERO;RE;IM;RE_ADD;REAL_SUB_RZERO;REAL_ADD_LID;REAL_ADD_RID;GSYM CX_DIV;IM_CX;RE] THEN
                                                        SIMPLE_COMPLEX_ARITH_TAC);;

(*===========================================================================*)
(*                       Theorem 5 of Table 4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                 Phase Constant for Distortionless Line                    *)
(*---------------------------------------------------------------------------*)

g `!R L G C (w:real). 
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < L /\ &0 < C /\ &0 < R /\ &0 < G /\ R / L = G / C 
           ==> Im(propagation_constant tlc w) = w * sqrt(L * C)`;;

e(LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN
REWRITE_TAC[propagation_constant] THEN
      SUBGOAL_THEN `(Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) =
          Cx R * Cx G * (Cx(&1) + (ii * Cx w * Cx L) / Cx R) * (Cx(&1) +
	   (ii * Cx w * Cx C) / Cx G)` ASSUME_TAC THENL 

    [ASSERT_TAC `Cx (&1) = Cx R / Cx R ` THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
    THEN UNDISCH_TAC `&0 < R` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx R / Cx R + (ii * Cx w * Cx L) / Cx R = (Cx R + ii * Cx w * Cx L) / Cx R`]
    THEN ASSERT_TAC `Cx R / Cx R = Cx (&1)` THENL [ASM_SIMP_TAC[];ALL_TAC]
    THEN ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx (&1) = Cx G / Cx G `
    THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
    THEN UNDISCH_TAC `&0 < G` THEN
    SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN REWRITE_TAC[ASSUME `Cx (&1) = Cx G / Cx G`]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx G / Cx G + (ii * Cx w * Cx C) / Cx G =
                                     (Cx G + ii * Cx w * Cx C) / Cx G`] THEN
SIMP_TAC[COMPLEX_FIELD `Cx R * Cx G * (Cx R + ii * Cx w * Cx L) / Cx R * (Cx G + ii * Cx w * Cx C) / Cx G =
   (Cx R * (Cx R + ii * Cx w * Cx L) / Cx R) * (Cx G * (Cx G + ii * Cx w * Cx C) / Cx G)`] THEN

 SUBGOAL_THEN `Cx R * (Cx R + ii * Cx w * Cx L) / Cx R = Cx R + ii * Cx w * Cx L` ASSUME_TAC
         THENL [SIMP_TAC[complex_div] THEN
	 REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex)(c:complex). a * b * c = a * c * b`] THEN

       ASSERT_TAC `Cx R * inv (Cx R) = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_MUL_RINV THEN
       UNDISCH_TAC `&0 < R` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
       THEN SIMP_TAC[COMPLEX_FIELD `Cx R * inv (Cx R) * (Cx R + ii * Cx L * Cx w) =
                      (Cx R * inv (Cx R)) * (Cx R + ii * Cx L * Cx w)`]
       THEN ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID];ALL_TAC] THEN 

REWRITE_TAC[ASSUME `Cx R * (Cx R + ii * Cx w * Cx L) / Cx R = Cx R + ii * Cx w * Cx L`] THEN 

SUBGOAL_THEN `Cx G * (Cx G + ii * Cx w * Cx C) / Cx G = Cx G + ii * Cx w * Cx C` ASSUME_TAC
        THENL [SIMP_TAC[complex_div] THEN
	REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex)(c:complex). a * b * c = a * c * b`]
	THEN ASSERT_TAC `Cx G * inv (Cx G) = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_MUL_RINV THEN
        UNDISCH_TAC `&0 < G` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN 

REWRITE_TAC[COMPLEX_FIELD `Cx G * inv (Cx G) * (Cx G + ii * Cx C * Cx w) =
               (Cx G * inv (Cx G)) * (Cx G + ii * Cx C * Cx w)`] THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID];ALL_TAC] THEN

REWRITE_TAC[ASSUME `Cx G * (Cx G + ii * Cx w * Cx C) / Cx G = Cx G + ii * Cx w * Cx C`];ALL_TAC] THEN 

ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx R = Cx G * Cx L / Cx C` THENL 
[SIMP_TAC[COMPLEX_FIELD `Cx G * Cx L / Cx C = (Cx G / Cx C) * Cx L`]
          THEN ASSERT_TAC `Cx G / Cx C = Cx R / Cx L` THENL 

[SIMP_TAC[GSYM CX_DIV] THEN ASM_SIMP_TAC[];ALL_TAC] THEN  ASM_SIMP_TAC[] THEN 

                ASSERT_TAC `Cx R / Cx L * Cx L = Cx R * (Cx(&1) / Cx L * Cx L)` THENL 
      [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN 

 ASSERT_TAC `Cx (&1) / Cx L * Cx L = Cx(&1)` THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN

  MATCH_MP_TAC COMPLEX_MUL_LINV THEN UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
       THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_RID];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN ASSERT_TAC `Cx G / Cx C = Cx R / Cx L`
       THENL [ASM_SIMP_TAC[] THEN
       REWRITE_TAC[COMPLEX_FIELD `(Cx G * Cx L / Cx C) / Cx L = Cx G / Cx C *  (Cx L /  Cx L)`]
  THEN ASSERT_TAC `Cx L / Cx L = Cx(&1)` THENL  [MATCH_MP_TAC COMPLEX_DIV_REFL THEN
       UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN  SIMP_TAC[COMPLEX_MUL_RID];ALL_TAC] THEN REWRITE_TAC[ASSUME `Cx G / Cx C = Cx R / Cx L`]
       THEN ASSERT_TAC `Cx R / Cx L * Cx L =  Cx R` THENL  [MATCH_MP_TAC COMPLEX_DIV_RMUL THEN
       UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
  THEN SUBGOAL_THEN `(ii * Cx w * Cx L) / (Cx G * Cx L / Cx C) = (ii * Cx w * Cx C) / Cx G` ASSUME_TAC
  THENL [SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) / (Cx G * Cx L / Cx C) =
                   (ii * Cx w * Cx L) * Cx(&1) / (Cx G * Cx L / Cx C)`] THEN
  SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx (&1) / (Cx G * Cx L / Cx C) =
                    (ii * Cx w * Cx L) * Cx (&1) / ((Cx G * Cx L) / Cx C)`] THEN
  SIMP_TAC[COMPLEX_FIELD ` a / (b / c) = a * c / b`] THEN REWRITE_TAC[COMPLEX_MUL_LID]
           THEN REWRITE_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx C / (Cx G * Cx L) =
 	            ii * Cx w * Cx C * Cx L /(Cx L * Cx G)`] THEN
  SIMP_TAC[COMPLEX_FIELD `Cx L / (Cx L * Cx G) = (Cx L * Cx(&1) / Cx L) * (Cx(&1) / Cx G)`] THEN

         ASSERT_TAC `Cx L * Cx (&1) / Cx L = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
           UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 
       REWRITE_TAC[COMPLEX_MUL_LID] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN  SIMP_TAC[GSYM COMPLEX_POW_2] THEN ASSERT_TAC `Cx G * Cx L / Cx C = Cx R`
 THENL  [ASM_SIMP_TAC[];ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 
         REWRITE_TAC[COMPLEX_FIELD `Cx R * Cx G * (Cx (&1) + (ii * Cx w * Cx C) / Cx G) pow 2 =
	       (Cx R * Cx G) * (Cx (&1) + (ii * Cx w * Cx C) / Cx G) pow 2`] THEN
  REWRITE_TAC[GSYM CX_MUL] THEN
   SUBGOAL_THEN `csqrt (Cx (R * G) * (Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2) = Cx (sqrt(R * G)) * csqrt((Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2)` ASSUME_TAC
   THENL [MATCH_MP_TAC CSQRT_MUL_LCX_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
         CONJ_TAC THEN ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
   THEN SUBGOAL_THEN `csqrt ((Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2) =
                            Cx (&1) + (ii * Cx (w * C)) / Cx G` ASSUME_TAC THENL

 [MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[complex_mul;RE_II;IM_II;COMPLEX_MUL_LZERO;REAL_MUL_LZERO;REAL_MUL_LID;REAL_SUB_RZERO;REAL_SUB_LZERO;REAL_ADD_LID;RE_CX;IM_CX;RE_ADD;IM_ADD;RE_CX;IM_CX;REAL_ADD_LID;RE;IM]
       THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 

         SIMP_TAC[COMPLEX_FIELD `Cx (sqrt (R * G)) * (Cx (&1) + (ii * Cx (w * C)) / Cx G) =
	         Cx (sqrt (R * G)) * Cx (&1) + Cx (sqrt (R * G)) * (ii * Cx (w * C)) / Cx G`] THEN
   REWRITE_TAC[COMPLEX_MUL_RID] THEN SIMP_TAC[COMPLEX_FIELD `(ii * Cx (w * C)) / Cx G = ii * Cx (w * C) / Cx G`]

THEN ASSERT_TAC `Cx (sqrt (R * G)) = csqrt (Cx (R * G))` THENL
[MATCH_MP_TAC CX_SQRT THEN
MATCH_MP_TAC REAL_LE_MUL THEN 
ASM_REAL_ARITH_TAC;ALL_TAC] THEN
REWRITE_TAC[ASSUME `Cx (sqrt (R * G)) = csqrt (Cx (R * G))`] THEN 
SIMP_TAC[CX_MUL] THEN
REWRITE_TAC[ASSUME `Cx R = Cx G * Cx L / Cx C`] THEN
SIMP_TAC[GSYM CX_DIV] THEN
SIMP_TAC[GSYM CX_MUL]);;

e(ASSERT_TAC `csqrt (Cx ((G * L / C) * G)) = Cx(sqrt ((G * L / C) * G))`);; 
e(MATCH_MP_TAC CSQRT_CX);; 
e(MATCH_MP_TAC REAL_LE_MUL);;  
e(CONJ_TAC);; 
e(MATCH_MP_TAC REAL_LE_MUL);; 
e(CONJ_TAC);; 
e(ASM_REAL_ARITH_TAC);;
e(MATCH_MP_TAC REAL_LE_DIV);; 
e(ASM_REAL_ARITH_TAC);; 
e(ASM_REAL_ARITH_TAC);; 

e(REWRITE_TAC[ASSUME `csqrt (Cx ((G * L / C) * G)) = Cx (sqrt ((G * L / C) * G))`]) ;;

e(REWRITE_TAC[IM_ADD;complex_mul;RE_II;IM_II;REAL_MUL_LZERO;REAL_MUL_LID;REAL_SUB_LZERO;RE_CX;IM_CX;REAL_MUL_LZERO;
RE;IM]);;
e(SIMP_TAC[REAL_ADD_LID;REAL_ADD_RID;GSYM CX_DIV;RE_CX;SQRT_MUL]);;
e(REWRITE_TAC[REAL_MUL_SYM]);;

e(SIMP_TAC[REAL_FIELD `(C * w) / G * sqrt G * sqrt G * sqrt (L / C) = (C * w) / G * (sqrt G * sqrt G) * sqrt (L / C)`]);;

e(SIMP_TAC[REAL_FIELD ` (sqrt G * sqrt G) = sqrt G pow 2`]);; 
e(ASSERT_TAC `sqrt G pow 2 = G`);;
e(REWRITE_TAC[SQRT_POW2]);;
e(ASM_REAL_ARITH_TAC);;
e(REWRITE_TAC[ASSUME `sqrt G pow 2 = G`]);;
e(SIMP_TAC[REAL_FIELD `(C * w) / G * G * sqrt (L / C) = G * (C * w) / G * sqrt (L / C)`]);;
e(SIMP_TAC[REAL_FIELD `G * (C * w) / G * sqrt (L / C) = (G * (C * w) / G) * sqrt (L / C)`]);;
e(SIMP_TAC[REAL_FIELD `(G * (C * w) / G) = (G * &1 / G) * (C * w)`]);;
e(REWRITE_TAC[REAL_FIELD `(G * &1 / G) = (G / G)`]);;
e(ASSERT_TAC `G / G = &1`);;
e(MATCH_MP_TAC REAL_DIV_REFL);;

e(ASM_REAL_ARITH_TAC);;
e(ONCE_ASM_REWRITE_TAC[]);; 
e(REWRITE_TAC[REAL_MUL_LID]);; 
e(SIMP_TAC[SQRT_DIV]);;

e(ASSERT_TAC `sqrt L / sqrt C = sqrt L / sqrt C * sqrt C / sqrt C`);;
e(ASSERT_TAC `sqrt C / sqrt C = &1`);;
e(REWRITE_TAC[GSYM SQRT_DIV]);;
e(ASSERT_TAC `C / C = &1`);;
e(MATCH_MP_TAC REAL_DIV_REFL);;
e(ASM_REAL_ARITH_TAC);;
e(ONCE_ASM_REWRITE_TAC[]);; 
e(SIMP_TAC[SQRT_1]);;
e(ONCE_ASM_REWRITE_TAC[]);; 
e(SIMP_TAC[REAL_MUL_RID]);; 
e(ONCE_ASM_REWRITE_TAC[]);; 
e(SIMP_TAC[REAL_FIELD `sqrt L / sqrt C * sqrt C / sqrt C = sqrt L *( &1 / sqrt C) * sqrt C *( &1 / sqrt C)`]);;
e(SIMP_TAC[REAL_FIELD `sqrt L * &1 / sqrt C * sqrt C * &1 / sqrt C = sqrt L * sqrt C * &1 / sqrt C * &1 / sqrt C`]);;
e(SIMP_TAC[REAL_FIELD `&1 / sqrt C * &1 / sqrt C = &1 / sqrt C pow 2`]);;
e(ASSERT_TAC `sqrt C pow 2 = C`);;
e(REWRITE_TAC[SQRT_POW2]);;
e(ASM_REAL_ARITH_TAC);; 
e(ONCE_ASM_REWRITE_TAC[]);; 
e(SIMP_TAC[REAL_FIELD `(C * w) * sqrt L * sqrt C * &1 / C = w * sqrt L * C * sqrt C / C`]);;
e(ASSERT_TAC ` C * sqrt C / C = sqrt C`);;
e(MATCH_MP_TAC REAL_DIV_LMUL);;
e(ASM_REAL_ARITH_TAC);;
e(ONCE_ASM_REWRITE_TAC[]);;
e(REAL_ARITH_TAC);;

let DISTORTIONLESS_IMAGINARY = top_thm();;

(*===========================================================================*)
(*                       Theorem 6 of Table 4                                *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*           Characteristic Impedance for a Distortionless Line              *)
(*---------------------------------------------------------------------------*)

g `!R L G C w. 
     let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < L /\ &0 < C /\ &0 < R /\ &0 < G  /\
                  ~(Cx G + ii * Cx w * Cx C = Cx (&0)) /\
                       R / L = G / C
                        ==> characteristic_impedance tlc w = csqrt(Cx L * Cx C) / Cx C`;;

e(LET_TAC THEN POP_ASSUM (K ALL_TAC) THEN
REPEAT STRIP_TAC THEN
REWRITE_TAC[characteristic_impedance] THEN LET_TAC
 THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC []
 THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
 THEN REWRITE_TAC [propagation_constant] THEN
      SUBGOAL_THEN `(Cx R + ii * Cx w * Cx L) * (Cx G + ii * Cx w * Cx C) =
          Cx R * Cx G * (Cx(&1) + (ii * Cx w * Cx L) / Cx R) * (Cx(&1) +
	   (ii * Cx w * Cx C) / Cx G)` ASSUME_TAC THENL 

    [ASSERT_TAC `Cx (&1) = Cx R / Cx R ` THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
    THEN UNDISCH_TAC `&0 < R` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx R / Cx R + (ii * Cx w * Cx L) / Cx R = (Cx R + ii * Cx w * Cx L) / Cx R`]
    THEN ASSERT_TAC `Cx R / Cx R = Cx (&1)` THENL [ASM_SIMP_TAC[];ALL_TAC]
    THEN ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx (&1) = Cx G / Cx G `
    THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
    THEN UNDISCH_TAC `&0 < G` THEN
    SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN REWRITE_TAC[ASSUME `Cx (&1) = Cx G / Cx G`]
    THEN REWRITE_TAC[COMPLEX_FIELD `Cx G / Cx G + (ii * Cx w * Cx C) / Cx G =
                                     (Cx G + ii * Cx w * Cx C) / Cx G`] THEN
SIMP_TAC[COMPLEX_FIELD `Cx R * Cx G * (Cx R + ii * Cx w * Cx L) / Cx R * (Cx G + ii * Cx w * Cx C) / Cx G =
   (Cx R * (Cx R + ii * Cx w * Cx L) / Cx R) * (Cx G * (Cx G + ii * Cx w * Cx C) / Cx G)`] THEN

 SUBGOAL_THEN `Cx R * (Cx R + ii * Cx w * Cx L) / Cx R = Cx R + ii * Cx w * Cx L` ASSUME_TAC
         THENL [SIMP_TAC[complex_div] THEN
	 REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex)(c:complex). a * b * c = a * c * b`] THEN

       ASSERT_TAC `Cx R * inv (Cx R) = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_MUL_RINV THEN
       UNDISCH_TAC `&0 < R` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
       THEN SIMP_TAC[COMPLEX_FIELD `Cx R * inv (Cx R) * (Cx R + ii * Cx L * Cx w) =
                      (Cx R * inv (Cx R)) * (Cx R + ii * Cx L * Cx w)`]
       THEN ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID];ALL_TAC] THEN 

REWRITE_TAC[ASSUME `Cx R * (Cx R + ii * Cx w * Cx L) / Cx R = Cx R + ii * Cx w * Cx L`] THEN 

SUBGOAL_THEN `Cx G * (Cx G + ii * Cx w * Cx C) / Cx G = Cx G + ii * Cx w * Cx C` ASSUME_TAC
        THENL [SIMP_TAC[complex_div] THEN
	REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex)(c:complex). a * b * c = a * c * b`]
	THEN ASSERT_TAC `Cx G * inv (Cx G) = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_MUL_RINV THEN
        UNDISCH_TAC `&0 < G` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN 

REWRITE_TAC[COMPLEX_FIELD `Cx G * inv (Cx G) * (Cx G + ii * Cx C * Cx w) =
               (Cx G * inv (Cx G)) * (Cx G + ii * Cx C * Cx w)`] THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID];ALL_TAC] THEN

REWRITE_TAC[ASSUME `Cx G * (Cx G + ii * Cx w * Cx C) / Cx G = Cx G + ii * Cx w * Cx C`];ALL_TAC] THEN 

ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx R = Cx G * Cx L / Cx C` THENL 
[SIMP_TAC[COMPLEX_FIELD `Cx G * Cx L / Cx C = (Cx G / Cx C) * Cx L`]
          THEN ASSERT_TAC `Cx G / Cx C = Cx R / Cx L` THENL 

[SIMP_TAC[GSYM CX_DIV] THEN ASM_SIMP_TAC[];ALL_TAC] THEN  ASM_SIMP_TAC[] THEN 

                ASSERT_TAC `Cx R / Cx L * Cx L = Cx R * (Cx(&1) / Cx L * Cx L)` THENL 
      [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN 

 ASSERT_TAC `Cx (&1) / Cx L * Cx L = Cx(&1)` THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN

  MATCH_MP_TAC COMPLEX_MUL_LINV THEN UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
       THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_RID];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN ASSERT_TAC `Cx G / Cx C = Cx R / Cx L`
       THENL [ASM_SIMP_TAC[] THEN
       REWRITE_TAC[COMPLEX_FIELD `(Cx G * Cx L / Cx C) / Cx L = Cx G / Cx C *  (Cx L /  Cx L)`]
  THEN ASSERT_TAC `Cx L / Cx L = Cx(&1)` THENL  [MATCH_MP_TAC COMPLEX_DIV_REFL THEN
       UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN  SIMP_TAC[COMPLEX_MUL_RID];ALL_TAC] THEN REWRITE_TAC[ASSUME `Cx G / Cx C = Cx R / Cx L`]
       THEN ASSERT_TAC `Cx R / Cx L * Cx L =  Cx R` THENL  [MATCH_MP_TAC COMPLEX_DIV_RMUL THEN
       UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
  THEN SUBGOAL_THEN `(ii * Cx w * Cx L) / (Cx G * Cx L / Cx C) = (ii * Cx w * Cx C) / Cx G` ASSUME_TAC
  THENL [SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) / (Cx G * Cx L / Cx C) =
                   (ii * Cx w * Cx L) * Cx(&1) / (Cx G * Cx L / Cx C)`] THEN
  SIMP_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx (&1) / (Cx G * Cx L / Cx C) =
                    (ii * Cx w * Cx L) * Cx (&1) / ((Cx G * Cx L) / Cx C)`] THEN
  SIMP_TAC[COMPLEX_FIELD ` a / (b / c) = a * c / b`] THEN REWRITE_TAC[COMPLEX_MUL_LID]
           THEN REWRITE_TAC[COMPLEX_FIELD `(ii * Cx w * Cx L) * Cx C / (Cx G * Cx L) =
 	            ii * Cx w * Cx C * Cx L /(Cx L * Cx G)`] THEN
  SIMP_TAC[COMPLEX_FIELD `Cx L / (Cx L * Cx G) = (Cx L * Cx(&1) / Cx L) * (Cx(&1) / Cx G)`] THEN

         ASSERT_TAC `Cx L * Cx (&1) / Cx L = Cx (&1)` THENL [MATCH_MP_TAC COMPLEX_DIV_LMUL THEN
           UNDISCH_TAC `&0 < L` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 
       REWRITE_TAC[COMPLEX_MUL_LID] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN  SIMP_TAC[GSYM COMPLEX_POW_2] THEN ASSERT_TAC `Cx G * Cx L / Cx C = Cx R`
 THENL  [ASM_SIMP_TAC[];ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[] THEN 
         REWRITE_TAC[COMPLEX_FIELD `Cx R * Cx G * (Cx (&1) + (ii * Cx w * Cx C) / Cx G) pow 2 =
	       (Cx R * Cx G) * (Cx (&1) + (ii * Cx w * Cx C) / Cx G) pow 2`] THEN
  REWRITE_TAC[GSYM CX_MUL] THEN
   SUBGOAL_THEN `csqrt (Cx (R * G) * (Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2) = Cx (sqrt(R * G)) * csqrt((Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2)` ASSUME_TAC
   THENL [MATCH_MP_TAC CSQRT_MUL_LCX_LT THEN MATCH_MP_TAC REAL_LT_MUL THEN
         CONJ_TAC THEN ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
   THEN SUBGOAL_THEN `csqrt ((Cx (&1) + (ii * Cx (w * C)) / Cx G) pow 2) =
                            Cx (&1) + (ii * Cx (w * C)) / Cx G` ASSUME_TAC THENL

 [MATCH_MP_TAC POW_2_CSQRT THEN REWRITE_TAC[complex_mul;RE_II;IM_II;COMPLEX_MUL_LZERO;REAL_MUL_LZERO;REAL_MUL_LID;REAL_SUB_RZERO;REAL_SUB_LZERO;REAL_ADD_LID;RE_CX;IM_CX;RE_ADD;IM_ADD;RE_CX;IM_CX;REAL_ADD_LID;RE;IM]
       THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN  ONCE_ASM_REWRITE_TAC[]);;



e (SIMP_TAC[COMPLEX_FIELD `(Cx R + ii * Cx (w * L)) /
 (Cx (sqrt (R * G)) * (Cx (&1) + (ii * Cx (w * C)) / Cx G)) = (Cx R + ii * Cx (w * L)) * Cx(&1) /Cx (sqrt (R * G)) * Cx(&1) / (Cx (&1) + (ii * Cx (w * C)) / Cx G)`]);;
e (REWRITE_TAC[ASSUME `Cx R = Cx G * Cx L / Cx C`]);;

e (ASSERT_TAC `ii * Cx (w * L) = ii * Cx (w * L) * Cx C / Cx C`);;
e (ASSERT_TAC `Cx C / Cx C = Cx(&1)`);;
e (MATCH_MP_TAC COMPLEX_DIV_REFL);;
e (UNDISCH_TAC `&0 < C`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[COMPLEX_MUL_RID]);;
e (REWRITE_TAC[ASSUME `ii * Cx (w * L) = ii * Cx (w * L) * Cx C / Cx C`]);;
e (SIMP_TAC[COMPLEX_FIELD `(Cx G * Cx L / Cx C + ii * Cx (w * L) * Cx C / Cx C) = (Cx G * Cx L + ii * Cx (w * L) * Cx C) / Cx C`]);;
e (SUBGOAL_THEN `Cx (sqrt (R * G)) = csqrt (Cx (R * G))` ASSUME_TAC);;
e (MATCH_MP_TAC CX_SQRT);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (ASSERT_TAC `Cx (R * G) = Cx R * Cx G`);;
e (REWRITE_TAC[GSYM CX_MUL]);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[ASSUME `Cx R = Cx G * Cx L / Cx C`]);;
e (SIMP_TAC[COMPLEX_FIELD `(Cx G * Cx L / Cx C) * Cx G = (Cx G pow 2 * Cx L) / Cx C`]);;
e (ASSERT_TAC `(Cx G pow 2 * Cx L) = Cx(G pow 2 * L)`);;
e (REWRITE_TAC[CX_MUL;COMPLEX_POW_2;REAL_POW_2]);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[GSYM CX_DIV]);;
e (ASSERT_TAC `csqrt (Cx ((G pow 2 * L) / C)) = Cx (sqrt ((G pow 2 * L) / C))`);;
e (CONV_TAC SYM_CONV);;
e (MATCH_MP_TAC CX_SQRT);;
e (MATCH_MP_TAC REAL_LE_DIV);;
e (CONJ_TAC);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (CONJ_TAC);;
e (REWRITE_TAC[REAL_POW_2]);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ASM_REAL_ARITH_TAC);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[SQRT_DIV;SQRT_MUL]);;
e (ASSERT_TAC `sqrt (G pow 2) = G`);;
e (SIMP_TAC[REAL_POW_2;SQRT_MUL]);;
e (SIMP_TAC[REAL_FIELD `sqrt G * sqrt G = sqrt G pow 2`]);;
e (REWRITE_TAC[SQRT_POW2]);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[CX_DIV;CX_MUL]);;
e (SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((Cx G * Cx (sqrt L)) / Cx (sqrt C)) *
 Cx (&1) / (Cx (&1) + (ii * Cx w * Cx C) / Cx G) = Cx (&1) / ((Cx G * Cx (sqrt L)) / Cx (sqrt C) * (Cx (&1) + (ii * Cx w * Cx C) / Cx G))`]);;
e (SIMP_TAC[COMPLEX_FIELD `(Cx G * Cx L + ii * (Cx w * Cx L) * Cx C) / Cx C * Cx (&1) / ((Cx G * Cx (sqrt L)) / Cx (sqrt C) * (Cx (&1) + (ii * Cx w * Cx C) / Cx G)) = (Cx G * Cx L + ii * (Cx w * Cx L) * Cx C) / Cx C / ((Cx G * Cx (sqrt L)) / Cx (sqrt C) * (Cx (&1) + (ii * Cx w * Cx C) / Cx G))`]);;

e (ASSERT_TAC `Cx (&1) = Cx G / Cx G`);;
e (CONV_TAC SYM_CONV);;
e (MATCH_MP_TAC COMPLEX_DIV_REFL);;
e (UNDISCH_TAC `&0 < G`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[COMPLEX_FIELD `(Cx G / Cx G + (ii * Cx w * Cx C) / Cx G) = (Cx G + (ii * Cx w * Cx C)) / Cx G`]);;
e (SIMP_TAC[COMPLEX_FIELD `((Cx G * Cx (sqrt L)) / Cx (sqrt C) * (Cx G + ii * Cx w * Cx C) / Cx G) = (Cx (sqrt L) / Cx (sqrt C)) * (Cx G * Cx(&1) / Cx G) * (Cx G + ii * Cx w * Cx C)`]);;
e (SUBGOAL_THEN `Cx G * Cx (&1) / Cx G = Cx(&1)`ASSUME_TAC);;
e(REWRITE_TAC[complex_div;COMPLEX_MUL_LID]);;
e (MATCH_MP_TAC COMPLEX_MUL_RINV);;
e (UNDISCH_TAC `&0 < G`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_MUL_LID]);;
e (SIMP_TAC[COMPLEX_FIELD `(Cx G * Cx L + ii * (Cx w * Cx L) * Cx C) /
 Cx C = (Cx G * Cx L) / Cx C + (ii * (Cx w * Cx L) * Cx C) / Cx C`]);;
e (SIMP_TAC[COMPLEX_FIELD `((Cx G * Cx L) / Cx C + (ii * (Cx w * Cx L) * Cx C) / Cx C) = Cx L / Cx C * (Cx G + ii * Cx w  * Cx C)`]);;
e (REWRITE_TAC[COMPLEX_FIELD `Cx (sqrt L) / Cx (sqrt C) * (Cx G + ii * Cx w * Cx C) = (Cx G + ii * Cx w * Cx C) * Cx (sqrt L) / Cx (sqrt C)`]);;
e (SIMP_TAC[COMPLEX_FIELD `(Cx L / Cx C * (Cx G + ii * Cx w * Cx C)) /
 ((Cx G + ii * Cx w * Cx C) * Cx (sqrt L) / Cx (sqrt C)) = (Cx L / Cx C * (Cx G + ii * Cx w * Cx C)) * Cx(&1) / ((Cx G + ii * Cx w * Cx C) * Cx (sqrt L) / Cx (sqrt C))`]);;
 e (SIMP_TAC[COMPLEX_FIELD `(Cx L / Cx C * (Cx G + ii * Cx w * Cx C)) *
 Cx (&1) / ((Cx G + ii * Cx w * Cx C) * Cx (sqrt L) / Cx (sqrt C)) = (Cx L / Cx C * (Cx G + ii * Cx w * Cx C)) * (Cx (&1) / (Cx G + ii * Cx w * Cx C)) * Cx(&1) / (Cx (sqrt L) / Cx (sqrt C))`]);;
 e (SIMP_TAC[COMPLEX_FIELD `(Cx L / Cx C * (Cx G + ii * Cx w * Cx C)) *
 Cx (&1) / (Cx G + ii * Cx w * Cx C) *
 Cx (&1) / (Cx (sqrt L) / Cx (sqrt C)) = (Cx L / Cx C) * ((Cx G + ii * Cx w * Cx C) *
 Cx (&1) / (Cx G + ii * Cx w * Cx C)) *
 Cx (&1) / (Cx (sqrt L) / Cx (sqrt C))`]);;
 e (SUBGOAL_THEN `(Cx G + ii * Cx w * Cx C) * Cx (&1) / (Cx G + ii * Cx w * Cx C) = Cx(&1)`ASSUME_TAC);;
e (REWRITE_TAC[complex_div;COMPLEX_MUL_LID]);;
e (MATCH_MP_TAC COMPLEX_MUL_RINV);;
e (ASM_SIMP_TAC[]);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_MUL_LID]);;
e (SIMP_TAC[COMPLEX_FIELD `Cx L / Cx C * Cx G / Cx G / (Cx (sqrt L) / Cx (sqrt C)) = Cx L / Cx C * Cx G * (Cx(&1) / Cx G) / (Cx (sqrt L) / Cx (sqrt C))`]);;
e (SIMP_TAC[COMPLEX_FIELD `Cx L / Cx C * Cx G * Cx (&1) / Cx G / (Cx (sqrt L) / Cx (sqrt C)) = Cx L / Cx C * (Cx G * Cx (&1) / Cx G) / (Cx (sqrt L) / Cx (sqrt C))`]);;
e (REWRITE_TAC[ASSUME `Cx G * Cx (&1) / Cx G = Cx (&1)`]);;
e (SIMP_TAC[COMPLEX_FIELD `Cx L / Cx C * Cx (&1) / (Cx (sqrt L) / Cx (sqrt C)) = Cx L / Cx C * Cx (sqrt C) / Cx (sqrt L)`]);;
e (SUBGOAL_THEN `Cx L / Cx C * Cx (sqrt C) / Cx (sqrt L) = Cx L / Cx C * Cx (sqrt C) / Cx (sqrt L) * Cx (sqrt L) / Cx (sqrt L)`ASSUME_TAC);;
e (ASSERT_TAC `Cx (sqrt L) / Cx (sqrt L) = Cx(&1)`);;
e (MATCH_MP_TAC COMPLEX_DIV_REFL);;
e (ASSERT_TAC `&0 < sqrt L`);;
e (MATCH_MP_TAC SQRT_POS_LT);;
e (ASM_SIMP_TAC[]);;
e (UNDISCH_TAC `&0 < sqrt L`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_MUL_RID]);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[COMPLEX_FIELD `Cx L / Cx C * Cx (sqrt C) / Cx (sqrt L) * Cx (sqrt L) / Cx (sqrt L) = Cx L / Cx C * (Cx (sqrt C) * Cx (sqrt L)) / (Cx (sqrt L) * Cx (sqrt L))`]);;
e (SIMP_TAC[GSYM CX_MUL]);;
e (SIMP_TAC[GSYM REAL_POW_2]);;
e (ASSERT_TAC `sqrt L pow 2 = L`);;
e (REWRITE_TAC[SQRT_POW2]);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[COMPLEX_FIELD `Cx L / Cx C * Cx (sqrt C * sqrt L) / Cx L = (Cx L * Cx(&1) / Cx L) * Cx (sqrt C * sqrt L) / Cx C`]);;
e (SUBGOAL_THEN `Cx L * Cx (&1) / Cx L = Cx(&1)` ASSUME_TAC);;
e (SIMP_TAC[complex_div;COMPLEX_MUL_LID]);;
e (MATCH_MP_TAC COMPLEX_MUL_RINV);;
e (UNDISCH_TAC `&0 < L`);;
e (SIMPLE_COMPLEX_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (REWRITE_TAC[COMPLEX_MUL_LID;REAL_MUL_SYM;GSYM SQRT_MUL]);;
e (ASSERT_TAC `Cx (sqrt (C * L)) = csqrt (Cx (C * L))`);;
e (MATCH_MP_TAC CX_SQRT);;
e (MATCH_MP_TAC REAL_LE_MUL);;
e (ASM_REAL_ARITH_TAC);;
e (ONCE_ASM_REWRITE_TAC[]);;
e (SIMP_TAC[]);;

let CHARACTERISTIC_IMPEDANCE_DISTORTIONLESS = top_thm();;

(*===========================================================================*)
(*                             Section 5.3                                   *)
(*               Verification of the Solutions in Time-Domain                *)
(*===========================================================================*)

(*===========================================================================*)
(*                         Definition 5.4                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                      Wave Solution for Voltage                            *)
(*---------------------------------------------------------------------------*)

let wave_solution_voltage_time = new_definition `
 wave_solution_voltage_time (V1:complex) (V2:complex) (tlc:trans_line_const) (w:real) (z:complex) (t:complex) =
   Re((wave_solution_voltage_phasor V1 V2 tlc w z) * cexp(ii * Cx w * t))`;;

(*---------------------------------------------------------------------------*)
(*               Auxiliary Lemmas to prove Lemma 5.1                         *)
(*---------------------------------------------------------------------------*)

let PROPAGATION_CONSTANT_COMPLEX_ALT = prove (
`!R L G C w. 
  complex (Re (propagation_constant ((R,L,G,C):trans_line_const) w),
                       Im (propagation_constant (R,L,G,C) w))
                          = propagation_constant (R,L,G,C) w`,
MESON_TAC[COMPLEX]);;


let PROPAGATION_CONSTANT_COMPLEX = prove (
`!R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  complex (Re (propagation_constant tlc w),
                       Im (propagation_constant tlc w))
                          = propagation_constant tlc w`,
LET_TAC THEN REWRITE_TAC [PROPAGATION_CONSTANT_COMPLEX_ALT]);;


let REAL_COMPLEX_1 = prove (
`!x y. Re(Cx(x) + ii * Cx(y)) = x`,
REWRITE_TAC[ii] THEN 
SIMPLE_COMPLEX_ARITH_TAC);;


let PROPAGATION_CONSTANT_COMPLEX_TRAD_ALT = prove (
`!R L G C w.  
    complex (Re(propagation_constant ((R,L,G,C):trans_line_const) w),
                        Im(propagation_constant (R,L,G,C) w))
                         = Cx(Re(propagation_constant (R,L,G,C) w)) +
                          ii * Cx(Im(propagation_constant (R,L,G,C) w))`,
MESON_TAC[COMPLEX_TRAD]);;


let PROPAGATION_CONSTANT_COMPLEX_TRAD = prove (
`!R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
    complex (Re(propagation_constant tlc w),
                        Im(propagation_constant tlc w))
                         = Cx(Re(propagation_constant tlc w)) +
                          ii * Cx(Im(propagation_constant tlc w))`,
LET_TAC THEN REWRITE_TAC [PROPAGATION_CONSTANT_COMPLEX_TRAD_ALT]);;


let WAVE_VOLTAGE_TIME_1_ALT = prove (
 `!V1 V2 R C L G z w t. 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
   ==> wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t =
    Re(V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant (R,L,G,C) w)) * z)) +
        V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant (R,L,G,C) w)) * z)))`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
     REWRITE_TAC[wave_solution_voltage_time;wave_solution_voltage_phasor] THEN
     ONCE_ASM_REWRITE_TAC[GSYM PROPAGATION_CONSTANT_COMPLEX_ALT] THEN
     ONCE_ASM_REWRITE_TAC[PROPAGATION_CONSTANT_COMPLEX_TRAD_ALT] THEN
     REWRITE_TAC[COMPLEX_ADD_RDISTRIB] THEN
     ASSERT_TAC `Re (propagation_constant (R,L,G,C) w) = &0` THENL
     [ASM_SIMP_TAC[ATTENUATION_COEFFICIENT_ALT]; ALL_TAC]
     THEN REWRITE_TAC[ASSUME `Re (propagation_constant (R,L,G,C) w) = &0`]
     THEN SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_ADD_LID] THEN
 SUBGOAL_THEN `(V1 * cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)) *
    cexp (ii * Cx w * t) = (V1 * cexp (ii * Cx w * t) *
    cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z) )` ASSUME_TAC
    THENL [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(V1 * cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)) *
    cexp (ii * Cx w * t) = V1 * cexp (ii * Cx w * t) *
    cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)`] THEN
 SUBGOAL_THEN `(V2 * cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)) *
    cexp (ii * Cx w * t) = (V2 * cexp (ii * Cx w * t) *
    cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z))` ASSUME_TAC
   THENL [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[ASSUME `(V2 * cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)) *
   cexp (ii * Cx w * t) = V2 * cexp (ii * Cx w * t) *
   cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)`]
   THEN SIMP_TAC[GSYM CEXP_ADD;IM_MUL_II;RE_CX]
   THEN SIMP_TAC[COMPLEX_FIELD `a + --(b) * c = a - (b) * c`]
   THEN REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t - (ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z
        = ii * (Cx w * t - (Cx (Im (propagation_constant (R,L,G,C) w))) * z)`]
  THEN REWRITE_TAC[GSYM COMPLEX_MUL_LNEG]
  THEN SIMP_TAC[COMPLEX_FIELD `ii * Cx w * t + (ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z =
                                     ii * (Cx w * t + Cx (Im (propagation_constant (R,L,G,C) w)) * z)`]);;


let WAVE_VOLTAGE_TIME_1 = prove (
 `!V1 V2 R C L G z w t. 
   let tlc = ((R,L,G,C):trans_line_const) in  
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
   ==> wave_solution_voltage_time V1 V2 tlc w z t =
    Re(V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant tlc w)) * z)) +
        V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant tlc w)) * z)))`,

LET_TAC THEN REWRITE_TAC [WAVE_VOLTAGE_TIME_1_ALT]);;


let WAVE_VOLTAGE_TIME_2_ALT = prove (`
 !V1 V2 R C L G z w t. 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
  Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0
    ==> Re(V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant ((R,L,G,C):trans_line_const) w)) * z)) +
     V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant (R,L,G,C) w)) * z))) =
      Re(V1) * (cos(w * Re t - (Im(propagation_constant (R,L,G,C) w)) * Re z)) +
       Re (V2) * (cos(w * Re t +  Im((propagation_constant (R,L,G,C) w)) * Re z))`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
 ASSERT_TAC `(Cx w * t - Cx (Im (propagation_constant (R,L,G,C) w)) * z) =
  Cx (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z)`
  THENL [REWRITE_TAC[CX_SUB;CX_MUL]
   THEN SHORT_TAC; ALL_TAC] THEN
   REWRITE_TAC[ASSUME `Cx w * t - Cx (Im (propagation_constant (R,L,G,C) w)) * z =
    Cx (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN
 SUBGOAL_THEN `(Cx w * t + Cx (Im (propagation_constant (R,L,G,C) w)) * z) =
   Cx (w * Re t + (Im (propagation_constant (R,L,G,C) w)) * Re z)` ASSUME_TAC
   THENL [REWRITE_TAC[CX_ADD;CX_MUL]
   THEN SHORT_TAC; ALL_TAC] THEN
   REWRITE_TAC [ASSUME `Cx w * t + Cx (Im (propagation_constant (R,L,G,C) w)) * z =
      Cx (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN
  PURE_REWRITE_TAC[EULER] THEN
  SIMP_TAC[complex_mul;IM;RE;IM_CX;REAL_MUL_LZERO;
  REAL_ADD_RID;RE_CX;REAL_SUB_RZERO; RE_II;IM_II; REAL_MUL_LZERO;REAL_MUL_RZERO;
  REAL_ADD_LID;REAL_ADD_RID;REAL_ADD_LID; REAL_ADD_RID; REAL_SUB_RZERO;REAL_SUB_LZERO]
  THEN  REWRITE_TAC[GSYM complex_mul] THEN
  REWRITE_TAC[RE_ADD;IM_ADD;RE_SUB;IM_SUB; RE;IM;REAL_MUL_LID;REAL_NEG_0;REAL_EXP_0]
  THEN SIMP_TAC[REAL_MUL_LID;REAL_ADD_RID;RE_CX;IM_CX;REAL_ADD_LID]
  THEN ASSERT_TAC `Im V1 = Im (Cx (Re V1))`
  THENL [REWRITE_TAC[IM_CX] THEN ASM_SIMP_TAC[]; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_MUL_LZERO;REAL_SUB_RZERO]);;


let WAVE_VOLTAGE_TIME_2 = prove (`
 !V1 V2 R C L G z w t. 
   let tlc = ((R,L,G,C):trans_line_const) in  
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
  Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0
    ==> Re(V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant tlc w)) * z)) +
     V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant tlc w)) * z))) =
      Re(V1) * (cos(w * Re t - (Im(propagation_constant tlc w)) * Re z)) +
       Re (V2) * (cos(w * Re t +  Im((propagation_constant tlc w)) * Re z))`,

LET_TAC THEN REWRITE_TAC [WAVE_VOLTAGE_TIME_2_ALT]);;

(*===========================================================================*)
(*                           Lemma 5.1                                       *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*     Relationship between Phasor and Time-Domain Functions for Voltage     *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_TIME_3_ALT = prove (`
 !V1 V2 R L G C w z t. 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
  Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0
    ==> wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t =
     Re(V1) * (cos(w * Re t - (Im(propagation_constant (R,L,G,C) w)) * Re z)) +
      Re (V2) * (cos(w * Re t +  Im((propagation_constant (R,L,G,C) w)) * Re z))`,

ASM_SIMP_TAC[WAVE_VOLTAGE_TIME_1_ALT; WAVE_VOLTAGE_TIME_2_ALT]);;


let WAVE_VOLTAGE_TIME_3 = prove (`
 !V1 V2 R L G C w z t. 
    let tlc = ((R,L,G,C):trans_line_const) in 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
  Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0
    ==> wave_solution_voltage_time V1 V2 tlc w z t =
     Re(V1) * (cos(w * Re t - (Im(propagation_constant tlc w)) * Re z)) +
      Re (V2) * (cos(w * Re t +  Im((propagation_constant tlc w)) * Re z))`,

LET_TAC THEN SIMP_TAC [WAVE_VOLTAGE_TIME_3_ALT]);;

(*---------------------------------------------------------------------------*)
(*                Auxiliary Lemmas to Prove Lemma 1 of Table 5               *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_SOL_TIME_ALT_1 = prove (
`!V1 V2 R L G C w. (!t. Im t = &0) /\ (!z. Im z = &0)
  ==> complex_derivative (\z. Cx (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) +
       Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z))) z =
        Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * (--(w * sqrt (L * C))) +
	 Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))))`,

  REPEAT STRIP_TAC THEN REWRITE_TAC[CX_ADD;CX_MUL]
  THEN SIMP_TAC[CX_COS;CX_NEG;CX_SIN] THEN
ASSERT_TAC `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) = Cx (w) * t - Cx(w * sqrt (L * C)) * z`
  THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN
  ASSERT_TAC `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) = Cx (w) * t + Cx(w * sqrt (L * C)) * z`
  THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP; ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN
  COMPLEX_DIFF_TAC THEN SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;
  COMPLEX_ADD_LID;COMPLEX_MUL_RID;CX_MUL] THEN CONV_TAC COMPLEX_RING);;

let WAVE_VOLTAGE_SOL_TIME_ALT_2 = prove (
 `!V1 V2 R L G C w z t. (!t. Im t = &0) /\ (!z. Im z = &0)
   ==> complex_derivative (\z. Cx (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) +
        Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))  =
	 (\z. Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * (--(w * sqrt (L * C))) +
	  Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C)))))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WAVE_VOLTAGE_SOL_TIME_ALT_1]);;

(*===========================================================================*)
(*                           Lemma 1 of Table 5                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    First-Order Partial Derivative of                      *)
(*                General Solution for Voltage w.r.t distance                *)
(*---------------------------------------------------------------------------*)

let FIRST_ORDER_GENERAL_SOL_TIME_Z_ALT = prove (
`!V1 V2 R L G C w.  
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> complex_derivative (\z. Cx(wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t)) z = 
	 Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * (--(w * sqrt (L * C))) +
	  Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))))`,

REPEAT STRIP_TAC THEN
ASSERT_TAC `!z t.  wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) + Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)` THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_VOLTAGE_TIME_3_ALT];ALL_TAC] THEN
REWRITE_TAC[ASSUME `!z t. wave_solution_voltage_time V1 V2 (R,L,G,C) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) +  Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC]
       THEN ONCE_ASM_REWRITE_TAC[] THEN
       ASM_SIMP_TAC[WAVE_VOLTAGE_SOL_TIME_ALT_1]);;


let FIRST_ORDER_GENERAL_SOL_TIME_Z = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> complex_derivative (\z. Cx(wave_solution_voltage_time V1 V2 tlc w z t)) z = 
	 Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * (--(w * sqrt (L * C))) +
	  Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))))`,

LET_TAC THEN REWRITE_TAC [FIRST_ORDER_GENERAL_SOL_TIME_Z_ALT]);;

(*---------------------------------------------------------------------------*)
(*                Auxiliary Lemma to Prove Lemma 2 of Table 5                *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_SOL_TIME_ALT_3 = prove (
 `!V1 V2 R L G C w z t. (!t. Im t = &0) /\ (!z. Im z = &0)
   ==> complex_derivative (\z. Cx (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
        Re V2 * --sin (w * Re t + (w * sqrt (L * C)) * Re z) * w * sqrt (L * C))) z = 
         Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2 +
	  Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2)`,

   REPEAT STRIP_TAC THEN REWRITE_TAC[CX_ADD;CX_MUL]
     THEN SIMP_TAC[CX_COS;CX_NEG;CX_SIN] THEN
     SUBGOAL_THEN `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
        Cx (w) * t - Cx(w * sqrt (L * C)) * z` ASSUME_TAC
	THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
	THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
	 Cx (w) * t + Cx(w * sqrt (L * C)) * z` ASSUME_TAC
	 THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
	 THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN COMPLEX_DIFF_TAC THEN
  SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;COMPLEX_MUL_RID;CX_MUL]
  THEN
  ASSERT_TAC `--(--(Cx w * Cx (sqrt (L * C))) *
    ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z)) = -- --(Cx w * Cx (sqrt (L * C))) *
    ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z)`
  THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[]
  THEN SIMP_TAC[COMPLEX_NEG_NEG;CX_POW;COMPLEX_POW_2] THEN
  REWRITE_TAC[COMPLEX_FIELD `Cx (Re V1) * ((Cx w * Cx (sqrt (L * C))) *
   ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z)) *  --(Cx w * Cx (sqrt (L * C))) +
   Cx (Re V2) * --((Cx w * Cx (sqrt (L * C))) * ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z)) *
   Cx w * Cx (sqrt (L * C)) = Cx (Re V1) * (Cx w * Cx (sqrt (L * C))) *
   ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) * --(Cx w * Cx (sqrt (L * C))) +
   Cx (Re V2) * --(Cx w * Cx (sqrt (L * C))) * ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) *
   Cx w * Cx (sqrt (L * C))`] THEN SIMP_TAC[CX_MUL] THEN

  SIMP_TAC[COMPLEX_FIELD `Cx (Re V1) * (Cx w * Cx (sqrt (L * C))) * --(Cx w * Cx (sqrt (L * C))) *
   ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) + Cx (Re V2) * --(Cx w * Cx (sqrt (L * C))) *
   ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx w * Cx (sqrt (L * C)) =
   Cx (Re V1) * (Cx w * Cx (sqrt (L * C))) * (Cx w * Cx (sqrt (L * C))) *
   --ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) + Cx (Re V2) *
   (Cx w * Cx (sqrt (L * C))) * --ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) *
   Cx w * Cx (sqrt (L * C))`]

THEN CONV_TAC COMPLEX_FIELD);;

(*===========================================================================*)
(*                           Lemma 2 of Table 5                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                 Second-Order Partial Derivative of                        *)
(*               General Solution for Voltage w.r.t distance                 *)
(*---------------------------------------------------------------------------*)

let HIGHER_DERIV_GENERAL_SOL_TIME_Z_1 = prove (
`!V1 V2 R L G C w.  
&0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
	 ==> higher_complex_derivative 2 (\z. Cx(wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t)) z = 
	 Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2 +
	    Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2)`,

REPEAT STRIP_TAC THEN
ASSERT_TAC `!z t.  wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) + Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)` THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_VOLTAGE_TIME_3_ALT];ALL_TAC] THEN
REWRITE_TAC[ASSUME `!z t. wave_solution_voltage_time V1 V2 (R,L,G,C) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) +  Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
       REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1] THEN
ASM_SIMP_TAC[WAVE_VOLTAGE_SOL_TIME_ALT_2;WAVE_VOLTAGE_SOL_TIME_ALT_3] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let HIGHER_DERIV_GENERAL_SOL_TIME_Z = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
&0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\z. Cx(wave_solution_voltage_time V1 V2 tlc w z t)) z = 
	 Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2 +
	    Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2)`,

LET_TAC THEN REWRITE_TAC [HIGHER_DERIV_GENERAL_SOL_TIME_Z_1]);;


let HIGHER_DERIV_GENERAL_SOL_TIME_Z_ALT_1 = prove (
`!V1 V2 R L G C w.  
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\z.(Cx(wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t))) = 
	 (\z. Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2 +
	  Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[HIGHER_DERIV_GENERAL_SOL_TIME_Z_1]);;


let HIGHER_DERIV_GENERAL_SOL_TIME_Z_ALT = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
	 ==> higher_complex_derivative 2 (\z.(Cx(wave_solution_voltage_time V1 V2 tlc w z t))) = 
	 (\z. Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2 +
	  Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * ((w * sqrt (L * C))) pow 2))`,

LET_TAC THEN REWRITE_TAC[HIGHER_DERIV_GENERAL_SOL_TIME_Z_ALT_1]);;

(*---------------------------------------------------------------------------*)
(*             Auxiliary Lemmas to Prove Lemma 3 of Table 5                  *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_SOL_TIME_ALT_4 = prove (
 `!V1 V2 R L G C w z t. (!t. Im t = &0) /\ (!z. Im z = &0)
   ==> complex_derivative (\t. Cx (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) +
        Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z))) t =
	 Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	  Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w)`,

   REPEAT STRIP_TAC THEN REWRITE_TAC[CX_ADD;CX_MUL]
          THEN SIMP_TAC[CX_COS;CX_NEG;CX_SIN] THEN
   ASSERT_TAC `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
                     Cx (w) * t - Cx(w * sqrt (L * C)) * z`
   THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
   THEN ASM_REWRITE_TAC[] THEN
   SUBGOAL_THEN `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
                        Cx (w) * t + Cx(w * sqrt (L * C)) * z` ASSUME_TAC
   THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
   THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
   THEN COMPLEX_DIFF_TAC THEN
   SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;COMPLEX_MUL_RID;CX_MUL]
   THEN CONV_TAC COMPLEX_FIELD);;

let WAVE_VOLTAGE_SOL_TIME_ALT_5 = prove (
    `!V1 V2 R L G C w z t. (!t. Im t = &0) /\ (!z. Im z = &0)
       ==> complex_derivative (\t. Cx (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) +
            Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z))) =
	     (\t. Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	      Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w))`,


REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WAVE_VOLTAGE_SOL_TIME_ALT_4]);;

(*===========================================================================*)
(*                           Lemma 3 of Table 5                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                 First-Order Partial Derivative of                         *)
(*                General Solution for Voltage w.r.t time                    *)
(*---------------------------------------------------------------------------*)

let FIRST_ORDER_GENERAL_SOL_TIME_T_ALT = prove (
`!V1 V2 R L G C w.  
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> complex_derivative (\t. Cx(wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t)) = 
	 (\t. Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	  Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w))`,

REPEAT STRIP_TAC THEN
ASSERT_TAC `!z t.  wave_solution_voltage_time V1 V2 (R,L,G,C) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) + Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)` THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_VOLTAGE_TIME_3_ALT];ALL_TAC] THEN
REWRITE_TAC[ASSUME `!z t. wave_solution_voltage_time V1 V2 (R,L,G,C) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) +  Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC [WAVE_VOLTAGE_SOL_TIME_ALT_4; WAVE_VOLTAGE_SOL_TIME_ALT_5]);;


let FIRST_ORDER_GENERAL_SOL_TIME_T = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
	 ==> complex_derivative (\t. Cx(wave_solution_voltage_time V1 V2 tlc w z t)) = 
	 (\t. Cx (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	  Re V2 * (--sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w))`,

LET_TAC THEN REWRITE_TAC [FIRST_ORDER_GENERAL_SOL_TIME_T_ALT]);;

(*---------------------------------------------------------------------------*)
(*             Auxiliary Lemmas to Prove Lemma 4 of Table 5                  *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_SOL_TIME_ALT_6 = prove (
 `!V1 V2 R L G C w z t. (!t. Im t = &0) /\ (!z. Im z = &0)
    ==> complex_derivative (\t. Cx (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * w +
         Re V2 * --sin (w * Re t + (w * sqrt (L * C)) * Re z) * w)) t =
	  Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	   Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2)`,

  REPEAT STRIP_TAC THEN REWRITE_TAC[CX_ADD;CX_MUL]
  THEN SIMP_TAC[CX_COS;CX_NEG;CX_SIN] THEN
  ASSERT_TAC `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
                     Cx (w) * t - Cx(w * sqrt (L * C)) * z`
  THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
                       Cx (w) * t + Cx(w * sqrt (L * C)) * z` ASSUME_TAC
  THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
  THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
  THEN COMPLEX_DIFF_TAC THEN
  SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;COMPLEX_MUL_RID;CX_MUL]
  THEN SIMP_TAC[COMPLEX_SUB_RZERO;COMPLEX_ADD_RID]
  THEN
   REWRITE_TAC[COMPLEX_FIELD `Cx (Re V1) * --(Cx w * ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z)) *
   Cx w + Cx (Re V2) * --(Cx w * ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z)) *
   Cx w = Cx (Re V1) * Cx w * --ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) *
   Cx w + Cx (Re V2) * Cx w * --ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx w`] THEN
   SIMP_TAC[CX_POW;COMPLEX_POW_2] THEN CONV_TAC COMPLEX_RING);;

(*===========================================================================*)
(*                           Lemma 4 of Table 5                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                 Second-Order Partial Derivative of                        *)
(*                General Solution for Voltage w.r.t time                    *)
(*---------------------------------------------------------------------------*)

let HIGHER_DERIV_GENERAL_SOL_TIME_T_1 = prove (
`!V1 V2 R L G C w.  
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
	 ==> higher_complex_derivative 2 (\t. Cx(wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t)) t =  
	 Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	   Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2)`,

REPEAT STRIP_TAC THEN
ASSERT_TAC `!z t. wave_solution_voltage_time V1 V2 (R,L,G,C) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) + Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)` THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_VOLTAGE_TIME_3_ALT];ALL_TAC] THEN
REWRITE_TAC[ASSUME `!z t. wave_solution_voltage_time V1 V2 (R,L,G,C) w z t = Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) +  Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
       REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1] THEN
ASM_SIMP_TAC[WAVE_VOLTAGE_SOL_TIME_ALT_5;WAVE_VOLTAGE_SOL_TIME_ALT_6] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let HIGHER_DERIV_GENERAL_SOL_TIME_T = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\t. Cx(wave_solution_voltage_time V1 V2 tlc w z t)) t =  
	 Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	   Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2)`,

LET_TAC THEN REWRITE_TAC [HIGHER_DERIV_GENERAL_SOL_TIME_T_1]);;


let HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT_1 = prove (
`!V1 V2 R L G C w.  
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\t. Cx(wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t)) = 
	 (\t. Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	   Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[HIGHER_DERIV_GENERAL_SOL_TIME_T_1]);;


let HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\t. Cx(wave_solution_voltage_time V1 V2 tlc w z t)) = 
	 (\t. Cx (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	   Re V2 * (--cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2))`,

LET_TAC THEN REWRITE_TAC[HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT_1]);;

(*===========================================================================*)
(*                            Theorem 5.5                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*               General Solution of Wave Equation for Voltage               *)
(*---------------------------------------------------------------------------*)

let WAVE_VOLTAGE_TIME_PDE_VERIFIED_ALT = prove (
 `!V V1 V2 R L G C w.
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
	 (!z t. V z t = Cx (wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t))
	   ==> wave_voltage_equation V ((R,L,G,C):trans_line_const) z t`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC
        THEN REWRITE_TAC[wave_voltage_equation] THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_ADD_LID]
	 THEN ASM_SIMP_TAC[HIGHER_DERIV_GENERAL_SOL_TIME_Z_ALT_1;HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT_1] THEN
       SIMP_TAC[REAL_POW_2;SQRT_MUL] THEN
 ASSERT_TAC `(w * sqrt L * sqrt C) * w * sqrt L * sqrt C = w pow 2 * L * C`
 THENL [SIMP_TAC[REAL_FIELD `!(a:real)(b:real)(c:real). (a * b * c) * a * b * c = a * a * b pow 2 * c pow 2`]
      THEN
 ASSERT_TAC `sqrt L pow 2 = L` THENL [REWRITE_TAC[SQRT_POW2] THEN ASM_REAL_ARITH_TAC;ALL_TAC]
      THEN ASM_REWRITE_TAC[] THEN ASSERT_TAC `sqrt C pow 2 = C` THENL [REWRITE_TAC[SQRT_POW2]
      THEN ASM_REAL_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2]
      THEN REAL_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
      THEN ASSERT_TAC `Cx (Re V1 * --cos (w * Re t - (w * sqrt L * sqrt C) * Re z) * w pow 2 * L * C +
                        Re V2 * --cos (w * Re t + (w * sqrt L * sqrt C) * Re z) * w pow 2 * L * C) =
			 Cx (w pow 2 * L * C * (Re V1 * --cos (w * Re t - (w * sqrt L * sqrt C) * Re z) +
                          Re V2 * --cos (w * Re t + (w * sqrt L * sqrt C) * Re z)))`
     THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
     THEN SIMP_TAC[REAL_POW_2] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let WAVE_VOLTAGE_TIME_PDE_VERIFIED = prove (
 `!V V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
	 (!z t. V z t = Cx (wave_solution_voltage_time V1 V2 tlc w z t))
	   ==> wave_voltage_equation V tlc z t`,

LET_TAC THEN REWRITE_TAC[WAVE_VOLTAGE_TIME_PDE_VERIFIED_ALT]);;

(*===========================================================================*)
(*                         Definition 5.4                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                      Wave Solution for Current                            *)
(*---------------------------------------------------------------------------*)

let wave_solution_current_time = new_definition `
 wave_solution_current_time (V1:complex) (V2:complex) (tlc:trans_line_const)
   (w:real) (z:complex) (t:complex) =
      Re((wave_solution_current_phasor V1 V2 tlc w z) * cexp(ii * Cx w * t))`;;
   
(*---------------------------------------------------------------------------*)
(*               Auxiliary Lemmas to prove Lemma 5.2                         *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_TIME_1_ALT = prove (
 `!V1 V2 R C L G z w t. 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
     ==> wave_solution_current_time V1 V2 (R,L,G,C) w z t =
     Re(Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w *
      (V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant (R,L,G,C) w)) * z)) -
        V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant (R,L,G,C) w)) * z))))`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
 REWRITE_TAC[wave_solution_current_time] THEN
 REWRITE_TAC[wave_solution_current_phasor] THEN
 REWRITE_TAC[characteristic_impedance] THEN
REPEAT LET_TAC THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN SIMP_TAC [] THEN
 DISCH_TAC THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
 SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((Cx R + ii * Cx w * Cx L) / propagation_constant (R,L,G,C) w) =
              propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L)`]
	  THEN ONCE_ASM_REWRITE_TAC[GSYM PROPAGATION_CONSTANT_COMPLEX_ALT]
	  THEN ONCE_ASM_REWRITE_TAC[PROPAGATION_CONSTANT_COMPLEX_TRAD_ALT]
	  THEN SIMP_TAC[COMPLEX_SUB_RDISTRIB; COMPLEX_SUB_LDISTRIB]
	  THEN SUBGOAL_THEN `Re (propagation_constant (R,L,G,C) w) = &0` ASSUME_TAC
	  THENL [ASM_SIMP_TAC[ATTENUATION_COEFFICIENT_ALT];ALL_TAC]
	  THEN REWRITE_TAC[ASSUME `Re (propagation_constant (R,L,G,C) w) = &0`]
	  THEN SIMP_TAC[COMPLEX_ADD_LID] THEN
 ASSERT_TAC `Re (((ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) * V1 *
   cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)) * cexp (ii * Cx w * t) -
  ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) *
   V2 * cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)) * cexp (ii * Cx w * t)) =
  Re ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) *
  V1 * cexp (ii * Cx w * t - ii * Cx (Im (ii * Cx (Im (propagation_constant (R,L,G,C) w)))) * z) -
  (ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) *
   V2 * cexp (ii * (Cx w * t + Cx (Im (ii * Cx (Im (propagation_constant (R,L,G,C) w)))) * z))) <=>
   Re ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) *
   V1 * cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z) *
   cexp (ii * Cx w * t) - (ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) *
   V2 * cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z) * cexp (ii * Cx w * t)) =
  Re ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) * V1 *
  cexp (ii * Cx w * t - ii * Cx (Im (ii * Cx (Im (propagation_constant (R,L,G,C) w)))) * z) -
  (ii * Cx (Im (propagation_constant (R,L,G,C) w))) / (ii * Cx w * Cx L) * V2 *
  cexp (ii * (Cx w * t + Cx (Im (ii * Cx (Im (propagation_constant (R,L,G,C) w)))) * z)))`
  THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
  THEN SIMP_TAC[COMPLEX_FIELD `V1 * cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z) *
                                     cexp (ii * Cx w * t) = V1 * cexp (ii * Cx w * t) * 
                                      cexp (--(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)`]
  THEN REWRITE_TAC[COMPLEX_FIELD `V2 * cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z) *
                                        cexp (ii * Cx w * t) = V2 * cexp (ii * Cx w * t) *
					  cexp ((ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z)`]
  THEN SIMP_TAC[GSYM CEXP_ADD]
  THEN SIMP_TAC[COMPLEX_FIELD `ii * Cx w * t + --(ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z =
                                ii * Cx w * t - ii * Cx (Im (propagation_constant (R,L,G,C) w)) * z`]
  THEN REWRITE_TAC[COMPLEX_FIELD `ii * Cx w * t + (ii * Cx (Im (propagation_constant (R,L,G,C) w))) * z =
                                   ii * (Cx w * t + (Cx (Im (propagation_constant (R,L,G,C) w)) * z))`]
  THEN SIMP_TAC[IM_MUL_II;RE_CX]);;


let WAVE_CURRENT_TIME_1 = prove (
 `!V1 V2 R C L G z w t. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  (&0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0
    ==> wave_solution_current_time V1 V2 tlc w z t =
     Re(Cx (&1) / characteristic_impedance tlc w *
      (V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant tlc w)) * z)) -
        V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant tlc w)) * z)))))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_TIME_1_ALT]);;


let WAVE_CURRENT_TIME_2_ALT = prove (`
 !V1 V2 R C L G z w t. 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0 /\
    Im (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) = &0 
     ==> Re(Cx (&1) / characteristic_impedance (R,L,G,C) w *
      (V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant (R,L,G,C) w)) * z)) -
        V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant (R,L,G,C) w)) * z)))) =
	 Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
	  (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) -
	    Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  ASSERT_TAC `(Cx w * t - Cx (Im (propagation_constant (R,L,G,C) w)) * z) =
                Cx (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z)`
         THENL [REWRITE_TAC[CX_SUB;CX_MUL] THEN BINOP_TAC THEN BINOP_TAC
	 THEN SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
	 MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[] THEN SIMP_TAC[]
	 THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[];ALL_TAC]
	 THEN
 REWRITE_TAC[ASSUME `Cx w * t - Cx (Im (propagation_constant (R,L,G,C) w)) * z =
                      Cx (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN
      
 SUBGOAL_THEN `(Cx w * t + Cx (Im (propagation_constant (R,L,G,C) w)) * z) =
                 Cx (w * Re t + (Im (propagation_constant (R,L,G,C) w)) * Re z)` ASSUME_TAC
        THENL [REWRITE_TAC[CX_ADD;CX_MUL] THEN BINOP_TAC THEN BINOP_TAC THEN SIMP_TAC[]
	THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[]
	THEN SIMP_TAC[] THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[];ALL_TAC] THEN
        REWRITE_TAC[ASSUME `Cx w * t + Cx (Im (propagation_constant (R,L,G,C) w)) * z =
                             Cx (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z)`] THEN

 ASSERT_TAC `Cx (&1) / characteristic_impedance (R,L,G,C) w =
              (Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w)) +
	        ii * Cx (Im (Cx (&1) / characteristic_impedance (R,L,G,C) w)))`
	THENL [SIMP_TAC[COMPLEX_EXPAND];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
	THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REPEAT STRIP_TAC
	THEN
 REWRITE_TAC[ASSUME `Im (Cx (&1) / characteristic_impedance (R,L,G,C) w) = &0`]
       THEN SIMP_TAC[COMPLEX_MUL_RZERO;COMPLEX_ADD_RID;EULER;complex_mul;
       IM;RE;IM_CX;REAL_MUL_LZERO;REAL_ADD_RID;RE_CX; REAL_SUB_RZERO;RE_II;IM_II]
       THEN REWRITE_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_ADD_LID;REAL_ADD_RID;
       REAL_SUB_RZERO;REAL_SUB_LZERO;GSYM complex_mul;RE_ADD;IM_ADD;RE_SUB;IM_SUB;RE;
       IM;REAL_MUL_LID;REAL_NEG_0;REAL_EXP_0;RE_CX;IM_CX]
       THEN
 ASSERT_TAC `Im V1 = Im (Cx (Re V1))` THENL [SIMP_TAC[IM_CX]
       THEN ASM_SIMP_TAC[];ALL_TAC] THEN REWRITE_TAC[ASSUME `Im V1 = Im (Cx (Re V1))`]
       THEN SIMP_TAC[IM_CX] THEN REWRITE_TAC[REAL_MUL_LZERO;REAL_SUB_RZERO]
       THEN POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN REPEAT STRIP_TAC
       THEN REWRITE_TAC[ASSUME `Im V2 = &0`]
       THEN SIMP_TAC[REAL_MUL_LZERO;REAL_ADD_RID;REAL_SUB_RZERO]);;


let WAVE_CURRENT_TIME_2 = prove (`
 !V1 V2 R C L G z w t. 
   let tlc = ((R,L,G,C):trans_line_const) in 
 &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0 /\
    Im (Cx (&1) / characteristic_impedance tlc w) = &0 
      ==> Re(Cx (&1) / characteristic_impedance tlc w *
      (V1 * cexp(ii * (Cx w * t - Cx (Im(propagation_constant tlc w)) * z)) -
        V2 * cexp(ii * (Cx w * t + Cx (Im(propagation_constant tlc w)) * z)))) =
	 Re (Cx (&1) / characteristic_impedance tlc w) *
	  (Re V1 * cos (w * Re t - Im (propagation_constant tlc w) * Re z) -
	    Re V2 * cos (w * Re t + Im (propagation_constant tlc w) * Re z))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_TIME_2_ALT]);;

(*===========================================================================*)
(*                           Lemma 5.2                                       *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*     Relationship between Phasor and Time-Domain Functions for Current     *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_TIME_3_ALT = prove (
  `!V1 V2 R L G C z w t. 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
     Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0 /\
      Im (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) = &0
	 ==> wave_solution_current_time V1 V2 (R,L,G,C) w z t =
	  Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
	   (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) -
	     Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))`,

ASM_SIMP_TAC[WAVE_CURRENT_TIME_1_ALT; WAVE_CURRENT_TIME_2_ALT]);;


let WAVE_CURRENT_TIME_3 = prove (
  `!V1 V2 R L G C z w t. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
     Im t = &0 /\ Im z = &0 /\ Im V1 = &0 /\ Im V2 = &0 /\
      Im (Cx (&1) / characteristic_impedance tlc w) = &0
	 ==> wave_solution_current_time V1 V2 tlc w z t =
	  Re (Cx (&1) / characteristic_impedance tlc w) *
	   (Re V1 * cos (w * Re t - Im (propagation_constant tlc w) * Re z) -
	     Re V2 * cos (w * Re t + Im (propagation_constant tlc w) * Re z))`,

LET_TAC THEN REWRITE_TAC[WAVE_CURRENT_TIME_3_ALT]);;

(*---------------------------------------------------------------------------*)
(*                Auxiliary Lemmas to Prove Lemma 1 of Table 6               *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_SOL_TIME_ALT_1_ALTN = prove (
`!V1 V2 R L G C w. 
  (!t. Im t = &0) /\ (!z. Im z = &0)
   ==> complex_derivative (\z. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
        (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) -
	  Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))) z =
	   Cx (Re ((Cx (&1) / characteristic_impedance (R,L,G,C) w)) *
	    (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
	      Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C))))`,

REPEAT STRIP_TAC THEN REWRITE_TAC[CX_MUL;CX_SUB]
        THEN SIMP_TAC[CX_COS;CX_SIN] THEN
 ASSERT_TAC `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) = Cx (w) * t - Cx(w * sqrt (L * C)) * z`
        THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
	THEN ASM_REWRITE_TAC[] THEN
 SUBGOAL_THEN `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) = Cx (w) * t + Cx(w * sqrt (L * C)) * z` ASSUME_TAC
       THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
       THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE THEN COMPLEX_DIFF_TAC
       THEN SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;COMPLEX_MUL_RID;CX_MUL]
       THEN SIMP_TAC[CX_ADD;CX_MUL;CX_NEG;CX_SIN;CX_MUL]
       THEN REWRITE_TAC[COMPLEX_FIELD `Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
            (Cx (Re V1) * --(Cx w * Cx (sqrt (L * C))) * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) -
	      Cx (Re V2) * (Cx w * Cx (sqrt (L * C))) * --csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z)) =
	       Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) * (Cx (Re V1) *
	     --(Cx w * Cx (sqrt (L * C))) * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) -
	      --csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx (Re V2) * (Cx w * Cx (sqrt (L * C)))) `]
       THEN REWRITE_TAC[COMPLEX_FIELD `Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                 (Cx (Re V1) * --(Cx w * Cx (sqrt (L * C))) * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) -
                --csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx (Re V2) * Cx w *
                   Cx (sqrt (L * C))) = Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                   (Cx (Re V1) * --(Cx w * Cx (sqrt (L * C))) *  --csin (Cx w * t -
		    (Cx w * Cx (sqrt (L * C))) * z) + csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) *
		     Cx (Re V2) * Cx w *  Cx (sqrt (L * C)))`]
      THEN SIMP_TAC[COMPLEX_FIELD `Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                  (Cx (Re V1) * --(Cx w * Cx (sqrt (L * C))) * --csin (Cx w * t -
		   (Cx w * Cx (sqrt (L * C))) * z) + csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) *
		    Cx (Re V2) *  Cx w *  Cx (sqrt (L * C))) =
		     Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                     (Cx (Re V1) * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) *
                    --(Cx w * Cx (sqrt (L * C))) + csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) *
                        Cx (Re V2) * Cx w * Cx (sqrt (L * C))) `]
     THEN ASSERT_TAC `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
                             Cx (w) * t - Cx(w * sqrt (L * C)) * z`
     THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
     THEN ASM_REWRITE_TAC[] THEN SUBGOAL_THEN  `Cx w * Cx (Re t) + (Cx w * Cx (sqrt (L * C))) * Cx (Re z) =
                                                 Cx (w * Re t + (w * sqrt (L * C)) * Re z)` ASSUME_TAC
     THEN REWRITE_TAC[CX_ADD] THEN BINOP_TAC THEN REWRITE_TAC[CX_MUL]
     THEN SIMP_TAC[] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[CX_MUL]
     THEN CONV_TAC COMPLEX_FIELD);;

let WAVE_CURRENT_SOL_TIME_ALT_1 = prove (
`!V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  (!t. Im t = &0) /\ (!z. Im z = &0)
   ==> complex_derivative (\z. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
        (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) -
	  Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))) z =
	   Cx (Re ((Cx (&1) / characteristic_impedance tlc w)) *
	    (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
	      Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C))))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_SOL_TIME_ALT_1_ALTN]);;

let WAVE_CURRENT_SOL_TIME_ALT_2_ALTN = prove (
  `!V1 V2 R L G C w. 
  (!t. Im t = &0) /\ (!z. Im z = &0)
     ==> complex_derivative (\z. Cx (Re ((Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w)) *
         (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) - Re V2 *
	   cos (w * Re t + (w * sqrt (L * C)) * Re z)))) =
	   (\z. Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
	    (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) *
	     --(w * sqrt (L * C)) + Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)))))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WAVE_CURRENT_SOL_TIME_ALT_1_ALTN]);;


let WAVE_CURRENT_SOL_TIME_ALT_2 = prove (
  `!V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  (!t. Im t = &0) /\ (!z. Im z = &0)
     ==> complex_derivative (\z. Cx (Re ((Cx (&1) / characteristic_impedance tlc w)) *
         (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) - Re V2 *
	   cos (w * Re t + (w * sqrt (L * C)) * Re z)))) =
	   (\z. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	    (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) *
	     --(w * sqrt (L * C)) + Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)))))`,

LET_TAC THEN REWRITE_TAC[WAVE_CURRENT_SOL_TIME_ALT_2_ALTN]);;

(*===========================================================================*)
(*                           Lemma 1 of Table 6                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    First-Order Partial Derivative of                      *)
(*                General Solution for Current w.r.t distance                *)
(*---------------------------------------------------------------------------*)


let FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_Z_ALT = prove (
`!V1 V2 R L G C w.  
   &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> complex_derivative (\z. Cx(wave_solution_current_time V1 V2 (R,L,G,C) w z t)) = 
	 (\z. Cx (Re ((Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w)) *
	    (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
	      Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)))))`,

REPEAT STRIP_TAC THEN
SUBGOAL_THEN `!z t. wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))` ASSUME_TAC THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_CURRENT_TIME_3_ALT];ALL_TAC] THEN
REWRITE_TAC[ASSUME `!z t.wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WAVE_CURRENT_SOL_TIME_ALT_1_ALTN;WAVE_CURRENT_SOL_TIME_ALT_2_ALTN]);;


let FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_Z = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
   &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
	 ==> complex_derivative (\z. Cx(wave_solution_current_time V1 V2 tlc w z t)) = 
	 (\z. Cx (Re ((Cx (&1) / characteristic_impedance tlc w)) *
	    (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
	      Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)))))`,

LET_TAC THEN REWRITE_TAC [FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_Z_ALT]);;

(*---------------------------------------------------------------------------*)
(*                 Auxiliary Lemma to Prove Lemma 2 of Table 6               *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_SOL_TIME_ALT_3_ALTN =  prove (
  `!V1 V2 R L G C w. 
   (!t. Im t = &0) /\ (!z. Im z = &0)
    ==> complex_derivative (\z. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
     (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
      Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * w * sqrt (L * C)))) z =
       Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
       (Re V1 * --cos (w * Re t - (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2 +
         Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2))`,

REPEAT STRIP_TAC THEN REWRITE_TAC[CX_MUL;CX_ADD] THEN SIMP_TAC[CX_COS;CX_SIN;CX_NEG]
       THEN SUBGOAL_THEN `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
                           Cx (w) * t - Cx(w * sqrt (L * C)) * z` ASSUME_TAC
       THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
       THEN ASM_REWRITE_TAC[] THEN ASSERT_TAC `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
                                                Cx (w) * t + Cx(w * sqrt (L * C)) * z`
      THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
      THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
      THEN COMPLEX_DIFF_TAC THEN SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;
      COMPLEX_MUL_RID;CX_MUL;CX_ADD;CX_MUL;CX_NEG;CX_SIN ]
      THEN  ASSERT_TAC `--(--(Cx w * Cx (sqrt (L * C))) * ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z)) = --
                         --(Cx w * Cx (sqrt (L * C))) * ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z)`
      THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[]
      THEN SIMP_TAC[COMPLEX_NEG_NEG] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let WAVE_CURRENT_SOL_TIME_ALT_3 =  prove (
  `!V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
   (!t. Im t = &0) /\ (!z. Im z = &0)
    ==> complex_derivative (\z. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
     (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * --(w * sqrt (L * C)) +
      Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * w * sqrt (L * C)))) z =
       Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
       (Re V1 * --cos (w * Re t - (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2 +
         Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_SOL_TIME_ALT_3_ALTN]);;

(*===========================================================================*)
(*                           Lemma 2 of Table 6                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    Second-Order Partial Derivative of                     *)
(*                General Solution for Current w.r.t distance                *)
(*---------------------------------------------------------------------------*)

let HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT = prove (
`!V1 V2 R L G C w.  
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\z. Cx(wave_solution_current_time V1 V2 (R,L,G,C) w z t)) z = 
	 Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
       (Re V1 * --cos (w * Re t - (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2 +
         Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2))`,

REPEAT STRIP_TAC THEN
SUBGOAL_THEN `!z t. wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))` ASSUME_TAC THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_CURRENT_TIME_3_ALT];ALL_TAC] THEN

REWRITE_TAC[ASSUME `!z t.wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
       REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1] THEN
ASM_SIMP_TAC[WAVE_CURRENT_SOL_TIME_ALT_2_ALTN;WAVE_CURRENT_SOL_TIME_ALT_3_ALTN] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\z. Cx(wave_solution_current_time V1 V2 tlc w z t)) z = 
	 Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
       (Re V1 * --cos (w * Re t - (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2 +
         Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2))`,

LET_TAC THEN REWRITE_TAC [HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT]);;

let HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT_1 = prove (
`!V1 V2 R L G C w.  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0
       ==> higher_complex_derivative 2 (\z.(Cx(wave_solution_current_time V1 V2 (R,L,G,C) w z t))) = (\z. Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
       (Re V1 * --cos (w * Re t - (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2 +
         Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2)))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT]);;

let HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT = prove (
`!V1 V2 R L G C w.
   let tlc = ((R,L,G,C):trans_line_const) in 
&0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0
     ==> higher_complex_derivative 2 (\z.(Cx(wave_solution_current_time V1 V2 tlc w z t))) =
     (\z. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
       (Re V1 * --cos (w * Re t - (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2 +
         Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z) * (w * sqrt (L * C)) pow 2)))`,

LET_TAC THEN REWRITE_TAC[HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT_1]);;

(*---------------------------------------------------------------------------*)
(*                 Auxiliary Lemmas to Prove Lemma 3 of Table 6              *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_SOL_TIME_ALT_4_ALTN = prove (
    `!V1 V2 R L G C w. 
	  (!t. Im t = &0) /\ (!z. Im z = &0)
       ==> complex_derivative (\t. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
            (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) -
	     Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))) t =
	      Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
	       (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	        Re V2 * (sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w))`,

 REPEAT STRIP_TAC THEN REWRITE_TAC[CX_SUB;CX_MUL]
        THEN SIMP_TAC[CX_COS;CX_NEG;CX_SIN]
	THEN ASSERT_TAC `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
	                        Cx (w) * t - Cx(w * sqrt (L * C)) * z`
	THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
	THEN ASM_REWRITE_TAC[]
	THEN ASSERT_TAC `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
	                        Cx (w) * t + Cx(w * sqrt (L * C)) * z`
	THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
	THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
	THEN COMPLEX_DIFF_TAC
	THEN SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;COMPLEX_MUL_RID;
	CX_MUL;COMPLEX_SUB_RZERO;COMPLEX_ADD_RID]
	THEN REWRITE_TAC[CX_ADD;CX_MUL;CX_SIN;CX_NEG] THEN SIMP_TAC[CX_SIN]
	THEN REWRITE_TAC[COMPLEX_FIELD `Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
	                                (Cx (Re V1) * Cx w * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) -
					  Cx (Re V2) * Cx w * --csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z)) =                                            
					  Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                                           (Cx (Re V1) * Cx w * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) -
                                          --csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) *  Cx (Re V2) * Cx w)`]       
										  THEN SIMP_TAC[COMPLEX_FIELD `Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
			            (Cx (Re V1) * Cx w * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) -
				     --csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx (Re V2) * Cx w) =
				       Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                                       (Cx (Re V1) * Cx w * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) +
				        csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx (Re V2) * Cx w)`]
     THEN ASSERT_TAC `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
                             Cx (w) * t + Cx(w * sqrt (L * C)) * z`
     THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
     THEN ASM_REWRITE_TAC[] THEN
     SIMP_TAC[COMPLEX_FIELD `Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                             (Cx (Re V1) * Cx w * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) +
                              csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx (Re V2) * Cx w) =
			       Cx (Re (propagation_constant (R,L,G,C) w / (Cx R + ii * Cx w * Cx L))) *
                                (Cx (Re V1) * --csin (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) * Cx w  +
                                  Cx (Re V2) * csin (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z) * Cx w)`]
    THEN SIMP_TAC[CX_MUL]
    THEN ASSERT_TAC ` Cx (Re t) = t`
    THENL [MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[];ALL_TAC]
    THEN ONCE_ASM_REWRITE_TAC[] THEN
    ASSERT_TAC ` Cx (Re z) = z` THENL
    [MATCH_MP_TAC LEMMA_RE_ALT THEN ASM_SIMP_TAC[];ALL_TAC]
    THEN ONCE_ASM_REWRITE_TAC[] THEN CONV_TAC COMPLEX_FIELD);;


let WAVE_CURRENT_SOL_TIME_ALT_4 = prove (
    `!V1 V2 R C L G w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
	  (!t. Im t = &0) /\ (!z. Im z = &0)
       ==> complex_derivative (\t. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
            (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) -
	     Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))) t =
	      Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	       (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	        Re V2 * (sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_SOL_TIME_ALT_4_ALTN]);;

let WAVE_CURRENT_SOL_TIME_ALT_5_ALTN = prove (
   `!V1 V2 R L G C w. 
     (!t. Im t = &0) /\ (!z. Im z = &0)
      ==> complex_derivative (\t. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
          (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) -
	   Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))) =
	   (\t. Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
	    (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	     Re V2 * (sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w)))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[WAVE_CURRENT_SOL_TIME_ALT_4_ALTN]);;


let WAVE_CURRENT_SOL_TIME_ALT_5 = prove (
   `!V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
     (!t. Im t = &0) /\ (!z. Im z = &0)
      ==> complex_derivative (\t. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
          (Re V1 * cos (w * Re t - (w * sqrt (L * C)) * Re z) -
	   Re V2 * cos (w * Re t + (w * sqrt (L * C)) * Re z)))) =
	   (\t. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	    (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	     Re V2 * (sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w)))`,

LET_TAC THEN REWRITE_TAC[WAVE_CURRENT_SOL_TIME_ALT_5_ALTN]);;

(*===========================================================================*)
(*                           Lemma 3 of Table 6                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    First-Order Partial Derivative of                      *)
(*                General Solution for Current w.r.t time                    *)
(*---------------------------------------------------------------------------*)

let FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_T_ALT = prove (
`!V1 V2 R L G C w.  
   &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
	 ==> complex_derivative (\t. Cx(wave_solution_current_time V1 V2 (R,L,G,C) w z t)) = 
	 (\t. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
	    (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	     Re V2 * (sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w)))`,

REPEAT STRIP_TAC THEN
SUBGOAL_THEN `!z t. wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))` ASSUME_TAC THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_CURRENT_TIME_3_ALT];ALL_TAC] THEN
REWRITE_TAC[ASSUME `!z t.wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[WAVE_CURRENT_SOL_TIME_ALT_4_ALTN;WAVE_CURRENT_SOL_TIME_ALT_5_ALTN]);;


let FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_T = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
   &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> complex_derivative (\t. Cx(wave_solution_current_time V1 V2 tlc w z t)) = 
	 (\t. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	    (Re V1 * (--sin (w * Re t - (w * sqrt (L * C)) * Re z)) * w +
	     Re V2 * (sin (w * Re t + (w * sqrt (L * C)) * Re z)) * w)))`,

LET_TAC THEN REWRITE_TAC [FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_T_ALT]);;
       
(*---------------------------------------------------------------------------*)
(*                 Auxiliary Lemma to Prove Lemma 4 of Table 6               *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_SOL_TIME_ALT_6_ALTN = prove (
  `!V1 V2 R L G C w. 
   (!t. Im t = &0) /\ (!z. Im z = &0)
    ==> complex_derivative (\t. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
         (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * w +
	   Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * w))) t =
	    Cx (Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) *
	     (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	       Re V2 * (cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2))`,

        REPEAT STRIP_TAC THEN REWRITE_TAC[CX_ADD;CX_MUL]
        THEN SIMP_TAC[CX_COS;CX_NEG;CX_SIN]
	THEN SUBGOAL_THEN `!z t. Cx (w * Re t - (w * sqrt (L * C)) * Re z) =
	                          Cx (w) * t - Cx(w * sqrt (L * C)) * z` ASSUME_TAC
	THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_SUB] THEN EQ_DIFF_SIMP;ALL_TAC]
	THEN ASM_REWRITE_TAC[]
	THEN ASSERT_TAC `!z t. Cx (w * Re t + (w * sqrt (L * C)) * Re z) =
	                        Cx (w) * t + Cx(w * sqrt (L * C)) * z`
	THENL [REPEAT GEN_TAC THEN REWRITE_TAC[CX_ADD] THEN EQ_DIFF_SIMP;ALL_TAC]
	THEN ASM_REWRITE_TAC[]
	THEN MATCH_MP_TAC HAS_COMPLEX_DERIVATIVE_DERIVATIVE
	THEN COMPLEX_DIFF_TAC THEN
	SIMP_TAC[COMPLEX_SUB_LZERO;COMPLEX_MUL_LID;COMPLEX_ADD_LID;
	COMPLEX_MUL_RID;CX_MUL;COMPLEX_SUB_RZERO;COMPLEX_ADD_RID]
	THEN REWRITE_TAC[COMPLEX_FIELD `Cx (Re V1) * --(Cx w * ccos (Cx w * t -
	                                (Cx w * Cx (sqrt (L * C))) * z)) * Cx w + Cx (Re V2) *
				       --(Cx w * ccos (Cx w * t + (Cx w * Cx (sqrt (L * C))) * z)) * Cx w =
					  Cx (Re V1) * Cx w * --ccos (Cx w * t - (Cx w * Cx (sqrt (L * C))) * z) *                                             Cx w + Cx (Re V2) * Cx w * --ccos (Cx w * t + (Cx w * Cx (sqrt (L * C)))                                                                                                        * z) * Cx w`]
      THEN SIMP_TAC[CX_POW;COMPLEX_POW_2] THEN CONV_TAC COMPLEX_FIELD);;


let WAVE_CURRENT_SOL_TIME_ALT_6 = prove (
  `!V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
   (!t. Im t = &0) /\ (!z. Im z = &0)
    ==> complex_derivative (\t. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
         (Re V1 * --sin (w * Re t - (w * sqrt (L * C)) * Re z) * w +
	   Re V2 * sin (w * Re t + (w * sqrt (L * C)) * Re z) * w))) t =
	    Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	     (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	       Re V2 * (cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2))`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_SOL_TIME_ALT_6_ALTN]);;

(*===========================================================================*)
(*                           Lemma 4 of Table 6                              *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    Second-Order Partial Derivative of                     *)
(*                General Solution for Current w.r.t time                    *)
(*---------------------------------------------------------------------------*)

let HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_T_1 = prove (
`!V1 V2 R L G C w.  
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\t. Cx(wave_solution_current_time V1 V2 (R,L,G,C) w z t)) t =  
	    Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
	     (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	       Re V2 * (cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2))`,

REPEAT STRIP_TAC THEN
SUBGOAL_THEN `!z t. wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))` ASSUME_TAC THENL
[REPEAT STRIP_TAC THEN
ASM_SIMP_TAC[WAVE_CURRENT_TIME_3_ALT];ALL_TAC] THEN

REWRITE_TAC[ASSUME `!z t.wave_solution_current_time V1 V2 (R,L,G,C) w z t = Re (Cx (&1) / characteristic_impedance (R,L,G,C) w) * (Re V1 * cos (w * Re t - Im (propagation_constant (R,L,G,C) w) * Re z) - Re V2 * cos (w * Re t + Im (propagation_constant (R,L,G,C) w) * Re z))`] THEN

SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` ASSUME_TAC
       THENL [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
       THEN SIMP_TAC [ARITH_RULE `2 = SUC 1`] THEN
       REWRITE_TAC [higher_complex_derivative_alt; HIGHER_COMPLEX_DERIVATIVE_1] THEN
ASM_SIMP_TAC[WAVE_CURRENT_SOL_TIME_ALT_5_ALTN;WAVE_CURRENT_SOL_TIME_ALT_6_ALTN] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_T = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
	 ==> higher_complex_derivative 2 (\t. Cx(wave_solution_current_time V1 V2 tlc w z t)) t =  
	    Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	     (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	       Re V2 * (cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2))`,

LET_TAC THEN REWRITE_TAC [HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_T_1]);;


let HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT_1 = prove (
`!V1 V2 R L G C w.  
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0  
    ==> higher_complex_derivative 2 (\t. Cx(wave_solution_current_time V1 V2 (R,L,G,C) w z t)) =
	   (\t. Cx (Re (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) *
	     (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	       Re V2 * (cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2)))`,

REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_T_1]);;

let HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT = prove (
`!V1 V2 R L G C w.  
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 
    ==> higher_complex_derivative 2 (\t. Cx(wave_solution_current_time V1 V2 tlc w z t)) =
	   (\t. Cx (Re (Cx (&1) / characteristic_impedance tlc w) *
	     (Re V1 * (--cos (w * Re t - (w * sqrt (L * C)) * Re z)) * w pow 2 +
	       Re V2 * (cos (w * Re t + (w * sqrt (L * C)) * Re z)) * w pow 2)))`,

LET_TAC THEN REWRITE_TAC[HIGHER_DERIV_GENERAL_SOL_TIME_T_ALT_1]);;

(*===========================================================================*)
(*                            Theorem 5.6                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*               General Solution of Wave Equation for Current               *)
(*---------------------------------------------------------------------------*)

let WAVE_CURRENT_TIME_PDE_VERIFIED_ALT = prove (
    `!V V1 V2 R L G C w. 
	  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
      (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
        Im (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) = &0
	  /\ (!z t. II z t = Cx (wave_solution_current_time V1 V2 (R,L,G,C) w z t)) 
	   ==> wave_current_equation II (R,L,G,C) z t`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC
                THEN REWRITE_TAC[wave_current_equation] THEN
                ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_ADD_LID] THEN 
 ASM_SIMP_TAC[HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_Z_ALT_1;HIGHER_DERIV_CURRENT_GENERAL_SOL_TIME_T_1]
      THEN SIMP_TAC[REAL_POW_2;SQRT_MUL]
      THEN ASSERT_TAC `(w * sqrt L * sqrt C) * w * sqrt L * sqrt C = w pow 2 * L * C`
      THENL[SIMP_TAC[REAL_FIELD `!(a:real)(b:real)(c:real). (a * b * c) * a * b * c = a * a * b pow 2 * c pow 2`]
      THEN ASSERT_TAC `sqrt L pow 2 = L`
      THENL [REWRITE_TAC[SQRT_POW2] THEN ASM_REAL_ARITH_TAC;ALL_TAC]
      THEN ASM_REWRITE_TAC[] THEN
      ASSERT_TAC `sqrt C pow 2 = C` THENL [REWRITE_TAC[SQRT_POW2] THEN ASM_REAL_ARITH_TAC;ALL_TAC]
      THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_POW_2] THEN REAL_ARITH_TAC;ALL_TAC]
      THEN ONCE_ASM_REWRITE_TAC[] THEN ASSERT_TAC `Cx (Re V1 * --cos (w * Re t - (w * sqrt L * sqrt C) * Re z) *
                                                    w pow 2 * L * C + Re V2 *
						     --cos (w * Re t + (w * sqrt L * sqrt C) * Re z) *
						      w pow 2 * L * C) = Cx (w pow 2 * L * C *
						       (Re V1 * --cos (w * Re t - (w * sqrt L * sqrt C) * Re z) +
                                                         Re V2 * --cos (w * Re t + (w * sqrt L * sqrt C) * Re z)))`     
									THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
    THEN SIMP_TAC[REAL_POW_2] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let WAVE_CURRENT_TIME_PDE_VERIFIED = prove (
    `!V V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
	  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
      (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
        Im (Cx (&1) / characteristic_impedance tlc w) = &0 /\
	 (!z t. II z t = Cx (wave_solution_current_time V1 V2 tlc w z t)) 
	   ==> wave_current_equation II tlc z t`,

LET_TAC THEN REWRITE_TAC [WAVE_CURRENT_TIME_PDE_VERIFIED_ALT]);;

(*===========================================================================*)
(*                            Theorem 5.7                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*            General Solution of Telegrapher's Equation for Voltage         *)
(*---------------------------------------------------------------------------*)

let TELEGRAPH_VERIFIED_FIRST_ALT = prove (
 `!V V1 V2 R L G C w. 
   &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
     Im (Cx (&1) / characteristic_impedance ((R,L,G,C):trans_line_const) w) = &0
        /\ (!z t. V z t = Cx (wave_solution_voltage_time V1 V2 (R,L,G,C) w z t)) /\ 
		(!z t. II z t = Cx (wave_solution_current_time V1 V2 (R,L,G,C) w z t))
	   ==> telegraph_equation_voltage V II R L z t` ,

REPEAT STRIP_TAC
                THEN REWRITE_TAC[telegraph_equation_voltage] THEN
 ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_ADD_LID] THEN
 ASM_SIMP_TAC[FIRST_ORDER_GENERAL_SOL_TIME_Z_ALT;FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_T_ALT;characteristic_impedance;propagation_constant] THEN LET_TAC THEN
 POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_SIMP_TAC [] THEN
 REWRITE_TAC [propagation_constant] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC)
 THEN ONCE_REWRITE_TAC [EQ_SYM_EQ]
 THEN ASM_SIMP_TAC[] THEN SIMP_TAC[COMPLEX_ADD_LID] THEN
         REWRITE_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C =
	                                  (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`]
         THEN ASSERT_TAC `Cx w * Cx w * Cx L * Cx C * ii pow 2 =
                   Cx (w * w * L * C) * ii pow 2` THENL [REWRITE_TAC[CX_MUL]
         THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]
	 THEN ASSERT_TAC `Cx(w * w * L * C) = Cx (w pow 2 * L * C)`
	 THENL [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]
	 THEN ASSERT_TAC `csqrt (Cx (w pow 2 * L * C) * ii pow 2) =
                           Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)`
	 THENL [MATCH_MP_TAC CSQRT_MUL_LCX THEN MATCH_MP_TAC REAL_LE_MUL
         THEN CONJ_TAC THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
	 THEN ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
         THEN ASM_REWRITE_TAC[] THEN
                          ASSERT_TAC `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))`
         THENL [MATCH_MP_TAC CX_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC
	 THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
         THEN ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
         THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC [COMPLEX_POW_II_2]
         THEN ASSERT_TAC `csqrt (--Cx (&1)) = ii`
	 THENL [MATCH_MP_TAC CSQRT_MINUS THEN SIMP_TAC[RE_II;IM_II] THEN ASM_REAL_ARITH_TAC; ALL_TAC]
         THEN ASM_REWRITE_TAC[] THEN
                     ASSERT_TAC `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))`
         THENL [MATCH_MP_TAC CSQRT_CX THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC
	 THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
         THEN ASM_REAL_ARITH_TAC THEN  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
	 THEN ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[IM_MUL_II] THEN REWRITE_TAC[RE_CX]
         THEN REWRITE_TAC[SQRT_MUL] THEN ASSERT_TAC `sqrt (w pow 2) = w`
         THENL [REWRITE_TAC[REAL_POW_2] THEN REWRITE_TAC[SQRT_MUL]
	 THEN REWRITE_TAC[REAL_FIELD `sqrt w * sqrt w = sqrt (w) pow 2`]
                 THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC]
                     THEN ONCE_ASM_REWRITE_TAC[] THEN
  SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((ii * Cx w * Cx L) / (Cx (w * sqrt L * sqrt C) * ii)) =
                                     Cx (w * sqrt L * sqrt C) * ii / (ii * Cx w * Cx L)`] THEN
         SIMP_TAC[CX_MUL] THEN
           SIMP_TAC[COMPLEX_FIELD `(Cx w * Cx (sqrt L) * Cx (sqrt C)) * ii / (ii * Cx w * Cx L) =
	     (Cx (sqrt L) * Cx (sqrt C) * Cx w) * (ii * Cx(&1) / ii) * Cx(&1) /(Cx w * Cx L)`] THEN
                   ASSERT_TAC `ii * Cx (&1) / ii = Cx(&1)` THENL
                          [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN
                                            MATCH_MP_TAC COMPLEX_MUL_RINV THEN REWRITE_TAC[ii]
	THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
	  THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LID]
	   THEN SIMP_TAC[COMPLEX_FIELD `(Cx (sqrt L) * Cx (sqrt C) * Cx w) * Cx (&1) / (Cx w * Cx L) =
	     Cx (sqrt L) * Cx (sqrt C) * (Cx w * Cx (&1) / (Cx w) * Cx(&1) / Cx L)`] THEN
  REWRITE_TAC[COMPLEX_FIELD `Cx (sqrt L) * Cx (sqrt C) * Cx w * Cx (&1) / Cx w * Cx (&1) / Cx L =
                        Cx (sqrt L) * Cx (sqrt C) * (Cx w * Cx (&1) / Cx w) * Cx (&1) / Cx L`] THEN
                ASSERT_TAC `Cx w * Cx (&1) / Cx w = Cx(&1)`
  THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV
  THEN UNDISCH_TAC `&0 < w` THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
	    THEN  ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LID] THEN
                  SIMP_TAC[GSYM CX_DIV;GSYM CX_MUL;RE_CX] THEN
                    ASSERT_TAC `--Cx (L * (sqrt L * sqrt C * &1 / L) * (Re V1 *
		      --sin (w * Re t - (w * sqrt L * sqrt C) * Re z) * w +
            Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z) * w)) =
	     --Cx ((L * (sqrt L * sqrt C * &1 / L)) * (Re V1 * --sin (w * Re t - (w * sqrt L * sqrt C) * Re z) * w
	        + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z) * w))`
  THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
    THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[REAL_FIELD `L * (sqrt L * sqrt C * &1 / L) =
                     (L * &1 / L) * (sqrt L * sqrt C)`] THEN ASSERT_TAC `L * &1 / L = &1`
    THENL [SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_MUL_RINV
    THEN ASM_REAL_ARITH_TAC;ALL_TAC] THEN ONCE_ASM_REWRITE_TAC[]
      THEN SIMP_TAC[REAL_MUL_LID] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let TELEGRAPH_VERIFIED_FIRST = prove (
 `!V V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
   &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
     Im (Cx (&1) / characteristic_impedance tlc w) = &0
        /\ (!z t. V z t = Cx (wave_solution_voltage_time V1 V2 tlc w z t)) /\ 
		(!z t. II z t = Cx (wave_solution_current_time V1 V2 tlc w z t))
	   ==> telegraph_equation_voltage V II R L z t` ,

LET_TAC THEN REWRITE_TAC [TELEGRAPH_VERIFIED_FIRST_ALT]);;

(*===========================================================================*)
(*                            Theorem 5.8                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*            General Solution of Telegrapher's Equation for Current         *)
(*---------------------------------------------------------------------------*)

let TELEGRAPH_VERIFIED_SECOND_ALT = prove (
`!V V1 V2 R L G C w. 
  &0 < w /\ &0 < L /\ &0 < C /\
   R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
     Im (Cx (&1) / characteristic_impedance (R,L,G,C) w) = &0
        /\ (!z t. V z t = Cx (wave_solution_voltage_time V1 V2 ((R,L,G,C):trans_line_const) w z t)) /\ 
		(!z t. II z t = Cx (wave_solution_current_time V1 V2 (R,L,G,C)  w z t))
	   ==> telegraph_equation_current V II G C z t`,

REPEAT STRIP_TAC
                THEN REWRITE_TAC[telegraph_equation_current] THEN
                ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_ADD_LID] THEN

 ASM_SIMP_TAC[FIRST_ORDER_GENERAL_SOL_CURRENT_TIME_Z_ALT;FIRST_ORDER_GENERAL_SOL_TIME_T_ALT;characteristic_impedance;propagation_constant] THEN LET_TAC THEN
 POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN ASM_SIMP_TAC [] THEN
 REWRITE_TAC [propagation_constant] THEN DISCH_TAC THEN POP_ASSUM (K ALL_TAC)
 THEN ONCE_REWRITE_TAC [EQ_SYM_EQ] 
THEN ASM_SIMP_TAC[] THEN SIMP_TAC[COMPLEX_ADD_LID] THEN
         REWRITE_TAC [COMPLEX_FIELD `(ii * Cx w * Cx L) * ii * Cx w * Cx C =
	                                  (Cx w) * (Cx w) * Cx L * Cx C * ii pow 2`]
         THEN ASSERT_TAC `Cx w * Cx w * Cx L * Cx C * ii pow 2 =
                   Cx (w * w * L * C) * ii pow 2` THENL [REWRITE_TAC[CX_MUL]
         THEN SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]
	 THEN ASSERT_TAC `Cx(w * w * L * C) = Cx (w pow 2 * L * C)`
	 THENL [SIMPLE_COMPLEX_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]
	 THEN ASSERT_TAC `csqrt (Cx (w pow 2 * L * C) * ii pow 2) =
                           Cx(sqrt (w pow 2 * L * C)) * csqrt (ii pow 2)`
	 THENL [MATCH_MP_TAC CSQRT_MUL_LCX THEN MATCH_MP_TAC REAL_LE_MUL
         THEN CONJ_TAC THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
	 THEN ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
         THEN ASM_REWRITE_TAC[] THEN
                          ASSERT_TAC `Cx(sqrt (w pow 2 * L * C)) = csqrt(Cx (w pow 2 * L * C))`
         THENL [MATCH_MP_TAC CX_SQRT THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC
	 THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
         THEN ASM_REAL_ARITH_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
         THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC [COMPLEX_POW_II_2]
         THEN ASSERT_TAC `csqrt (--Cx (&1)) = ii`
	 THENL [MATCH_MP_TAC CSQRT_MINUS THEN SIMP_TAC[RE_II;IM_II] THEN ASM_REAL_ARITH_TAC; ALL_TAC]
         THEN ASM_REWRITE_TAC[] THEN
                     ASSERT_TAC `csqrt(Cx (w pow 2 * L * C)) = Cx(sqrt (w pow 2 * L * C))`
         THENL [MATCH_MP_TAC CSQRT_CX THEN MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC
	 THEN REWRITE_TAC[REAL_POW_2] THEN MATCH_MP_TAC REAL_LE_MUL
         THEN ASM_REAL_ARITH_TAC THEN  MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC]
	 THEN ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[IM_MUL_II] THEN REWRITE_TAC[RE_CX]
         THEN REWRITE_TAC[SQRT_MUL] THEN ASSERT_TAC `sqrt (w pow 2) = w`
         THENL [REWRITE_TAC[REAL_POW_2] THEN REWRITE_TAC[SQRT_MUL]
	 THEN REWRITE_TAC[REAL_FIELD `sqrt w * sqrt w = sqrt (w) pow 2`]
                 THEN MATCH_MP_TAC SQRT_POW_2 THEN ASM_REAL_ARITH_TAC; ALL_TAC]
                     THEN ONCE_ASM_REWRITE_TAC[] THEN
  SIMP_TAC[COMPLEX_FIELD `Cx (&1) / ((ii * Cx w * Cx L) / (Cx (w * sqrt L * sqrt C) * ii)) =
                                     Cx (w * sqrt L * sqrt C) * ii / (ii * Cx w * Cx L)`] THEN
         SIMP_TAC[CX_MUL] THEN
           SIMP_TAC[COMPLEX_FIELD `(Cx w * Cx (sqrt L) * Cx (sqrt C)) * ii / (ii * Cx w * Cx L) =
	     (Cx (sqrt L) * Cx (sqrt C) * Cx w) * (ii * Cx(&1) / ii) * Cx(&1) /(Cx w * Cx L)`] THEN
                   ASSERT_TAC `ii * Cx (&1) / ii = Cx(&1)` THENL
                          [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN
                                            MATCH_MP_TAC COMPLEX_MUL_RINV THEN REWRITE_TAC[ii]
	THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
	  THEN ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_LID]
	   THEN SIMP_TAC[COMPLEX_FIELD `(Cx (sqrt L) * Cx (sqrt C) * Cx w) * Cx (&1) / (Cx w * Cx L) =
	     Cx (sqrt L) * Cx (sqrt C) * (Cx w * Cx (&1) / (Cx w) * Cx(&1) / Cx L)`] THEN
  REWRITE_TAC[COMPLEX_FIELD `Cx (sqrt L) * Cx (sqrt C) * Cx w * Cx (&1) / Cx w * Cx (&1) / Cx L =
                        Cx (sqrt L) * Cx (sqrt C) * (Cx w * Cx (&1) / Cx w) * Cx (&1) / Cx L`] THEN
                ASSERT_TAC `Cx w * Cx (&1) / Cx w = Cx(&1)`
  THENL [SIMP_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV
  THEN UNDISCH_TAC `&0 < w`
            THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
	    THEN  ONCE_ASM_REWRITE_TAC[] THEN

SIMP_TAC[COMPLEX_MUL_LID;GSYM CX_DIV; GSYM CX_MUL;RE_CX] THEN

SIMP_TAC[REAL_FIELD `(Re V1 * --sin (w * Re t - (w * sqrt L * sqrt C) * Re z) * --(w * sqrt L * sqrt C) +
 Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z) * w * sqrt L * sqrt C) = (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) * (w * sqrt L * sqrt C) + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z) * w *
sqrt L * sqrt C)`] THEN

SIMP_TAC[REAL_FIELD ` Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) * w * sqrt L *
sqrt C + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z) * w * sqrt L * sqrt C = w *
sqrt L * sqrt C * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z))`] THEN
ASSERT_TAC `Cx ((sqrt L * sqrt C * &1 / L) * w * sqrt L *
  sqrt C * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z))) = Cx(sqrt L * sqrt C * &1 / L * w * sqrt L * sqrt C * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z)))` THENL
[SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
  
ONCE_ASM_REWRITE_TAC[] THEN
REWRITE_TAC[REAL_FIELD `sqrt L * sqrt C * &1 / L * w * sqrt L * sqrt C *
(Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z)) = sqrt L * sqrt L *  &1 / L * sqrt C * sqrt C  * w * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) +
   Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z))`] THEN
ASSERT_TAC `Cx (sqrt L * sqrt L * &1 / L * sqrt C *  sqrt C * w *
 (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) + Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z))) = Cx ((sqrt L * sqrt L) * &1 / L * (sqrt C * sqrt C) * w * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) +
Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z)))` THENL 
[SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
  
ONCE_ASM_REWRITE_TAC[] THEN
SIMP_TAC[GSYM REAL_POW_2] THEN
SUBGOAL_THEN `sqrt L pow 2 = L` ASSUME_TAC THENL
[REWRITE_TAC[SQRT_POW2] THEN
ASM_REAL_ARITH_TAC;ALL_TAC] THEN
ONCE_ASM_REWRITE_TAC[] THEN
SUBGOAL_THEN `sqrt C pow 2 = C` ASSUME_TAC THENL
[REWRITE_TAC[SQRT_POW2] THEN
ASM_REAL_ARITH_TAC;ALL_TAC] THEN
ONCE_ASM_REWRITE_TAC[] THEN
ASSERT_TAC `L * &1 / L = &1` THENL
[REWRITE_TAC[real_div;REAL_MUL_LID] THEN
MATCH_MP_TAC REAL_MUL_RINV THEN
ASM_REAL_ARITH_TAC;ALL_TAC] THEN
ASSERT_TAC `Cx (L * &1 / L * C * w * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) +
   Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z))) = 
    Cx ((L * &1 / L) * C * w * (Re V1 * sin (w * Re t - (w * sqrt L * sqrt C) * Re z) + 
     Re V2 * sin (w * Re t + (w * sqrt L * sqrt C) * Re z)))` THENL
[SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
ONCE_ASM_REWRITE_TAC[] THEN
REWRITE_TAC[ASSUME `L * &1 / L = &1`] THEN
REWRITE_TAC[REAL_MUL_LID] THEN
SIMPLE_COMPLEX_ARITH_TAC);;

let TELEGRAPH_VERIFIED_SECOND = prove (
`!V V1 V2 R L G C w. 
   let tlc = ((R,L,G,C):trans_line_const) in 
  &0 < w /\ &0 < L /\ &0 < C /\
   R = &0 /\ G = &0 /\
   (!t. Im t = &0) /\ (!z. Im z = &0) /\ Im V1 = &0 /\ Im V2 = &0 /\
     Im (Cx (&1) / characteristic_impedance tlc w) = &0
        /\ (!z t. V z t = Cx (wave_solution_voltage_time V1 V2 tlc w z t)) /\ 
		(!z t. II z t = Cx (wave_solution_current_time V1 V2 tlc w z t))
	   ==> telegraph_equation_current V II G C z t`,

LET_TAC THEN REWRITE_TAC [TELEGRAPH_VERIFIED_SECOND_ALT]);;


(*===========================================================================*)
(*                               Section 6                                   *)
(*                  Application: Terminated Transmission Line                *)
(*===========================================================================*)

(*===========================================================================*)
(*                         Definition 6.1                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                          Line Impedance                                   *)
(*---------------------------------------------------------------------------*)

let line_impedance = new_definition `line_impedance V1 V2 (tlc:trans_line_const) w z =
       wave_solution_voltage_phasor V1 V2 tlc w z  / wave_solution_current_phasor V1 V2 tlc w z`;;

(*---------------------------------------------------------------------------*)
(*                 Auxiliary Lemma to Prove Theorem 6.1                      *)
(*---------------------------------------------------------------------------*)

let SOL_BC1_ALT = prove(
 `!V1 V2 R L G C w z.  
   z = Cx (&0)
   ==> (wave_solution_voltage_phasor V1 V2 ((R,L,G,C):trans_line_const) w z = V1 + V2) /\
      (wave_solution_current_phasor V1 V2 (R,L,G,C) w z = 
	        (Cx(&1) / characteristic_impedance (R,L,G,C) w) * (V1 - V2))`,

REPEAT STRIP_TAC THEN REWRITE_TAC[characteristic_impedance;wave_solution_current_phasor;
                       wave_solution_voltage_phasor;propagation_constant] THEN ASM_REWRITE_TAC[]
		  THEN SIMP_TAC[COMPLEX_MUL_RZERO] THEN ASSERT_TAC `cexp (Cx (&0)) = Cx (exp (&0))`
		  THEN SIMP_TAC[GSYM CX_EXP] THEN ASM_REWRITE_TAC[]
		  THEN SIMP_TAC[REAL_EXP_0;COMPLEX_MUL_LID;COMPLEX_MUL_RID]
		  THEN REWRITE_TAC[wave_solution_current_phasor;propagation_constant]
		  THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_ADD_LID;COMPLEX_MUL_RZERO]
		  THEN ASSERT_TAC `cexp (Cx (&0)) = Cx (exp (&0))`
		  THEN SIMP_TAC[GSYM CX_EXP] THEN ASM_REWRITE_TAC[]
		  THEN SIMP_TAC[REAL_EXP_0;COMPLEX_MUL_LID;COMPLEX_MUL_RID]);;

let SOL_BC1 = prove(
 `!V1 V2 R L G C w z.  
   let tlc = ((R,L,G,C):trans_line_const) in 
   z = Cx (&0)
   ==> (wave_solution_voltage_phasor V1 V2 tlc w z = V1 + V2) /\
      (wave_solution_current_phasor V1 V2 tlc w z = 
	        (Cx(&1) / characteristic_impedance tlc w) * (V1 - V2))`,

LET_TAC THEN REWRITE_TAC [SOL_BC1_ALT]);;


(*===========================================================================*)
(*                           Theorem 6.1                                     *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*               Line Impedance at the Load Position (z=0)                   *)
(*---------------------------------------------------------------------------*)

let LOAD_IMPEDANCE_ALT = prove (
  `!V1 V2 R L G C w z. 
    z = Cx (&0)
    ==> line_impedance V1 V2 ((R,L,G,C):trans_line_const) w z =
             characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2))`,

REPEAT STRIP_TAC THEN REWRITE_TAC[line_impedance]
                  THEN ASM_SIMP_TAC[SOL_BC1_ALT] THEN
 SIMP_TAC[COMPLEX_FIELD `(Cx (&1) / characteristic_impedance ((&0),L,(&0),C) w  * (V1 - V2)) =
                           (V1 - V2) / characteristic_impedance ((&0),L,(&0),C) w`]
	          THEN SIMP_TAC[COMPLEX_FIELD ` a / (b / c) = a * c / b`]
		  THEN CONV_TAC COMPLEX_FIELD);;

let LOAD_IMPEDANCE = prove (
  `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
    z = Cx (&0)
    ==> line_impedance V1 V2 tlc w z = characteristic_impedance tlc w * ((V1 + V2) / (V1 - V2))`,

LET_TAC THEN REWRITE_TAC [LOAD_IMPEDANCE_ALT]);;


(*===========================================================================*)
(*                         Definition 6.2                                    *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                    Voltage Reflection Coefficient                         *)
(*---------------------------------------------------------------------------*)

let voltage_reflection_coefficient =
 new_definition `voltage_reflection_coefficient V1 V2 tlc w z =
  (line_impedance V1 V2 tlc w z - characteristic_impedance tlc w) /
    (line_impedance V1 V2 tlc w z + characteristic_impedance tlc w)`;;

(*===========================================================================*)
(*                           Theorem 6.2                                     *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*            Relating Forward-Going Voltage to Reflected Voltage            *)
(*---------------------------------------------------------------------------*)

let VOLTAGE_REFLECTION_COEFFICIENT_ALT =
prove (`!V1 V2 R L G C z. 
 ~(V1 = V2)  /\
(!w. ~(characteristic_impedance ((R,L,G,C):trans_line_const) w = Cx(&0))) /\ z = Cx (&0)
   ==> voltage_reflection_coefficient V1 V2 (R,L,G,C) w z = V2 / V1`,

REPEAT STRIP_TAC THEN
  REWRITE_TAC[voltage_reflection_coefficient]
  THEN ASSERT_TAC `line_impedance V1 V2 (R,L,G,C) w z =
                   characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2))`
  THENL [ASM_SIMP_TAC[LOAD_IMPEDANCE_ALT];ALL_TAC]
  THEN REWRITE_TAC[ASSUME `line_impedance V1 V2 (R,L,G,C) w z =
      characteristic_impedance (R,L,G,C) w * (V1 + V2) / (V1 - V2)`]
  THEN ASSERT_TAC `characteristic_impedance (R,L,G,C) w * (V1 + V2) / (V1 - V2) -
                     characteristic_impedance (R,L,G,C) w =
		      characteristic_impedance (R,L,G,C) w * ((V1 + V2 )/ (V1 - V2) - Cx (&1))`
  THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[]
  THEN SUBGOAL_THEN `(characteristic_impedance (R,L,G,C) w * (V1 + V2) / (V1 - V2) +
                       characteristic_impedance (R,L,G,C) w) =
		        characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2) + Cx (&1))` ASSUME_TAC
  THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC]
  THEN  ASM_REWRITE_TAC[]
  THEN SIMP_TAC [COMPLEX_FIELD `(characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2) - Cx (&1))) /
                                 (characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2) + Cx (&1))) =
				   characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2) - Cx (&1)) /
				    characteristic_impedance (R,L,G,C) w * Cx(&1) / ((V1 + V2) / (V1 - V2) +
				     Cx (&1))`]
  THEN ASSERT_TAC `!w. characteristic_impedance (R,L,G,C) w *
                    ((V1 + V2) / (V1 - V2) - Cx (&1)) / characteristic_impedance (R,L,G,C) w =
		     ((V1 + V2) / (V1 - V2) - Cx (&1))`
  THENL [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPLEX_DIV_LMUL THEN ASM_SIMP_TAC[];ALL_TAC]
  THEN SIMP_TAC[COMPLEX_FIELD `characteristic_impedance (R,L,G,C) w * ((V1 + V2) / (V1 - V2) -
                                Cx (&1)) / characteristic_impedance (R,L,G,C) w *
                                  Cx (&1) / ((V1 + V2) / (V1 - V2) + Cx (&1)) = V2 / V1 <=>
				   (characteristic_impedance (R,L,G,C) w *
                                    ((V1 + V2) / (V1 - V2) - Cx (&1)) / characteristic_impedance (R,L,G,C) w) *
                                      Cx (&1) / ((V1 + V2) / (V1 - V2) + Cx (&1)) = V2 / V1`]
 THEN ONCE_ASM_REWRITE_TAC[]

 THEN SIMP_TAC[COMPLEX_FIELD `((V1 + V2) / (V1 - V2) - Cx (&1)) * Cx (&1) / ((V1 + V2) / (V1 - V2) + Cx (&1)) =
                                ((V1 + V2) / (V1 - V2) - Cx (&1)) / ((V1 + V2) / (V1 - V2) + Cx (&1)) `]
 THEN ASSERT_TAC `Cx (&1) = (V1 - V2) / (V1 - V2)`
 THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
 THEN SIMP_TAC[COMPLEX_FIELD `a - b = Cx (&0) <=> a = b`] THEN ASM_SIMP_TAC[];ALL_TAC]
 THEN REWRITE_TAC[ASSUME `Cx (&1) = (V1 - V2) / (V1 - V2)`]
 THEN REWRITE_TAC[complex_div]
 THEN SIMP_TAC[COMPLEX_FIELD `((V1 + V2) * inv (V1 - V2) - (V1 - V2) * inv (V1 - V2)) =
                                inv (V1 - V2) * ((V1 + V2)- (V1 - V2))`]
 THEN REWRITE_TAC[COMPLEX_FIELD `(V1 + V2) * inv (V1 - V2) + (V1 - V2) * inv (V1 - V2) =
                                   inv (V1 - V2) * ((V1 + V2) + (V1 - V2))`]
 THEN SIMP_TAC[COMPLEX_FIELD `(inv (V1 - V2) * ((V1 + V2) - (V1 - V2))) = inv (V1 - V2) * (Cx(&2) * V2)`]
 THEN SIMP_TAC[COMPLEX_FIELD `inv (V1 - V2) * ((V1 + V2) + V1 - V2) = inv (V1 - V2) * (Cx(&2) * V1)`]
 THEN REWRITE_TAC[COMPLEX_FIELD `(inv (V1 - V2) * Cx (&2) * V2) / (inv (V1 - V2) * Cx (&2) * V1) =
                                  inv (V1 - V2) * (Cx (&2) * V2) / inv (V1 - V2) * Cx(&1) / (Cx (&2) * V1)`]
 THEN ASSERT_TAC `inv (V1 - V2) * (Cx (&2) * V2) / inv (V1 - V2) = (Cx (&2) * V2)`
 THENL [MATCH_MP_TAC COMPLEX_DIV_LMUL THEN UNDISCH_TAC `~((V1:complex) = (V2:complex))` THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
 THEN REWRITE_TAC[COMPLEX_INV_MUL;COMPLEX_INV_INV]
 THEN  SIMP_TAC[COMPLEX_FIELD `(inv (V1 - V2) * Cx (&2) * V2) * (V1 - V2) * inv (Cx (&2)) * inv V1 =
                                inv (V1 - V2) * Cx (&2) * V2 * (V1 - V2) * inv (Cx (&2)) * inv V1`]
 THEN  SIMP_TAC[COMPLEX_FIELD `inv (V1 - V2) * Cx (&2) * V2 * (V1 - V2) * inv (Cx (&2)) * inv V1 =
                                 V2 * inv V1 <=> inv (V1 - V2) *  (V1 - V2) * Cx (&2) * V2 * inv (Cx (&2)) *
				 inv V1 = V2 * inv V1`]
 THEN ASSERT_TAC `inv (V1 - V2) * (V1 - V2) = Cx(&1)`
 THENL  [MATCH_MP_TAC COMPLEX_MUL_LINV
 THEN SIMP_TAC[COMPLEX_FIELD `a - b = Cx (&0) <=> a = b`]
 THEN ASM_SIMP_TAC[];ALL_TAC]
 THEN REWRITE_TAC[COMPLEX_FIELD `inv (V1 - V2) * (V1 - V2) * Cx (&2) * V2 * inv (Cx (&2)) * inv V1 =
                                  V2 * inv V1 <=> (inv (V1 - V2) * (V1 - V2)) * Cx (&2) * V2 * inv (Cx (&2)) *
				  inv V1 = V2 * inv V1`]
 THEN ASM_REWRITE_TAC[]
 THEN ASSERT_TAC `(V1 - V2) / (V1 - V2) = Cx(&1)`
 THENL [MATCH_MP_TAC COMPLEX_DIV_REFL
 THEN SIMP_TAC[COMPLEX_FIELD `a - b = Cx (&0) <=> a = b`]
 THEN ASM_SIMP_TAC[];ALL_TAC]
 THEN  REWRITE_TAC[ASSUME `(V1 - V2) / (V1 - V2) = Cx (&1) `]
 THEN SIMP_TAC[COMPLEX_MUL_LID] THEN SIMPLE_COMPLEX_ARITH_TAC);;


let VOLTAGE_REFLECTION_COEFFICIENT =
prove (`!V1 V2 R L G C z.
  let tlc = ((R,L,G,C):trans_line_const) in 
 ~(V1 = V2)  /\
(!w. ~(characteristic_impedance tlc w = Cx(&0))) /\ z = Cx (&0)
   ==> voltage_reflection_coefficient V1 V2 tlc w z = V2 / V1`,

LET_TAC THEN REWRITE_TAC[VOLTAGE_REFLECTION_COEFFICIENT_ALT]);;


(*===========================================================================*)
(*                           Theorem 6.3                                     *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*         Final Equation for Line Impedance at the Load Position            *)
(*---------------------------------------------------------------------------*)

let INPUT_LOAD_IMPEDANCE_ALT =
 prove (`!V1 V2 R L G C w z. 
  ~(V1 = V2) /\ ~(V1 = Cx (&0)) /\
 (!w. ~(characteristic_impedance ((R,L,G,C):trans_line_const) w = Cx (&0))) /\ z = Cx (&0) 
  ==> line_impedance V1 V2 (R,L,G,C) w z =  
    characteristic_impedance (R,L,G,C) w * 
	  ((Cx(&1) + (voltage_reflection_coefficient V1 V2 (R,L,G,C) w z)) / 
	     (Cx(&1) - (voltage_reflection_coefficient V1 V2 (R,L,G,C) w z)))`,

REPEAT STRIP_TAC THEN
       REWRITE_TAC[VOLTAGE_REFLECTION_COEFFICIENT_ALT] THEN ASSERT_TAC `voltage_reflection_coefficient V1 V2 (R,L,G,C) w z = V2 / V1` THENL [ASM_MESON_TAC[VOLTAGE_REFLECTION_COEFFICIENT_ALT];ALL_TAC] THEN REWRITE_TAC[ASSUME `voltage_reflection_coefficient V1 V2 (R,L,G,C) w z = V2 / V1`] THEN
       ASM_SIMP_TAC[LOAD_IMPEDANCE_ALT;VOLTAGE_REFLECTION_COEFFICIENT_ALT] THEN
       SUBGOAL_THEN `Cx (&1) = V1 / V1` ASSUME_TAC
       THENL [CONV_TAC SYM_CONV THEN MATCH_MP_TAC COMPLEX_DIV_REFL
       THEN ASM_SIMP_TAC[];ALL_TAC]
       THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[complex_div]
       THEN SIMP_TAC[COMPLEX_FIELD `V1 * inv V1 - V2 * inv V1 = inv V1 * (V1 - V2)`]
       THEN SIMP_TAC[COMPLEX_FIELD `V1 * inv V1 + V2 * inv V1 = inv V1 * (V1 + V2)`]
       THEN REWRITE_TAC[GSYM complex_div]
       THEN SIMP_TAC[COMPLEX_FIELD `(inv V1 * (V1 + V2)) / (inv V1 * (V1 - V2)) =
                      (inv V1 * (V1 + V2)) / (inv V1) * Cx (&1) / (V1 - V2)`]
       THEN SUBGOAL_THEN `(inv V1 * (V1 + V2)) / inv V1 = (V1 + V2) ` ASSUME_TAC
       THENL [REWRITE_TAC[COMPLEX_FIELD `(inv V1 * (V1 + V2)) / inv V1 = V1 + V2 <=>
                           inv V1 * (V1 + V2) / inv V1 = V1 + V2`]
       THEN MATCH_MP_TAC COMPLEX_DIV_LMUL
       THEN UNDISCH_TAC `~(V1 = Cx (&0))`
       THEN CONV_TAC COMPLEX_FIELD;ALL_TAC]
       THEN ASM_REWRITE_TAC[] THEN ASSERT_TAC `V1 / V1 = Cx (&1)`
       THENL [ASM_SIMP_TAC[];ALL_TAC] THEN REWRITE_TAC[ASSUME `V1 / V1 = Cx (&1)`]
       THEN CONV_TAC COMPLEX_FIELD);;

let INPUT_LOAD_IMPEDANCE = prove(`!V1 V2 R L G C w z.
 let tlc = ((R,L,G,C):trans_line_const) in 
  ~(V1 = V2) /\ ~(V1 = Cx (&0)) /\
 (!w. ~(characteristic_impedance tlc w = Cx (&0))) /\ z = Cx (&0) 
  ==> line_impedance V1 V2 tlc w z =  
    characteristic_impedance tlc w * 
	  ((Cx(&1) + (voltage_reflection_coefficient V1 V2 tlc w z)) / 
	     (Cx(&1) - (voltage_reflection_coefficient V1 V2 tlc w z)))`,
	     
LET_TAC THEN REWRITE_TAC[INPUT_LOAD_IMPEDANCE_ALT]);;

(*===========================================================================*)
(*                  Auxiliary Lemmas to Prove Theorem 6.4                    *)
(*===========================================================================*)

let SHORT_CIRCUITED_ALT_ALTN = prove (
`!V1 V2 R L G C w z. 
     V2 = --V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0  
	  ==> line_impedance V1 V2 ((R,L,G,C):trans_line_const) w z =
	   characteristic_impedance (R,L,G,C) w *
	   ((--Cx(&2) * ii * V1 * csin(Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /
	      (Cx(&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)))`,

REPEAT GEN_TAC THEN
REPEAT DISCH_TAC THEN
REWRITE_TAC[line_impedance;wave_solution_voltage_phasor;wave_solution_current_phasor] THEN

ASSERT_TAC `V1 * cexp (--propagation_constant (R,L,G,C) w * z) +
  V2 * cexp (propagation_constant (R,L,G,C) w * z) = V1 * cexp (--propagation_constant (R,L,G,C) w * z) + --V1 *  cexp (propagation_constant (R,L,G,C) w * z)` THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
REWRITE_TAC[ASSUME `V1 * cexp (--propagation_constant (R,L,G,C) w * z) +
      V2 * cexp (propagation_constant (R,L,G,C) w * z) =
      V1 * cexp (--propagation_constant (R,L,G,C) w * z) +
      --V1 * cexp (propagation_constant (R,L,G,C) w * z)`] THEN

SUBGOAL_THEN `V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
   V2 * cexp (propagation_constant (R,L,G,C) w * z) = V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
   --V1 * cexp (propagation_constant (R,L,G,C) w * z)`ASSUME_TAC THENL
   
[ASM_SIMP_TAC[];ALL_TAC] THEN

 REWRITE_TAC[ASSUME `V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
 V2 * cexp (propagation_constant (R,L,G,C) w * z) = V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
   --V1 * cexp (propagation_constant (R,L,G,C) w * z)`] THEN

 ONCE_ASM_REWRITE_TAC[GSYM PROPAGATION_CONSTANT_COMPLEX_ALT] THEN
     ONCE_ASM_REWRITE_TAC[PROPAGATION_CONSTANT_COMPLEX_TRAD_ALT] THEN

  ASSERT_TAC `Re (propagation_constant (R,L,G,C) w) = &0` THENL
      [ASM_SIMP_TAC[ATTENUATION_COEFFICIENT_ALT];ALL_TAC] THEN
        REWRITE_TAC[ASSUME `Re (propagation_constant (R,L,G,C) w) = &0`] THEN
           REWRITE_TAC[COMPLEX_ADD_LID] THEN
  ASSERT_TAC `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)` THENL 
   [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN
    REWRITE_TAC[ASSUME `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)`] THEN
     ASSERT_TAC `(ii * Cx (w * sqrt (L * C))) * z = ii * Cx (w * sqrt (L * C)) * z` THENL
       [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
  REWRITE_TAC[ASSUME `(ii * Cx (w * sqrt (L * C))) * z = ii * Cx (w * sqrt (L * C)) * z`] THEN
   ASSERT_TAC `--(ii * Cx (w * sqrt (L * C))) * z = --ii * Cx (w * sqrt (L * C)) * z` THENL
   [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
     REWRITE_TAC[ASSUME `--(ii * Cx (w * sqrt (L * C))) * z = --ii * Cx (w * sqrt (L * C)) * z`] THEN
 REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex). --a * b = a * --b`] THEN
   SIMP_TAC[CEXP_EULER;CSIN_NEG;CCOS_NEG;COMPLEX_ADD_LDISTRIB] THEN

    SIMP_TAC[COMPLEX_FIELD `V1 * --(ccos (Cx (w * sqrt (L * C)) * z) + ii * csin (Cx (w * sqrt (L * C)) * z)) =
      --V1 * ccos (Cx (w * sqrt (L * C)) * z) - V1 * ii * csin (Cx (w * sqrt (L * C)) * z)`] THEN

     SIMP_TAC[COMPLEX_FIELD `((V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) +  --V1 * ccos (Cx (w * sqrt (L * C)) * z) - V1 * ii * csin (Cx (w * sqrt (L * C)) * z)) = (V1 * ii * --csin (Cx (w * sqrt (L * C)) * z) - V1 * ii * csin (Cx (w * sqrt (L * C)) * z))`] THEN

   SIMP_TAC[COMPLEX_FIELD `((V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) -
   (--V1 * ccos (Cx (w * sqrt (L * C)) * z) - V1 * ii * csin (Cx (w * sqrt (L * C)) * z))) =
       ((V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ccos (Cx (w * sqrt (L * C)) * z)))`] THEN

   SIMP_TAC[COMPLEX_FIELD `(V1 * ii * --csin (Cx (w * sqrt (L * C)) * z) -
   V1 * ii * csin (Cx (w * sqrt (L * C)) * z)) = --Cx(&2) * V1 * ii * csin (Cx (w * sqrt (L * C)) * z)`]
   
   THEN SIMP_TAC[COMPLEX_FIELD `(V1 * ccos (Cx (w * sqrt (L * C)) * z) +
   V1 * ccos (Cx (w * sqrt (L * C)) * z)) = Cx(&2) * V1 * ccos (Cx (w * sqrt (L * C)) * z)`] THEN

  ASSERT_TAC `Cx (Re (characteristic_impedance (R,L,G,C) w)) + ii * Cx (Im (characteristic_impedance (R,L,G,C) w)) =
    complex(Re (characteristic_impedance (R,L,G,C) w), Im (characteristic_impedance (R,L,G,C) w))`
    THENL  [SIMP_TAC[GSYM COMPLEX_TRAD];ALL_TAC] THEN

   REWRITE_TAC[ASSUME `Cx (Re (characteristic_impedance (R,L,G,C) w)) +
    ii * Cx (Im (characteristic_impedance (R,L,G,C) w)) =
     complex (Re (characteristic_impedance (R,L,G,C) w), Im (characteristic_impedance (R,L,G,C) w))`]

  THEN SIMP_TAC[COMPLEX] THEN ASSERT_TAC `Im (ii * Cx (w * sqrt (L * C))) =
                                      Im (Cx(&0) + ii * Cx (w * sqrt (L * C)))` THENL[

  SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN REWRITE_TAC[ASSUME `Im (ii * Cx (w * sqrt (L * C))) =
           Im (Cx (&0) + ii * Cx (w * sqrt (L * C)))`] THEN REWRITE_TAC[GSYM COMPLEX_TRAD;IM]

  THEN REWRITE_TAC[COMPLEX_FIELD `(--Cx (&2) * V1 * ii * csin (Cx (w * sqrt (L * C)) * z)) / 
      (Cx (&1) / characteristic_impedance (R,L,G,C) w * Cx (&2) * V1 * ccos (Cx (w * sqrt (L * C)) * z)) =
     characteristic_impedance (R,L,G,C) w *((--Cx (&2) * V1 * ii * csin (Cx (w * sqrt (L * C)) * z)) /(Cx (&2) * V1 *          
	    ccos (Cx (w * sqrt (L * C)) * z)))`]

  THEN SIMP_TAC[COMPLEX_RING `Cx (&2) * --(ii * V1 * csin (Cx (w * sqrt (L * C)) * z)) =
                    --Cx (&2) * ii * V1 * csin (Cx (w * sqrt (L * C)) * z)`]

  THEN SIMPLE_COMPLEX_ARITH_TAC);;


let SHORT_CIRCUITED_ALT = prove (
`!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
     V2 = --V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0  
	  ==> line_impedance V1 V2 tlc w z =
	   characteristic_impedance tlc w *
	   ((--Cx(&2) * ii * V1 * csin(Cx (Im (propagation_constant tlc w)) * z)) /
	      (Cx(&2) * V1 * ccos (Cx (Im (propagation_constant tlc w)) * z)))`,

LET_TAC THEN REWRITE_TAC [SHORT_CIRCUITED_ALT_ALTN]);;


let SHORT_CIRCUITED_ALT_2_ALTN = prove (
   `!V1 V2 R L G C w z. 
     ~(V1 = Cx (&0)) 
	   ==> characteristic_impedance ((R,L,G,C):trans_line_const) w * ((--Cx(&2) * ii * V1 * csin(Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / 
	     (Cx(&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z))) =
   --ii * characteristic_impedance (R,L,G,C) w * ctan(Cx (Im (propagation_constant (R,L,G,C) w)) * z)`,

REPEAT STRIP_TAC THEN

SIMP_TAC[COMPLEX_FIELD `(--Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /
 (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) =
 ((--Cx (&2) * ii * V1 * Cx (&1) / (Cx (&2) * V1))  * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) *
 Cx (&1) / ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`] THEN

      SIMP_TAC[COMPLEX_FIELD `(--Cx (&2) * ii * V1 * Cx (&1) / (Cx (&2) * V1)) =
           --ii * (Cx (&2) * Cx(&1) / Cx(&2)) * (V1 * Cx (&1) / V1)`] THEN

   SUBGOAL_THEN `Cx (&2) * Cx (&1) / Cx (&2) = Cx(&1)` ASSUME_TAC THENL
      [REWRITE_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV THEN
        SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID] THEN
  SUBGOAL_THEN `V1 * Cx (&1) / V1 = Cx(&1)`ASSUME_TAC THENL
   [REWRITE_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV THEN
    ASM_SIMP_TAC[];ALL_TAC] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_RID]
     THEN REWRITE_TAC[COMPLEX_FIELD `(--ii * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) *
 Cx (&1) / ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z) = --ii * (csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z) / ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z))`] THEN
    SIMP_TAC[GSYM ctan] THEN CONV_TAC COMPLEX_RING);;


let SHORT_CIRCUITED_ALT_2 = prove (
   `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
     ~(V1 = Cx (&0)) 
	   ==> characteristic_impedance tlc w * ((--Cx(&2) * ii * V1 * csin(Cx (Im (propagation_constant tlc w)) * z)) / 
	     (Cx(&2) * V1 * ccos (Cx (Im (propagation_constant tlc w)) * z))) =
   --ii * characteristic_impedance tlc w * ctan(Cx (Im (propagation_constant tlc w)) * z)`,

LET_TAC THEN REWRITE_TAC [SHORT_CIRCUITED_ALT_2_ALTN ]);;


(*===========================================================================*)
(*                         Theorem 6.4                                       *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                     Short-Circuited Line                                  *)
(*---------------------------------------------------------------------------*)

let SHORT_CIRCUITED_LINE_ALT = prove(
  `!V1 V2 R L G C w z. 
      V2 = --V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\ ~(V1 = Cx (&0))
	  ==> line_impedance V1 V2 ((R,L,G,C):trans_line_const) w z = --ii * characteristic_impedance (R,L,G,C) w * 
	  ctan (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`,

REPEAT GEN_TAC THEN
   REPEAT DISCH_TAC THEN
    SUBGOAL_THEN ` line_impedance V1 V2 (R,L,G,C) w z = characteristic_impedance (R,L,G,C) w * ((--Cx(&2) *
       ii * V1 * csin(Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / (Cx(&2) *
         V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)))` ASSUME_TAC THENL
  [ASM_SIMP_TAC[SHORT_CIRCUITED_ALT_ALTN];ALL_TAC] THEN
    REWRITE_TAC[ASSUME `line_impedance V1 V2 (R,L,G,C) w z = characteristic_impedance (R,L,G,C) w * (--Cx (&2) *
ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /(Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z))`] THEN
   SUBGOAL_THEN `characteristic_impedance (R,L,G,C) w * ((--Cx(&2) * ii * V1 * csin(Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / (Cx(&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z))) = --ii * characteristic_impedance (R,L,G,C) w * ctan(Cx (Im (propagation_constant (R,L,G,C) w)) * z)` ASSUME_TAC THENL

  [ASM_SIMP_TAC[SHORT_CIRCUITED_ALT_2_ALTN];ALL_TAC] THEN

REWRITE_TAC[ASSUME `characteristic_impedance (R,L,G,C) w * 
   (--Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / 
    (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) = --ii * 
      characteristic_impedance (R,L,G,C) w * ctan (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`]);;


let SHORT_CIRCUITED_LINE = prove(
  `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
      V2 = --V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\ ~(V1 = Cx (&0))
	  ==> line_impedance V1 V2 tlc w z = --ii * characteristic_impedance tlc w * 
	  ctan (Cx (Im (propagation_constant tlc w)) * z)`,

LET_TAC THEN REWRITE_TAC [SHORT_CIRCUITED_LINE_ALT]);;

(*===========================================================================*)
(*                  Auxiliary Lemmas to Prove Theorem 6.5                    *)
(*===========================================================================*)

let OPEN_CIRCUITED_ALT_ALTN = prove
(`!V1 V2 R L G C w z. 
      V2 = V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0  
	  ==> line_impedance V1 V2 ((R,L,G,C):trans_line_const) w z =
	  characteristic_impedance (R,L,G,C) w * ((Cx(&2) * V1 * ccos(Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / 
	      (--Cx(&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)))`,

REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
     REWRITE_TAC[line_impedance;wave_solution_voltage_phasor;wave_solution_current_phasor] THEN
 SUBGOAL_THEN `V1 * cexp (--propagation_constant (R,L,G,C) w * z) + V2 * cexp (propagation_constant (R,L,G,C) w * z) =
       V1 * cexp (--propagation_constant (R,L,G,C) w * z) + V1 *  cexp (propagation_constant (R,L,G,C) w * z)`ASSUME_TAC
       THENL [ASM_SIMP_TAC[];ALL_TAC] THEN
        REWRITE_TAC[ASSUME `V1 * cexp (--propagation_constant (R,L,G,C) w * z) + V2 * cexp (propagation_constant (R,L,G,C) w * z) = V1 * cexp (--propagation_constant (R,L,G,C) w * z) + V1 * cexp (propagation_constant (R,L,G,C) w * z)`]
 THEN SUBGOAL_THEN `V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
   V2 * cexp (propagation_constant (R,L,G,C) w * z) = V1 * cexp (--propagation_constant (R,L,G,C) w * z) -
   V1 * cexp (propagation_constant (R,L,G,C) w * z)`ASSUME_TAC THENL [ASM_SIMP_TAC[];ALL_TAC]
   THEN REWRITE_TAC[ASSUME `V1 * cexp (--propagation_constant (R,L,G,C) w * z) - V2 * cexp (propagation_constant (R,L,G,C) w * z) = V1 * cexp (--propagation_constant (R,L,G,C) w * z) - V1 * cexp (propagation_constant (R,L,G,C) w * z)`]
   THEN ONCE_ASM_REWRITE_TAC[GSYM PROPAGATION_CONSTANT_COMPLEX_ALT] THEN
     ONCE_ASM_REWRITE_TAC[PROPAGATION_CONSTANT_COMPLEX_TRAD_ALT] THEN

  ASSERT_TAC `Re (propagation_constant (R,L,G,C) w) = &0` THENL [ASM_SIMP_TAC[ATTENUATION_COEFFICIENT_ALT];ALL_TAC]
   THEN REWRITE_TAC[ASSUME `Re (propagation_constant (R,L,G,C) w) = &0`] 
    THEN REWRITE_TAC[COMPLEX_ADD_LID] THEN
     SUBGOAL_THEN `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)`ASSUME_TAC THENL
  [ASM_SIMP_TAC[PHASE_COEFFICIENT_ALT];ALL_TAC] THEN
    REWRITE_TAC[ASSUME `Im (propagation_constant (R,L,G,C) w) = w * sqrt (L * C)`] THEN
   SUBGOAL_THEN `(ii * Cx (w * sqrt (L * C))) * z = ii * Cx (w * sqrt (L * C)) * z` ASSUME_TAC
    THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
     REWRITE_TAC[ASSUME `(ii * Cx (w * sqrt (L * C))) * z = ii * Cx (w * sqrt (L * C)) * z`] THEN
   SUBGOAL_THEN `--(ii * Cx (w * sqrt (L * C))) * z = --ii * Cx (w * sqrt (L * C)) * z`ASSUME_TAC THENL
     [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
   REWRITE_TAC[ASSUME `--(ii * Cx (w * sqrt (L * C))) * z = --ii * Cx (w * sqrt (L * C)) * z`] THEN
    REWRITE_TAC[COMPLEX_FIELD `!(a:complex)(b:complex). --a * b = a * --b`] THEN
       SIMP_TAC[CEXP_EULER] THEN SIMP_TAC[CSIN_NEG;CCOS_NEG;COMPLEX_ADD_LDISTRIB] THEN

   SIMP_TAC[COMPLEX_FIELD `(V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) +
  V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * csin (Cx (w * sqrt (L * C)) * z) =
     Cx(&2) * V1 * ccos (Cx (w * sqrt (L * C)) * z)`] THEN

   (REWRITE_TAC[COMPLEX_FIELD `Cx (&1) /(Cx (Re (characteristic_impedance (R,L,G,C) w)) + ii * Cx (Im (characteristic_impedance (R,L,G,C) w))) *  ((V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) -
   (V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * csin (Cx (w * sqrt (L * C)) * z))) =
    Cx (&1) / (Cx (Re (characteristic_impedance (R,L,G,C) w)) + ii * Cx (Im (characteristic_impedance (R,L,G,C) w))) *       ((V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) -
       (V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * csin (Cx (w * sqrt (L * C)) * z)))`]) THEN

   SIMP_TAC[COMPLEX_FIELD `(V1 * ccos (Cx (w * sqrt (L * C)) * z) +
    V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) - (V1 * ccos (Cx (w * sqrt (L * C)) * z) +
     V1 * ii * csin (Cx (w * sqrt (L * C)) * z)) =  V1 * ccos (Cx (w * sqrt (L * C)) * z) +
      V1 * ii * --csin (Cx (w * sqrt (L * C)) * z) - V1 * ccos (Cx (w * sqrt (L * C)) * z) -
      V1 * ii * csin (Cx (w * sqrt (L * C)) * z)`] THEN
    
   REWRITE_TAC[COMPLEX_FIELD `V1 * ccos (Cx (w * sqrt (L * C)) * z) + V1 * ii * --csin (Cx (w * sqrt (L * C)) * z) -
 V1 * ccos (Cx (w * sqrt (L * C)) * z) - V1 * ii * csin (Cx (w * sqrt (L * C)) * z) = V1 * ii * --csin (Cx (w * sqrt (L * C)) * z) +  V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)`] THEN
 
  SIMP_TAC[COMPLEX_FIELD `a  + a = Cx(&2) * a`] THEN

 SIMP_TAC[COMPLEX_FIELD `(Cx (&2) * V1 * ccos (Cx (w * sqrt (L * C)) * z)) / (Cx (&1) /(Cx (Re (characteristic_impedance (R,L,G,C) w)) + ii * Cx (Im (characteristic_impedance (R,L,G,C) w))) * Cx (&2) * V1 * ii * --csin (Cx (w * sqrt (L * C)) * z)) =  (Cx (Re (characteristic_impedance (R,L,G,C) w)) + ii * Cx (Im (characteristic_impedance (R,L,G,C) w))) * ((Cx (&2) * V1 * ccos (Cx (w * sqrt (L * C)) * z)) / (Cx (&2) * V1 *
 ii * --csin (Cx (w * sqrt (L * C)) * z)))`] THEN

SIMP_TAC[COMPLEX_FIELD `--(a * b * c) = a * b * --c`] THEN

  SUBGOAL_THEN `Im (ii * Cx (w * sqrt (L * C))) = Im (Cx(&0) + ii * Cx (w * sqrt (L * C)))`ASSUME_TAC

   THENL [SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
    REWRITE_TAC[ASSUME `Im (ii * Cx (w * sqrt (L * C))) = Im (Cx (&0) + ii * Cx (w * sqrt (L * C)))`] THEN
     REWRITE_TAC[GSYM COMPLEX_TRAD;IM;COMPLEX] THEN
       CONV_TAC COMPLEX_FIELD);;


let OPEN_CIRCUITED_ALT = prove
(`!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
      V2 = V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0  
	  ==> line_impedance V1 V2 tlc w z =
	  characteristic_impedance tlc w * ((Cx(&2) * V1 * ccos(Cx (Im (propagation_constant tlc w)) * z)) / 
	      (--Cx(&2) * ii * V1 * csin (Cx (Im (propagation_constant tlc w)) * z)))`,

LET_TAC THEN REWRITE_TAC [OPEN_CIRCUITED_ALT_ALTN]);;


let OPEN_CIRCUITED_ALT_2_ALTN = prove (
   `!V1 V2 R L G C w z. 
      ~(V1 = Cx (&0)) ==> characteristic_impedance ((R,L,G,C):trans_line_const) w * (Cx (&2) * V1 *
      ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / (--Cx (&2) * ii * V1 *
       csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) =
       (Cx(&1) / --ii) * characteristic_impedance (R,L,G,C) w * ccot(Cx (Im (propagation_constant (R,L,G,C) w)) * z)`,

REPEAT STRIP_TAC THEN
   SIMP_TAC[COMPLEX_FIELD `(Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /
     (--Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) =
     (Cx(&1) / --ii) * (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /
      (Cx (&2) *  V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z))`] THEN

  SIMP_TAC[COMPLEX_FIELD `(Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /
 (Cx (&2) * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) =
   (Cx (&2) * Cx(&1) / Cx(&2)) * (V1 * Cx(&1) / V1) *
    ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z) / csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`]

 THEN ASSERT_TAC `Cx (&2) * Cx (&1) / Cx (&2) = Cx(&1)` THENL [REWRITE_TAC[complex_div;COMPLEX_MUL_LID] THEN
   MATCH_MP_TAC COMPLEX_MUL_RINV THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN REWRITE_TAC[COMPLEX_MUL_LID] THEN
    ASSERT_TAC `V1 * Cx (&1) / V1 = Cx(&1)` THENL
     [REWRITE_TAC[complex_div;COMPLEX_MUL_LID] THEN MATCH_MP_TAC COMPLEX_MUL_RINV THEN
       ASM_SIMP_TAC[];ALL_TAC] THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[COMPLEX_MUL_RID;COMPLEX_MUL_LID]
       THEN SIMP_TAC[GSYM ccot] THEN CONV_TAC COMPLEX_RING);;


let OPEN_CIRCUITED_ALT_2 = prove (
   `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
      ~(V1 = Cx (&0)) ==> characteristic_impedance tlc w * (Cx (&2) * V1 *
      ccos (Cx (Im (propagation_constant tlc w)) * z)) / (--Cx (&2) * ii * V1 *
       csin (Cx (Im (propagation_constant tlc w)) * z)) =
       (Cx(&1) / --ii) * characteristic_impedance tlc w * ccot(Cx (Im (propagation_constant tlc w)) * z)`,

LET_TAC THEN REWRITE_TAC [OPEN_CIRCUITED_ALT_2_ALTN]);;


let OPEN_CIRCUITED_LINE_ALT_3_ALTN = prove (
 `!V1 V2 R L G C w z. 
    V2 = V1 /\  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   ~(V1 = Cx (&0)) 
	  ==> line_impedance V1 V2 ((R,L,G,C):trans_line_const) w z = Cx (&1) / --ii *
             characteristic_impedance (R,L,G,C) w *
             ccot (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`,

 REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `line_impedance V1 V2 (R,L,G,C) w z =
     characteristic_impedance (R,L,G,C) w * (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) /
     (--Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z))` ASSUME_TAC THENL

 [ASM_SIMP_TAC[OPEN_CIRCUITED_ALT_ALTN];ALL_TAC] THEN
   REWRITE_TAC[ASSUME `line_impedance V1 V2 (R,L,G,C) w z =
     characteristic_impedance (R,L,G,C) w * (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / (--   Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z))`] THEN

  SUBGOAL_THEN `characteristic_impedance (R,L,G,C) w * (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / (--Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) = Cx (&1) / --ii *
characteristic_impedance (R,L,G,C) w * ccot (Cx (Im (propagation_constant (R,L,G,C) w)) * z)` ASSUME_TAC THENL

 [ASM_SIMP_TAC[OPEN_CIRCUITED_ALT_2_ALTN];ALL_TAC] THEN
  REWRITE_TAC[ASSUME `characteristic_impedance (R,L,G,C) w * (Cx (&2) * V1 * ccos (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) / (--Cx (&2) * ii * V1 * csin (Cx (Im (propagation_constant (R,L,G,C) w)) * z)) = Cx (&1) / --ii *
characteristic_impedance (R,L,G,C) w * ccot (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`]);;


let OPEN_CIRCUITED_LINE_ALT_3 = prove (
 `!V1 V2 R L G C w z. 
   let tlc = ((R,L,G,C):trans_line_const) in 
    V2 = V1 /\  &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\
   ~(V1 = Cx (&0)) 
	  ==> line_impedance V1 V2 tlc w z = Cx (&1) / --ii *
             characteristic_impedance tlc w *
             ccot (Cx (Im (propagation_constant tlc w)) * z)`,

LET_TAC THEN REWRITE_TAC [OPEN_CIRCUITED_LINE_ALT_3_ALTN]);;


(*===========================================================================*)
(*                         Theorem 6.5                                       *)
(*===========================================================================*)
(*---------------------------------------------------------------------------*)
(*                     Open-Circuited Line                                   *)
(*---------------------------------------------------------------------------*)

let OPEN_CIRCUITED_LINE_ALT = prove(
 `!V1 V2 R L G C w z.  
    z = --(Cx (pi) / Cx(&2)) /\ V2 = V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\ ~(V1 = Cx (&0))
	  ==> line_impedance V1 V2 ((R,L,G,C):trans_line_const) w z = ii *
             characteristic_impedance (R,L,G,C) w *
             ccot (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`,

REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `line_impedance V1 V2 (R,L,G,C) w z = Cx (&1) / --ii *
   characteristic_impedance (R,L,G,C) w * ccot (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`ASSUME_TAC THENL
    [ASM_SIMP_TAC[OPEN_CIRCUITED_LINE_ALT_3_ALTN];ALL_TAC] THEN
    
 REWRITE_TAC[ASSUME `line_impedance V1 V2 (R,L,G,C) w z = Cx (&1) / --ii * characteristic_impedance (R,L,G,C) w *
    ccot (Cx (Im (propagation_constant (R,L,G,C) w)) * z)`] THEN

  ASSERT_TAC `--ii = cexp (ii * --(Cx pi / Cx (&2)))` THENL
    [ASM_SIMP_TAC[MINUS_II_EXP];ALL_TAC] THEN
       REWRITE_TAC [ASSUME `--ii = cexp (ii * --(Cx pi / Cx (&2)))`] THEN
 ASSERT_TAC `Cx(&1) / (cexp (ii * --(Cx (pi) / Cx(&2)))) = cexp ((ii * (Cx (pi) / Cx(&2))))` THENL
   [ASM_SIMP_TAC[II_EXP];ALL_TAC] THEN
    REWRITE_TAC[ASSUME `Cx (&1) / cexp (ii * --(Cx pi / Cx (&2))) = cexp (ii * Cx pi / Cx (&2))`] THEN
     SIMP_TAC[CEXP_EULER;GSYM CX_DIV] THEN
 ASSERT_TAC `ccos (Cx (pi / &2)) = Cx (cos (pi / &2))` THENL [SIMP_TAC [CX_COS];ALL_TAC] THEN
   ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[COS_PI2;COMPLEX_ADD_LID] THEN

 ASSERT_TAC `csin (Cx (pi / &2)) = Cx (sin (pi / &2))` THENL [SIMP_TAC [CX_SIN];ALL_TAC] THEN
   ONCE_ASM_REWRITE_TAC[] THEN SIMP_TAC[SIN_PI2;COMPLEX_MUL_RID]);;

let OPEN_CIRCUITED_LINE = prove(
 `!V1 V2 R L G C w z.  
   let tlc = ((R,L,G,C):trans_line_const) in 
    z = --(Cx (pi) / Cx(&2)) /\ V2 = V1 /\ 
         &0 < w /\ &0 < L /\ &0 < C /\ R = &0 /\ G = &0 /\ ~(V1 = Cx (&0))
	  ==> line_impedance V1 V2 tlc w z = ii *
             characteristic_impedance tlc w *
             ccot (Cx (Im (propagation_constant tlc w)) * z)`,

LET_TAC THEN REWRITE_TAC [OPEN_CIRCUITED_LINE_ALT]);;

(*=================================================================*)
(*                  End of the Formalization                       *)
(*=================================================================*)