import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Interference.ProgramCore

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram

theorem truth_eq_decide (z : ℤ) : truth z = decide (z ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [truth, bne_iff_ne, decide_eq_true_eq]

theorem getD_append (left right : Array ℤ) (i : Nat) :
    (left ++ right).getD i 0 =
      if i < left.size then left.getD i 0 else right.getD (i-left.size) 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

private theorem runCode_trace (environment : Nat → Bool) (initial : Array ℤ)
    (code : List Node) (expected : List ℤ) (lengths : expected.length = code.length)
    (steps : ∀ i (h : i < code.length),
      (code[i]).run environment (initial ++ (expected.take i).toArray) = expected.getD i 0) :
    runCode environment initial code = initial ++ expected.toArray := by
  induction code generalizing initial expected with
  | nil =>
      have h : expected = [] := List.length_eq_zero_iff.mp lengths
      subst expected
      simp [runCode]
  | cons node rest ih =>
      cases expected with
      | nil => simp at lengths
      | cons value remaining =>
          have first := steps 0 (by simp)
          have first' : node.run environment initial = value := by simpa using first
          rw [runCode, first']
          have localSteps : ∀ i (h : i < rest.length),
              (rest[i]).run environment ((initial.push value) ++ (remaining.take i).toArray) =
                remaining.getD i 0 := by
            intro i h
            have old := steps (i+1) (by simp only [List.length_cons]; omega)
            have cache : (initial.push value) ++ (remaining.take i).toArray =
                initial ++ ((value :: remaining).take (i+1)).toArray := by
              apply Array.toList_inj.mp
              simp [List.take_succ_cons]
            rw [cache]
            simpa using old
          rw [ih _ remaining (by simpa using lengths) localSteps]
          apply Array.toList_inj.mp
          simp

def pairWeight (w00 w01 w10 w11 p00 p01 p10 p11 : ℤ) : ℤ :=
  let left := truth p10 ^^ truth p00
  let right := truth p01 ^^ truth p00
  let joint := (truth p11 ^^ truth p10) ^^ right
  let common := w00 + sign (bit left) * w10 + sign (bit right) * w01
  let last := sign (bit (left ^^ right)) * w11
  if bit joint = 0 then common + last else common - last

theorem pairWeight_correct (w00 w01 w10 w11 p00 p01 p10 p11 : ℤ) :
    pairWeight w00 w01 w10 w11 p00 p01 p10 p11 * sign p00 =
      w00 * sign p00 + w01 * sign p01 + w10 * sign p10 + w11 * sign p11 := by
  by_cases h00 : p00 = 0 <;> by_cases h01 : p01 = 0 <;>
    by_cases h10 : p10 = 0 <;> by_cases h11 : p11 = 0 <;>
    simp [pairWeight, truth_eq_decide, bit, sign, h00, h01, h10, h11] <;> ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem run_pairTail_weight (environment : Nat → Bool) (values : Array ℤ) (n w p : Nat)
    (size : values.size = 4*n) (hw : w < n) (hp : p < n) :
    (runCode environment values (pairTail n w p).toList).getD (4*n+16) 0 =
      pairWeight (values.getD w 0) (values.getD (n+w) 0)
        (values.getD (2*n+w) 0) (values.getD (3*n+w) 0)
        (values.getD p 0) (values.getD (n+p) 0)
        (values.getD (2*n+p) 0) (values.getD (3*n+p) 0) := by
  let w00 := values.getD w 0
  let w01 := values.getD (n+w) 0
  let w10 := values.getD (2*n+w) 0
  let w11 := values.getD (3*n+w) 0
  let p00 := values.getD p 0
  let p01 := values.getD (n+p) 0
  let p10 := values.getD (2*n+p) 0
  let p11 := values.getD (3*n+p) 0
  let left := truth p10 ^^ truth p00
  let right := truth p01 ^^ truth p00
  let aux := truth p11 ^^ truth p10
  let joint := aux ^^ right
  let term := sign (bit (left ^^ right)) * w11
  let common := w00 + sign (bit left)*w10 + sign (bit right)*w01
  let expected : List ℤ := [bit left, bit right, bit aux, bit joint,
    sign (bit left), sign (bit right), bit (left ^^ right), sign (bit (left ^^ right)),
    sign (bit left)*w10, sign (bit right)*w01, term,
    w00+sign (bit left)*w10, common, common+term, -term, common-term,
    pairWeight w00 w01 w10 w11 p00 p01 p10 p11]
  have trace := runCode_trace environment values (pairTail n w p).toList expected (by rfl)
  have steps : ∀ i (h : i < (pairTail n w p).toList.length),
      ((pairTail n w p).toList[i]).run environment (values ++ (expected.take i).toArray) =
        expected.getD i 0 := by
    intro i h
    have hi : i < 17 := by simpa [pairTail] using h
    have hp0 : p < 4*n := by omega
    have hp1 : n+p < 4*n := by omega
    have hp2 : 2*n+p < 4*n := by omega
    have hp3 : 3*n+p < 4*n := by omega
    have hw0 : w < 4*n := by omega
    have hw1 : n+w < 4*n := by omega
    have hw2 : 2*n+w < 4*n := by omega
    have hw3 : 3*n+w < 4*n := by omega
    interval_cases i <;>
      simp (disch := omega) [pairTail, expected, Node.run, Array.getElem?_append, Array.getElem?_push, size,
        left, right, aux, joint, term, common, w00, w01, w10, w11, p00, p01, p10, p11,
        pairWeight, hp2, hp3, hw0, hw1, hw2, hw3,
        Nat.ne_of_lt hp0, Nat.ne_of_lt hp1] <;>
      simp [truth_bit, sub_eq_add_neg]
  rw [trace steps]
  have index : 4*n+16 = values.size+16 := by omega
  rw [index, getD_append_right]
  rfl

theorem getD_four_zero (v0 v1 v2 v3 : Array ℤ) (n i : Nat)
    (s0 : v0.size = n) (hi : i < n) :
    (((v0 ++ v1) ++ v2) ++ v3).getD i 0 = v0.getD i 0 := by
  rw [getD_append_left _ _ _ (by simp only [Array.size_append, s0]; omega)]
  rw [getD_append_left _ _ _ (by simp only [Array.size_append, s0]; omega)]
  exact getD_append_left _ _ _ (by omega)

theorem getD_four_one (v0 v1 v2 v3 : Array ℤ) (n i : Nat)
    (s0 : v0.size = n) (s1 : v1.size = n) (hi : i < n) :
    (((v0 ++ v1) ++ v2) ++ v3).getD (n+i) 0 = v1.getD i 0 := by
  rw [getD_append_left _ _ _ (by simp only [Array.size_append, s0, s1]; omega)]
  rw [getD_append_left _ _ _ (by simp only [Array.size_append, s0, s1]; omega)]
  simpa only [s0] using getD_append_right v0 v1 i

theorem getD_four_two (v0 v1 v2 v3 : Array ℤ) (n i : Nat)
    (s0 : v0.size = n) (s1 : v1.size = n) (s2 : v2.size = n) (hi : i < n) :
    (((v0 ++ v1) ++ v2) ++ v3).getD (2*n+i) 0 = v2.getD i 0 := by
  rw [getD_append_left _ _ _ (by simp only [Array.size_append, s0, s1, s2]; omega)]
  have h := getD_append_right (v0 ++ v1) v2 i
  simpa only [Array.size_append, s0, s1, two_mul] using h

theorem getD_four_three (v0 v1 v2 v3 : Array ℤ) (n i : Nat)
    (s0 : v0.size = n) (s1 : v1.size = n) (s2 : v2.size = n) :
    (((v0 ++ v1) ++ v2) ++ v3).getD (3*n+i) 0 = v3.getD i 0 := by
  have h := getD_append_right ((v0 ++ v1) ++ v2) v3 i
  have index : 3*n+i = ((v0 ++ v1) ++ v2).size+i := by simp only [Array.size_append, s0, s1, s2]; omega
  rw [index]
  exact h

theorem Program.eval_eliminatePair (program : Program) (a b : Nat) (environment : Nat → Bool) :
    (program.eliminatePair a b).eval environment =
      program.eval (Function.update (Function.update environment a false) b false) +
      program.eval (Function.update (Function.update environment a false) b true) +
      program.eval (Function.update (Function.update environment a true) b false) +
      program.eval (Function.update (Function.update environment a true) b true) := by
  let v00 := run environment (program.cofactorPair a b false false).code
  let v01 := run environment (program.cofactorPair a b false true).code
  let v10 := run environment (program.cofactorPair a b true false).code
  let v11 := run environment (program.cofactorPair a b true true).code
  have sizes (x y : Bool) : (run environment (program.cofactorPair a b x y).code).size = program.code.size := by
    simp [cofactorPair]
  have result : run environment (copies program a b) = ((v00 ++ v01) ++ v10) ++ v11 := by
    simp only [copies, run_join', v00, v01, v10, v11]
  have initialSize : (run environment (copies program a b)).size = 4*program.code.size := by simp
  have weight := run_pairTail_weight environment (run environment (copies program a b))
    program.code.size program.weight.val program.phase.val initialSize program.weight.isLt program.phase.isLt
  have phase := runCode_before environment (run environment (copies program a b))
    (pairTail program.code.size program.weight.val program.phase.val).toList program.phase.val
    (by rw [initialSize]; have h := program.phase.isLt; omega)
  rw [result] at weight phase
  simp only [getD_four_zero v00 v01 v10 v11 _ _ (sizes false false) program.weight.isLt,
    getD_four_one v00 v01 v10 v11 _ _ (sizes false false) (sizes false true) program.weight.isLt,
    getD_four_two v00 v01 v10 v11 _ _ (sizes false false) (sizes false true) (sizes true false) program.weight.isLt,
    getD_four_three v00 v01 v10 v11 _ _ (sizes false false) (sizes false true) (sizes true false),
    getD_four_zero v00 v01 v10 v11 _ _ (sizes false false) program.phase.isLt,
    getD_four_one v00 v01 v10 v11 _ _ (sizes false false) (sizes false true) program.phase.isLt,
    getD_four_two v00 v01 v10 v11 _ _ (sizes false false) (sizes false true) (sizes true false) program.phase.isLt] at weight phase
  have equation : (program.eliminatePair a b).eval environment =
      (program.cofactorPair a b false false).eval environment +
      (program.cofactorPair a b false true).eval environment +
      (program.cofactorPair a b true false).eval environment +
      (program.cofactorPair a b true true).eval environment := by
    simp only [eliminatePair, eval, run, Array.toList_append, runCode_append]
    change (runCode environment (run environment (copies program a b)) _).getD _ 0 *
      sign ((runCode environment (run environment (copies program a b)) _).getD _ 0) = _
    rw [result, weight, phase]
    exact pairWeight_correct _ _ _ _ _ _ _ _
  simpa only [eval_cofactorPair] using equation

end SaturationMonoid.ComplexityProjection.SATSource.InterferenceProgram
