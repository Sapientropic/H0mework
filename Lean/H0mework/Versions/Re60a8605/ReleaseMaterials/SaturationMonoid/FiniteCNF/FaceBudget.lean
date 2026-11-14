import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.FaceReduction
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointBudget

/-!
Budgets for the actual parent/face program.  The instrumented scans return the
same result as the original scans and count executed predicate attempts and
full cube comparisons.  One such comparison is not a Turing-machine microstep.
-/

namespace SaturationMonoid.ComplexityProjection.SATJoint

theorem contractPair_coefficient {n : ℕ} (coords : List (Fin n × Bool))
    (t u result : ℤ × Cube n) (h : contractPair coords t u = some result) :
    result.1 = t.1 ∨ result.1 = u.1 := by
  induction coords with
  | nil => simp [contractPair] at h
  | cons coord coords ih =>
      obtain ⟨v, bit⟩ := coord
      by_cases ht : Cancellable v bit t u
      · have he : complementaryTerm v bit t = result := by simpa [contractPair, ht] using h
        exact Or.inl (congrArg Prod.fst he).symm
      · by_cases hu : Cancellable v bit u t
        · have he : complementaryTerm v bit u = result := by simpa [contractPair, ht, hu] using h
          exact Or.inr (congrArg Prod.fst he).symm
        · exact ih (by simpa [contractPair, ht, hu] using h)

theorem contractPair_weight_le {n : ℕ} (coords : List (Fin n × Bool))
    (t u result : ℤ × Cube n) (h : contractPair coords t u = some result) :
    result.1.natAbs ≤ t.1.natAbs + u.1.natAbs := by
  rcases contractPair_coefficient coords t u result h with h | h <;> simp [h]

theorem insertFace_weight_le {n : ℕ} (coords : List (Fin n × Bool))
    (t : ℤ × Cube n) (terms : Terms n) :
    termsWeight (insertFace coords t terms) ≤ t.1.natAbs + termsWeight terms := by
  induction terms with
  | nil => simp [insertFace, termsWeight]
  | cons u terms ih =>
      cases hp : contractPair coords t u with
      | none =>
          simp only [insertFace, hp, termsWeight, List.map_cons, List.sum_cons] at *
          omega
      | some result =>
          have hr := contractPair_weight_le coords t u result hp
          simp only [insertFace, hp, termsWeight, List.map_cons, List.sum_cons]
          omega

theorem facePass_weight_le {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n) :
    termsWeight (facePass coords terms) ≤ termsWeight terms := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [facePass, List.foldr_cons]
      exact (insertFace_weight_le coords t _).trans (Nat.add_le_add_left ih t.1.natAbs)

theorem faceMarginalRun_weight_le {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms : Terms n) :
    termsWeight (faceMarginalRun coords formula terms) ≤
      2 ^ marginalBudget formula * termsWeight terms := by
  induction formula generalizing terms with
  | nil => simp [faceMarginalRun, marginalBudget]
  | cons clause rest ih =>
      have hp : termsWeight (collectTerms (facePass coords (clauseStep clause terms))) ≤
          2 * termsWeight terms := (collectTerms_weight_le _).trans
            ((facePass_weight_le coords _).trans (by rw [clauseStep_weight]))
      calc
        termsWeight (faceMarginalRun coords (clause :: rest) terms) ≤
            2 ^ marginalBudget rest * termsWeight
              (retireTerms (retireAfter clause rest)
                (collectTerms (facePass coords (clauseStep clause terms)))) := ih _
        _ ≤ 2 ^ marginalBudget rest *
            (2 ^ (retireAfter clause rest).length * (2 * termsWeight terms)) :=
          Nat.mul_le_mul_left _ ((retireTerms_weight_le _ _).trans (Nat.mul_le_mul_left _ hp))
        _ = 2 ^ marginalBudget (clause :: rest) * termsWeight terms := by
          simp only [marginalBudget, pow_add, pow_one]
          ring

def faceMarginalStates {n : ℕ} (coords : List (Fin n × Bool)) :
    CNFFormula n → Terms n → List (Terms n)
  | [], terms => [terms]
  | clause :: rest, terms => terms :: clauseStep clause terms ::
      facePass coords (clauseStep clause terms) ::
      (retireStates (retireAfter clause rest)
          (collectTerms (facePass coords (clauseStep clause terms))) ++
        faceMarginalStates coords rest (retireTerms (retireAfter clause rest)
          (collectTerms (facePass coords (clauseStep clause terms)))))

private theorem face_power_weight_mono (a b w : ℕ) (h : a ≤ b) :
    2 ^ a * w ≤ 2 ^ b * w :=
  Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by omega) h)

theorem faceMarginalStates_weight_le {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms state : Terms n)
    (h : state ∈ faceMarginalStates coords formula terms) :
    termsWeight state ≤ 2 ^ marginalBudget formula * termsWeight terms := by
  induction formula generalizing terms with
  | nil =>
      simp only [faceMarginalStates, List.mem_singleton] at h
      subst state
      simp [marginalBudget]
  | cons clause rest ih =>
      have hp : termsWeight (facePass coords (clauseStep clause terms)) ≤
          2 * termsWeight terms := (facePass_weight_le coords _).trans (by rw [clauseStep_weight])
      have hcol := (collectTerms_weight_le (facePass coords (clauseStep clause terms))).trans hp
      have hret : 2 ^ (retireAfter clause rest).length *
          termsWeight (collectTerms (facePass coords (clauseStep clause terms))) ≤
          2 ^ (1 + (retireAfter clause rest).length) * termsWeight terms := by
        calc
          _ ≤ 2 ^ (retireAfter clause rest).length * (2 * termsWeight terms) :=
            Nat.mul_le_mul_left _ hcol
          _ = _ := by simp [pow_add, Nat.mul_left_comm, Nat.mul_assoc]
      have htwo : 2 * termsWeight terms ≤
          2 ^ marginalBudget (clause :: rest) * termsWeight terms := by
        simpa using face_power_weight_mono 1 (marginalBudget (clause :: rest))
          (termsWeight terms) (by simp only [marginalBudget]; omega)
      rcases List.mem_cons.mp h with h | h
      · subst state
        simpa using face_power_weight_mono 0 (marginalBudget (clause :: rest))
          (termsWeight terms) (by omega)
      · rcases List.mem_cons.mp h with h | h
        · subst state
          simpa only [clauseStep_weight] using htwo
        · rcases List.mem_cons.mp h with h | h
          · subst state
            exact hp.trans htwo
          · rcases List.mem_append.mp h with h | h
            · exact ((retireStates_weight_le _ _ _ h).trans hret).trans
                (face_power_weight_mono _ _ _ (by simp [marginalBudget]))
            · calc
                termsWeight state ≤ 2 ^ marginalBudget rest * termsWeight
                    (retireTerms (retireAfter clause rest)
                      (collectTerms (facePass coords (clauseStep clause terms)))) := ih _ h
                _ ≤ 2 ^ marginalBudget rest *
                    (2 ^ (1 + (retireAfter clause rest).length) * termsWeight terms) :=
                  Nat.mul_le_mul_left _ ((retireTerms_weight_le _ _).trans hret)
                _ = 2 ^ marginalBudget (clause :: rest) * termsWeight terms := by
                  simp only [marginalBudget, pow_add, pow_one]
                  ring

private theorem face_bits_of_weight {n : ℕ} (formula : CNFFormula n)
    (terms : Terms n) (hw : termsWeight terms ≤ 2 ^ marginalBudget formula)
    (t : ℤ × Cube n) (ht : t ∈ terms) :
    1 + Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 2 := by
  have he := ((mem_coefficient_le_weight t terms ht).trans hw).trans
    (Nat.pow_le_pow_right (by omega) (marginalBudget_le_source formula))
  have hs : Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 1 := by
    apply Nat.size_le.mpr
    have hp : 0 < 2 ^ (formula.length + literalCount formula) := by positivity
    rw [pow_succ]
    omega
  omega

theorem faceMarginalRun_coefficient_bits {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (t : ℤ × Cube n)
    (h : t ∈ faceMarginalRun coords formula [(1, topCube n)]) :
    1 + Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 2 := by
  apply face_bits_of_weight formula _ _ t h
  simpa [termsWeight] using faceMarginalRun_weight_le coords formula [(1, topCube n)]

theorem faceMarginalStates_coefficient_bits {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (state : Terms n)
    (hs : state ∈ faceMarginalStates coords formula [(1, topCube n)])
    (t : ℤ × Cube n) (ht : t ∈ state) :
    1 + Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 2 := by
  apply face_bits_of_weight formula state _ t ht
  simpa [termsWeight] using faceMarginalStates_weight_le coords formula [(1, topCube n)] state hs

structure FaceWork (α : Type) where
  value : α
  /-- Executed oriented `Cancellable` predicate attempts. -/
  attempts : ℕ
  /-- Executed full function equalities inside `checkFace`. -/
  cubeComparisons : ℕ

/-- The full cube equality is reached only after the tested coordinate is free. -/
def checkFace {n : ℕ} (v : Fin n) (bit : Bool) (parent face : ℤ × Cube n) : Bool × ℕ :=
  if parent.2 v = Finset.univ then
    (decide (face.2 = restrictFace parent.2 v bit ∧ face.1 = -parent.1), 1)
  else (false, 0)

theorem checkFace_value {n : ℕ} (v : Fin n) (bit : Bool) (parent face : ℤ × Cube n) :
    (checkFace v bit parent face).1 = decide (Cancellable v bit parent face) := by
  by_cases h : parent.2 v = Finset.univ <;>
    simp only [checkFace, Cancellable, h, if_true, if_false, true_and, false_and, decide_false]

theorem checkFace_cubes_le {n : ℕ} (v : Fin n) (bit : Bool) (parent face : ℤ × Cube n) :
    (checkFace v bit parent face).2 ≤ 1 := by
  unfold checkFace
  split <;> simp

def contractPairWork {n : ℕ} : List (Fin n × Bool) → (ℤ × Cube n) → (ℤ × Cube n) →
    FaceWork (Option (ℤ × Cube n))
  | [], _, _ => ⟨none, 0, 0⟩
  | (v, bit) :: coords, t, u =>
      let first := checkFace v bit t u
      if first.1 then ⟨some (complementaryTerm v bit t), 1, first.2⟩
      else
        let second := checkFace v bit u t
        if second.1 then ⟨some (complementaryTerm v bit u), 2, first.2 + second.2⟩
        else
          let tail := contractPairWork coords t u
          ⟨tail.value, 2 + tail.attempts, first.2 + second.2 + tail.cubeComparisons⟩

theorem contractPairWork_value {n : ℕ} (coords : List (Fin n × Bool)) (t u : ℤ × Cube n) :
    (contractPairWork coords t u).value = contractPair coords t u := by
  induction coords with
  | nil => rfl
  | cons coord coords ih =>
      obtain ⟨v, bit⟩ := coord
      by_cases ht : Cancellable v bit t u <;> by_cases hu : Cancellable v bit u t <;>
        simp [contractPairWork, checkFace_value, contractPair, ht, hu, ih]

theorem contractPairWork_attempts_le {n : ℕ} (coords : List (Fin n × Bool))
    (t u : ℤ × Cube n) : (contractPairWork coords t u).attempts ≤ 2 * coords.length := by
  induction coords with
  | nil => simp [contractPairWork]
  | cons coord coords ih =>
      obtain ⟨v, bit⟩ := coord
      by_cases ht : Cancellable v bit t u <;> by_cases hu : Cancellable v bit u t <;>
        simp [contractPairWork, checkFace_value, ht, hu] <;> omega

theorem contractPairWork_cubes_le {n : ℕ} (coords : List (Fin n × Bool)) (t u : ℤ × Cube n) :
    (contractPairWork coords t u).cubeComparisons ≤ (contractPairWork coords t u).attempts := by
  induction coords with
  | nil => simp [contractPairWork]
  | cons coord coords ih =>
      obtain ⟨v, bit⟩ := coord
      have h₁ := checkFace_cubes_le v bit t u
      have h₂ := checkFace_cubes_le v bit u t
      by_cases ht : Cancellable v bit t u <;> by_cases hu : Cancellable v bit u t <;>
        simp only [contractPairWork, checkFace_value, ht, hu, decide_true, decide_false,
          Bool.false_eq_true, if_false, if_true] <;> omega

def insertFaceWork {n : ℕ} (coords : List (Fin n × Bool)) (t : ℤ × Cube n) :
    Terms n → FaceWork (Terms n)
  | [] => ⟨[t], 0, 0⟩
  | u :: terms =>
      let pair := contractPairWork coords t u
      match pair.value with
      | some result => ⟨result :: terms, pair.attempts, pair.cubeComparisons⟩
      | none =>
          let tail := insertFaceWork coords t terms
          ⟨u :: tail.value, pair.attempts + tail.attempts, pair.cubeComparisons + tail.cubeComparisons⟩

theorem insertFaceWork_value {n : ℕ} (coords : List (Fin n × Bool)) (t : ℤ × Cube n)
    (terms : Terms n) : (insertFaceWork coords t terms).value = insertFace coords t terms := by
  induction terms with
  | nil => rfl
  | cons u terms ih =>
      cases hp : contractPair coords t u <;>
        simp [insertFaceWork, contractPairWork_value, insertFace, hp, ih]

theorem insertFaceWork_attempts_le {n : ℕ} (coords : List (Fin n × Bool))
    (t : ℤ × Cube n) (terms : Terms n) :
    (insertFaceWork coords t terms).attempts ≤ 2 * coords.length * terms.length := by
  induction terms with
  | nil => simp [insertFaceWork]
  | cons u terms ih =>
      have hp := contractPairWork_attempts_le coords t u
      cases hv : (contractPairWork coords t u).value <;>
        simp only [insertFaceWork, hv, List.length_cons]
      · nlinarith
      · nlinarith

theorem insertFaceWork_cubes_le {n : ℕ} (coords : List (Fin n × Bool))
    (t : ℤ × Cube n) (terms : Terms n) :
    (insertFaceWork coords t terms).cubeComparisons ≤ (insertFaceWork coords t terms).attempts := by
  induction terms with
  | nil => simp [insertFaceWork]
  | cons u terms ih =>
      have hp := contractPairWork_cubes_le coords t u
      cases hv : (contractPairWork coords t u).value <;>
        simp only [insertFaceWork, hv] <;> omega

def facePassWork {n : ℕ} (coords : List (Fin n × Bool)) : Terms n → FaceWork (Terms n)
  | [] => ⟨[], 0, 0⟩
  | t :: terms =>
      let tail := facePassWork coords terms
      let insertion := insertFaceWork coords t tail.value
      ⟨insertion.value, tail.attempts + insertion.attempts,
        tail.cubeComparisons + insertion.cubeComparisons⟩

theorem facePassWork_value {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n) :
    (facePassWork coords terms).value = facePass coords terms := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [facePassWork, insertFaceWork_value, ih, facePass, List.foldr_cons]

theorem facePassWork_attempts_le {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n) :
    (facePassWork coords terms).attempts ≤ coords.length * terms.length ^ 2 := by
  induction terms with
  | nil => simp [facePassWork]
  | cons t terms ih =>
      have hins := insertFaceWork_attempts_le coords t (facePassWork coords terms).value
      rw [facePassWork_value] at hins
      have hlen := facePass_length_le coords terms
      have hscan : (insertFaceWork coords t (facePass coords terms)).attempts ≤
          2 * coords.length * terms.length :=
        hins.trans (Nat.mul_le_mul_left _ hlen)
      simp only [facePassWork, facePassWork_value, List.length_cons]
      nlinarith

theorem facePassWork_cubes_le {n : ℕ} (coords : List (Fin n × Bool)) (terms : Terms n) :
    (facePassWork coords terms).cubeComparisons ≤ (facePassWork coords terms).attempts := by
  induction terms with
  | nil => simp [facePassWork]
  | cons t terms ih =>
      have h := insertFaceWork_cubes_le coords t (facePassWork coords terms).value
      simp only [facePassWork]
      omega

theorem sourceCoordinates_length_le {n : ℕ} (formula : CNFFormula n) :
    (sourceCoordinates formula).length ≤ 2 * literalCount formula := by
  have h := SATSource.Shared.sourceVars_length_le formula
  have he : (sourceCoordinates formula).length =
      2 * (SATSource.Shared.sourceVars formula).length := by
    simp [sourceCoordinates, List.length_flatMap, List.sum_replicate, Nat.mul_comm]
  rw [he]
  apply Nat.mul_le_mul_left 2
  simpa [literalCount, List.length_flatten] using h

theorem sourceFacePassWork_bound {n : ℕ} (formula : CNFFormula n) (terms : Terms n) :
    (facePassWork (sourceCoordinates formula) terms).value =
        facePass (sourceCoordinates formula) terms ∧
      (facePassWork (sourceCoordinates formula) terms).value.length ≤ terms.length ∧
      (facePassWork (sourceCoordinates formula) terms).attempts ≤
        2 * literalCount formula * terms.length ^ 2 ∧
      (facePassWork (sourceCoordinates formula) terms).cubeComparisons ≤
        2 * literalCount formula * terms.length ^ 2 := by
  have ha := (facePassWork_attempts_le (sourceCoordinates formula) terms).trans
    (Nat.mul_le_mul_right _ (sourceCoordinates_length_le formula))
  exact ⟨facePassWork_value _ _, by rw [facePassWork_value]; exact facePass_length_le _ _,
    ha, (facePassWork_cubes_le _ _).trans ha⟩

/-- Accumulate parent/face scan work along the actual marginal program. -/
def faceMarginalWork {n : ℕ} (coords : List (Fin n × Bool)) :
    CNFFormula n → Terms n → FaceWork (Terms n)
  | [], terms => ⟨terms, 0, 0⟩
  | clause :: rest, terms =>
      let pass := facePassWork coords (clauseStep clause terms)
      let tail := faceMarginalWork coords rest
        (retireTerms (retireAfter clause rest) (collectTerms pass.value))
      ⟨tail.value, pass.attempts + tail.attempts, pass.cubeComparisons + tail.cubeComparisons⟩

/-- The sum is generated from the actual tables reached by the original program. -/
def faceTableSquareSum {n : ℕ} (coords : List (Fin n × Bool)) :
    CNFFormula n → Terms n → ℕ
  | [], _ => 0
  | clause :: rest, terms => (clauseStep clause terms).length ^ 2 +
      faceTableSquareSum coords rest
        (retireTerms (retireAfter clause rest) (collectTerms (facePass coords (clauseStep clause terms))))

theorem faceMarginalWork_value {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms : Terms n) :
    (faceMarginalWork coords formula terms).value = faceMarginalRun coords formula terms := by
  induction formula generalizing terms with
  | nil => rfl
  | cons clause rest ih =>
      simp only [faceMarginalWork, facePassWork_value, ih, faceMarginalRun]

theorem faceMarginalWork_attempts_le {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms : Terms n) :
    (faceMarginalWork coords formula terms).attempts ≤
      coords.length * faceTableSquareSum coords formula terms := by
  induction formula generalizing terms with
  | nil => simp [faceMarginalWork, faceTableSquareSum]
  | cons clause rest ih =>
      simp only [faceMarginalWork, facePassWork_value, faceTableSquareSum, Nat.mul_add]
      exact Nat.add_le_add (facePassWork_attempts_le coords (clauseStep clause terms)) (ih _)

theorem faceMarginalWork_cubes_le {n : ℕ} (coords : List (Fin n × Bool))
    (formula : CNFFormula n) (terms : Terms n) :
    (faceMarginalWork coords formula terms).cubeComparisons ≤
      (faceMarginalWork coords formula terms).attempts := by
  induction formula generalizing terms with
  | nil => simp [faceMarginalWork]
  | cons clause rest ih =>
      simp only [faceMarginalWork]
      exact Nat.add_le_add (facePassWork_cubes_le coords (clauseStep clause terms)) (ih _)

theorem sourceFaceMarginalWork_bound {n : ℕ} (formula : CNFFormula n) :
    (faceMarginalWork (sourceCoordinates formula) formula [(1, topCube n)]).attempts ≤
        2 * literalCount formula *
          faceTableSquareSum (sourceCoordinates formula) formula [(1, topCube n)] ∧
      (faceMarginalWork (sourceCoordinates formula) formula [(1, topCube n)]).cubeComparisons ≤
        2 * literalCount formula *
          faceTableSquareSum (sourceCoordinates formula) formula [(1, topCube n)] := by
  have ha := (faceMarginalWork_attempts_le (sourceCoordinates formula) formula
    [(1, topCube n)]).trans (Nat.mul_le_mul_right _ (sourceCoordinates_length_le formula))
  exact ⟨ha, (faceMarginalWork_cubes_le _ _ _).trans ha⟩

end SaturationMonoid.ComplexityProjection.SATJoint
