import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.JointMarginal
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Nat.Size

/-!
Source bounds for the exact signed coefficients of the marginal algorithm.
These count magnitude growth of actual integer operations; they do not identify
one source operation with a Turing-machine microstep.
-/

namespace SaturationMonoid.ComplexityProjection.SATJoint

def termsWeight {n : ℕ} (terms : Terms n) : ℕ :=
  (terms.map fun t => t.1.natAbs).sum

theorem clauseStep_weight {n : ℕ} (clause : CNFClause n) (terms : Terms n) :
    termsWeight (clauseStep clause terms) = 2 * termsWeight terms := by
  simp [termsWeight, clauseStep, List.map_map, two_mul, Function.comp_def]

theorem insertTerm_weight_le {n : ℕ} (t : ℤ × Cube n) (terms : Terms n) :
    termsWeight (insertTerm t terms) ≤ t.1.natAbs + termsWeight terms := by
  induction terms with
  | nil =>
      by_cases h : t.1 = 0 <;> simp [insertTerm, termsWeight, h]
  | cons u terms ih =>
      by_cases h : t.2 = u.2
      · by_cases hz : t.1 + u.1 = 0
        · simp [insertTerm, termsWeight, h, hz]
          omega
        · simp only [insertTerm, h, if_true, hz, if_false, termsWeight,
            List.map_cons, List.sum_cons]
          have ha := Int.natAbs_add_le t.1 u.1
          omega
      · simp only [insertTerm, h, if_false, termsWeight,
          List.map_cons, List.sum_cons] at *
        omega

theorem collectTerms_weight_le {n : ℕ} (terms : Terms n) :
    termsWeight (collectTerms terms) ≤ termsWeight terms := by
  induction terms with
  | nil => rfl
  | cons t terms ih =>
      simp only [collectTerms, List.foldr_cons]
      exact (insertTerm_weight_le t _).trans (Nat.add_le_add_left ih t.1.natAbs)

theorem cube_coordinate_card_le_two {n : ℕ} (c : Cube n) (v : Fin n) :
    (c v).card ≤ 2 := by
  simpa using (c v).card_le_univ

theorem forgetTerm_weight_le {n : ℕ} (v : Fin n) (t : ℤ × Cube n) :
    (forgetTerm v t).1.natAbs ≤ 2 * t.1.natAbs := by
  simp only [forgetTerm, Int.natAbs_mul, Int.natAbs_natCast]
  calc
    _ ≤ t.1.natAbs * 2 := Nat.mul_le_mul_left _ (cube_coordinate_card_le_two t.2 v)
    _ = _ := Nat.mul_comm _ _

theorem forgetTerms_weight_le {n : ℕ} (v : Fin n) (terms : Terms n) :
    termsWeight (forgetTerms v terms) ≤ 2 * termsWeight terms := by
  induction terms with
  | nil => simp [forgetTerms, termsWeight]
  | cons t terms ih =>
      simp only [forgetTerms, termsWeight, List.map_cons, List.sum_cons] at *
      have ht := forgetTerm_weight_le v t
      omega

theorem retireTerms_weight_le {n : ℕ} (vars : List (Fin n)) (terms : Terms n) :
    termsWeight (retireTerms vars terms) ≤ 2 ^ vars.length * termsWeight terms := by
  induction vars generalizing terms with
  | nil => simp [retireTerms]
  | cons v vars ih =>
      calc
        termsWeight (retireTerms (v :: vars) terms) ≤
            2 ^ vars.length * termsWeight (collectTerms (forgetTerms v terms)) := ih _
        _ ≤ 2 ^ vars.length * (2 * termsWeight terms) :=
          Nat.mul_le_mul_left _ ((collectTerms_weight_le _).trans (forgetTerms_weight_le v terms))
        _ = 2 ^ (v :: vars).length * termsWeight terms := by
          simp [pow_succ, Nat.mul_assoc]

def literalCount {n : ℕ} (formula : CNFFormula n) : ℕ :=
  (formula.map List.length).sum

def marginalBudget {n : ℕ} : CNFFormula n → ℕ
  | [] => 0
  | clause :: rest => 1 + (retireAfter clause rest).length + marginalBudget rest

theorem retireAfter_length_le {n : ℕ} (clause : CNFClause n) (rest : CNFFormula n) :
    (retireAfter clause rest).length ≤ clause.length := by
  exact (List.length_filter_le _ _).trans
    (by simpa using (List.dedup_sublist (clause.map CNFLiteral.var)).length_le)

theorem marginalBudget_le_source {n : ℕ} (formula : CNFFormula n) :
    marginalBudget formula ≤ formula.length + literalCount formula := by
  induction formula with
  | nil => simp [marginalBudget, literalCount]
  | cons clause rest ih =>
      have h := retireAfter_length_le clause rest
      simp only [marginalBudget, literalCount, List.map_cons,
        List.sum_cons, List.length_cons] at *
      omega

theorem marginalRun_weight_le {n : ℕ} (formula : CNFFormula n) (terms : Terms n) :
    termsWeight (marginalRun formula terms) ≤
      2 ^ marginalBudget formula * termsWeight terms := by
  induction formula generalizing terms with
  | nil => simp [marginalRun, marginalBudget]
  | cons clause rest ih =>
      calc
        termsWeight (marginalRun (clause :: rest) terms) ≤
            2 ^ marginalBudget rest * termsWeight
              (retireTerms (retireAfter clause rest) (collectTerms (clauseStep clause terms))) := ih _
        _ ≤ 2 ^ marginalBudget rest *
            (2 ^ (retireAfter clause rest).length * (2 * termsWeight terms)) :=
          Nat.mul_le_mul_left _ ((retireTerms_weight_le _ _).trans
            (Nat.mul_le_mul_left _ ((collectTerms_weight_le _).trans (by rw [clauseStep_weight]))))
        _ = 2 ^ marginalBudget (clause :: rest) * termsWeight terms := by
          simp only [marginalBudget, pow_add, pow_one]
          ring

def retireStates {n : ℕ} : List (Fin n) → Terms n → List (Terms n)
  | [], terms => [terms]
  | v :: vars, terms => terms :: forgetTerms v terms ::
      retireStates vars (collectTerms (forgetTerms v terms))

def marginalStates {n : ℕ} : CNFFormula n → Terms n → List (Terms n)
  | [], terms => [terms]
  | clause :: rest, terms => terms :: clauseStep clause terms ::
      (retireStates (retireAfter clause rest) (collectTerms (clauseStep clause terms)) ++
        marginalStates rest
          (retireTerms (retireAfter clause rest) (collectTerms (clauseStep clause terms))))

private theorem power_weight_mono (a b w : ℕ) (h : a ≤ b) :
    2 ^ a * w ≤ 2 ^ b * w :=
  Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by omega) h)

theorem retireStates_weight_le {n : ℕ} (vars : List (Fin n)) (terms state : Terms n)
    (h : state ∈ retireStates vars terms) :
    termsWeight state ≤ 2 ^ vars.length * termsWeight terms := by
  induction vars generalizing terms with
  | nil =>
      simp only [retireStates, List.mem_singleton] at h
      subst state
      simp
  | cons v vars ih =>
      rcases List.mem_cons.mp h with h | h
      · subst state
        simpa using power_weight_mono 0 (v :: vars).length (termsWeight terms) (by omega)
      · rcases List.mem_cons.mp h with h | h
        · subst state
          exact (forgetTerms_weight_le v terms).trans
            (by
              simpa using power_weight_mono 1 (v :: vars).length (termsWeight terms) (by simp))
        · calc
            termsWeight state ≤ 2 ^ vars.length *
                termsWeight (collectTerms (forgetTerms v terms)) := ih _ h
            _ ≤ 2 ^ vars.length * (2 * termsWeight terms) :=
              Nat.mul_le_mul_left _ ((collectTerms_weight_le _).trans
                (forgetTerms_weight_le v terms))
            _ = 2 ^ (v :: vars).length * termsWeight terms := by
              simp [pow_succ, Nat.mul_assoc]

theorem marginalStates_weight_le {n : ℕ} (formula : CNFFormula n) (terms state : Terms n)
    (h : state ∈ marginalStates formula terms) :
    termsWeight state ≤ 2 ^ marginalBudget formula * termsWeight terms := by
  induction formula generalizing terms with
  | nil =>
      simp only [marginalStates, List.mem_singleton] at h
      subst state
      simp [marginalBudget]
  | cons clause rest ih =>
      have hcol : termsWeight (collectTerms (clauseStep clause terms)) ≤
          2 * termsWeight terms := (collectTerms_weight_le _).trans (by rw [clauseStep_weight])
      have hret : 2 ^ (retireAfter clause rest).length *
          termsWeight (collectTerms (clauseStep clause terms)) ≤
          2 ^ (1 + (retireAfter clause rest).length) * termsWeight terms := by
        calc
          _ ≤ 2 ^ (retireAfter clause rest).length * (2 * termsWeight terms) :=
            Nat.mul_le_mul_left _ hcol
          _ = _ := by simp [pow_add, Nat.mul_left_comm, Nat.mul_assoc]
      rcases List.mem_cons.mp h with h | h
      · subst state
        simpa using power_weight_mono 0 (marginalBudget (clause :: rest))
          (termsWeight terms) (by omega)
      · rcases List.mem_cons.mp h with h | h
        · subst state
          rw [clauseStep_weight]
          simpa using power_weight_mono 1 (marginalBudget (clause :: rest))
            (termsWeight terms) (by simp only [marginalBudget]; omega)
        · rcases List.mem_append.mp h with h | h
          · exact ((retireStates_weight_le _ _ _ h).trans hret).trans
              (power_weight_mono _ _ _ (by simp [marginalBudget]))
          · calc
              termsWeight state ≤ 2 ^ marginalBudget rest * termsWeight
                  (retireTerms (retireAfter clause rest) (collectTerms (clauseStep clause terms))) :=
                ih _ h
              _ ≤ 2 ^ marginalBudget rest *
                  (2 ^ (1 + (retireAfter clause rest).length) * termsWeight terms) :=
                Nat.mul_le_mul_left _ ((retireTerms_weight_le _ _).trans hret)
              _ = 2 ^ marginalBudget (clause :: rest) * termsWeight terms := by
                simp only [marginalBudget, pow_add, pow_one]
                ring

theorem mem_coefficient_le_weight {n : ℕ} (t : ℤ × Cube n) (terms : Terms n)
    (h : t ∈ terms) : t.1.natAbs ≤ termsWeight terms := by
  induction terms with
  | nil => simp at h
  | cons u terms ih =>
      rcases List.mem_cons.mp h with h | h
      · subst t
        simp [termsWeight]
      · exact (ih h).trans (by simp [termsWeight])

theorem collectTerms_intermediate_add_le {n : ℕ} (t u : ℤ × Cube n) (terms : Terms n)
    (hu : u ∈ collectTerms terms) :
    (t.1 + u.1).natAbs ≤ termsWeight (t :: terms) := by
  have hu' := (mem_coefficient_le_weight u _ hu).trans (collectTerms_weight_le terms)
  have ha := Int.natAbs_add_le t.1 u.1
  simp only [termsWeight, List.map_cons, List.sum_cons]
  exact ha.trans (Nat.add_le_add_left hu' t.1.natAbs)

theorem marginalRun_coefficient_bits {n : ℕ} (formula : CNFFormula n)
    (t : ℤ × Cube n) (h : t ∈ marginalRun formula [(1, topCube n)]) :
    1 + Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 2 := by
  have hw := (mem_coefficient_le_weight t _ h).trans
    (marginalRun_weight_le formula [(1, topCube n)])
  have he : t.1.natAbs ≤ 2 ^ (formula.length + literalCount formula) := by
    have hb : t.1.natAbs ≤ 2 ^ marginalBudget formula := by simpa [termsWeight] using hw
    exact hb.trans
      (Nat.pow_le_pow_right (by omega) (marginalBudget_le_source formula))
  have hs : Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 1 := by
    apply Nat.size_le.mpr
    have hp : 0 < 2 ^ (formula.length + literalCount formula) := by positivity
    rw [pow_succ]
    omega
  omega

theorem marginalStates_coefficient_bits {n : ℕ} (formula : CNFFormula n)
    (state : Terms n) (hs : state ∈ marginalStates formula [(1, topCube n)])
    (t : ℤ × Cube n) (ht : t ∈ state) :
    1 + Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 2 := by
  have hw := (mem_coefficient_le_weight t _ ht).trans
    (marginalStates_weight_le formula [(1, topCube n)] state hs)
  have hb : t.1.natAbs ≤ 2 ^ marginalBudget formula := by simpa [termsWeight] using hw
  have he := hb.trans
    (Nat.pow_le_pow_right (by omega) (marginalBudget_le_source formula))
  have hs : Nat.size t.1.natAbs ≤ formula.length + literalCount formula + 1 := by
    apply Nat.size_le.mpr
    have hp : 0 < 2 ^ (formula.length + literalCount formula) := by positivity
    rw [pow_succ]
    omega
  omega

end SaturationMonoid.ComplexityProjection.SATJoint
