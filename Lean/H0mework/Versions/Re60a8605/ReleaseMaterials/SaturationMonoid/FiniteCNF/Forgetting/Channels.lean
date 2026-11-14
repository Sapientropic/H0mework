import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Action
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.Proposition141

set_option autoImplicit false

namespace SaturationMonoid.ComplexityProjection.SATSource.ForgettingChannels
open scoped BigOperators
noncomputable section

def keep {n : Nat} (formula : CNFFormula n) (point : Assignment n) : ℚ :=
  ((violationCount formula point : ℚ)+1)⁻¹

def sample {n : Nat} (formula : CNFFormula n) (steps : Nat) : ℚ :=
  finitePopulationAggregate (fun _ : Assignment n => (1 : ℚ)) (keep formula) steps

theorem sample_sum {n : Nat} (formula : CNFFormula n) (steps : Nat) :
    sample formula steps=∑ point : Assignment n, keep formula point^steps := by
  simp [sample,finitePopulationAggregate]

theorem sample_sourceMass {n : Nat} (formula : CNFFormula n) (steps : Nat) :
    sample formula steps=sourceMass n (fun point => keep formula point^steps) := by
  rw [sample_sum,sourceMass_apply]

theorem heterogeneity {n : Nat} (formula : CNFFormula n) :
    2*(sample formula 0*sample formula 2-sample formula 1^2)=
      ∑ left : Assignment n, ∑ right : Assignment n, (keep formula left-keep formula right)^2 := by
  simpa [sample,finitePopulationMomentResidual] using
    (finitePopulationMomentResidual_pairwise_double_sum
      (fun _ : Assignment n => (1 : ℚ)) (keep formula))

theorem keep_nonneg {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    0 ≤ keep formula point := by unfold keep; positivity

theorem keep_one_iff {n : Nat} (formula : CNFFormula n) (point : Assignment n) :
    keep formula point=1 ↔ CNFFormula.eval formula (extendAssignment point)=true := by
  rw [← violationCount_eq_zero_iff_eval]
  simp [keep,inv_eq_one]

theorem unsat_keep {n : Nat} (formula : CNFFormula n) (no : ¬ CNFSatisfiable formula)
    (point : Assignment n) : keep formula point ≤ (1/2 : ℚ) := by
  have positive : 0 < violationCount formula point := by
    by_contra! h
    have zero : violationCount formula point=0 := Nat.eq_zero_of_le_zero h
    exact no ⟨extendAssignment point,(violationCount_eq_zero_iff_eval formula point).mp zero⟩
  have bound : (2 : ℚ) ≤ (violationCount formula point : ℚ)+1 := by
    exact_mod_cast (show 2 ≤ violationCount formula point+1 by omega)
  simpa [keep,one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ)<2) bound

theorem sat_signal {n : Nat} (formula : CNFFormula n) (yes : CNFSatisfiable formula) (steps : Nat) :
    (1 : ℚ) ≤ sample formula steps := by
  obtain ⟨point,accepted⟩ := (satisfiable_iff_finite_assignment formula).mp yes
  have retained := (keep_one_iff formula point).mpr accepted
  rw [sample_sum]
  have bound : keep formula point^steps ≤ ∑ other : Assignment n, keep formula other^steps :=
    Finset.single_le_sum (fun other _ => pow_nonneg (keep_nonneg formula other) steps) (Finset.mem_univ point)
  simpa only [retained,one_pow] using bound

theorem unsat_signal {n : Nat} (formula : CNFFormula n) (no : ¬ CNFSatisfiable formula) :
    sample formula (n+2) ≤ (1/4 : ℚ) := by
  rw [sample_sum]
  calc
    (∑ point : Assignment n, keep formula point^(n+2)) ≤
        ∑ _ : Assignment n, (1/2 : ℚ)^(n+2) :=
      Finset.sum_le_sum (fun point _ => pow_le_pow_left₀ (keep_nonneg formula point) (unsat_keep formula no point) (n+2))
    _ = 1/4 := by
      simp [Assignment,nsmul_eq_mul,pow_add]
      norm_num

theorem approximate_decision {n : Nat} (formula : CNFFormula n) (estimate : ℚ)
    (error : |estimate-sample formula (n+2)| ≤ (1/8 : ℚ)) :
    (1/2 : ℚ)<estimate ↔ CNFSatisfiable formula := by
  have bounds := abs_le.mp error
  constructor
  · intro high
    by_contra no
    have small := unsat_signal formula no
    linarith
  · intro yes
    have large := sat_signal formula yes (n+2)
    linarith

end
end SaturationMonoid.ComplexityProjection.SATSource.ForgettingChannels
