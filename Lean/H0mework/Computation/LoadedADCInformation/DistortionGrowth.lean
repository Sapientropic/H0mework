import H0mework.Computation.LoadedADCInformation.DistortionFibres

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section

variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}

def gridBase (bound : Nat) : ℝ :=
  tick (hardware := hardware) ^ 2 / (3 * (bound + 1 : ℝ)) *
    ∑ side : Fin 2, (phaseCount bound side : ℝ) * ((phaseCount bound side : ℝ) ^ 2 - 1)

theorem gridBase_exact (bound : Nat) :
    gridBase (hardware := hardware) bound =
      tick (hardware := hardware) ^ 2 * ((bound + 1 : ℝ) ^ 2 - 4) / 12 +
        tick (hardware := hardware) ^ 2 *
          ((phaseCount bound 0 : ℝ) - (phaseCount bound 1 : ℝ)) ^ 2 / 4 := by
  have total : (phaseCount bound 0 : ℝ) + (phaseCount bound 1 : ℝ) = (bound + 1 : ℝ) := by
    exact_mod_cast phaseCount_total bound
  have totalNonzero : (phaseCount bound 0 : ℝ) + (phaseCount bound 1 : ℝ) ≠ 0 := by
    rw [total]
    positivity
  unfold gridBase
  rw [Fin.sum_univ_two, ← total]
  field_simp
  ring

theorem gridBase_lower (bound : Nat) :
    tick (hardware := hardware) ^ 2 * ((bound + 1 : ℝ) ^ 2 - 4) / 12 ≤
      gridBase (hardware := hardware) bound := by
  rw [gridBase_exact]
  have remainder : 0 ≤ tick (hardware := hardware) ^ 2 *
      ((phaseCount bound 0 : ℝ) - (phaseCount bound 1 : ℝ)) ^ 2 / 4 := by positivity
  linarith

theorem gridBase_eventually_exceeds (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) :
    ∃ first : Nat, ∀ bound : Nat, first ≤ bound → epsilon ^ 2 < gridBase (hardware := hardware) bound := by
  have positive : 0 < tick (hardware := hardware) ^ 2 := sq_pos_of_pos tick_pos
  obtain ⟨first, above⟩ := exists_nat_gt
    (12 * (epsilon + 1) ^ 2 / tick (hardware := hardware) ^ 2 + 4)
  refine ⟨first, ?_⟩
  intro bound later
  have laterReal : (first : ℝ) < (bound + 1 : ℝ) := by exact_mod_cast Nat.lt_succ_of_le later
  have threshold := above.trans laterReal
  have countLower : (1 : ℝ) ≤ (bound + 1 : ℝ) := by
    have sourceCount : 0 ≤ (bound : ℝ) := Nat.cast_nonneg bound
    linarith
  have countSquare : (bound + 1 : ℝ) ≤ (bound + 1 : ℝ) ^ 2 := by nlinarith
  have gap : 12 * (epsilon + 1) ^ 2 / tick (hardware := hardware) ^ 2 <
      (bound + 1 : ℝ) ^ 2 - 4 := by linarith
  have scaled := mul_lt_mul_of_pos_right gap positive
  rw [div_mul_cancel₀ _ positive.ne'] at scaled
  have accuracy : epsilon ^ 2 < tick (hardware := hardware) ^ 2 * ((bound + 1 : ℝ) ^ 2 - 4) / 12 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 12)).mpr
    nlinarith
  exact accuracy.trans_le (gridBase_lower bound)

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
