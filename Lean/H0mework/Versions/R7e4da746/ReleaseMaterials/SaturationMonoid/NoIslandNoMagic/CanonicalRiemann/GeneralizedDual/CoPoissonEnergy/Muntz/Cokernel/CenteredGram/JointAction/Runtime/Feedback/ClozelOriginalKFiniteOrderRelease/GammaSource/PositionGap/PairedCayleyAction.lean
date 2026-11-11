import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.PairedCayleyAction

open Complex BurnolPhysicalState UnitPowerJordanSource
open OriginalKFullAdjointSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource

open private fourier_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator
open private original_R_Fourier_adjoint from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.PhysicalOutsideSource
open private actualAdjoint_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
open private actual_adjoint_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private source_left_inverse source_right_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "F" => fourierL2
local notation "R" => burnolDirectRightResolventCLM
local notation "T" => sourceCayley
local notation "S" => sourceStep
local notation "δ" => sourceDamping
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem fourier_R (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    F (R c v) = S (d c) (F v) :=
  (original_R_Fourier_adjoint c v).trans
    ((actualAdjoint_read (d c) (F v)).symm.trans (sourceStep_actual (d c) (F v)))

private theorem fourier_adjoint (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    F ((T c).adjoint v) = T (d c) (F v) := by
  have damping : δ (d c) = δ c := by
    simp only [sourceDamping, OriginalPrimitiveRankBalance.conjugateCoordinate, Complex.star_def, Complex.conj_re]
  rw [actual_adjoint_source, map_add, map_smul, fourier_source, sourceCayley_apply, damping]
  rfl

private theorem fourier_R_power (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    F (((R c)^n) v) = ((S (d c))^n) (F v) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n earlier =>
    rw [pow_succ' (R c), mul_apply_eq_comp, fourier_R, earlier, pow_succ' (S (d c)), mul_apply_eq_comp]

private theorem fourier_adjoint_power (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    F ((((T c).adjoint)^n) v) = ((T (d c))^n) (F v) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n earlier =>
    rw [pow_succ' (T c).adjoint, mul_apply_eq_comp, fourier_adjoint, earlier,
      pow_succ' (T (d c)), mul_apply_eq_comp]

/-- The literal outward R after its own forward Cayley action produces the same first difference. -/
def differenceStep (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (δ c : ℂ)⁻¹ • (1-T c)

private theorem step_commutes (c : BurnolCompletedMellinCoordinate) : Commute (S c) (T c) := by
  apply ContinuousLinearMap.ext
  intro v
  change S c (T c v) = T c (S c v)
  have left := source_left_inverse c v
  have right := source_right_inverse c v
  rw [actual_adjoint_source] at left
  rw [actual_adjoint_source, map_add, map_smul] at right
  have damping : (δ c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
  apply smul_right_injective BurnolL2 damping
  exact add_left_cancel (left.trans right.symm)

private theorem step_cayley (c : BurnolCompletedMellinCoordinate) : S c * T c = differenceStep c := by
  apply ContinuousLinearMap.ext
  intro v
  change S c (T c v) = (δ c : ℂ)⁻¹ • (v - T c v)
  have returned := source_left_inverse c v
  rw [actual_adjoint_source] at returned
  have price : (δ c : ℂ) • S c (T c v) = v - T c v := by
    linear_combination (norm := module) returned
  have damping : (δ c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
  rw [← price, smul_smul, inv_mul_cancel₀ damping, one_smul]

/-- Both actual powers on the same field reduce to the native Fourier-side difference word. -/
theorem actual_fourier_mixed_return (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    F (((R c)^n) ((((T c).adjoint)^n) v)) = ((differenceStep (d c))^n) (F v) := by
  rw [fourier_R_power, fourier_adjoint_power]
  change (((S (d c))^n)*((T (d c))^n)) (F v) = _
  rw [← (step_commutes (d c)).mul_pow, step_cayley]

/-- The native difference word preserves its own gap and transports the full conjugate price. -/
theorem actual_difference_gap_read (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (gap : v ∈ G) (n : Nat) :
    ((differenceStep c)^n) v ∈ G ∧
      M (d c) (((differenceStep c)^n) v) = ((δ c : ℂ)⁻¹)^n * M (d c) v := by
  induction n with
  | zero => simpa only [pow_zero, one_apply_eq_self, one_mul] using And.intro gap (rfl : M (d c) v = M (d c) v)
  | succ n earlier =>
    let prior := ((differenceStep c)^n) v
    rw [pow_succ' (differenceStep c), mul_apply_eq_comp]
    change (δ c : ℂ)⁻¹ • (prior - T c prior) ∈ G ∧
      M (d c) ((δ c : ℂ)⁻¹ • (prior - T c prior)) = _
    refine ⟨(G).smul_mem _ ((G).sub_mem earlier.1 (actual_gap_cayley c prior earlier.1)), ?_⟩
    rw [map_smul, map_sub, actual_gap_cayley_conjugate_zero c prior earlier.1, sub_zero,
      smul_eq_mul, earlier.2, pow_succ', mul_assoc]

end OriginalKFiniteOrderRelease.PositionGapCayley.PairedCayleyAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
