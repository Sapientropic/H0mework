import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.MellinSeparation

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley

open Complex Filter BurnolPhysicalState
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped Topology

open private right_quarter below_half adjoint_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private coordinate_eq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CrossUnitKSource
open private source_left_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

local notation "G" => locallyConstantFace burnolUnscaledCommonGapRadius
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "T" => sourceCayley
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem power_norm (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    ‖((T c)^n) v‖ = ‖v‖ := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self]
  | succ n earlier => rw [pow_succ', mul_apply_eq_comp, sourceCayley_norm, earlier]

/-- The original position-gap Cayley action has trivial intersection of its full finite images. -/
theorem actual_gap_cayley_pure (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v)
    (all : ∀ n : Nat, ∃ prior : BurnolL2, prior ∈ G ∧ reflectL2 prior = prior ∧ ((T c)^n) prior = v) :
    v = 0 := by
  apply actual_mellin_separates_positionGap v gap even
  intro reader _
  let w := reader.value/2
  have chart : burnolDivisionCompletedMellinCoordinate w (right_quarter reader) (below_half reader) = reader := by
    apply coordinate_eq
    change 2*(reader.value/2)=reader.value
    ring
  have bound (n : Nat) : ‖M reader v‖ ≤ ‖gapMultiplier c w‖^n * (‖M reader‖ * ‖v‖) := by
    obtain ⟨prior, before, parity, performed⟩ := all n
    have normal : ‖prior‖ = ‖v‖ := (power_norm c prior n).symm.trans (congrArg norm performed)
    have actual := actual_gap_cayley_power_scalar c prior before parity n w (right_quarter reader) (below_half reader)
    rw [chart, performed] at actual
    rw [actual, norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (norm_nonneg _) n)
    rw [← normal]
    exact (M reader).le_opNorm prior
  have limit := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (gapMultiplier c w))
    (gapMultiplier_norm_lt_one c w (right_quarter reader))).mul_const (‖M reader‖ * ‖v‖)
  have erased : ‖M reader v‖ ≤ 0 := by
    simpa only [zero_mul] using ge_of_tendsto limit (Eventually.of_forall bound)
  exact norm_eq_zero.mp (le_antisymm erased (norm_nonneg _))

private theorem adjoint_power_inverse (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    (((T c).adjoint)^n) (((T c)^n) v) = v := by
  induction n with
  | zero => rw [pow_zero, one_apply_eq_self, pow_zero, one_apply_eq_self]
  | succ n previous =>
    rw [pow_succ (T c).adjoint, mul_apply_eq_comp, pow_succ' (T c), mul_apply_eq_comp,
      source_left_inverse, previous]

/-- Every nonzero even position-gap field has a first actual backward step leaving that gap. -/
theorem actual_gap_cayley_first_escape (c : BurnolCompletedMellinCoordinate) (v : BurnolL2)
    (gap : v ∈ G) (even : reflectL2 v = v) (nonzero : v ≠ 0) :
    ∃ n : Nat, (∀ i < n, M (d c) ((((T c).adjoint)^i) v) = 0) ∧
      M (d c) ((((T c).adjoint)^n) v) ≠ 0 ∧
      (((T c).adjoint)^n) v ∈ G ∧ ¬ (((T c).adjoint)^(n+1)) v ∈ G := by
  classical
  let seen (n : Nat) := M (d c) ((((T c).adjoint)^n) v)
  have existsEscape : ∃ n, seen n ≠ 0 := by
    by_contra absent
    have silent (i : Nat) : seen i = 0 := by
      by_contra live
      exact absent ⟨i,live⟩
    apply nonzero (actual_gap_cayley_pure c v gap even ?_)
    intro n
    exact (actual_gap_cayley_power_image c n v gap even).2 (fun i _ => silent i)
  let n := Nat.find existsEscape
  have first : seen n ≠ 0 := Nat.find_spec existsEscape
  have earlier (i : Nat) (within : i < n) : seen i = 0 := by
    by_contra priced
    exact (not_lt_of_ge (Nat.find_min' existsEscape priced)) within
  obtain ⟨prior, before, parity, reached⟩ := (actual_gap_cayley_power_image c n v gap even).2 earlier
  have backward : (((T c).adjoint)^n) v = prior := by
    rw [← reached, adjoint_power_inverse]
  have lastGap : (((T c).adjoint)^n) v ∈ G := by rw [backward]; exact before
  have lastEven : reflectL2 ((((T c).adjoint)^n) v) = (((T c).adjoint)^n) v := by rw [backward]; exact parity
  refine ⟨n, earlier, first, lastGap, ?_⟩
  rw [pow_succ', mul_apply_eq_comp]
  exact fun next => first ((actual_gap_cayley_adjoint_iff c _ lastGap lastEven).1 next)

end OriginalKFiniteOrderRelease.PositionGapCayley
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
