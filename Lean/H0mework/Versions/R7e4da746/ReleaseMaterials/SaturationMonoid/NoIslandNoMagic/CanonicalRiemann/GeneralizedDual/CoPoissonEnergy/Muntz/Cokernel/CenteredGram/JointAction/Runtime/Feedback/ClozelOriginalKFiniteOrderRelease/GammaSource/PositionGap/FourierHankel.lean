import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open Complex BurnolPhysicalState OriginalRieszSource
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace lp

open private basis_read orbit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
open private fourier_adjoint from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction
open private source_left_inverse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource
open private position_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private extension_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

local notation "S" => PositionField
local notation "G" => positionSpace.toSubmodule
local notation "F" => fourierL2
local notation "T" => sourceCayley
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Z" => Constructor.zeroMean
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "Seq" => ℓ²(Nat, ℂ)

local instance : CompleteSpace S :=
  IsComplete.completeSpace_coe positionSpace.isClosed.isComplete

private theorem fourier_forward (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    F (T c v) = (T (d c)).adjoint (F v) := by
  have actual := fourier_adjoint c (T c v)
  rw [source_left_inverse] at actual
  rw [actual, source_left_inverse]

private theorem fourier_forward_power (c : BurnolCompletedMellinCoordinate) (v : BurnolL2) (n : Nat) :
    F (((T c)^n) v) = (((T (d c)).adjoint)^n) (F v) := by
  induction n with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ n previous =>
    rw [pow_succ' (T c), mul_apply_eq_comp, fourier_forward, previous, pow_succ', mul_apply_eq_comp]

private theorem orbit_read (c : BurnolCompletedMellinCoordinate) (i : Nat) :
    (basis c i : BurnolL2) = ((T c)^i) (positionHead c) :=
  congrArg (fun w : S => (w : BurnolL2)) (basis_read c i)

/-- The Fourier action between the two generated gap inventories. -/
def hankel (c : BurnolCompletedMellinCoordinate) : Seq →L[ℂ] Seq :=
  (basis (d c)).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((G).orthogonalProjectionOnto.comp
      ((F).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((G).subtypeL.comp (basis c).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap)))

private theorem hankel_inner (c : BurnolCompletedMellinCoordinate) (a : Seq) (i : Nat) :
    hankel c a i = inner ℂ (basis (d c) i : BurnolL2)
      (F ((basis c).repr.symm a : BurnolL2)) := by
  change (basis (d c)).repr ((G).orthogonalProjectionOnto (F ((basis c).repr.symm a : BurnolL2))) i = _
  rw [HilbertBasis.repr_apply_apply]
  exact (G).inner_orthogonalProjectionOnto_eq_of_mem_left _ _

private theorem power_adjoint_pair (c : BurnolCompletedMellinCoordinate)
    (u v : BurnolL2) (j : Nat) :
    inner ℂ u ((((T c).adjoint)^j) v) = inner ℂ (((T c)^j) u) v := by
  induction j generalizing u with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ j previous =>
    rw [pow_succ' (T c).adjoint, mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right,
      previous, pow_succ, mul_apply_eq_comp]

/-- Every matrix entry is read from the same Fourier image of the original gap head. -/
theorem actual_hankel_entry (c : BurnolCompletedMellinCoordinate) (i j : Nat) :
    hankel c (lp.single 2 j (1 : ℂ)) i = hankel c (lp.single 2 0 (1 : ℂ)) (i+j) := by
  rw [hankel_inner, hankel_inner, HilbertBasis.repr_symm_single, HilbertBasis.repr_symm_single,
    orbit_read c j, orbit_read c 0, pow_zero, one_apply_eq_self,
    fourier_forward_power, power_adjoint_pair, orbit_read (d c) i, orbit_read (d c) (i+j)]
  rw [add_comm i j, pow_add, mul_apply_eq_comp]

/-- The accompanying full centered quarter field of the same Fourier action. -/
def centeredFourier (c : BurnolCompletedMellinCoordinate) : Seq →L[ℂ] M :=
  (Z).comp ((Rq).comp ((F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((G).subtypeL.comp (basis c).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap)))

private theorem centered_split (v : BurnolL2) (even : reflectL2 v = v) :
    (G).starProjection v + E (Z (Rq v) : BurnolQuarterIntervalL2) = v := by
  let z := Z (Rq v)
  have zEven : reflectRestricted (1/4 : ℝ) (z : BurnolQuarterIntervalL2) = z := by
    have paid := burnolAmbientMeanZeroPosition_reflection_fixed v
    rw [position_read v even] at paid
    exact paid
  have split : (G).starProjection v = v - E (z : BurnolQuarterIntervalL2) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · refine ⟨?_, mem_evenL2ClosedFace_iff.mpr ?_⟩
      · change Rq (v - E (z : BurnolQuarterIntervalL2)) ∈ intervalConstantLine (1/4 : ℝ)
        rw [map_sub, burnolQuarterRestriction_zeroExtension, show (z : BurnolQuarterIntervalL2) =
          Rq v - burnolQuarterMeanCoefficient (Rq v) • intervalConstant (1/4 : ℝ) from
            Constructor.zeroMean_read (Rq v), sub_sub_cancel]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · rw [map_sub, even, extension_even _ zEven]
    · intro w member
      rw [sub_sub_cancel]
      unfold burnolQuarterZeroExtension burnolRadiusZeroExtension
      rw [ContinuousLinearMap.adjoint_inner_left, inner_eq_zero_symm]
      exact z.property _ member.1
  rw [split, sub_add_cancel]

/-- The wave coefficients and the actual quarter field reconstruct the whole original Fourier result. -/
theorem actual_fourier_readback (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    ((basis (d c)).repr.symm (hankel c a) : BurnolL2) +
      E (centeredFourier c a : BurnolQuarterIntervalL2) = F ((basis c).repr.symm a : BurnolL2) := by
  let v := (basis c).repr.symm a
  change ((basis (d c)).repr.symm ((basis (d c)).repr ((G).orthogonalProjectionOnto (F (v : BurnolL2)))) :
    BurnolL2) + E (Z (Rq (F (v : BurnolL2))) : BurnolQuarterIntervalL2) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact centered_split _ (mem_evenL2ClosedFace_iff.mp (fourierL2_mem_evenL2ClosedFace v.property.2))

/-- Centering the quarter keeps the original Fourier mean in the wave inventory. -/
theorem actual_fourier_mean (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    burnolQuarterMeanCoefficient (Rq ((basis (d c)).repr.symm (hankel c a) : BurnolL2)) =
      burnolQuarterMeanCoefficient (Rq (F ((basis c).repr.symm a : BurnolL2))) := by
  rw [← actual_fourier_readback c a, map_add, burnolQuarterRestriction_zeroExtension]
  have centered : inner ℂ (intervalConstant (1/4 : ℝ))
      (centeredFourier c a : BurnolQuarterIntervalL2) = 0 :=
    (centeredFourier c a).property _ (Submodule.mem_span_singleton_self _)
  unfold burnolQuarterMeanCoefficient
  rw [inner_add_right, centered, add_zero]

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
