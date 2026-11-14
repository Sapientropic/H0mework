import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.DyadicCompact

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Inverse.Projection
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszSourceGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.DyadicCompact
open scoped InnerProductSpace
open private native_inverse_source from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PrimeDual
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "E" => burnolQuarterZeroExtension
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "h₀" => Real.log stageZeroSonineQ
local notation "Q" => pairedBurnolMultiplicativeDilation h₀

private theorem compact_meanZero_projection (state : M) : P (E (state : Hq)) = 0 := by
  apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
  intro value inside
  rw [show E = burnolQuarterRestriction.adjoint from rfl,
    ContinuousLinearMap.adjoint_inner_right]
  exact (Submodule.mem_orthogonal _ _).mp state.property _ inside.1.1

private theorem elementary_projection (c : BurnolCompletedMellinCoordinate) :
    P (gapState c) = K c := by
  unfold gapState
  have odd : P (burnolAmbientCompletedMellinKernelFormula c -
      burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula c)) = 0 := by
    apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
    intro test membership
    rw [inner_eq_zero_symm]
    exact burnolAmbientOddResidual_inner_physical_eq_zero _ ⟨test, membership⟩
  rw [map_sub] at odd
  rw [← sub_eq_zero.mp odd]
  rw [← burnolAmbientCompletedMellinRieszVector_eq_kernelFormula,
    burnolCompletedMellinRieszVector_eq_ambientProjection]
  rfl

/-- The mean-zero native correction is paid before the original physical projection. -/
theorem actual_native_inverse_projection (c : BurnolCompletedMellinCoordinate) :
    P (nativeInverseSource c) = -K c := by
  change P (fourierL2.symm (nativeSource c)) = _
  rw [native_inverse_source, map_sub, compact_meanZero_projection, zero_sub,
    elementary_projection]

/-- Both physical slots are restrictions of the same whole native inverse input. -/
theorem actual_native_same_input_cotest (c : BurnolCompletedMellinCoordinate) :
    physicalCotest c =
      P (Q (P (nativeInverseSource c) : BurnolL2)) -
        star (pairedMellinTranslationCharacter c.value h₀) • P (nativeInverseSource c) := by
  rw [actual_native_inverse_projection]
  change star (pairedMellinTranslationCharacter c.value h₀) • K c -
    P (OriginalKPairedBEulerJunctionSource.sourceAction c) =
      P (Q (-(K c : BurnolL2))) -
        star (pairedMellinTranslationCharacter c.value h₀) • (-K c)
  rw [map_neg, map_neg, smul_neg]
  change _ = -P (OriginalKPairedBEulerJunctionSource.sourceAction c) -
    -(star (pairedMellinTranslationCharacter c.value h₀) • K c)
  module

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Inverse.Projection
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
