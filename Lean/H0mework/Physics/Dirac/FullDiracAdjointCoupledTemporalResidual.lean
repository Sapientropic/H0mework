import H0mework.Physics.Dirac.FullDiracAdjointPreservation
import H0mework.Physics.SynchronizedJoint.FixedDiracVectorCurrentTemporalRateZeroSlice
import H0mework.Physics.SynchronizedJoint.FixedActionSelectedJointSuccessor

/-!
# Coupled-temporal full Dirac-adjoint residual

The action-selected carry is already one full material.  Consequently the
coupled temporal write is paired exactly when its two generated corrections
have zero canonical-adjoint residual.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1200000

namespace SaturationMonoid.PhysicsCore
namespace StageNineFullDiracAdjointCoupledTemporalResidual

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeFixedP506ActionSelectedDiracVectorCurrentTemporalRateZeroSlice
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathActionSelectedJointSuccessor
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineEnrichedProofFreeSource
open StageNineFullDiracAdjointMaterial
open StageNineHolonomicField
open StageNineP286DiracAdjointCoefficientMaterial

noncomputable section

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

private abbrev Carry : StageNineHolonomicConfiguration :=
  completeJointActionSelectedScalarMomentumCarryActual Source Current

private abbrev Coupled : StageNineHolonomicConfiguration :=
  completeJointActionSelectedCoupledTemporalActual Source Current

/-- Primal correction installed by the coupled temporal writer. -/
def coupledTemporalMatterCorrection (point : BasePoint) :=
  matterCoordinateEquiv.symm
    (canonicalTimePrimitive
      (completeJointMatterTemporalCoordinateCorrection Source Carry) point)

/-- Dual correction installed by the same writer. -/
def coupledTemporalAdjointCorrection (point : BasePoint) :=
  matterDualOfCoordinates
    (canonicalTimePrimitive
      (completeJointAdjointTemporalCoordinateCorrection Source Carry) point)

def CoupledTemporalCorrectionPairedAt (point : BasePoint) : Prop :=
  FullDiracAdjointPaired
    (coupledTemporalMatterCorrection point)
    (coupledTemporalAdjointCorrection point)

/-- Earliest source-operator residual after removing the paired carry. -/
def coupledTemporalSourceOperatorResidual (point : BasePoint) :=
  fullDiracAdjointResidual
    (coupledTemporalMatterCorrection point)
    (coupledTemporalAdjointCorrection point)

@[simp] theorem coupled_matter_read (point : BasePoint) :
    Coupled.matter point =
      Carry.matter point + coupledTemporalMatterCorrection point :=
  rfl

@[simp] theorem coupled_adjoint_read (point : BasePoint) :
    Coupled.conjugateMatter point =
      Carry.conjugateMatter point + coupledTemporalAdjointCorrection point :=
  rfl

/-- The action-selected carry is full material at every spacetime point. -/
theorem carry_fullDiracAdjointPaired
    (time : ℝ) (space : StageNineSpatialPoint) :
    FullDiracAdjointPaired
      (Carry.matter (canonicalCauchySlicePoint time space))
      (Carry.conjugateMatter (canonicalCauchySlicePoint time space)) := by
  have paired := fixedActionSelectedCarry_p286DiracPaired time space
  unfold FullDiracAdjointPaired
  rw [paired.1, paired.2, fullCanonicalDiracAdjoint_p286SpinMatter]

/-- Removing the paired carry leaves exactly the correction responsibility. -/
theorem coupled_fullDiracAdjointPaired_iff_correction
    (time : ℝ) (space : StageNineSpatialPoint) :
    FullDiracAdjointPaired
        (Coupled.matter (canonicalCauchySlicePoint time space))
        (Coupled.conjugateMatter (canonicalCauchySlicePoint time space)) ↔
      CoupledTemporalCorrectionPairedAt
        (canonicalCauchySlicePoint time space) := by
  have carry := carry_fullDiracAdjointPaired time space
  constructor
  · intro total
    rw [coupled_matter_read, coupled_adjoint_read] at total
    unfold FullDiracAdjointPaired at total carry
    unfold CoupledTemporalCorrectionPairedAt FullDiracAdjointPaired
    rw [fullCanonicalDiracAdjoint_add, ← carry] at total
    exact add_left_cancel total
  · intro correction
    rw [coupled_matter_read, coupled_adjoint_read]
    exact carry.add correction

/-- Coupled pairing is exactly vanishing of the generated operator residual. -/
theorem coupled_fullDiracAdjointPaired_iff_sourceOperatorResidual_zero
    (time : ℝ) (space : StageNineSpatialPoint) :
    FullDiracAdjointPaired
        (Coupled.matter (canonicalCauchySlicePoint time space))
        (Coupled.conjugateMatter (canonicalCauchySlicePoint time space)) ↔
      coupledTemporalSourceOperatorResidual
          (canonicalCauchySlicePoint time space) = 0 := by
  rw [coupled_fullDiracAdjointPaired_iff_correction]
  exact fullDiracAdjointPaired_iff_residual_zero _ _

end
end StageNineFullDiracAdjointCoupledTemporalResidual
end SaturationMonoid.PhysicsCore
