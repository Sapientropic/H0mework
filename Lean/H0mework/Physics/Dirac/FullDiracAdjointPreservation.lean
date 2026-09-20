import H0mework.Physics.Dirac.GeneratedFullDiracAdjointMaterial

/-!
# Full Dirac-adjoint preservation

The source-generated primal and dual first jets are one material.  Their
affine actual lift therefore preserves the canonical full Dirac adjoint at
every generated point.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore
namespace StageNineFullDiracAdjointPreservation

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineConjugateMatterActionTimeVelocity
open StageNineEnrichedProofFreeSource
open StageNineFullDiracAdjointMaterial
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineP286ActionVelocityLocalActualLift
open StageNineSourceGeneratedFullDiracAdjointMaterial
open StageNineSourceGeneratedMatterSpinActionUpdate

noncomputable section

/-- Primal carrier generated in one direction of the affine germ. -/
def actionGeneratedMatterLocalJet
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    DiracExteriorMatterAction.DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (actionGeneratedMatterLocalJetCoordinate state space direction)

/-- Positive formal-adjoint law for all four generated first jets. -/
def FullDiracAdjointLocalJetPaired
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint) : Prop :=
  ∀ direction : LorentzianIndex,
    FullDiracAdjointPaired
      (actionGeneratedMatterLocalJet state space direction)
      (actionGeneratedConjugateMatterLocalJet state space direction)

private theorem fullCanonicalDiracAdjoint_sum
    {Index : Type} [Fintype Index]
    (matter : Index → DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint (∑ index, matter index) =
      ∑ index, fullCanonicalDiracAdjoint (matter index) := by
  classical
  induction (Finset.univ : Finset Index) using Finset.induction_on with
  | empty => simp
  | @insert index indices hnotmem ih =>
      simp [Finset.sum_insert, hnotmem, fullCanonicalDiracAdjoint_add, ih]

private theorem actionGeneratedMatterLocalIncrement_read
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    matterCoordinateEquiv.symm
        (actionGeneratedMatterLocalIncrement state space point) =
      ∑ direction : LorentzianIndex,
        (localBaseCoordinate direction point : ℝ) •
          actionGeneratedMatterLocalJet state space direction := by
  simp only [actionGeneratedMatterLocalIncrement, sum_apply,
    ContinuousLinearMap.smulRight_apply, map_sum]
  apply Finset.sum_congr rfl
  intro direction _
  exact matterCoordinateEquiv.symm.toLinearMap.map_smul_of_tower
    (localBaseCoordinate direction point)
    (actionGeneratedMatterLocalJetCoordinate state space direction)

/-- Four paired jets force the complete affine write to remain paired. -/
theorem sourceActionGeneratedMatterDualLocalActualLift_fullDiracAdjointPaired_of_jet
    (state : StageNineCauchyState)
    (space : StageNineSpatialPoint)
    (seed : FullDiracAdjointPaired
      (state.matter space) (state.conjugateMatter space))
    (jet : FullDiracAdjointLocalJetPaired state space)
    (point : BasePoint) :
    FullDiracAdjointPaired
      ((sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource state space).matter point)
      ((sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource state space).conjugateMatter point) := by
  unfold FullDiracAdjointPaired at seed ⊢
  change
    actionGeneratedConjugateMatterLocalField state space point =
      fullCanonicalDiracAdjoint
        (actionGeneratedMatterLocalField state space point)
  unfold actionGeneratedConjugateMatterLocalField
    actionGeneratedMatterLocalField actionGeneratedMatterLocalCoordinate
  simp only [map_add, matterCoordinateEquiv.symm_apply_apply]
  rw [actionGeneratedMatterLocalIncrement_read,
    fullCanonicalDiracAdjoint_add, seed,
    fullCanonicalDiracAdjoint_sum]
  apply congrArg (fun tail =>
    fullCanonicalDiracAdjoint (state.matter space) + tail)
  apply Finset.sum_congr rfl
  intro direction _
  change
    ((localBaseCoordinate direction point : ℝ) : ℂ) •
        actionGeneratedConjugateMatterLocalJet state space direction =
      fullCanonicalDiracAdjoint
        (((localBaseCoordinate direction point : ℝ) : ℂ) •
          actionGeneratedMatterLocalJet state space direction)
  rw [fullCanonicalDiracAdjoint_smul, jet direction]
  simp

/-- The three spatial source jets are paired because both seed fields are
spatially constant. -/
theorem positiveSourceTargetMatterCauchyState_spatialJetPaired
    (space : StageNineSpatialPoint)
    (direction : Fin 3) :
    FullDiracAdjointPaired
      (actionGeneratedMatterLocalJet positiveSourceTargetMatterCauchyState
        space direction.succ)
      (actionGeneratedConjugateMatterLocalJet
        positiveSourceTargetMatterCauchyState space direction.succ) := by
  fin_cases direction <;>
    unfold FullDiracAdjointPaired actionGeneratedMatterLocalJet <;>
    simp [actionGeneratedMatterLocalJetCoordinate,
      actionGeneratedConjugateMatterLocalJet,
      cauchyConjugateMatterSpatialDerivative,
      cauchyConjugateMatterSpatialDerivativeCoordinate,
      cauchyMatterSpatialDerivativeCoordinate,
      positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState]

/-- The source-selected time jets satisfy the formal-adjoint law. -/
theorem positiveSourceTargetMatterCauchyState_temporalFormalAdjoint
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterTimeDerivative
        positiveSourceTargetMatterCauchyState space =
      fullCanonicalDiracAdjoint
        (actionGeneratedMatterRawTimeVelocity
          positiveSourceTargetMatterCauchyState space) := by
  rw [positiveSourceTargetConjugateMatterTimeDerivative_zero,
    positiveSourceTargetMatterRawTimeVelocity_zero]
  simp

/-- All four source-generated jets are restrictions of one material. -/
theorem positiveSourceTargetMatterCauchyState_localJetPaired
    (space : StageNineSpatialPoint) :
    FullDiracAdjointLocalJetPaired
      positiveSourceTargetMatterCauchyState space := by
  intro direction
  fin_cases direction
  · simpa [FullDiracAdjointPaired, actionGeneratedMatterLocalJet,
      actionGeneratedMatterLocalJetCoordinate,
      actionGeneratedConjugateMatterLocalJet] using
      positiveSourceTargetMatterCauchyState_temporalFormalAdjoint space
  · exact positiveSourceTargetMatterCauchyState_spatialJetPaired space 0
  · exact positiveSourceTargetMatterCauchyState_spatialJetPaired space 1
  · exact positiveSourceTargetMatterCauchyState_spatialJetPaired space 2

/-- The independently generated affine actual write preserves full material
at every spacetime point. -/
theorem positiveSourceTargetMatterDualLocalActualLift_fullDiracAdjointPaired
    (space : StageNineSpatialPoint)
    (point : BasePoint) :
    FullDiracAdjointPaired
      ((sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        space).matter point)
      ((sourceActionGeneratedMatterDualLocalActualLift
        positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState
        space).conjugateMatter point) :=
  sourceActionGeneratedMatterDualLocalActualLift_fullDiracAdjointPaired_of_jet
    positiveSourceTargetMatterCauchyState space
    (positiveSourceTargetMatterCauchyState_fullDiracAdjointPaired space)
    (positiveSourceTargetMatterCauchyState_localJetPaired space) point

end
end StageNineFullDiracAdjointPreservation
end SaturationMonoid.PhysicsCore
