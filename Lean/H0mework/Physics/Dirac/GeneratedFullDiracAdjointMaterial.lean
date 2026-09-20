import H0mework.Physics.Dirac.GeneratedMatterSpinActionUpdate
import H0mework.Physics.Dirac.FullDiracAdjointMaterial
import H0mework.Physics.Matter.SU7ExteriorYukawaMassSpectrum

/-!
# Source-generated full Dirac-adjoint material

The fixed Stage-Eight matter occurrence already generates the primal field
and its canonical full Dirac adjoint from one source amplitude.  This is the
seed material whose preservation is owed by later action developments.
-/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore
namespace StageNineSourceGeneratedFullDiracAdjointMaterial

open ProofFreeRicherAnholonomicSource
open StageEightProofFreeSource
open StageEightSourceGeneratedMatter
open StageNineEnrichedProofFreeSource
open StageNineCanonicalCauchyState
open StageNineHolonomicField
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineSourceGeneratedMatterSpinActionUpdate
open StageNineFullDiracAdjointMaterial
open StageNineJointActionLocalActualLift
open StageNineMatterActionTimeVelocity
open StageNineConjugateMatterActionTimeVelocity
open StageNineDynamicBreakingVacuum
open StageNineP286ActionCauchySplit
open SU7ExteriorBreakingYukawa
open SU7ExteriorMatterGaugeCovariantJet
open SU7ExteriorMatterRestriction
open SU7ExteriorYukawaMassSpectrum

noncomputable section

/-- Every spatial read of the fixed source Cauchy seed is one full material. -/
theorem positiveSourceTargetMatterCauchyState_fullDiracAdjointPaired
    (space : StageNineSpatialPoint) :
    FullDiracAdjointPaired
      (positiveSourceTargetMatterCauchyState.matter space)
      (positiveSourceTargetMatterCauchyState.conjugateMatter space) := by
  unfold FullDiracAdjointPaired
  rw [show positiveSourceTargetMatterCauchyState.matter space =
      diracSpinTwoMatterProbe by
    simp [positiveSourceTargetMatterCauchyState,
      sourceTargetMatterCauchyState, sourceGeneratedMatterJet,
      sourceMatterAmplitude, positiveSmoothUnifiedSource,
      canonicalSource_physicalPhaseAmplitude]]
  rw [show positiveSourceTargetMatterCauchyState.conjugateMatter space =
      diracSpinZeroMatterCoordinate by
    simp [positiveSourceTargetMatterCauchyState,
      sourceTargetMatterCauchyState, sourceGeneratedMatterJet,
      sourceMatterAmplitude, positiveSmoothUnifiedSource,
      canonicalSource_physicalPhaseAmplitude,
      canonicalTargetRebasedConjugateMatter_eq_source]]
  exact fullCanonicalDiracAdjoint_diracSpinTwoMatterProbe.symm

/-- The first actual local write preserves the source material at its anchor. -/
theorem positiveSourceTargetMatterActual_fullDiracAdjointPaired_origin :
    FullDiracAdjointPaired
      (positiveSourceTargetMatterActual.matter 0)
      (positiveSourceTargetMatterActual.conjugateMatter 0) := by
  unfold FullDiracAdjointPaired
  rw [show positiveSourceTargetMatterActual.matter 0 =
      positiveSourceTargetMatterCauchyState.matter 0 by
    change (sourceActionGeneratedMatterLocalActualLift
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0).matter 0 = _
    exact sourceActionGeneratedMatterLocalActualLift_matter_origin _ _ _]
  rw [show positiveSourceTargetMatterActual.conjugateMatter 0 =
      positiveSourceTargetMatterCauchyState.conjugateMatter 0 by
    change (sourceActionGeneratedMatterDualLocalActualLift
      positiveSmoothUnifiedSource positiveSourceTargetMatterCauchyState 0).conjugateMatter 0 = _
    exact sourceActionGeneratedMatterDualLocalActualLift_conjugate_origin _ _ _]
  rw [positiveSourceTargetMatterCauchyState_matter,
    positiveSourceTargetMatterCauchyState_conjugate]
  exact fullCanonicalDiracAdjoint_diracSpinTwoMatterProbe.symm

private theorem positiveSourceVacuumMassMap_hyperchargeProbe_zero :
    exteriorYukawaMassMap
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
        (su7ExteriorBasis 2 hyperchargeDegreeTwoIndex) = 0 := by
  rw [positive_sourceGeneratedVacuumBase]
  have overlaps :
      ∀ output input : Fin 2,
        ¬ Disjoint hyperchargeDegreeTwoIndex.1
          (finiteGenerationScalarIndex output input).1 := by
    intro output input
    fin_cases output <;> fin_cases input <;> decide
  simp [finiteGenerationJointBreakingScalar, Fin.sum_univ_two,
    exteriorYukawaMassMap_add_breaking, finiteGenerationBreakingTensor,
    exteriorYukawaMassMap_basisPair_of_not_disjoint, overlaps]

/-- The fixed source vacuum annihilates its occupied matter probe. -/
theorem positiveSourceVacuum_chiralYukawa_spinTwo_zero :
    chiralExteriorYukawaAction
        (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
        diracSpinTwoMatterProbe = 0 := by
  unfold chiralExteriorYukawaAction
  simp only [LinearMap.comp_apply]
  have projector :
      diracMatrixMatterAction rightChiralityProjector
          diracSpinTwoMatterProbe = diracSpinTwoMatterProbe := by
    funext spin
    fin_cases spin <;>
      simp [diracMatrixMatterAction, rightChiralityProjector,
        diracGammaFive, Fin.sum_univ_four, diracSpinTwoMatterProbe]
    all_goals norm_num
  rw [projector]
  have internalZero :
      diracExteriorYukawaInternalAction
          (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
          diracSpinTwoMatterProbe = 0 := by
    funext spin
    fin_cases spin
    · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
        exteriorYukawaInternalAction, diracSpinTwoMatterProbe]
    · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
        exteriorYukawaInternalAction, diracSpinTwoMatterProbe]
    · change
        exteriorYukawaInternalAction
            (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
            p286HyperchargeMatterProbe = 0
      apply Prod.ext
      · exact positiveSourceVacuumMassMap_hyperchargeProbe_zero
      · rfl
    · simp [diracExteriorYukawaInternalAction, internalMatterLinearAction,
        exteriorYukawaInternalAction, diracSpinTwoMatterProbe]
  rw [internalZero]
  simp

private theorem positiveSourceTargetMatterKnownVector_zero
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterKnownVector
      positiveSourceTargetMatterCauchyState space = 0 := by
  have scalar_eq :
      scalarCoordinateEquiv.symm
          (positiveSourceTargetMatterCauchyState.scalar space) =
        sourceGeneratedVacuumBase positiveSmoothUnifiedSource := by
    simp [positiveSourceTargetMatterCauchyState,
      sourceTargetMatterCauchyState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm, sourceGeneratedVacuumCoordinates]
  have matter_eq :
      positiveSourceTargetMatterCauchyState.matter space =
        diracSpinTwoMatterProbe := by
    simp [positiveSourceTargetMatterCauchyState,
      sourceTargetMatterCauchyState, sourceGeneratedMatterJet,
      sourceMatterAmplitude, positiveSmoothUnifiedSource,
      canonicalSource_physicalPhaseAmplitude]
  unfold actionGeneratedMatterKnownVector
  rw [scalar_eq, matter_eq, positiveSourceVacuum_chiralYukawa_spinTwo_zero]
  simp [cauchyMatterSpatialCovariantDerivative,
    cauchyMatterSpatialDerivativeCoordinate, cauchyMatterConnectionAction,
    positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm]

/-- The fixed source probe has zero generated primal time velocity. -/
theorem positiveSourceTargetMatterRawTimeVelocity_zero
    (space : StageNineSpatialPoint) :
    actionGeneratedMatterRawTimeVelocity
      positiveSourceTargetMatterCauchyState space = 0 := by
  have connectionZero :
      cauchyMatterConnectionAction positiveSourceTargetMatterCauchyState
        space canonicalLorentzianTimeDirection = 0 := by
    simp [cauchyMatterConnectionAction,
      positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
      positivePhaseProbeCauchyState_eq_normalForm,
      positiveProbeCauchyStateNormalForm]
  unfold actionGeneratedMatterRawTimeVelocity
    actionGeneratedMatterTimeCovariantDerivative
  rw [positiveSourceTargetMatterKnownVector_zero, connectionZero]
  simp [identityCoframeMatterTimePrincipal]

/-- The same source generates a zero adjoint time derivative. -/
theorem positiveSourceTargetConjugateMatterTimeDerivative_zero
    (space : StageNineSpatialPoint) :
    actionGeneratedConjugateMatterTimeDerivative
      positiveSourceTargetMatterCauchyState space = 0 := by
  apply LinearMap.ext
  intro candidate
  simp [actionGeneratedConjugateMatterTimeDerivative,
    actionGeneratedConjugateMatterKnownDual,
    actionGeneratedConjugateMatterSpatialTransport,
    actionGeneratedMatterAlgebraicOperator,
    cauchyConjugateMatterSpatialDerivative,
    cauchyConjugateMatterSpatialDerivativeCoordinate,
    cauchyMatterVariationConnectionOperator,
    identityCoframeMatterPrincipal,
    positiveSourceTargetMatterCauchyState, sourceTargetMatterCauchyState,
    sourceGeneratedMatterJet, sourceMatterAmplitude,
    positiveSmoothUnifiedSource, canonicalSource_physicalPhaseAmplitude,
    canonicalTargetRebasedConjugateMatter_eq_source,
    positivePhaseProbeCauchyState_eq_normalForm,
    positiveProbeCauchyStateNormalForm,
    diracSpinZeroMatterCoordinate_chiralExteriorYukawaAction_eq_zero]

end
end StageNineSourceGeneratedFullDiracAdjointMaterial
end SaturationMonoid.PhysicsCore
