import H0mework.Versions.Y.Arithmetic.CoPoisson.QuarterMellinGraphCovariance
import H0mework.Versions.Y.Arithmetic.RiemannGraph.IntegralGraphJointAction

/-!
# Source-character joint action

The source dilation already acts diagonally on the functional graph: unitary
translation on the energy coordinate and the generated Mellin character on
the measurement coordinate.  Installing that action on the integral graph
orbit makes both selected and reversal action squares strict.  The older
owner-free action, which freezes measurement to the identity, is retained as
an observer restriction; its incidence is exactly the difference between the
identity detector and this source-generated character action.

No critical-line, separator, residual-zero, bounded extension, or energy
support premise is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction

open Character.GlobalCoPoissonCurrent
open MuntzConductor.HalfPositionSource.GraphAction
open SourceGeneratedFaithfulIntegralFace
open SourceGeneratedFunctionalGraphPerfectification
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentJointAction
open ThetaJRoleRepresentation

noncomputable section

def selectedSourceGraphCovariance
    (observation : GeneratedRiemannZeroObservation)
    (_nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :=
  quarterDilationGraphCovariance
    (selectedCoPoissonMuntzParameter observation)
    (scaleSquare scale) (scaleSquare_pos scale)

def reversalSourceGraphCovariance
    (observation : GeneratedRiemannZeroObservation)
    (_nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :=
  quarterDilationGraphCovariance
    (reversalCoPoissonMuntzParameter observation)
    (scaleSquare scale) (scaleSquare_pos scale)

theorem selectedSourceGraphAction_basis
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    graphTargetAction
        (selectedSourceGraphCovariance observation nontrivial left)
        (selectedGraphOrbitBasis observation nontrivial right) =
      selectedGraphOrbitBasis observation nontrivial (left * right) := by
  unfold selectedGraphOrbitBasis selectedSourceGraphCovariance
  rw [graphTargetAction_source]
  apply congrArg (graphFeature
    (quarterMellinL2Feature (selectedCoPoissonMuntzParameter observation))
    (quarterMellinL2Functional (selectedCoPoissonMuntzParameter observation)))
  have composition := LinearMap.congr_fun
    (quarterDilationTestAction_comp
      (selectedCoPoissonMuntzParameter observation)
      (scaleSquare left) (scaleSquare right)
      (scaleSquare_pos left) (scaleSquare_pos right))
    (normalizedCoPoissonMuntzQuarterShellTest
      (selectedCoPoissonMuntzParameter observation)
      (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))
  change quarterDilationTestAction
      (selectedCoPoissonMuntzParameter observation) (scaleSquare left)
        (scaleSquare_pos left)
        (quarterDilationTestAction
          (selectedCoPoissonMuntzParameter observation) (scaleSquare right)
          (scaleSquare_pos right)
          (normalizedCoPoissonMuntzQuarterShellTest
            (selectedCoPoissonMuntzParameter observation)
            (selectedCoPoissonMuntzParameter_re_pos observation nontrivial))) = _
  simpa only [LinearMap.comp_apply, scaleSquare_mul] using composition

theorem reversalSourceGraphAction_basis
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    graphTargetAction
        (reversalSourceGraphCovariance observation nontrivial left)
        (reversalGraphOrbitBasis observation nontrivial right) =
      reversalGraphOrbitBasis observation nontrivial (left * right) := by
  unfold reversalGraphOrbitBasis reversalSourceGraphCovariance
  rw [graphTargetAction_source]
  apply congrArg (graphFeature
    (quarterMellinL2Feature (reversalCoPoissonMuntzParameter observation))
    (quarterMellinL2Functional (reversalCoPoissonMuntzParameter observation)))
  have composition := LinearMap.congr_fun
    (quarterDilationTestAction_comp
      (reversalCoPoissonMuntzParameter observation)
      (scaleSquare left) (scaleSquare right)
      (scaleSquare_pos left) (scaleSquare_pos right))
    (normalizedCoPoissonMuntzQuarterShellTest
      (reversalCoPoissonMuntzParameter observation)
      (reversalCoPoissonMuntzParameter_re_pos observation nontrivial))
  change quarterDilationTestAction
      (reversalCoPoissonMuntzParameter observation) (scaleSquare left)
        (scaleSquare_pos left)
        (quarterDilationTestAction
          (reversalCoPoissonMuntzParameter observation) (scaleSquare right)
          (scaleSquare_pos right)
          (normalizedCoPoissonMuntzQuarterShellTest
            (reversalCoPoissonMuntzParameter observation)
            (reversalCoPoissonMuntzParameter_re_pos observation nontrivial))) = _
  simpa only [LinearMap.comp_apply, scaleSquare_mul] using composition

def pairedSourceGraphAction
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (JointGraphTarget × JointGraphTarget) →ₗ[ℤ]
      (JointGraphTarget × JointGraphTarget) :=
  ((graphTargetAction
    (selectedSourceGraphCovariance observation nontrivial scale)
      ).toLinearMap.restrictScalars ℤ).prodMap
    ((graphTargetAction
      (reversalSourceGraphCovariance observation nontrivial scale)
        ).toLinearMap.restrictScalars ℤ)

def pairedSourceCharacterAction
    (observation : GeneratedRiemannZeroObservation)
    (_nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    QRich.ClozelJPair →ₗ[ℤ] QRich.ClozelJPair :=
  (complexScalarAction
      (quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation) (scaleSquare scale))).prodMap
    (complexScalarAction
      (quarterDilationCharacter
        (reversalCoPoissonMuntzParameter observation) (scaleSquare scale)))

def pairedSourceJointInput
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    SourceGeneratedIntegralCoherentJointAction.Input
      IntegralScaleCarrier (JointGraphTarget × JointGraphTarget)
        QRich.ClozelJPair where
  integralAction := (leftTranslation scale).toLinearMap
  coherentAction := pairedSourceGraphAction observation nontrivial scale
  measurementAction := pairedSourceCharacterAction observation nontrivial scale
  coherentRead := zeroOwnedJointIntegralGraphOrbit observation nontrivial
  measurementRead := pairedGraphMeasurementRead observation nontrivial

theorem pairedSourceJointInput_coherent_covariance
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (pairedSourceJointInput observation nontrivial scale).coherentAction.comp
        (pairedSourceJointInput observation nontrivial scale).coherentRead =
      (pairedSourceJointInput observation nontrivial scale).coherentRead.comp
        (pairedSourceJointInput observation nontrivial scale).integralAction := by
  apply MonoidAlgebra.lhom_ext'
  intro scale'
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale' coefficient =
      coefficient • delta scale' by simp [delta], map_smul, map_smul,
    map_smul]
  rw [map_smul]
  apply congrArg (fun value => coefficient • value)
  change pairedSourceGraphAction observation nontrivial scale
      (zeroOwnedJointIntegralGraphOrbit observation nontrivial (delta scale')) =
    zeroOwnedJointIntegralGraphOrbit observation nontrivial
      ((leftTranslation scale).toLinearMap (delta scale'))
  change pairedSourceGraphAction observation nontrivial scale
      (selectedIntegralGraphOrbit observation nontrivial (delta scale'),
        reversalIntegralGraphOrbit observation nontrivial (delta scale')) =
    (selectedIntegralGraphOrbit observation nontrivial
        ((leftTranslation scale).toLinearMap (delta scale')),
      reversalIntegralGraphOrbit observation nontrivial
        ((leftTranslation scale).toLinearMap (delta scale')))
  have translated :
      (leftTranslation scale).toLinearMap (delta scale') =
        delta (scale * scale') := leftTranslation_delta scale scale'
  rw [selectedIntegralGraphOrbit_delta, reversalIntegralGraphOrbit_delta,
    pairedSourceGraphAction]
  change
    (graphTargetAction
        (selectedSourceGraphCovariance observation nontrivial scale)
        (selectedGraphOrbitBasis observation nontrivial scale'),
      graphTargetAction
        (reversalSourceGraphCovariance observation nontrivial scale)
        (reversalGraphOrbitBasis observation nontrivial scale')) = _
  rw [selectedSourceGraphAction_basis, reversalSourceGraphAction_basis,
    translated,
    selectedIntegralGraphOrbit_delta,
    reversalIntegralGraphOrbit_delta]

theorem pairedSourceJointInput_measurement_covariance
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (pairedSourceJointInput observation nontrivial scale).measurementAction.comp
        (pairedSourceJointInput observation nontrivial scale).measurementRead =
      (pairedSourceJointInput observation nontrivial scale).measurementRead.comp
        (pairedSourceJointInput observation nontrivial scale).integralAction := by
  apply MonoidAlgebra.lhom_ext'
  intro scale'
  apply LinearMap.ext
  intro coefficient
  simp only [LinearMap.comp_apply, MonoidAlgebra.lsingle_apply]
  rw [show MonoidAlgebra.single scale' coefficient =
      coefficient • delta scale' by simp [delta], map_smul, map_smul,
    map_smul]
  rw [map_smul]
  apply congrArg (fun value => coefficient • value)
  change pairedSourceCharacterAction observation nontrivial scale
      (pairedGraphMeasurementRead observation nontrivial (delta scale')) =
    pairedGraphMeasurementRead observation nontrivial
      ((leftTranslation scale).toLinearMap (delta scale'))
  change pairedSourceCharacterAction observation nontrivial scale
      ((selectedIntegralGraphOrbit observation nontrivial (delta scale')).snd,
        (reversalIntegralGraphOrbit observation nontrivial (delta scale')).snd) =
    ((selectedIntegralGraphOrbit observation nontrivial
        ((leftTranslation scale).toLinearMap (delta scale'))).snd,
      (reversalIntegralGraphOrbit observation nontrivial
        ((leftTranslation scale).toLinearMap (delta scale'))).snd)
  have translated :
      (leftTranslation scale).toLinearMap (delta scale') =
        delta (scale * scale') := leftTranslation_delta scale scale'
  rw [selectedIntegralGraphOrbit_delta, reversalIntegralGraphOrbit_delta,
    pairedSourceCharacterAction]
  apply Prod.ext
  · change
      quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation) (scaleSquare scale) *
        (selectedGraphOrbitBasis observation nontrivial scale').snd = _
    rw [selectedGraphOrbitBasis_snd, translated,
      selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_snd,
      quarterDilationCharacter_scaleSquare_mul]
  · change
      quarterDilationCharacter
          (reversalCoPoissonMuntzParameter observation) (scaleSquare scale) *
        (reversalGraphOrbitBasis observation nontrivial scale').snd = _
    rw [reversalGraphOrbitBasis_snd, translated,
      reversalIntegralGraphOrbit_delta, reversalGraphOrbitBasis_snd,
      quarterDilationCharacter_scaleSquare_mul]

theorem pairedSourceJointInput_incidenceResidual_eq_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    (pairedSourceJointInput observation nontrivial scale).incidenceResidual event = 0 := by
  rw [Input.incidenceResidual_eq_zero_iff]
  exact ⟨LinearMap.congr_fun
      (pairedSourceJointInput_coherent_covariance observation nontrivial scale) event,
    LinearMap.congr_fun
      (pairedSourceJointInput_measurement_covariance observation nontrivial scale) event⟩

theorem ownerFreeMeasurementResidual_eq_sourceActionDefect
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    (pairedJointInput observation nontrivial scale).measurementFace
        ((pairedJointInput observation nontrivial scale).incidenceResidual event) =
      (pairedJointInput observation nontrivial scale).measurementRead event -
        (pairedSourceJointInput observation nontrivial scale).measurementAction
          ((pairedJointInput observation nontrivial scale).measurementRead event) := by
  rw [Input.incidenceResidual_measurementFace]
  have covariance := LinearMap.congr_fun
    (pairedSourceJointInput_measurement_covariance observation nontrivial scale) event
  have covariance' :
      (pairedSourceJointInput observation nontrivial scale).measurementAction
          ((pairedJointInput observation nontrivial scale).measurementRead event) =
        (pairedJointInput observation nontrivial scale).measurementRead
          ((leftTranslation scale).toLinearMap event) := by
    simpa [pairedSourceJointInput, pairedJointInput] using covariance
  change (pairedJointInput observation nontrivial scale).measurementRead event -
      (pairedJointInput observation nontrivial scale).measurementRead
        ((leftTranslation scale).toLinearMap event) = _
  rw [← covariance']

end
end IntegralGraphJointAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
