import H0mework.Realization.JointState.ActionOccurrence
import H0mework.Arithmetic.RiemannGraph.IntegralGraphCharacterReadback
import H0mework.Arithmetic.RiemannGraph.IntegralGraphCouplingResidual
import H0mework.Arithmetic.RiemannGraph.JointStateModuleQRichReadback

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

open Character
open Character.GlobalCoPoissonCurrent
open SourceGeneratedIntegralCharacterGroupRing
open SourceGeneratedIntegralCoherentJointAction
open ThetaJRoleRepresentation

noncomputable section

/-- The graph character is the measurement face of the same integral graph
orbit used by the coherent read. -/
def selectedGraphMeasurementRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  ((WithLp.sndₗ 2 ℂ PositiveMellinQuarterEnergy ℂ).restrictScalars ℤ).comp
    (selectedIntegralGraphOrbit observation nontrivial)

/-- The selected A1c graph occurrence as one integral/coherent/measurement
joint action.  No covariance or vanishing law is supplied as input. -/
def selectedJointInput
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    SourceGeneratedIntegralCoherentJointAction.Input
      IntegralScaleCarrier JointGraphTarget ℂ where
  integralAction := (leftTranslation scale).toLinearMap
  coherentAction :=
    (ownerFreeGraphProductAction scale).toLinearMap.restrictScalars ℤ
  measurementAction := LinearMap.id
  coherentRead := selectedIntegralGraphOrbit observation nontrivial
  measurementRead := selectedGraphMeasurementRead observation nontrivial

/-- All three A1c faces are projections of one generated action `Ω`. -/
theorem selected_jointOmega_faces
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    let input := selectedJointInput observation nontrivial scale
    input.integralFace.comp input.omega =
        input.integralAction.comp input.integralFace ∧
      input.coherentFace.comp input.omega =
          input.coherentAction.comp input.coherentFace ∧
        input.measurementFace.comp input.omega =
          input.measurementAction.comp input.measurementFace := by
  dsimp only
  exact ⟨Input.integralFace_omega _, Input.coherentFace_omega _,
    Input.measurementFace_omega _⟩

/-- The coherent face of the generated joint incidence residual is literally
the already installed owner-free graph coupling residual. -/
theorem selected_incidence_coherent_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    let input := selectedJointInput observation nontrivial scale
    input.coherentFace (input.incidenceResidual event) =
      selectedOwnerFreeCouplingResidual observation nontrivial scale event := by
  rfl

/-- The measurement face is the detector coordinate of that same residual,
not a separately compared scalar. -/
theorem selected_incidence_measurement_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    let input := selectedJointInput observation nontrivial scale
    input.measurementFace (input.incidenceResidual event) =
      (selectedOwnerFreeCouplingResidual
        observation nontrivial scale event).snd := by
  rfl

theorem selected_incidence_measurement_delta
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (left right : Units NNReal) :
    let input := selectedJointInput observation nontrivial left
    input.measurementFace (input.incidenceResidual (delta right)) =
      quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare right) -
        quarterDilationCharacter
          (selectedCoPoissonMuntzParameter observation)
          (scaleSquare (left * right)) := by
  dsimp only
  rw [selected_incidence_measurement_readback]
  exact selectedOwnerFreeCouplingResidual_delta_snd
    observation nontrivial left right

theorem selected_measurement_is_graph_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (selectedJointInput observation nontrivial scale).measurementRead
        (delta scale) =
      quarterDilationCharacter
        (selectedCoPoissonMuntzParameter observation)
        (scaleSquare scale) := by
  change
    (selectedIntegralGraphOrbit observation nontrivial (delta scale)).snd = _
  rw [selectedIntegralGraphOrbit_delta, selectedGraphOrbitBasis_snd]

theorem selected_normalized_measurement_reads_existing_character
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
        (selectedJointInput observation nontrivial scale).measurementRead
          (delta scale) =
      selectedGraphCharacterEvaluation observation nontrivial (delta scale) := by
  rw [selectedGraphCharacterEvaluation_delta,
    selected_measurement_is_graph_character]
  unfold selectedGraphCharacterBasisReadback
  rw [selectedGraphOrbitBasis_snd]

def reversalGraphMeasurementRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] ℂ :=
  ((WithLp.sndₗ 2 ℂ PositiveMellinQuarterEnergy ℂ).restrictScalars ℤ).comp
    (reversalIntegralGraphOrbit observation nontrivial)

/-- The two raw graph measurements are sibling projections of the same
zero-owned joint integral orbit. -/
def pairedGraphMeasurementRead
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    IntegralScaleCarrier →ₗ[ℤ] QRich.ClozelJPair :=
  (selectedGraphMeasurementRead observation nontrivial).prod
    (reversalGraphMeasurementRead observation nontrivial)

@[simp] theorem pairedGraphMeasurementRead_eq_jointOrbit
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (event : IntegralScaleCarrier) :
    pairedGraphMeasurementRead observation nontrivial event =
      (((zeroOwnedJointIntegralGraphOrbit
          observation nontrivial event).1).snd,
        ((zeroOwnedJointIntegralGraphOrbit
          observation nontrivial event).2).snd) := by
  rfl

def pairedOwnerFreeGraphAction (scale : Units NNReal) :
    (JointGraphTarget × JointGraphTarget) →ₗ[ℤ]
      JointGraphTarget × JointGraphTarget :=
  let action :=
    (ownerFreeGraphProductAction scale).toLinearMap.restrictScalars ℤ
  action.prodMap action

/-- Selected and reversal are one paired action occurrence, not two inputs
later identified by a scalar comparison. -/
def pairedJointInput
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    SourceGeneratedIntegralCoherentJointAction.Input
      IntegralScaleCarrier (JointGraphTarget × JointGraphTarget)
        QRich.ClozelJPair where
  integralAction := (leftTranslation scale).toLinearMap
  coherentAction := pairedOwnerFreeGraphAction scale
  measurementAction := LinearMap.id
  coherentRead := zeroOwnedJointIntegralGraphOrbit observation nontrivial
  measurementRead := pairedGraphMeasurementRead observation nontrivial

theorem paired_jointOmega_faces
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    let input := pairedJointInput observation nontrivial scale
    input.integralFace.comp input.omega =
        input.integralAction.comp input.integralFace ∧
      input.coherentFace.comp input.omega =
          input.coherentAction.comp input.coherentFace ∧
        input.measurementFace.comp input.omega =
          input.measurementAction.comp input.measurementFace := by
  dsimp only
  exact ⟨Input.integralFace_omega _, Input.coherentFace_omega _,
    Input.measurementFace_omega _⟩

theorem paired_incidence_coherent_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    let input := pairedJointInput observation nontrivial scale
    input.coherentFace (input.incidenceResidual event) =
      (selectedOwnerFreeCouplingResidual
          observation nontrivial scale event,
        reversalOwnerFreeCouplingResidual
          observation nontrivial scale event) := by
  rfl

/-- The q-rich pair face retains both existing detector residuals without a
zero-fibre assumption. -/
theorem paired_incidence_measurement_readback
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    let input := pairedJointInput observation nontrivial scale
    input.measurementFace (input.incidenceResidual event) =
      ((selectedOwnerFreeCouplingResidual
          observation nontrivial scale event).snd,
        (reversalOwnerFreeCouplingResidual
          observation nontrivial scale event).snd) := by
  rfl

theorem paired_incidence_zmodTwo_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    let input := pairedJointInput observation nontrivial scale
    QRich.clozelJPairToZModTwo
        (input.measurementFace (input.incidenceResidual event)) 0 =
      (selectedOwnerFreeCouplingResidual
        observation nontrivial scale event).snd := by
  dsimp only
  rw [paired_incidence_measurement_readback]
  rfl

theorem paired_incidence_zmodTwo_one
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) (event : IntegralScaleCarrier) :
    let input := pairedJointInput observation nontrivial scale
    QRich.clozelJPairToZModTwo
        (input.measurementFace (input.incidenceResidual event)) 1 =
      (reversalOwnerFreeCouplingResidual
        observation nontrivial scale event).snd := by
  dsimp only
  rw [paired_incidence_measurement_readback]
  rfl

/-- Density normalization of the raw paired measurement is the already
installed joint-state q-rich pair evaluation on each integral basis event. -/
theorem paired_normalized_measurement_reads_jointStateModulePair
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (scale : Units NNReal) :
    (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ •
        (pairedJointInput observation nontrivial scale).measurementRead
          (delta scale) =
      jointStateModulePairEvaluation observation nontrivial (delta scale) := by
  apply Prod.ext
  · change
      (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
          (selectedIntegralGraphOrbit
            observation nontrivial (delta scale)).snd =
        jointStateModuleSelectedEvaluation
          observation nontrivial (delta scale)
    rw [jointStateModuleSelectedEvaluation_delta,
      jointStateModuleSelectedBasisReadback_eq_graph,
      selectedIntegralGraphOrbit_delta]
    rfl
  · change
      (positiveMellinQuarterDilationWeight (scaleSquare scale))⁻¹ *
          (reversalIntegralGraphOrbit
            observation nontrivial (delta scale)).snd =
        jointStateModuleReversalEvaluation
          observation nontrivial (delta scale)
    rw [jointStateModuleReversalEvaluation_delta,
      jointStateModuleReversalBasisReadback_eq_graph,
      reversalIntegralGraphOrbit_delta]
    rfl

#print axioms selected_jointOmega_faces
#print axioms selected_incidence_coherent_readback
#print axioms selected_incidence_measurement_readback
#print axioms selected_incidence_measurement_delta
#print axioms selected_normalized_measurement_reads_existing_character
#print axioms paired_jointOmega_faces
#print axioms paired_incidence_coherent_readback
#print axioms paired_incidence_measurement_readback
#print axioms paired_incidence_zmodTwo_zero
#print axioms paired_incidence_zmodTwo_one
#print axioms paired_normalized_measurement_reads_jointStateModulePair

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
