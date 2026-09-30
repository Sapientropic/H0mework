import H0mework.Versions.Y.Arithmetic.PrimeLeakage.PrimePowerWeilBoundaryReadback
import H0mework.Versions.Y.Arithmetic.PoleOrbit.OrbitSource
import H0mework.Versions.Y.Arithmetic.EulerLog.ConductorCurrent
import H0mework.Versions.Y.Arithmetic.RiemannGraph.RuntimeMuntzSourceCurrentGraph
import H0mework.Versions.Y.Arithmetic.RiemannGraph.SourceCharacterJointAction
import H0mework.Versions.Y.Arithmetic.SonineCoupling.ModifiedWeakFEPoleSourceEnergy

/-!
# Occurrence-sensitive all-place Weil runtime material

The exact lower runtime occurrence is paired, before emission, with the
zero-owned Euler--Müntz source, its current-stage source-character graph
action, and the already generated joint whole roles.  They are one dependent
projection payload, not sibling values compared after emission.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlace
namespace WeilQuadratic
namespace Runtime
namespace Material

open CanonicalUnitArithmeticRoot
open Character.GlobalCoPoissonCurrent
open Character.IntegralCharacterGroupRing
open ClozelGeneralizedDual
open ClozelGeneralizedDual.CenteredGram
open ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
open ClozelGeneralizedDual.ThetaJRoleRepresentation
open AllPlaceOriginDefect.Orbit
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog
open NoIslandNoMagic.CanonicalArithmeticState.AllPlaceEulerLog.Conductor
open MuntzGraph
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Source
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Occurrence

noncomputable section

abbrev JointRuntimeOccurrenceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (current : Current) :=
  (runtimeJointFaithfulAuthoritySource observation nontrivial
    ).restructuringSource.source.toRootSource.actual.OccurrenceAt current

structure GeneratedRuntimeAllPlaceWeilFaceAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : JointRuntimeOccurrenceAt observation nontrivial current) where
  private mk ::
  exactOccurrence : JointRuntimeOccurrenceAt
    observation nontrivial current
  stage : Nat
  eulerCoefficients : ArithmeticFunction ℝ
  eulerConductorCurrent : ArithmeticFunction ℝ
  muntzSourceCurrentGraph :
    GeneratedRuntimeMuntzSourceCurrentGraphAt observation nontrivial
  selectedCharacterEvaluation : IntegralScaleCarrier →ₗ[ℤ] ℂ
  reversalCharacterEvaluation : IntegralScaleCarrier →ₗ[ℤ] ℂ
  sourceCharacterJointInput :
    SourceGeneratedIntegralCoherentJointAction.Input
      IntegralScaleCarrier (JointGraphTarget × JointGraphTarget)
        QRich.ClozelJPair
  selectedPoleAllPlaceOrbit :
    AllPlaceOriginOrbitJointCarrier
      (selectedCoPoissonMuntzParameter observation)
  reversalPoleAllPlaceOrbit :
    AllPlaceOriginOrbitJointCarrier
      (reversalCoPoissonMuntzParameter observation)
  selectedPoleSourceEnergy : PositiveMellinQuarterEnergy
  reversalPoleSourceEnergy : PositiveMellinQuarterEnergy
  sourceBoundaryWhole : PairedOmegaJointRelationCarrier
  quarterSourceBoundaryWhole : PairedOmegaJointRelationCarrier
  quarterBoundaryEnergy : PairedOmegaJointRelationCarrier
  quarterBoundaryRemainder : PairedOmegaJointRelationCarrier
  phaseWhole : PairedOmegaJointRelationCarrier
  retained : PairedOmegaJointRelationCarrier
  centeredTrace : PairedOmegaJointRelationCarrier
  exactOccurrence_eq : exactOccurrence = occurrence
  stage_eq : stage = currentEffectStage current
  eulerCoefficients_eq : eulerCoefficients =
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.eulerFace.coefficients
  eulerConductorCurrent_eq : eulerConductorCurrent =
    generatedEulerConductorCurrent
      (jointStateAnalyticOwner
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root.1)
  muntzSourceCurrentGraph_eq : muntzSourceCurrentGraph =
    generateRuntimeMuntzSourceCurrentGraph observation nontrivial
  selectedCharacterEvaluation_eq : selectedCharacterEvaluation =
    selectedGraphCharacterEvaluationFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root.1
  reversalCharacterEvaluation_eq : reversalCharacterEvaluation =
    reversalGraphCharacterEvaluationFromSource
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root.1
  sourceCharacterJointInput_eq : sourceCharacterJointInput =
    pairedSourceJointInput observation nontrivial
      (stageSqrtScaleUnit stage)
  selectedPoleAllPlaceOrbit_eq : selectedPoleAllPlaceOrbit =
    selectedAllPlacePoleOrbitJointValue observation nontrivial
  reversalPoleAllPlaceOrbit_eq : reversalPoleAllPlaceOrbit =
    reversalAllPlacePoleOrbitJointValue observation nontrivial
  selectedPoleSourceEnergy_eq : selectedPoleSourceEnergy =
    positiveMellinQuarterEnergyTranslationIsometry
      (Real.log (scaleSquare (stageSqrtScaleUnit stage)))
      (quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation)
        selectedPoleAllPlaceOrbit.1)
  reversalPoleSourceEnergy_eq : reversalPoleSourceEnergy =
    positiveMellinQuarterEnergyTranslationIsometry
      (Real.log (scaleSquare (stageSqrtScaleUnit stage)))
      (quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation)
        reversalPoleAllPlaceOrbit.1)
  sourceBoundaryWhole_eq : sourceBoundaryWhole =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .sourceBoundary)
  quarterSourceBoundaryWhole_eq : quarterSourceBoundaryWhole =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .quarterSourceBoundary)
  quarterBoundaryEnergy_eq : quarterBoundaryEnergy =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .quarterBoundaryEnergy)
  quarterBoundaryRemainder_eq : quarterBoundaryRemainder =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .quarterBoundaryRemainder)
  phaseWhole_eq : phaseWhole =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .phase)
  retained_eq : retained =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .retained)
  centeredTrace_eq : centeredTrace =
    runtimeJointRelationGeneratorValue observation nontrivial
      (stage, .centeredTrace)

def generateRuntimeAllPlaceWeilFace
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : JointRuntimeOccurrenceAt observation nontrivial current) :
    GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence :=
  let stage := currentEffectStage current
  { exactOccurrence := occurrence
    stage := stage
    eulerCoefficients :=
      (zeroOwnedAllPrimeWeilQuadraticOccurrence
        observation nontrivial).root.2.eulerFace.coefficients
    eulerConductorCurrent :=
      generatedEulerConductorCurrent
        (jointStateAnalyticOwner
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root.1)
    muntzSourceCurrentGraph :=
      generateRuntimeMuntzSourceCurrentGraph observation nontrivial
    selectedCharacterEvaluation :=
      selectedGraphCharacterEvaluationFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root.1
    reversalCharacterEvaluation :=
      reversalGraphCharacterEvaluationFromSource
        (zeroOwnedAllPrimeWeilQuadraticOccurrence
          observation nontrivial).root.1
    sourceCharacterJointInput :=
      pairedSourceJointInput observation nontrivial
        (stageSqrtScaleUnit stage)
    selectedPoleAllPlaceOrbit :=
      selectedAllPlacePoleOrbitJointValue observation nontrivial
    reversalPoleAllPlaceOrbit :=
      reversalAllPlacePoleOrbitJointValue observation nontrivial
    selectedPoleSourceEnergy :=
      positiveMellinQuarterEnergyTranslationIsometry
        (Real.log (scaleSquare (stageSqrtScaleUnit stage)))
        (quarterMellinL2Feature
          (selectedCoPoissonMuntzParameter observation)
          (selectedAllPlacePoleOrbitJointValue
            observation nontrivial).1)
    reversalPoleSourceEnergy :=
      positiveMellinQuarterEnergyTranslationIsometry
        (Real.log (scaleSquare (stageSqrtScaleUnit stage)))
        (quarterMellinL2Feature
          (reversalCoPoissonMuntzParameter observation)
          (reversalAllPlacePoleOrbitJointValue
            observation nontrivial).1)
    sourceBoundaryWhole :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .sourceBoundary)
    quarterSourceBoundaryWhole :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .quarterSourceBoundary)
    quarterBoundaryEnergy :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .quarterBoundaryEnergy)
    quarterBoundaryRemainder :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .quarterBoundaryRemainder)
    phaseWhole :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .phase)
    retained :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .retained)
    centeredTrace :=
      runtimeJointRelationGeneratorValue observation nontrivial
        (stage, .centeredTrace)
    exactOccurrence_eq := rfl
    stage_eq := rfl
    eulerCoefficients_eq := rfl
    eulerConductorCurrent_eq := rfl
    muntzSourceCurrentGraph_eq := rfl
    selectedCharacterEvaluation_eq := rfl
    reversalCharacterEvaluation_eq := rfl
    sourceCharacterJointInput_eq := rfl
    selectedPoleAllPlaceOrbit_eq := rfl
    reversalPoleAllPlaceOrbit_eq := rfl
    selectedPoleSourceEnergy_eq := rfl
    reversalPoleSourceEnergy_eq := rfl
    sourceBoundaryWhole_eq := rfl
    quarterSourceBoundaryWhole_eq := rfl
    quarterBoundaryEnergy_eq := rfl
    quarterBoundaryRemainder_eq := rfl
    phaseWhole_eq := rfl
    retained_eq := rfl
    centeredTrace_eq := rfl }

theorem GeneratedRuntimeAllPlaceWeilFaceAt.sourceCharacterIncidence_eq_zero
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence)
    (event : IntegralScaleCarrier) :
    face.sourceCharacterJointInput.incidenceResidual event = 0 := by
  rw [face.sourceCharacterJointInput_eq]
  exact pairedSourceJointInput_incidenceResidual_eq_zero
    observation nontrivial _ event

theorem GeneratedRuntimeAllPlaceWeilFaceAt.poleSourceEnergies_ne_zero
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    face.selectedPoleSourceEnergy ≠ 0 ∧
      face.reversalPoleSourceEnergy ≠ 0 := by
  rw [face.selectedPoleSourceEnergy_eq, face.reversalPoleSourceEnergy_eq,
    face.selectedPoleAllPlaceOrbit_eq, face.reversalPoleAllPlaceOrbit_eq,
    selectedAllPlacePoleOrbit_fst, reversalAllPlacePoleOrbit_fst]
  exact ⟨selectedModifiedWeakFEPole_sourceEnergy_translation_ne_zero
      observation nontrivial _,
    reversalModifiedWeakFEPole_sourceEnergy_translation_ne_zero
      observation nontrivial _⟩

theorem GeneratedRuntimeAllPlaceWeilFaceAt.poleAllPlaceOriginDefects_zero
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    AllPlaceOriginDefect.Orbit.allPlaceOriginOrbitDefect
        (selectedCoPoissonMuntzParameter observation)
        face.selectedPoleAllPlaceOrbit 0 = 0 ∧
      AllPlaceOriginDefect.Orbit.allPlaceOriginOrbitDefect
        (reversalCoPoissonMuntzParameter observation)
        face.reversalPoleAllPlaceOrbit 0 = 0 := by
  rw [face.selectedPoleAllPlaceOrbit_eq,
    face.reversalPoleAllPlaceOrbit_eq]
  exact ⟨selectedAllPlacePoleOrbitDefect_zero_at_origin
      observation nontrivial,
    reversalAllPlacePoleOrbitDefect_zero_at_origin
      observation nontrivial⟩

theorem GeneratedRuntimeAllPlaceWeilFaceAt.eulerConductorCurrent_eq_coefficients
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    face.eulerConductorCurrent = face.eulerCoefficients := by
  rw [face.eulerConductorCurrent_eq, face.eulerCoefficients_eq,
    generatedEulerConductorCurrent_eq_eulerFace,
    (zeroOwnedAllPrimeWeilQuadraticOccurrence
      observation nontrivial).root.2.eulerFace_eq]

theorem GeneratedRuntimeAllPlaceWeilFaceAt.eulerConductorCurrent_eq_commutator
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    face.eulerConductorCurrent =
      ownerLogPositionCommutator
        (jointStateAnalyticOwner
          (zeroOwnedAllPrimeWeilQuadraticOccurrence
            observation nontrivial).root.1)
        (generatedOwnerDirichletInverse
          (jointStateAnalyticOwner
            (zeroOwnedAllPrimeWeilQuadraticOccurrence
              observation nontrivial).root.1)) := by
  rw [face.eulerConductorCurrent_eq]
  rfl

theorem GeneratedRuntimeAllPlaceWeilFaceAt.eulerConductorCurrent_eq_global
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    {current : Current}
    {occurrence : JointRuntimeOccurrenceAt observation nontrivial current}
    (face : GeneratedRuntimeAllPlaceWeilFaceAt
      observation nontrivial occurrence) :
    face.eulerConductorCurrent =
      globalEulerConductorOccurrence.root.2.conductorCurrent := by
  rw [face.eulerConductorCurrent_eq,
    globalEulerConductorOccurrence.root.2.conductorCurrent_eq]
  rfl

abbrev RuntimeAllPlaceWeilPayloadAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : JointRuntimeOccurrenceAt observation nontrivial current) :=
  GeneratedRuntimeAllPlaceWeilFaceAt observation nontrivial occurrence

def runtimeAllPlaceWeilProjectionLaw
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    SourceNativeProjectionLaw
      (runtimeJointFaithfulAuthoritySource observation nontrivial
        ).restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _projection {_current} _occurrence => PUnit
  InactiveAt := fun _projection {_current} _occurrence => PEmpty
  classify := fun _projection {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _projection {_current} occurrence _active =>
    RuntimeAllPlaceWeilPayloadAt observation nontrivial occurrence
  project := fun _projection {_current} occurrence _active =>
    generateRuntimeAllPlaceWeilFace observation nontrivial occurrence

@[simp] theorem runtimeAllPlaceWeilProjectionLaw_outcomeAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    {current : Current}
    (occurrence : JointRuntimeOccurrenceAt
      observation nontrivial current) :
    (runtimeAllPlaceWeilProjectionLaw observation nontrivial
      ).outcomeAt PUnit.unit occurrence =
        .inl ⟨PUnit.unit,
          generateRuntimeAllPlaceWeilFace
            observation nontrivial occurrence⟩ :=
  rfl

end
end Material
end Runtime
end WeilQuadratic
end AllPlace
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
