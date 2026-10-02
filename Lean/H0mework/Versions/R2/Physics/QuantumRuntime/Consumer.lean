import H0mework.Versions.R2.Physics.QuantumRuntime.Transport
import H0mework.Versions.R2.Physics.QuantumState.AlgebraSourceAction
import H0mework.Versions.R2.Physics.QuantumCompatibility.Acceptance
import H0mework.Versions.R2.Physics.QuantumObservation.Prediction
import H0mework.Versions.R2.Physics.Actual.RuntimeConsumer

/-! The original macro runtime consumes quantum physics at its first
post-unlock occurrence. Compilation, full classical carrier, positive state,
source interference, physical responses and the generated next are accepted
together, without adding a result field to the source or its writer. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineEnrichedProofFreeSource StageNineCClassicalWorldAcceptance
open Stage9C.Material.SpinPair Stage9DEF.State Stage9DEF.Dynamics
open DiracExteriorMatterAction
open scoped ComplexOrder Matrix

noncomputable section

def activatedEvent :=
  SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit (SpinPair.visit 4)

/-- Exact source compilation, before its mathematical answer is consumed. -/
def CompilationAt : Prop :=
  let state := (quantumPresentation 3).state.base
  let face := state.compilationFaceAt PUnit.unit
  HEq
    (state.root.toAuthoritativeRoot.source.projectionLaw.project
      face.projection activatedEvent.occurrence face.active)
    (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := state.entryAt PUnit.unit) (query := PUnit.unit)
      (event := state.emitInquiry PUnit.unit)
      (audit := (state.compileInquiry PUnit.unit).audit)
      (state.compileInquiry PUnit.unit).answerReadout)

/-- Joint acceptance is an output of the source's installed restriction. -/
structure ActivatedQuantumClosure : Prop where
  sourceUnique : ∃! _actual : Stage9CU.Runtime.energyFace.Actual, True
  unlockNext :
    (SpinPair.livingRoot.generatedCausalEntryAnswerAndNextAt (SpinPair.visit 2)
      Stage9CU.Runtime.energyFace.entry Stage9CU.Runtime.energyFace.standing).nextCurrent =
        SpinPair.livingRoot.generatedNextCurrentAt (SpinPair.visit 2)
  postUnlock : (physicalInquiryRuntime.stateAt 10).engine.node.erase = (quantumPresentation 3).erase
  compiled : CompilationAt
  occurrence : SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (SpinPair.visit 4) = activatedEvent
  wholeLedger : HEq activatedEvent.wholeLedgerWriteBack
    (SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt (SpinPair.visit 4).current)
  installed : SpinPair.authoritativeRoot.projectionOutcomeAt .quantumField (SpinPair.visit 4).current =
    .inl ⟨PUnit.unit, firstQuantumTick.answer⟩
  physicalSource : configurationAt 3 = actual
  quantumRestriction : firstQuantumTick.answer = Source.restrict (configurationAt 3)
  classical : ClassicalWorldAcceptance positiveSmoothUnifiedSource (configurationAt 3)
  normalized : ∀ point, (∑ index, Complex.normSq (firstQuantumTick.answer point index)) = 1
  positive : ∀ point (effect : Observable), effect.PosSemidef →
    0 ≤ vectorEvaluation (firstQuantumTick.answer point) effect
  noncommuting : Algebra.colorAction 0 * Algebra.colorAction 1 ≠
    Algebra.colorAction 1 * Algebra.colorAction 0
  interference : Observation.coherentWeight 0 = 1 ∧ Observation.exclusiveWeight 0 = 1 / 2 ∧
    Observation.coherentWeight 0 ≠ Observation.exclusiveWeight 0
  interference_reads_answer :
    (vectorEvaluation (firstQuantumTick.answer 0) (sourceEffect 0).matrix).re =
      Observation.coherentWeight 0
  nextField : ∀ point displacement,
    secondQuantumTick.answer (point + displacement) =
      (unitary displacement : Observable) *ᵥ firstQuantumTick.answer point
  nextDensity : ∀ point displacement, densityAt 4 (point + displacement) =
    automorphism displacement (densityAt 3 point)
  nextProbability : ∀ point displacement (effect : Effect),
    0 ≤ (vectorEvaluation (secondQuantumTick.answer (point + displacement)) effect.matrix).re ∧
      (vectorEvaluation (secondQuantumTick.answer (point + displacement)) effect.matrix).re +
        (vectorEvaluation (secondQuantumTick.answer (point + displacement))
          effect.complement.matrix).re = 1
  sourceResponse : ∀ point (action : Module.End ℂ DiracExteriorMatterCarrier),
    actual.conjugateMatter point (action (actual.matter point)) =
      4 * (spinScale : ℂ) *
        vectorEvaluation (firstQuantumTick.answer point) (Compatibility.responseMatrix action)
  kineticResponse : ∀ point,
    Compatibility.kineticLoad point = actualKineticLoad point
  compatibility : Compatibility.PhysicalCompatibility
  physicalTime : ∀ point time,
    HasDerivAt (fun t : ℝ => firstQuantumTick.answer (point + timeDisplacement t))
      (fun index => firstQuantumTick.answer (point + timeDisplacement time) index * generator index) time
  nonstationary : ¬ (∀ time : ℝ, ∃ scalar : ℂ, star scalar * scalar = 1 ∧
    firstQuantumTick.answer (timeDisplacement time) = scalar • firstQuantumTick.answer 0)
  prediction : Observation.coherentWeight (timeDisplacement Observation.darkTime) = 0 ∧
    Observation.coherentWeight (timeDisplacement (2 * Observation.darkTime)) = 1
  prediction_reads_next :
    (vectorEvaluation (secondQuantumTick.answer (timeDisplacement Observation.darkTime))
      (sourceEffect 0).matrix).re = Observation.coherentWeight (timeDisplacement Observation.darkTime)
  generatedNext : firstQuantumTick.next.node.erase = (quantumPresentation 4).erase
  nextQueryConsumed : secondQuantumTick.resolution =
    .directlyAnswered (quantumFace 5) (quantumConsumer 5)
  subsequentNext : secondQuantumTick.next.node.erase = (quantumPresentation 5).erase

theorem activatedQuantumClosure : ActivatedQuantumClosure := by
  have compilation := (quantumPresentation 3).state.generatedCompilation_factorizes PUnit.unit
  refine
    { sourceUnique := Stage9CU.Runtime.sourceRootedUniquenessUnlock.1
      unlockNext := Stage9CU.Runtime.sourceRootedUniquenessUnlock.2.2.2
      postUnlock := Stage9CU.History.runtime_suffix 3
      compiled := compilation.1
      occurrence := compilation.2
      wholeLedger := activatedEvent.wholeLedgerWriteBack_eq
      installed := rfl
      physicalSource := configurationAt_eq_actual 3
      quantumRestriction := rfl
      classical := ?_
      normalized := ?_
      positive := ?_
      noncommuting := Algebra.colorAction_noncommuting
      interference := Observation.source_interference
      interference_reads_answer := ?_
      nextField := activated_next_reads_current
      nextDensity := next_density_from_current 3
      nextProbability := fun point displacement effect =>
        ⟨activated_weight_positive point displacement effect,
          activated_weight_normalized point displacement effect⟩
      sourceResponse := ?_
      kineticResponse := Compatibility.kineticLoad_eq_actual
      compatibility := Compatibility.physicalCompatibility
      physicalTime := ?_
      nonstationary := ?_
      prediction := ⟨Observation.prediction_dark, Observation.prediction_return⟩
      prediction_reads_next := ?_
      generatedNext := firstQuantumTick_next
      nextQueryConsumed := secondQuantumTick_resolution
      subsequentNext := secondQuantumTick_next }
  · rw [configurationAt_eq_actual]
    exact actual_classicalWorldAcceptance
  · rw [firstQuantumTick_answer, fieldAt_eq_vector]
    exact Source.vector_normSq
  · rw [firstQuantumTick_answer, fieldAt_eq_vector]
    exact evaluation_positive
  · rw [firstQuantumTick_answer, fieldAt_eq_vector]
    rfl
  · rw [firstQuantumTick_answer, fieldAt_eq_vector]
    exact Compatibility.actual_action_quantumResponse
  · rw [firstQuantumTick_answer, fieldAt_eq_vector]
    exact vector_time_hasDerivAt
  · rw [firstQuantumTick_answer, fieldAt_eq_vector]
    exact not_only_global_phase
  · rw [secondQuantumTick_answer, fieldAt_eq_vector]
    rfl

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Runtime
