import H0mework.Physics.QuantumFoundation.RuntimeOccurrence

/-! Source, classical and quantum inventory entries factor through the one
post-DEF occurrence and its complete ledger. This is the original runtime's
activation, including the following inquiry's actual consumption. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9G.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

def SourceCompilation : Prop :=
  let state := (Stage9DEF.Runtime.quantumPresentation 6).state.base
  let face := state.compilationFaceAt PUnit.unit
  HEq
    (state.root.toAuthoritativeRoot.source.projectionLaw.project
      face.projection event.occurrence face.active)
    (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := state.entryAt PUnit.unit) (query := PUnit.unit)
      (event := state.emitInquiry PUnit.unit)
      (audit := (state.compileInquiry PUnit.unit).audit)
      (state.compileInquiry PUnit.unit).answerReadout)

structure SameOccurrenceActivation : Prop where
  compilation : SourceCompilation
  occurrence : SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    visit = event
  ingress : (physicalInquiryRuntime.stateAt 13).engine.node.erase =
    (Stage9DEF.Runtime.quantumPresentation 6).erase
  standing : Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt
    SpinPair.livingRoot visit entry)
  wholeLedger : HEq event.wholeLedgerWriteBack
    (SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current)
  sourceInstalled : SpinPair.authoritativeRoot.projectionOutcomeAt (.inherited .source) visit.current =
    .inl ⟨PUnit.unit, source⟩
  classicalInstalled :
    SpinPair.authoritativeRoot.projectionOutcomeAt (.inherited .configuration) visit.current =
      .inl ⟨PUnit.unit, configuration⟩
  quantumInstalled : SpinPair.authoritativeRoot.projectionOutcomeAt .quantumField visit.current =
    .inl ⟨PUnit.unit, tick.answer⟩
  directlyConsumed : tick.resolution =
    .directlyAnswered quantumFace (Stage9DEF.Runtime.quantumConsumer 7)
  classicalQuantum : tick.answer = Stage9DEF.Source.restrict configuration
  generatedNext : tick.next.node.erase = (Stage9DEF.Runtime.quantumPresentation 7).erase
  nextConsumed : nextTick.resolution =
    .directlyAnswered (Stage9DEF.Runtime.quantumFace 8) (Stage9DEF.Runtime.quantumConsumer 8)
  nextField : ∀ point displacement, nextTick.answer (point + displacement) =
    Matrix.mulVec (Stage9DEF.Dynamics.unitary displacement).val (tick.answer point)
  followingNext : nextTick.next.node.erase = (Stage9DEF.Runtime.quantumPresentation 8).erase

theorem sameOccurrenceActivation : SameOccurrenceActivation := by
  have compiled :=
    (Stage9DEF.Runtime.quantumPresentation 6).state.generatedCompilation_factorizes PUnit.unit
  exact
    { compilation := compiled.1
      occurrence := compiled.2
      ingress := Stage9CU.History.runtime_suffix 6
      standing := ⟨SpinPair.authorityAt 7⟩
      wholeLedger := event.wholeLedgerWriteBack_eq
      sourceInstalled := rfl
      classicalInstalled := rfl
      quantumInstalled := rfl
      directlyConsumed := tick_resolution
      classicalQuantum := rfl
      generatedNext := tick_next
      nextConsumed := nextTick_resolution
      nextField := next_quantum_from_current
      followingNext := nextTick_next }

end
end SaturationMonoid.PhysicsCore.Stage9G.Runtime
