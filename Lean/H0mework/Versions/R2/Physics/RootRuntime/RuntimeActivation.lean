import H0mework.Versions.R2.Physics.RootRuntime.RuntimeOccurrence

/-! Recognition retains both the original macro history across source actions
and the exact current root's ordered patch trace. The canonical next preserves
the generated living law, not merely the erased endpoint. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Runtime

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

def SourceCompilation : Prop :=
  let state := (Stage9DEF.Runtime.quantumPresentation 9).state.base
  let face := state.compilationFaceAt PUnit.unit
  HEq
    (state.root.toAuthoritativeRoot.source.projectionLaw.project
      face.projection event.occurrence face.active)
    (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := state.entryAt PUnit.unit) (query := PUnit.unit)
      (event := state.emitInquiry PUnit.unit)
      (audit := (state.compileInquiry PUnit.unit).audit)
      (state.compileInquiry PUnit.unit).answerReadout)

def MacroNextAt (index : ℕ) : Prop :=
  let state := physicalInquiryRuntime.stateAt index
  let activated := physicalInquiryRuntime.tickAt index
  state.engine.node.PreservesGeneratedLivingLawAt state.activation.query activated.next.node

theorem allMacroNext (index : ℕ) : MacroNextAt index :=
  (physicalInquiryRuntime.tickAt index).next_preservesGeneratedLivingLaw

structure SameOccurrenceActivation : Prop where
  historicalPrefix : ∀ index : Fin 7,
    (physicalInquiryRuntime.stateAt index.val).engine.node.erase =
      (SpinPair.historicalPresentation index).erase
  nativeSuffix : ∀ index : ℕ,
    (physicalInquiryRuntime.stateAt (index + 7)).engine.node.erase =
      (SpinPair.readPresentation index).erase
  macroNext : ∀ index, MacroNextAt index
  compiled : SourceCompilation
  occurrence : SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    visit = event
  priorPatches : event.priorPatches =
    SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedTemporalPriorPatchesAt visit.history
  currentPatch : event.currentPatch =
    SpinPair.livingRoot.toAuthoritativeRoot.toLedgerRoot.generatedPatchAt visit.current
  wholeLedger : HEq event.wholeLedgerWriteBack (SpinPair.generatedEvolution event.occurrence)
  currentRow : (SpinPair.generatedRows event.occurrence).sourceEntryAt ⟨0, Nat.zero_lt_one⟩ = entry
  successorRow : (SpinPair.generatedRows event.occurrence).targetEntryAt ⟨0, Nat.zero_lt_one⟩ =
    materialEntry (SpinPair.support (SpinPair.next visit.current))
  answer : Nonempty (SourceNativeLivingCausalEntryAnswerPayloadAt
    SpinPair.livingRoot visit entry standing)
  answerNext : answerAndNext.nextCurrent = SpinPair.livingRoot.generatedNextCurrentAt visit
  macroAnswerNext : tick.next.node.erase = ⟨MaterialN, answerAndNext.nextCurrent⟩
  installed : ∀ projection : SpinPair.Projection,
    HEq (event.projectionOutcome projection)
      (SpinPair.authoritativeRoot.projectionOutcomeAt projection visit.current)
  currentConsumed : tick.resolution =
    .directlyAnswered quantumFace (Stage9DEF.Runtime.quantumConsumer 10)
  sourceRestriction : tick.answer = Stage9DEF.Source.restrict configuration
  generatedNext : tick.next.node.erase = (Stage9DEF.Runtime.quantumPresentation 10).erase
  nextConsumed : nextTick.resolution =
    .directlyAnswered (Stage9DEF.Runtime.quantumFace 11) (Stage9DEF.Runtime.quantumConsumer 11)
  nextField : ∀ point displacement, nextTick.answer (point + displacement) =
    Matrix.mulVec (Stage9DEF.Dynamics.unitary displacement).val (tick.answer point)
  followingNext : nextTick.next.node.erase = (Stage9DEF.Runtime.quantumPresentation 11).erase

theorem sameOccurrenceActivation : SameOccurrenceActivation := by
  have compilation := (Stage9DEF.Runtime.quantumPresentation 9).state
    |>.generatedCompilation_factorizes PUnit.unit
  exact
    { historicalPrefix := Stage9CU.History.runtime_prefix
      nativeSuffix := Stage9CU.History.runtime_suffix
      macroNext := allMacroNext
      compiled := compilation.1
      occurrence := compilation.2
      priorPatches := event.priorPatches_eq
      currentPatch := event.currentPatch_eq
      wholeLedger := Recognition.rawEvent_wholeLedger visit event.occurrence
      currentRow := rfl
      successorRow := rfl
      answer := ⟨answerAndNext.answer⟩
      answerNext := answerAndNext.nextCurrent_eq
      macroAnswerNext := tick.next_erases_to_generated
      installed := zeroUnregisteredPhysicalAuthorityReceipt.allAuthority visit
      currentConsumed := tick_resolution
      sourceRestriction := tick_answer
      generatedNext := tick_next
      nextConsumed := nextTick_resolution
      nextField := next_quantum_from_current
      followingNext := nextTick_next }

end
end SaturationMonoid.PhysicsCore.Stage10.Runtime
