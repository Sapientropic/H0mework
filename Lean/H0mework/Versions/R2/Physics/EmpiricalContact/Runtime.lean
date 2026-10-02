import H0mework.Versions.R2.Physics.EmpiricalContact.History

/-! Conservative continuation of the original macro process. Every historical
transition reuses that process's own successor proof; only the new contact
occurrence performs the source-generated sequential actual action. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision

noncomputable section

private def prefixNext (index : Fin 20) : RuntimeState :=
  if before : index.val + 1 < 20 then .prior ⟨index.val + 1, before⟩ else .continuation 0

def continuationProcess : SourceNativeInquiryEngineProcess where
  State := RuntimeState
  stateAt := fun state => .active (runtimePresentation state)
  erase_injective := by
    intro left right leftPresentation rightPresentation leftActive rightActive equality
    cases leftActive
    cases rightActive
    exact runtimePresentation_erase_injective equality
  initial := .prior 0
  successorAt := by
    intro state query
    cases state with
    | prior index =>
        refine ⟨prefixNext index, ?_⟩
        fin_cases index <;> cases query
        · exact (physicalInquiryProcess.successorAt (.history 0) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.history 1) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.history 2) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.history 3) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.history 4) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.history 5) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.history 6) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 0) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 1) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 2) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 3) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 4) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 5) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 6) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 7) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 8) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 9) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 10) PUnit.unit).2
        · exact (physicalInquiryProcess.successorAt (.native 11) PUnit.unit).2
        · exact RootInquiryProcessNode.active_actualAction_successor_valid
            inquiryPresentation (readPresentation 1) PUnit.unit generatedAction rfl rfl HEq.rfl
    | continuation index =>
        refine ⟨.continuation (index + 1), ?_⟩
        cases query
        exact RootInquiryProcessNode.active_directlyAnswered_successor_valid
          (readPresentation (index + 1)) (readPresentation (index + 2)) PUnit.unit
          (answerFace (index + 1)) (answerConsumer (index + 1)) rfl rfl HEq.rfl

private theorem query_type (state : RuntimeState) :
    (continuationProcess.stateAt state).Query = PUnit := by
  cases state with
  | prior index => fin_cases index <;> rfl
  | continuation => rfl

private def uniqueQuery (state : RuntimeState) : (continuationProcess.stateAt state).Query :=
  (query_type state).symm ▸ PUnit.unit

private theorem uniqueQuery_eq (state : RuntimeState)
    (query : (continuationProcess.stateAt state).Query) : query = uniqueQuery state := by
  let : Subsingleton ((continuationProcess.stateAt state).Query) := by
    rw [query_type]
    infer_instance
  exact Subsingleton.elim _ _

/-- One active continuation, retaining the original initial physical root. -/
def physicalInquiryRuntimeWithContact : SourceNativeInquiryRuntime continuationProcess where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique
    (uniqueQuery _) (uniqueQuery_eq _)
    (fun state query => uniqueQuery (continuationProcess.successorAt state query).1)
    (fun state query => uniqueQuery_eq (continuationProcess.successorAt state query).1)

theorem original_seed : physicalInquiryRuntimeWithContact.initialState.engine.node.erase =
    physicalInquiryRuntime.initialState.engine.node.erase := rfl

private theorem next_prior (engine : Engine continuationProcess)
    (activation : Engine.SourceNativeInquiryActivationAt engine) (index : Fin 19)
    (current : engine.node.erase =
      (runtimePresentation (.prior ⟨index.val, by omega⟩)).erase) :
    (engine.ask activation).next.node.erase =
      (runtimePresentation (.prior ⟨index.val + 1, by omega⟩)).erase := by
  rcases engine with ⟨state⟩
  have same : state = .prior ⟨index.val, by omega⟩ := runtimePresentation_erase_injective current
  subst state
  change (runtimePresentation (prefixNext ⟨index.val, by omega⟩)).erase = _
  rw [prefixNext, dif_pos (show index.val + 1 < 20 by omega)]

theorem prefix_position (index : Nat) (before : index < 20) :
    (physicalInquiryRuntimeWithContact.stateAt index).engine.node.erase =
      (runtimePresentation (.prior ⟨index, before⟩)).erase := by
  induction index with
  | zero => rfl
  | succ index ih =>
      change ((physicalInquiryRuntimeWithContact.stateAt index).engine.ask
        (physicalInquiryRuntimeWithContact.stateAt index).activation).next.node.erase = _
      exact next_prior _ _ ⟨index, by omega⟩ (ih (by omega))

theorem original_prefix (index : Fin 19) :
    (physicalInquiryRuntimeWithContact.stateAt index.val).engine.node.erase =
      (physicalInquiryRuntime.stateAt index.val).engine.node.erase := by
  rw [prefix_position index.val (by omega), prefix_erase]
  by_cases historical : index.val < 7
  · simpa only [priorState, dif_pos historical, SpinPair.runtimePresentation] using
      (Stage9CU.History.runtime_prefix ⟨index.val, historical⟩).symm
  · have original := Stage9CU.History.runtime_suffix (index.val - 7)
    rw [Nat.sub_add_cancel (show 7 ≤ index.val by omega)] at original
    simpa only [priorState, dif_neg historical] using
      (SpinPair.runtimePresentation_native_erase (index.val - 7)).trans original.symm

private theorem same_prefix_compilation (newEngine : Engine continuationProcess)
    (newActivation : Engine.SourceNativeInquiryActivationAt newEngine)
    (oldEngine : Engine physicalInquiryProcess)
    (oldActivation : Engine.SourceNativeInquiryActivationAt oldEngine) (index : Fin 19)
    (newCurrent : newEngine.node.erase =
      (runtimePresentation (.prior ⟨index.val, by omega⟩)).erase)
    (oldCurrent : oldEngine.node.erase =
      (SpinPair.runtimePresentation (priorState ⟨index.val, by omega⟩)).erase) :
    HEq (newEngine.ask newActivation).resolution (oldEngine.ask oldActivation).resolution ∧
    RootInquiryProcessNode.resolutionKind (node := newEngine.node)
      (newEngine.ask newActivation).resolution =
    RootInquiryProcessNode.resolutionKind (node := oldEngine.node)
      (oldEngine.ask oldActivation).resolution := by
  rcases newEngine with ⟨newState⟩
  rcases oldEngine with ⟨oldState⟩
  have newSame : newState = .prior ⟨index.val, by omega⟩ := runtimePresentation_erase_injective newCurrent
  have oldSame : oldState = priorState ⟨index.val, by omega⟩ :=
    SpinPair.runtimePresentation_erase_injective oldCurrent
  subst newState
  subst oldState
  rcases newActivation with ⟨newQuery⟩
  rcases oldActivation with ⟨oldQuery⟩
  fin_cases index <;> cases newQuery <;> cases oldQuery <;> constructor <;> rfl

theorem original_prefix_compilation (index : Fin 19) :
    HEq (physicalInquiryRuntimeWithContact.tickAt index.val).resolution
      (physicalInquiryRuntime.tickAt index.val).resolution := by
  exact (same_prefix_compilation _ _ _ _ index (prefix_position index.val (by omega))
    ((original_prefix index).symm.trans
      ((prefix_position index.val (by omega)).trans (prefix_erase _)))).1

theorem original_prefix_resolution (index : Fin 19) :
    (physicalInquiryRuntimeWithContact.tickAt index.val).resolutionKind =
      (physicalInquiryRuntime.tickAt index.val).resolutionKind := by
  exact (same_prefix_compilation _ _ _ _ index (prefix_position index.val (by omega))
    ((original_prefix index).symm.trans
      ((prefix_position index.val (by omega)).trans (prefix_erase _)))).2

theorem contact_resolution : (physicalInquiryRuntimeWithContact.tickAt 19).resolution =
    .actualAction generatedAction := rfl

theorem contact_installed : SourceNativeInquiryRuntime.SequentialActualActionResumptionAt
    generatedAction physicalInquiryRuntimeWithContact 19 where
  contains_action := by rw [contact_resolution]; exact HEq.rfl

theorem contact_next : (physicalInquiryRuntimeWithContact.tickAt 19).next.node.erase =
    (readPresentation 1).erase := rfl

theorem next_consumes_demand : (physicalInquiryRuntimeWithContact.tickAt 20).resolution =
    .directlyAnswered (answerFace 1) (answerConsumer 1) := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
