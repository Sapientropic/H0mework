import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.RecurringServiceTermination

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PrimitiveRecoveryPair

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (past : JointResponse.Stages model) (worker : Fin model.source.code.sites)
abbrev current := EventStep.seed (EventHistory.execute start past)
abbrev signal := (current model start past).frame.inbox worker
abbrev request := NativeReview.action model start past worker
abbrev rule := WithdrawalInquiry.protocol model start (past.map Prod.fst) worker
abbrev row := StageTrace.material (EventHistory.execute start past) (rule model start past worker) (OriginQueue.environment start)
abbrev full := past ++ [(rule model start past worker, OriginQueue.environment start)]

structure Resources : Prop where
  uniform : ∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker (signal model start past worker),
    WithdrawalState.request model state worker = request model start past worker
  member : model.source.code.siteParty worker ∈ Delegation.members model.scope.task
  capacity : 2 ≤ model.source.code.actionLimit
  activation : Event.activate worker ∈ model.source.code.eventAlphabet
  memory : model.source.code.memoryReady (signal model start past worker) = true
  requestSupported : request model start past worker ∈ model.source.code.actions
  reaffirmSupported : WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions
  live : 0 < (current model start past).remaining
  owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
    (current model start past).history.length = some worker

instance : Decidable (Resources model start past worker) :=
  decidable_of_iff
    ((∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker (signal model start past worker),
      WithdrawalState.request model state worker = request model start past worker) ∧
      model.source.code.siteParty worker ∈ Delegation.members model.scope.task ∧
      2 ≤ model.source.code.actionLimit ∧ Event.activate worker ∈ model.source.code.eventAlphabet ∧
      model.source.code.memoryReady (signal model start past worker) = true ∧
      request model start past worker ∈ model.source.code.actions ∧
      WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions ∧
      0 < (current model start past).remaining ∧
      Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
        (current model start past).history.length = some worker)
    ⟨fun h => by rcases h with ⟨a,b,c,d,e,f,g,h,i⟩; exact ⟨a,b,c,d,e,f,g,h,i⟩,
      fun h => ⟨h.uniform,h.member,h.capacity,h.activation,h.memory,h.requestSupported,h.reaffirmSupported,h.live,h.owned⟩⟩

theorem actual_primitives_generate_the_original_material
    (resources : Resources model start past worker) :
    ∃ material, NativeRecoveryMaterial.produce model start past = .ready material ∧ material.worker = worker := by
  have prepared := InquiryServiceSource.primitive_local_information_generates_the_query model start past worker
    resources.uniform resources.member (by have := resources.capacity; omega) resources.activation resources.memory resources.requestSupported
  have query : NativeRecoveryMaterial.inquiry model start past worker = .ready (request model start past worker) := prepared
  have owned : Distributed.Recall.Information.Agency.ownerAt model.source.code
      (NativeRecoveryMaterial.current model start past).ownerStart
      (EventStep.seed (NativeRecoveryMaterial.current model start past)).history.length = some worker := resources.owned
  have live : 0 < (EventStep.seed (NativeRecoveryMaterial.current model start past)).remaining := resources.live
  cases produced : NativeRecoveryMaterial.produce model start past with
  | ready material =>
    exact ⟨material, rfl, Option.some.inj (material.owned.symm.trans owned)⟩
  | blocked reason =>
    unfold NativeRecoveryMaterial.produce at produced
    split at produced
    · rename_i observed
      have impossible := observed.symm.trans owned
      cases impossible
    · rename_i selected observed
      have same := Option.some.inj (observed.symm.trans owned)
      subst selected
      simp only [dif_pos live, dif_pos resources.reaffirmSupported, dif_pos resources.capacity] at produced
      split at produced <;> simp_all

theorem a_presentation_keeps_the_same_actual_current :
    model.source.code.law.step (current model start past).current (WithdrawalInquiry.reaffirm model worker) =
      (current model start past).current :=
  model.source.code.law.presentation_preserves_material_and_claims _ _ rfl

theorem primitive_local_resources_generate_both_exact_raw_items
    (resources : Resources model start past worker) :
    StageTrace.items (row model start past worker) =
      [⟨0, (current model start past).current, WithdrawalInquiry.reaffirm model worker⟩,
       ⟨1, (current model start past).current, request model start past worker⟩] := by
  have submitted := InquiryServiceSource.primitive_conditions_generate_the_actual_local_pair model start past worker
    resources.uniform resources.member resources.capacity resources.activation resources.memory resources.requestSupported
    resources.reaffirmSupported resources.live resources.owned (OriginQueue.environment start)
  change (row model start past worker).submitted = _ at submitted
  unfold StageTrace.items
  rw [submitted]
  change model.source.code.law.rawItems (current model start past).current
    [WithdrawalInquiry.reaffirm model worker, request model start past worker] = _
  simp only [RawLaw.rawItems, RawLaw.execute, a_presentation_keeps_the_same_actual_current]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PrimitiveRecoveryPair
