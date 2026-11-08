import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlServiceConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryServiceWindow

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryControlSource
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code) (allowance : Nat)

abbrev Stages := List (EventHistory.Stage (code := model.source.code))
def advance (past : Stages model) :=
  (InterferenceEnvelope.choices start past allowance).map fun move =>
    past ++ [(InquiryServiceWindow.rule model start past,EventStep.fixed move)]

def cases (past : Stages model) : Nat → List (Stages model) :=
  Nat.rec [past] (fun _ domain => domain.flatMap (advance model start allowance))

abbrev Command (past : Stages model) :=
  { move : Move model.source.code // move ∈ InterferenceEnvelope.choices start past allowance }

def firstCommand (past : Stages model) : Command model start allowance past :=
  ⟨(InterferenceEnvelope.choices start past allowance).head
      (InterferenceEnvelope.the_generated_domain_is_nonempty start past allowance),
    List.head_mem (InterferenceEnvelope.the_generated_domain_is_nonempty start past allowance)⟩

def actual (choose : Nat → (past : Stages model) → Command model start allowance past)
    (past : Stages model) (count : Nat) : Stages model :=
  Nat.rec past (fun index previous => previous ++
    [(InquiryServiceWindow.rule model start previous,EventStep.fixed (choose index previous).val)]) count

theorem every_actual_adaptive_source_selection_is_in_the_original_generated_domain
    (choose : Nat → (past : Stages model) → Command model start allowance past)
    (past : Stages model) (count : Nat) :
    actual model start allowance choose past count ∈ cases model start allowance past count := by
  induction count with
  | zero => exact List.mem_singleton_self _
  | succ count ih =>
    exact List.mem_flatMap.mpr ⟨_,ih,List.mem_map.mpr
      ⟨(choose count _).val,(choose count _).property,rfl⟩⟩

theorem every_generated_domain_has_an_actual_branch (past : Stages model) (count : Nat) :
    ∃ branch, branch ∈ cases model start allowance past count := by
  induction count with
  | zero => exact ⟨past,List.mem_singleton_self _⟩
  | succ count ih =>
    obtain ⟨branch,member⟩ := ih
    obtain ⟨move,allowed⟩ := List.exists_mem_of_ne_nil _
      (InterferenceEnvelope.the_generated_domain_is_nonempty start branch allowance)
    exact ⟨branch ++ [(InquiryServiceWindow.rule model start branch,EventStep.fixed move)],
      List.mem_flatMap.mpr ⟨branch,member,List.mem_map.mpr ⟨move,allowed,rfl⟩⟩⟩

theorem generated_branches_keep_the_original_prefix_and_pay_each_control_stage
    (past branch : Stages model) (count : Nat) (inside : branch ∈ cases model start allowance past count) :
    past <+: branch ∧ branch.length = past.length + count := by
  have retained : past <+: branch := by
    induction count generalizing branch with
    | zero => cases List.mem_singleton.mp inside; exact List.prefix_refl _
    | succ count ih =>
      obtain ⟨before,member,next⟩ := List.mem_flatMap.mp inside
      obtain ⟨move,_,same⟩ := List.mem_map.mp next
      rw [← same]
      exact (ih before member).trans (List.prefix_append _ _)
  refine ⟨retained,?_⟩
  clear retained
  induction count generalizing branch with
  | zero => cases List.mem_singleton.mp inside; omega
  | succ count ih =>
    obtain ⟨before,member,next⟩ := List.mem_flatMap.mp inside
    obtain ⟨move,_,same⟩ := List.mem_map.mp next
    rw [← same,List.length_append,List.length_singleton,ih before member]
    omega

theorem each_owned_step_regenerates_its_original_local_inquiry
    (past : Stages model) (worker : Fin model.source.code.sites)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length = some worker) :
    InquiryServiceWindow.rule model start past = WithdrawalInquiry.protocol model start (past.map Prod.fst) worker :=
  InquiryServiceWindow.every_owned_cut_uses_its_own_fresh_local_inquiry model start past worker owned

theorem primitive_local_information_generates_this_actual_owned_pair
    (past : Stages model) (worker : Fin model.source.code.sites)
    (uniform : ∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker
      (InquiryServiceSource.signal model start past worker),
      WithdrawalState.request model state worker = NativeReview.action model start past worker)
    (member : model.source.code.siteParty worker ∈ Delegation.members model.scope.task)
    (capacity : 2 ≤ model.source.code.actionLimit)
    (activation : Event.activate worker ∈ model.source.code.eventAlphabet)
    (memory : model.source.code.memoryReady (InquiryServiceSource.signal model start past worker) = true)
    (supported : NativeReview.action model start past worker ∈ model.source.code.actions)
    (reaffirm : WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions)
    (live : 0 < (EventStep.seed (EventHistory.execute start past)).remaining)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (EventStep.seed (EventHistory.execute start past)).history.length = some worker)
    (external : Opponent model.source.code) :
    (StageTrace.material (EventHistory.execute start past) (InquiryServiceWindow.rule model start past) external).submitted =
      [WithdrawalInquiry.reaffirm model worker,NativeReview.action model start past worker] := by
  rw [each_owned_step_regenerates_its_original_local_inquiry model start past worker owned]
  exact InquiryServiceSource.primitive_conditions_generate_the_actual_local_pair model start past worker
    uniform member capacity activation memory supported reaffirm live owned external

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.InquiryControlSource
