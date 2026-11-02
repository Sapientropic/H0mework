import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.History

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Provision
open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (base : Code Party Good Port (Mandate.State Party Technology) Instrument)

abbrev capacity (budget : Nat) := base.eventLimit + budget
abbrev code (budget : Nat) := lift base (capacity base budget)

/-- Recover the old local machine's state from this site's actual notices. -/
def state (site : Fin base.sites) (history : List (Notice base)) : Fin base.signals :=
  history.foldl (fun prior observed => match observed with
    | .sent recipient signal => base.afterSend site recipient prior signal
    | .received sender signal => base.afterDelivery site sender prior signal
    | .attempted word => base.afterAction site prior word) base.initialSignal

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem action_supported (policy : base.Policy) (generated : policy ∈ base.policies)
    (site : Fin base.sites) (signal : Fin base.signals) :
    base.action policy site signal ∈ words base.actions base.actionLimit := by
  unfold Code.action
  split
  · exact (List.mem_pi _ _).mp generated (site,signal) (base.key_mem _)
  · exact (mem_words_iff _ _ _).mpr (by simp)

def policy (budget : Nat) (original : base.Policy) : (code base budget).Policy :=
  Recall.tabulate base (capacity base budget) (fun site history => base.action original site (state base site history))

theorem policy_generated (budget : Nat) (original : base.Policy) (generated : original ∈ base.policies) :
    policy base budget original ∈ (code base budget).policies :=
  every_supported_history_programme_is_actually_tabulated base _ _
    (fun site history _ => action_supported base original generated site (state base site history))

private def importMove (budget : Nat) (site : Fin base.sites)
    (original : Information.Agency.Protocol.Rule base) (signal : Fin base.signals) :
    Information.Agency.Protocol.LocalMove (code base budget) site :=
  match found : Information.Agency.Protocol.localEvent base original site signal with
  | none => ⟨none,List.mem_cons_self⟩
  | some event =>
      let moved : Choice (code base budget) := ⟨event.val,event.property⟩
      ⟨some moved,by
        apply List.mem_cons_of_mem
        apply List.mem_map.mpr
        refine ⟨moved,?_,rfl⟩
        apply List.mem_filter.mpr
        refine ⟨List.mem_attach _ _,?_⟩
        have owned := Information.Agency.Protocol.every_local_event_has_its_own_worker base original site signal event found
        cases kind : event.val <;> simp_all only [decide_eq_true_eq]⟩

def importRule (budget : Nat) (original : Information.Agency.Protocol.Rule base) :
    Information.Agency.Protocol.History.Strategy base (capacity base budget) where
  work := fun site history => base.action original.work.val site (state base site history)
  supported := fun site history _ => action_supported base original.work.val original.work.property site (state base site history)
  event := fun site history => importMove base budget site original (state base site history)

def rule (budget : Nat) (original : Information.Agency.Protocol.Rule base) :=
  Information.Agency.Protocol.History.tabulate base (capacity base budget) (importRule base budget original)

theorem imported_work_is_the_original_local_programme (budget : Nat)
    (original : Information.Agency.Protocol.Rule base) (site : Fin base.sites)
    (history : List (Notice base)) (generated : history ∈ memories base (capacity base budget)) :
    (code base budget).action (rule base budget original).work.val site
        (encode base (capacity base budget) history) =
      base.action original.work.val site (state base site history) :=
  Information.Agency.Protocol.History.tabulated_work_reads_the_entire_local_history base _ _ site history generated


theorem imported_event_retains_the_original_owned_request (budget : Nat)
    (original : Information.Agency.Protocol.Rule base) (site : Fin base.sites)
    (history : List (Notice base)) (generated : history ∈ memories base (capacity base budget)) :
    ((Information.Agency.Protocol.localEvent (code base budget) (rule base budget original) site
      (encode base (capacity base budget) history)).map Subtype.val) =
    ((Information.Agency.Protocol.localEvent base original site (state base site history)).map Subtype.val) := by
  have mapped := congrArg (fun move => move.map Subtype.val)
    (Information.Agency.Protocol.History.tabulated_event_reads_the_entire_local_history
      base (capacity base budget) (importRule base budget original) site history generated)
  refine mapped.trans ?_
  change ((importMove base budget site original (state base site history)).val.map Subtype.val) = _
  unfold importMove
  split <;> simp_all only [Option.map_none,Option.map_some]

variable (budget : Nat)
  (source : Machine Party Good Port (Mandate.State Party Technology) Instrument)
  (same : source.code = code base budget)

private theorem chosen_is_supported (policy : source.code.Policy) (chosen : source.policy? = some policy) :
    policy ∈ source.code.policies := by
  unfold Machine.policy? Machine.policyForSide at chosen
  split at chosen
  · cases Option.some.inj chosen
    exact source.reference_generated
  · split at chosen
    · rename_i selected outcome
      cases Option.some.inj chosen
      exact selected.policy.generated
    · contradiction

/-- The prefix is read from the real initial response, including its paid events. -/
def initialHistory (site : Fin base.sites) : List (Notice base) :=
  match source.policy? with
  | none => []
  | some policy =>
      let changed := congrArg (fun c : Code Party Good Port (Mandate.State Party Technology) Instrument => Events c) same
      transcript base (capacity base budget)
        (cast (congrArg (fun c : Code Party Good Port (Mandate.State Party Technology) Instrument => c.Policy) same) policy)
        (source.code.historyCurrent source.history) (code base budget).start
        (cast changed (source.emissionEvents (source.code.historyCurrent source.history))) site


theorem initial_response_generates_its_own_memory (site : Fin base.sites) :
    decode base (capacity base budget) ((cast (congrArg (fun c : Code Party Good Port (Mandate.State Party Technology) Instrument => c.Frame) same) (source.responseFrame) : (code base budget).Frame).inbox site) =
      some (initialHistory base budget source same site) ∧
    initialHistory base budget source same site ∈ memories base (capacity base budget) ∧
    (initialHistory base budget source same site).length ≤ base.eventLimit := by
  rcases source with ⟨sourceCode,reference,referenceGenerated,history,original,opponent,side,continuation,feedback,overrides⟩
  cases same
  let source : Machine Party Good Port (Mandate.State Party Technology) Instrument :=
    ⟨code base budget,reference,referenceGenerated,history,original,opponent,side,continuation,feedback,overrides⟩
  change decode base (capacity base budget) (source.responseFrame.inbox site) =
      some (initialHistory base budget source rfl site) ∧
    initialHistory base budget source rfl site ∈ memories base (capacity base budget) ∧
    (initialHistory base budget source rfl site).length ≤ base.eventLimit
  cases chosen : source.policy? with
  | none =>
      simp only [initialHistory,chosen,Machine.responseFrame,Machine.frameFor]
      exact ⟨decode_encode base _ [] ((mem_sequences_iff _ _ _).mpr ⟨Nat.zero_le _,by simp⟩),
        (mem_sequences_iff _ _ _).mpr ⟨Nat.zero_le _,by simp⟩,Nat.zero_le _⟩
  | some policy =>
      have generated := chosen_is_supported source policy chosen
      have bounded : (source.emissionEvents (source.code.historyCurrent source.history)).length ≤ base.eventLimit := by
        simp only [Machine.emissionEvents,Machine.eventsFor,chosen]
        exact (traceFrom_is_supported source.code policy _ source.history source.opponent
          source.code.eventLimit [] source.code.start).1
      have recorded := transcript_is_generated_from_actual_notices base (capacity base budget) policy generated
        (source.code.historyCurrent source.history) (code base budget).start
        (source.emissionEvents (source.code.historyCurrent source.history))
        (bounded.trans (Nat.le_add_right _ _)) site
      have length := le_trans (transcript_length base (capacity base budget) policy
        (source.code.historyCurrent source.history) (code base budget).start
        (source.emissionEvents (source.code.historyCurrent source.history)) site) bounded
      refine ⟨?_,?_,?_⟩
      · simpa only [initialHistory,chosen,Machine.responseFrame,Machine.frameFor,Machine.emissionEvents,Machine.eventsFor,cast_eq] using
          every_bounded_actual_prefix_keeps_perfect_local_recall base _ policy generated
            (source.code.historyCurrent source.history) (source.emissionEvents (source.code.historyCurrent source.history))
            (bounded.trans (Nat.le_add_right _ _)) site
      · simpa only [initialHistory,chosen,cast_eq] using recorded
      · simpa only [initialHistory,chosen,cast_eq] using length

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Provision
