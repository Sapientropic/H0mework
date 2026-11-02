import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptDrivenMaterialization

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptBranchCoverage
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)
  (allowance : Nat)

abbrev Stages := ReceiptDrivenRun.Stages model
abbrev Mailbox := ReceiptDrivenRun.Mailbox model
abbrev Slot := ReceiptDrivenMaterialization.Slot model
abbrev Path := ReceiptDrivenMaterialization.Slots model

def select (paths : List (Path model)) (move : Move model.source.code) := paths.filter fun path =>
  match path with | [] => false | slot :: _ => decide (slot.move = move)

def checkHead (past : Stages model) (pending : Mailbox model) (base : Rule model.source.code) (slot : Slot model) :=
  let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
  LocalRuleTable.verify slot.rule (ReceiptDrivenRule.protocol base queued) &&
    (List.finRange model.source.code.sites).all fun site => decide
      (ReceiptDrivenRule.consume queued
        (StageTrace.material (EventHistory.execute start past) slot.rule (EventStep.fixed slot.move)) site = slot.pending site)

theorem checked_head_is_the_generated_rule_and_queue
    (past : Stages model) (pending : Mailbox model) (base : Rule model.source.code) (slot : Slot model)
    (checked : checkHead model start vocabulary encoding law past pending base slot = true) :
    let queued := FreshReception.queue pending (FreshReception.poll vocabulary encoding law start past)
    ReceiptDrivenRule.protocol base queued = slot.rule ∧
      ReceiptDrivenRule.consume queued
        (StageTrace.material (EventHistory.execute start past) slot.rule (EventStep.fixed slot.move)) = slot.pending := by
  simp only [checkHead, Bool.and_eq_true] at checked
  refine ⟨(LocalRuleTable.verified_table_is_the_entire_original_rule _ _ checked.1).symm, ?_⟩
  funext site
  exact of_decide_eq_true ((List.all_eq_true.mp checked.2) site (List.mem_finRange _))

-- A certificate must cover every original admitted move at every cut. It does
-- not evaluate Goal or choose a world outcome, and never enters the executor.
def covers : List (Rule model.source.code) → Stages model → Mailbox model → List (Path model) → Bool
  | [], _, _, paths => paths.any List.isEmpty
  | base :: tail, past, pending, paths =>
    if UnifiedResponse.fuel model start past = 0 then false else
    (InterferenceEnvelope.choices start past allowance).all fun move =>
      let branches := select model paths move
      match branches.head? with
      | some (slot :: _) =>
        branches.all (fun path => match path with
          | head :: _ => checkHead model start vocabulary encoding law past pending base head
          | [] => false) &&
        covers tail (LocalWindowRun.after model past slot.rule slot.move) slot.pending (branches.map List.tail)
      | _ => false

theorem covered_paths_contain_every_compliant_actual_execution
    (programme : List (Rule model.source.code)) (past : Stages model) (pending : Mailbox model)
    (paths : List (Path model)) (rival : Opponent model.source.code)
    (covered : covers model start vocabulary encoding law allowance programme past pending paths = true)
    (compliant : ((ReceiptDrivenRun.run model start vocabulary encoding law allowance programme past pending rival).inputs.all
      fun input => input.within) = true) :
    ∃ path ∈ paths, ReceiptDrivenMaterialization.verify model start vocabulary encoding law allowance rival
      programme past pending path = true := by
  induction programme generalizing past pending paths with
  | nil =>
    obtain ⟨path, member, empty⟩ := List.any_eq_true.mp covered
    have same : path = [] := List.isEmpty_iff.mp empty
    subst path
    exact ⟨[], member, rfl⟩
  | cons base tail ih =>
    by_cases stopped : UnifiedResponse.fuel model start past = 0
    · simp only [covers, if_pos stopped, Bool.false_eq_true] at covered
    · simp only [covers, if_neg stopped] at covered
      simp only [ReceiptDrivenRun.run, if_neg stopped, List.all_cons, Bool.and_eq_true] at compliant
      let move := (InterferenceEnvelope.observe start past allowance rival).admitted
      let branches := select model paths move
      have branch := List.all_eq_true.mp covered move (of_decide_eq_true compliant.1)
      change (match branches.head? with
        | some (slot :: _) => branches.all (fun path => match path with
            | head :: _ => checkHead model start vocabulary encoding law past pending base head
            | [] => false) && covers model start vocabulary encoding law allowance tail
              (LocalWindowRun.after model past slot.rule slot.move) slot.pending (branches.map List.tail)
        | _ => false) = true at branch
      cases first : branches.head? with
      | none => simp only [first, Bool.false_eq_true] at branch
      | some path =>
        cases path with
        | nil => simp only [first, Bool.false_eq_true] at branch
        | cons slot rest =>
          simp only [first, Bool.and_eq_true] at branch
          have selected : slot :: rest ∈ branches := List.mem_of_head? first
          have selectedHead := List.all_eq_true.mp branch.1 _ selected
          have generated := checked_head_is_the_generated_rule_and_queue model start vocabulary encoding law
            past pending base slot selectedHead
          have selectedMove : slot.move = move := of_decide_eq_true (List.mem_filter.mp selected).2
          have nextCompliant := compliant.2
          have selectedMoveExact : slot.move = (InterferenceEnvelope.observe start past allowance rival).admitted := selectedMove
          simp only [generated.1, ← selectedMoveExact, generated.2] at nextCompliant
          obtain ⟨suffix, suffixMember, suffixVerified⟩ := ih _ _ _ branch.2 nextCompliant
          obtain ⟨candidate, member, tailSame⟩ := List.mem_map.mp suffixMember
          cases candidate with
          | nil => have := (List.mem_filter.mp member).2; contradiction
          | cons head more =>
            have headCheck := List.all_eq_true.mp branch.1 _ member
            have headFacts := checked_head_is_the_generated_rule_and_queue model start vocabulary encoding law
              past pending base head headCheck
            have headMove : head.move = move := of_decide_eq_true (List.mem_filter.mp member).2
            have sameRule : head.rule = slot.rule := headFacts.1.symm.trans generated.1
            have samePending : head.pending = slot.pending := by
              rw [← headFacts.2, ← generated.2, sameRule, headMove, selectedMove]
            have sameTail : more = suffix := tailSame
            refine ⟨head :: more, (List.mem_filter.mp member).1, ?_⟩
            simp only [ReceiptDrivenMaterialization.verify, if_neg stopped, Bool.and_eq_true]
            refine ⟨?_, ?_⟩
            · simp only [ReceiptDrivenMaterialization.checkStep, checkHead, Bool.and_eq_true] at headCheck ⊢
              exact ⟨⟨headCheck.1, decide_eq_true headMove.symm⟩, headCheck.2⟩
            · simpa only [sameRule, samePending, sameTail, headMove, ← selectedMove] using suffixVerified

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReceiptBranchCoverage
