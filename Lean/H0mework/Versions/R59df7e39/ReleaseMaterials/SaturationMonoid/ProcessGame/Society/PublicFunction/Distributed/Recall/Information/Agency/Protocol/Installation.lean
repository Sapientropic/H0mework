import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Acceptance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation

open Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

namespace Installation

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))

inductive Chain : Nat → List (Cursor model.source.code) → Rule model.source.code → Type where
  | exhausted {domain reference} : Chain 0 domain reference
  | blocked {fuel domain reference}
      (rejected : ∀ rule : Rule model.source.code, Replanning.Rejection model domain reference rule)
      (exact : Replanning.compile model domain reference = .blocked rejected) : Chain (fuel+1) domain reference
  | selected {fuel domain reference} (choice : Replanning.Choice model domain reference)
      (exact : Replanning.compile model domain reference = .selected choice)
      (tail : Chain fuel (advance model.source.code domain choice.policy.protocol) choice.policy.protocol) :
      Chain (fuel+1) domain reference

def generate (fuel : Nat) (domain : List (Cursor model.source.code)) (reference : Rule model.source.code) :
    Chain model fuel domain reference :=
  match fuel with
  | 0 => .exhausted
  | fuel+1 => match exact : Replanning.compile model domain reference with
    | .blocked rejected => .blocked rejected exact
    | .selected choice => .selected choice exact
        (generate fuel (advance model.source.code domain choice.policy.protocol) choice.policy.protocol)

namespace Chain
variable {model} {fuel : Nat} {domain : List (Cursor model.source.code)} {reference : Rule model.source.code}

def rules : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → List (Rule model.source.code)
  | _,_,_,.exhausted => []
  | _,_,_,.blocked _ _ => []
  | _,_,_,.selected choice _ tail => choice.policy.protocol :: tail.rules

def review : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → Bool
  | _,_,_,.exhausted => true
  | _,domain,reference,.blocked rejected _ => Replanning.review model domain reference (.blocked rejected)
  | _,domain,reference,.selected choice _ tail => Replanning.review model domain reference (.selected choice) && tail.review

theorem every_compiled_step_is_independently_reviewable (chain : Chain model fuel domain reference) :
    chain.review = true := by
  induction chain with
  | exhausted => rfl
  | blocked rejected exact => exact Replanning.every_generated_outcome_is_independently_reviewable _ _ _ _
  | selected choice exact tail ih =>
    simp only [review,Bool.and_eq_true,Replanning.every_generated_outcome_is_independently_reviewable,ih,and_self]

theorem installed_rules_do_not_exceed_the_requested_finite_unfolding (chain : Chain model fuel domain reference) :
    chain.rules.length ≤ fuel := by
  induction chain with
  | exhausted => exact Nat.le_refl _
  | blocked => exact Nat.zero_le _
  | selected choice exact tail ih => exact Nat.succ_le_succ ih

def realize : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Cursor model.source.code
  | _,_,_,.exhausted,point,_ => point
  | _,_,_,.blocked _ _,point,_ => point
  | _,_,_,.selected choice _ tail,point,environment => tail.realize (point.after choice.policy.protocol environment) environment

def finalDomain : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → List (Cursor model.source.code)
  | _,domain,_,.exhausted => domain
  | _,domain,_,.blocked _ _ => domain
  | _,_,_,.selected _ _ tail => tail.finalDomain

def AllCutsCovered : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,domain,_,.exhausted,point,_ => Covered domain point
  | _,domain,_,.blocked _ _,point,_ => Covered domain point
  | _,domain,_,.selected choice _ tail,point,environment => Covered domain point ∧
      tail.AllCutsCovered (point.after choice.policy.protocol environment) environment

theorem every_cut_retains_an_actual_source_representative (chain : Chain model fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.AllCutsCovered point environment ∧ Covered chain.finalDomain (chain.realize point environment) := by
  induction chain generalizing point with
  | exhausted => exact ⟨covered,covered⟩
  | blocked => exact ⟨covered,covered⟩
  | selected choice exact tail ih =>
    have next := every_actual_installation_stays_in_its_own_public_information_domain _ point covered choice.policy.protocol environment
    have continued := ih (point.after choice.policy.protocol environment) next
    exact ⟨⟨covered,continued.1⟩,continued.2⟩

def AllCutsAccepted : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,_,.exhausted,_,_ => True
  | _,_,_,.blocked _ _,_,_ => True
  | _,_,reference,.selected choice _ tail,point,environment =>
      (∀ rival : Opponent model.source.code,
        Synthesis.accepts model.source.code (economicAxes point.source point.cut)
          (Replanning.actualEvaluation model point choice.policy.protocol rival)
          (Replanning.actualEvaluation model point reference rival)) ∧
      tail.AllCutsAccepted (point.after choice.policy.protocol environment) environment

theorem every_selected_cut_protects_its_actual_full_responsibility (chain : Chain model fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.AllCutsAccepted point environment := by
  induction chain generalizing point with
  | exhausted => trivial
  | blocked => trivial
  | @selected fuel domain reference choice exact tail ih =>
    refine ⟨?_,ih (point.after choice.policy.protocol environment)
      (every_actual_installation_stays_in_its_own_public_information_domain _ point covered choice.policy.protocol environment)⟩
    intro rival
    obtain ⟨representative,inside,matched⟩ := covered
    exact (Acceptance.aligned_acceptance model representative point matched rival choice.policy.protocol reference).mp
      (Replanning.every_verified_protocol_protects_its_own_actual_full_responsibility model domain reference choice.policy.protocol
        (Replanning.independently_replayed_choice_is_accepted model domain reference choice) ⟨representative,inside⟩ rival)

private theorem singleton_acceptance (point : Cursor model.source.code) (reference protocol : Rule model.source.code) :
    Replanning.acceptable model [point] reference protocol ↔
      ∀ rival : Opponent model.source.code,
        Synthesis.accepts model.source.code (economicAxes point.source point.cut)
          (Replanning.actualEvaluation model point protocol rival) (Replanning.actualEvaluation model point reference rival) := by
  rw [Replanning.acceptable_iff_every_common_external_opponent]
  constructor
  · intro all rival
    exact all ⟨point,List.mem_singleton_self _⟩ rival
  · intro all world rival
    rcases world with ⟨cursor,inside⟩
    have same : cursor = point := List.mem_singleton.mp inside
    subst cursor
    exact all rival

/-- Replays each actual cut's raw finite rows without calling the planner or reading its proof. -/
def replayActual : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Bool
  | _,_,_,.exhausted,_,_ => true
  | _,_,_,.blocked _ _,_,_ => true
  | _,_,reference,.selected choice _ tail,point,environment =>
      decide (Replanning.acceptable model [point] reference choice.policy.protocol) &&
        tail.replayActual (point.after choice.policy.protocol environment) environment

theorem replay_actual_iff (chain : Chain model fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) :
    chain.replayActual point environment = true ↔ chain.AllCutsAccepted point environment := by
  induction chain generalizing point with
  | exhausted => exact iff_of_true rfl True.intro
  | blocked => exact iff_of_true rfl True.intro
  | selected choice exact tail ih =>
    simp only [replayActual,AllCutsAccepted,Bool.and_eq_true,decide_eq_true_eq,singleton_acceptance,ih]

theorem every_actual_selected_cut_is_independently_reviewable (chain : Chain model fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.replayActual point environment = true :=
  (chain.replay_actual_iff point environment).mpr
    (chain.every_selected_cut_protects_its_actual_full_responsibility point environment covered)

def fold (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) : Cursor model.source.code :=
  rules.foldl (fun current rule => current.after rule environment) point

theorem realization_is_the_actual_installed_rule_fold (chain : Chain model fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) :
    chain.realize point environment = fold point environment chain.rules := by
  induction chain generalizing point with
  | exhausted => rfl
  | blocked => rfl
  | selected choice exact tail ih => exact ih (point.after choice.policy.protocol environment)

theorem fold_history (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) : (fold point environment rules).history = point.history := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih (point.after rule environment)

theorem fold_cut (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) : (fold point environment rules).cut = point.cut+rules.length := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih =>
    change (fold (point.after rule environment) environment tail).cut = _
    rw [ih]
    change point.cut+1+tail.length = point.cut+(tail.length+1)
    omega

theorem fold_owner (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) : (fold point environment rules).ownerStart = point.ownerStart := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih (point.after rule environment)

theorem fold_budget (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) : (fold point environment rules).entry.budget = point.entry.budget := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih (point.after rule environment)

theorem after_remaining (point : Cursor model.source.code) (rule : Rule model.source.code)
    (environment : Opponent model.source.code) :
    ((point.after rule environment).source.feedbackState (point.after rule environment).entry (point.cut+1)).remaining =
      (point.source.feedbackState point.entry point.cut).remaining-1 := by
  have actual := Future.the_whole_future_run_is_the_actual_state point.source point.entry point.cut
    (Cursor.controller point rule environment) (term point.source point.entry point.cut rule).val 1
  exact (congrArg State.remaining actual).trans (Residual.remaining_is_the_seed_budget _ _ _ _ _)

theorem fold_remaining (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) :
    ((fold point environment rules).source.feedbackState (fold point environment rules).entry (fold point environment rules).cut).remaining =
      (point.source.feedbackState point.entry point.cut).remaining-rules.length := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih =>
    change ((fold (point.after rule environment) environment tail).source.feedbackState
      (fold (point.after rule environment) environment tail).entry (fold (point.after rule environment) environment tail).cut).remaining = _
    rw [ih]
    change ((point.after rule environment).source.feedbackState (point.after rule environment).entry (point.cut+1)).remaining-tail.length = _
    rw [after_remaining]
    simp only [List.length_cons,Nat.sub_sub]
    rw [Nat.add_comm]

theorem fold_keeps_every_prior_emitter_word (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (earlier : current.round-model.source.code.initial.round-1 < point.history.length+1+point.cut) :
    (fold point environment rules).source.body current = point.source.body current := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih =>
    change (fold (point.after rule environment) environment tail).source.body current = _
    exact (ih (point.after rule environment) (by
      change _ < point.history.length+1+(point.cut+1);omega)).trans
      (Future.earlier_body point.source point.entry point.cut (Cursor.controller point rule environment)
        (term point.source point.entry point.cut rule).val rfl current earlier)

theorem fold_keeps_every_prior_raw_event (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Rule model.source.code)) (ordinal : Nat) (earlier : ordinal < point.history.length+2+point.cut) :
    ProgrammeSource.rawEvent (fold point environment rules).source.input (ProgrammeHistory.visitAt point.source.input ordinal).current =
      ProgrammeSource.rawEvent point.source.input (ProgrammeHistory.visitAt point.source.input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt point.source.input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (fold point environment rules).source.body current = point.source.body current
    apply fold_keeps_every_prior_emitter_word
    have rounds := ProgrammeHistory.visit_round point.source.input ordinal
    rw [view] at rounds
    change current.round = model.source.code.initial.round+ordinal at rounds
    omega

theorem fold_keeps_the_complete_native_financial_prefix (point : Cursor model.source.code)
    (environment : Opponent model.source.code) (rules : List (Rule model.source.code))
    (ordinal : Nat) (earlier : ordinal ≤ point.history.length+2+point.cut) :
    Native.Coupling.Match model.source.code point.source.input (fold point environment rules).source.input
      (Financial.accountAt point.source.input ordinal) (Financial.accountAt (fold point environment rules).source.input ordinal) :=
  Native.Coupling.History.complete_accounts model.source.code point.source.input (fold point environment rules).source.input rfl rfl
    (point.history.length+2+point.cut) (fold_keeps_every_prior_raw_event point environment rules)
    point.source.body (fold point environment rules).source.body rfl rfl ordinal earlier

def InstalledPrefixes : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Rule model.source.code} → Chain model fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,_,.exhausted,_,_ => True
  | _,_,_,.blocked _ _,_,_ => True
  | _,_,_,.selected choice _ tail,point,environment =>
      (∀ (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument),
        current.round-model.source.code.initial.round-1 < point.history.length+1+(point.cut+1) →
          (tail.realize (point.after choice.policy.protocol environment) environment).source.body current =
            (point.after choice.policy.protocol environment).source.body current) ∧
      tail.InstalledPrefixes (point.after choice.policy.protocol environment) environment

theorem every_installed_cut_is_retained_by_the_one_final_source (chain : Chain model fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) : chain.InstalledPrefixes point environment := by
  induction chain generalizing point with
  | exhausted => exact True.intro
  | blocked => exact True.intro
  | selected choice exact tail ih =>
    refine ⟨?_,ih (point.after choice.policy.protocol environment)⟩
    intro current earlier
    rw [realization_is_the_actual_installed_rule_fold]
    exact fold_keeps_every_prior_emitter_word (point.after choice.policy.protocol environment) environment tail.rules current earlier

end Chain
end Installation

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall.Information.Agency.Protocol.Continuation
