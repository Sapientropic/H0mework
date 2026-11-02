import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Continuation.StepNative
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Continuation.Acceptance
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Installation

open Successor
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (fallback : Rule model.source.code) (basis : Basis model.source.code)

/-- The remaining programme retains the old final stage when its explicit list ends. -/
def resume {code : Code Party Good Port (Mandate.State Party Technology) Instrument} : Program code → Program code
  | [] => []
  | [last] => [last]
  | _::next::rest => next::rest

omit [DecidableEq Port] [DecidableEq Technology] in
theorem resuming_keeps_the_exact_next_raw_stage
    {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
    (fallback : Rule code) (program : Program code) (ordinal : Nat) :
    stage code fallback (resume program) ordinal = stage code fallback program (ordinal+1) := by
  cases program with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil => cases ordinal <;> rfl
    | cons next tail => rfl

abbrev Pool (domain : List (Cursor model.source.code)) (reference : Program model.source.code) :=
  Counted.pool model domain fallback reference basis
abbrev Choice (domain : List (Cursor model.source.code)) (reference : Program model.source.code) :=
  Selection.Choice model domain fallback (Pool model fallback basis domain reference) reference
abbrev Rejected (domain : List (Cursor model.source.code)) (reference : Program model.source.code) :=
  ∀ program ∈ Pool model fallback basis domain reference,
    Selection.Rejection model domain fallback (Pool model fallback basis domain reference) reference program

inductive Chain : Nat → List (Cursor model.source.code) → Program model.source.code → Type where
  | exhausted {domain reference} : Chain 0 domain reference
  | blocked {fuel domain reference}
      (rejected : Rejected model fallback basis domain reference)
      (exact : Counted.compile model domain fallback reference basis = .blocked rejected) :
      Chain (fuel+1) domain reference
  | selected {fuel domain reference}
      (choice : Choice model fallback basis domain reference)
      (exact : Counted.compile model domain fallback reference basis = .selected choice)
      (tail : Chain fuel (advance domain fallback choice.policy.protocol) (resume choice.policy.protocol)) :
      Chain (fuel+1) domain reference

def generate (fuel : Nat) (domain : List (Cursor model.source.code)) (reference : Program model.source.code) :
    Chain model fallback basis fuel domain reference :=
  match fuel with
  | 0 => .exhausted
  | fuel+1 => match exact : Counted.compile model domain fallback reference basis with
    | .blocked rejected => .blocked rejected exact
    | .selected choice => .selected choice exact
        (generate fuel (advance domain fallback choice.policy.protocol) (resume choice.policy.protocol))

namespace Chain
variable {model fallback basis} {fuel : Nat} {domain : List (Cursor model.source.code)}
  {reference : Program model.source.code}

def rules : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → List (Program model.source.code)
  | _,_,_,.exhausted => []
  | _,_,_,.blocked _ _ => []
  | _,_,_,.selected choice _ tail => choice.policy.protocol :: tail.rules

def review : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Bool
  | _,_,_,.exhausted => true
  | _,domain,reference,.blocked rejected _ => Selection.review model domain fallback
      (Pool model fallback basis domain reference) reference (.blocked rejected)
  | _,domain,reference,.selected choice _ tail => Selection.review model domain fallback
      (Pool model fallback basis domain reference) reference (.selected choice) && tail.review

theorem every_compiled_step_is_independently_reviewable (chain : Chain model fallback basis fuel domain reference) :
    chain.review = true := by
  induction chain with
  | exhausted => rfl
  | @blocked fuel domain reference rejected exact =>
    exact Selection.every_generated_outcome_is_independently_reviewable model domain fallback
      (Pool model fallback basis domain reference) reference (.blocked rejected)
  | selected choice exact tail ih =>
    simp only [review,Bool.and_eq_true,Selection.every_generated_outcome_is_independently_reviewable,ih,and_self]

def realize : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Cursor model.source.code
  | _,_,_,.exhausted,point,_ => point
  | _,_,_,.blocked _ _,point,_ => point
  | _,_,_,.selected choice _ tail,point,environment => tail.realize (after point fallback choice.policy.protocol environment 1) environment

def finalDomain : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → List (Cursor model.source.code)
  | _,domain,_,.exhausted => domain
  | _,domain,_,.blocked _ _ => domain
  | _,_,_,.selected _ _ tail => tail.finalDomain

def AllCutsCovered : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,domain,_,.exhausted,point,_ => Covered domain point
  | _,domain,_,.blocked _ _,point,_ => Covered domain point
  | _,domain,_,.selected choice _ tail,point,environment => Covered domain point ∧
      tail.AllCutsCovered (after point fallback choice.policy.protocol environment 1) environment

theorem every_cut_retains_an_actual_source_representative (chain : Chain model fallback basis fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.AllCutsCovered point environment ∧ Covered chain.finalDomain (chain.realize point environment) := by
  induction chain generalizing point with
  | exhausted => exact ⟨covered,covered⟩
  | blocked => exact ⟨covered,covered⟩
  | selected choice exact tail ih =>
    have next := every_actual_raw_installation_has_a_public_successor _ point covered fallback choice.policy.protocol environment
    have continued := ih (after point fallback choice.policy.protocol environment 1) next
    exact ⟨⟨covered,continued.1⟩,continued.2⟩

def AllCutsAccepted : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,_,.exhausted,_,_ => True
  | _,_,_,.blocked _ _,_,_ => True
  | _,_,reference,.selected choice _ tail,point,environment =>
      (∀ rival : Opponent model.source.code,
        Synthesis.accepts model.source.code (economicAxes point.source point.cut)
          (Finite.actualEvaluation model point fallback choice.policy.protocol rival)
          (Finite.actualEvaluation model point fallback reference rival)) ∧
      tail.AllCutsAccepted (after point fallback choice.policy.protocol environment 1) environment

theorem every_selected_cut_protects_its_actual_full_responsibility (chain : Chain model fallback basis fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.AllCutsAccepted point environment := by
  induction chain generalizing point with
  | exhausted => trivial
  | blocked => trivial
  | @selected fuel domain reference choice exact tail ih =>
    refine ⟨?_,ih (after point fallback choice.policy.protocol environment 1)
      (every_actual_raw_installation_has_a_public_successor _ point covered fallback choice.policy.protocol environment)⟩
    intro rival
    obtain ⟨representative,inside,matched⟩ := covered
    exact (Acceptance.aligned_acceptance model representative point matched rival fallback choice.policy.protocol reference).mp
      (Counted.verified_program_protects_every_actual_responsibility model domain fallback reference basis
        choice.policy.protocol choice.policy.generated
        (Selection.independently_replayed_choice_is_accepted model domain fallback
          (Pool model fallback basis domain reference) reference choice) ⟨representative,inside⟩ rival)

private theorem singleton_acceptance (point : Cursor model.source.code)
    (reference protocol : Program model.source.code) :
    Selection.acceptable model [point] fallback [reference,protocol] reference protocol ↔
      ∀ rival : Opponent model.source.code,
        Synthesis.accepts model.source.code (economicAxes point.source point.cut)
          (Finite.actualEvaluation model point fallback protocol rival)
          (Finite.actualEvaluation model point fallback reference rival) := by
  rw [Selection.acceptable_iff_every_common_external_opponent model [point] fallback [reference,protocol]
    reference protocol (by simp) (by simp)]
  constructor
  · intro all rival
    exact all ⟨point,List.mem_singleton_self _⟩ rival
  · intro all world rival
    rcases world with ⟨cursor,inside⟩
    have same : cursor = point := List.mem_singleton.mp inside
    subst cursor
    exact all rival

/-- Recompute actual finite rows; no acceptance proof or planner result is read by this checker. -/
def replayActual : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Bool
  | _,_,_,.exhausted,_,_ => true
  | _,_,_,.blocked _ _,_,_ => true
  | _,_,reference,.selected choice _ tail,point,environment =>
      decide (Selection.acceptable model [point] fallback [reference,choice.policy.protocol] reference choice.policy.protocol) &&
        tail.replayActual (after point fallback choice.policy.protocol environment 1) environment

theorem replay_actual_iff (chain : Chain model fallback basis fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) :
    chain.replayActual point environment = true ↔ chain.AllCutsAccepted point environment := by
  induction chain generalizing point with
  | exhausted => exact iff_of_true rfl True.intro
  | blocked => exact iff_of_true rfl True.intro
  | selected choice exact tail ih =>
    simp only [replayActual,AllCutsAccepted,Bool.and_eq_true,decide_eq_true_eq,singleton_acceptance,ih]

theorem every_actual_cut_is_independently_reviewable (chain : Chain model fallback basis fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.replayActual point environment = true :=
  (chain.replay_actual_iff point environment).mpr
    (chain.every_selected_cut_protects_its_actual_full_responsibility point environment covered)

/-- These are generated data, including per-program raw refutations in every blocked cut. -/
def Audits : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Type
  | _,_,_,.exhausted => Unit
  | _,domain,reference,.blocked rejected _ =>
      Counted.Contracts.Failures model domain fallback reference basis (.blocked rejected)
  | _,domain,reference,.selected choice _ tail =>
      PLift (Counted.Contracts.Contract model domain fallback reference basis (.selected choice)) × tail.Audits

def audits : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → (chain : Chain model fallback basis fuel domain reference) → chain.Audits
  | _,_,_,.exhausted => ()
  | _,domain,reference,.blocked rejected _ => Counted.Contracts.failures model domain fallback reference basis (.blocked rejected)
  | _,domain,reference,.selected choice _ tail => ⟨⟨Counted.Contracts.every_outcome_contract model domain fallback reference basis (.selected choice)⟩,tail.audits⟩


def Migrations : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference →
      Cursor model.source.code → Opponent model.source.code → Type
  | _,_,_,.exhausted,_,_ => Unit
  | _,_,_,.blocked _ _,_,_ => Unit
  | _,_,_,.selected choice _ tail,point,environment =>
      StepNative.Payload model point fallback choice.policy.protocol environment ×
        tail.Migrations (after point fallback choice.policy.protocol environment 1) environment

def migrations : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → (chain : Chain model fallback basis fuel domain reference) →
      (point : Cursor model.source.code) → (environment : Opponent model.source.code) → chain.Migrations point environment
  | _,_,_,.exhausted,_,_ => ()
  | _,_,_,.blocked _ _,_,_ => ()
  | _,_,_,.selected choice _ tail,point,environment =>
      ⟨StepNative.generate model point fallback choice.policy.protocol environment,
        tail.migrations (after point fallback choice.policy.protocol environment 1) environment⟩



def fold (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) : Cursor model.source.code :=
  rules.foldl (fun current rule => after current fallback rule environment 1) point

theorem realization_is_the_actual_installed_rule_fold (chain : Chain model fallback basis fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) :
    chain.realize point environment = fold (fallback := fallback) point environment chain.rules := by
  induction chain generalizing point with
  | exhausted => rfl
  | blocked => rfl
  | selected choice exact tail ih => exact ih (after point fallback choice.policy.protocol environment 1)

theorem fold_history (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) : (fold (fallback := fallback) point environment rules).history = point.history := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih (after point fallback rule environment 1)

theorem fold_cut (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) : (fold (fallback := fallback) point environment rules).cut = point.cut+rules.length := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih =>
    change (fold (after point fallback rule environment 1) environment tail).cut = _
    rw [ih]
    change point.cut+1+tail.length = point.cut+(tail.length+1)
    omega

theorem fold_owner (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) : (fold (fallback := fallback) point environment rules).ownerStart = point.ownerStart := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih (after point fallback rule environment 1)

theorem fold_budget (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) : (fold (fallback := fallback) point environment rules).entry.budget = point.entry.budget := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih => exact ih (after point fallback rule environment 1)

theorem after_remaining (point : Cursor model.source.code) (rule : Program model.source.code)
    (environment : Opponent model.source.code) :
    ((after point fallback rule environment 1).source.feedbackState (after point fallback rule environment 1).entry (point.cut+1)).remaining =
      (point.source.feedbackState point.entry point.cut).remaining-1 := by
  have actual := Future.the_whole_future_run_is_the_actual_state point.source point.entry point.cut
    (controller point fallback rule environment) (schedule point fallback rule) 1
  exact (congrArg State.remaining actual).trans (Residual.remaining_is_the_seed_budget _ _ _ _ _)

theorem fold_remaining (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) :
    ((fold (fallback := fallback) point environment rules).source.feedbackState (fold (fallback := fallback) point environment rules).entry (fold (fallback := fallback) point environment rules).cut).remaining =
      (point.source.feedbackState point.entry point.cut).remaining-rules.length := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih =>
    change ((fold (after point fallback rule environment 1) environment tail).source.feedbackState
      (fold (after point fallback rule environment 1) environment tail).entry (fold (after point fallback rule environment 1) environment tail).cut).remaining = _
    rw [ih]
    change ((after point fallback rule environment 1).source.feedbackState (after point fallback rule environment 1).entry (point.cut+1)).remaining-tail.length = _
    rw [after_remaining]
    simp only [List.length_cons,Nat.sub_sub]
    rw [Nat.add_comm]

theorem fold_keeps_every_prior_emitter_word (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument)
    (earlier : current.round-model.source.code.initial.round-1 < point.history.length+1+point.cut) :
    (fold (fallback := fallback) point environment rules).source.body current = point.source.body current := by
  induction rules generalizing point with
  | nil => rfl
  | cons rule tail ih =>
    change (fold (after point fallback rule environment 1) environment tail).source.body current = _
    exact (ih (after point fallback rule environment 1) (by
      change _ < point.history.length+1+(point.cut+1);omega)).trans
      (Future.earlier_body point.source point.entry point.cut (controller point fallback rule environment)
        (schedule point fallback rule) rfl current earlier)

theorem fold_keeps_every_prior_raw_event (point : Cursor model.source.code) (environment : Opponent model.source.code)
    (rules : List (Program model.source.code)) (ordinal : Nat) (earlier : ordinal < point.history.length+2+point.cut) :
    ProgrammeSource.rawEvent (fold (fallback := fallback) point environment rules).source.input (ProgrammeHistory.visitAt point.source.input ordinal).current =
      ProgrammeSource.rawEvent point.source.input (ProgrammeHistory.visitAt point.source.input ordinal).current := by
  cases view : (ProgrammeHistory.visitAt point.source.input ordinal).current with
  | bootstrap => rfl
  | running current past =>
    change (fold (fallback := fallback) point environment rules).source.body current = point.source.body current
    apply fold_keeps_every_prior_emitter_word
    have rounds := ProgrammeHistory.visit_round point.source.input ordinal
    rw [view] at rounds
    change current.round = model.source.code.initial.round+ordinal at rounds
    omega

theorem fold_keeps_the_complete_native_financial_prefix (point : Cursor model.source.code)
    (environment : Opponent model.source.code) (rules : List (Program model.source.code))
    (ordinal : Nat) (earlier : ordinal ≤ point.history.length+2+point.cut) :
    Native.Coupling.Match model.source.code point.source.input (fold (fallback := fallback) point environment rules).source.input
      (Financial.accountAt point.source.input ordinal) (Financial.accountAt (fold (fallback := fallback) point environment rules).source.input ordinal) :=
  Native.Coupling.History.complete_accounts model.source.code point.source.input (fold (fallback := fallback) point environment rules).source.input rfl rfl
    (point.history.length+2+point.cut) (fold_keeps_every_prior_raw_event point environment rules)
    point.source.body (fold (fallback := fallback) point environment rules).source.body rfl rfl ordinal earlier

def InstalledPrefixes : {fuel : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback basis fuel domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,_,.exhausted,_,_ => True
  | _,_,_,.blocked _ _,_,_ => True
  | _,_,_,.selected choice _ tail,point,environment =>
      (∀ (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument),
        current.round-model.source.code.initial.round-1 < point.history.length+1+(point.cut+1) →
          (tail.realize (after point fallback choice.policy.protocol environment 1) environment).source.body current =
            (after point fallback choice.policy.protocol environment 1).source.body current) ∧
      tail.InstalledPrefixes (after point fallback choice.policy.protocol environment 1) environment

theorem every_installed_cut_is_retained_by_the_one_final_source (chain : Chain model fallback basis fuel domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) : chain.InstalledPrefixes point environment := by
  induction chain generalizing point with
  | exhausted => exact True.intro
  | blocked => exact True.intro
  | selected choice exact tail ih =>
    refine ⟨?_,ih (after point fallback choice.policy.protocol environment 1)⟩
    intro current earlier
    rw [realization_is_the_actual_installed_rule_fold]
    exact fold_keeps_every_prior_emitter_word (after point fallback choice.policy.protocol environment 1) environment tail.rules current earlier


end Chain
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Installation
