import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Runtime
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Closure
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Counted.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation

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
  (fallback : Rule model.source.code)

/-- Pending continues the original programme; it does not invent feasibility or a waiting action. -/
def selected {domain : List (Cursor model.source.code)} {reference : Program model.source.code} {budget : Nat} :
    Enquiry model domain fallback reference budget → Program model.source.code
  | .found discovery _ _ _ => discovery.program
  | .pending _ => reference

def nextCap {domain : List (Cursor model.source.code)} {reference : Program model.source.code} {budget : Nat} :
    Enquiry model domain fallback reference budget → Nat
  | .found _ _ _ _ => 0
  | .pending _ => budget+1

abbrev Safe (domain : List (Cursor model.source.code)) (reference candidate : Program model.source.code) :=
  Selection.acceptable model domain fallback [reference,candidate] reference candidate

abbrev requests (domain : List (Cursor model.source.code)) (program : Program model.source.code) :=
  Support.requests model fallback domain program
abbrev SourceSupported (domain : List (Cursor model.source.code)) (program : Program model.source.code) :=
  Support.SourceSupported model fallback domain program
abbrev support_exact := Support.support_exact model fallback

structure Unsupported (domain : List (Cursor model.source.code)) (program : Program model.source.code) where
  request : Request Party Good Port (Mandate.State Party Technology) Instrument
  occurs : request ∈ requests model fallback domain program
  outside : request ∉ model.source.code.actions

def unsupported (domain : List (Cursor model.source.code)) (program : Program model.source.code)
    (absent : ¬ SourceSupported model fallback domain program) : Unsupported model fallback domain program :=
  match inspect (fun request => request ∈ model.source.code.actions) (requests model fallback domain program) with
  | .rejected request occurs outside => ⟨request,occurs,outside⟩
  | .accepted generated => False.elim (absent generated)

def rejection (domain : List (Cursor model.source.code)) (reference candidate : Program model.source.code)
    (inadmissible : ¬ Safe model fallback domain reference candidate) :
    Selection.Rejection model domain fallback [reference,candidate] reference candidate :=
  match inspect (Selection.holds model domain fallback [reference,candidate] reference candidate)
      (Selection.rows model domain fallback [reference,candidate]) with
  | .rejected row generated broken => ⟨row,generated,broken⟩
  | .accepted accepted => False.elim (inadmissible accepted)

inductive Chain : Nat → Nat → List (Cursor model.source.code) → Program model.source.code → Type where
  | exhausted {budget domain reference} : Chain 0 budget domain reference
  | complete {fuel budget domain reference}
      (receipt : Closure.Receipt model domain fallback reference budget)
      (exact : Closure.prepare model domain fallback reference budget = .complete receipt) : Chain (fuel+1) budget domain reference
  | unsupported {fuel budget domain reference}
      (query : Enquiry model domain fallback reference budget)
      (exact : query = inquire model domain fallback reference budget)
      (failure : Unsupported model fallback domain (selected model fallback query)) :
      Chain (fuel+1) budget domain reference
  | rejected {fuel budget domain reference}
      (query : Enquiry model domain fallback reference budget)
      (exact : query = inquire model domain fallback reference budget)
      (failure : Selection.Rejection model domain fallback [reference,selected model fallback query]
        reference (selected model fallback query)) : Chain (fuel+1) budget domain reference
  | step {fuel budget domain reference}
      (query : Enquiry model domain fallback reference budget)
      (exact : query = inquire model domain fallback reference budget)
      (safe : Safe model fallback domain reference (selected model fallback query))
      (supported : SourceSupported model fallback domain (selected model fallback query))
      (tail : Chain fuel (nextCap model fallback query)
        (advance domain fallback (selected model fallback query))
        (Counted.Installation.resume (selected model fallback query))) :
      Chain (fuel+1) budget domain reference

def generate : (fuel budget : Nat) → (domain : List (Cursor model.source.code)) →
    (reference : Program model.source.code) → Chain model fallback fuel budget domain reference
  | 0,_,_,_ => .exhausted
  | fuel+1,budget,domain,reference =>
    match generated : Closure.prepare model domain fallback reference budget with
    | .complete receipt => .complete receipt generated
    | .enquiry query queryExact =>
      if supported : SourceSupported model fallback domain (selected model fallback query) then
        if safe : Safe model fallback domain reference (selected model fallback query) then
          .step query queryExact safe supported (generate fuel (nextCap model fallback query)
            (advance domain fallback (selected model fallback query))
            (Counted.Installation.resume (selected model fallback query)))
        else .rejected query queryExact (rejection model fallback domain reference (selected model fallback query) safe)
      else .unsupported query queryExact (unsupported model fallback domain (selected model fallback query) supported)

namespace Chain
variable {model fallback} {fuel budget : Nat} {domain : List (Cursor model.source.code)}
  {reference : Program model.source.code}

def rules : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → List (Program model.source.code)
  | _,_,_,_,.exhausted => []
  | _,_,_,reference,.complete _ _ => [reference]
  | _,_,_,_,.rejected _ _ _ => []
  | _,_,_,_,.unsupported _ _ _ => []
  | _,_,_,_,.step query _ _ _ tail => selected model fallback query :: tail.rules

def observations : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → List (Nat × Bool)
  | _,_,_,_,.exhausted => []
  | _,_,domain,reference,.complete receipt _ => Closure.Receipt.observations model domain fallback reference receipt
  | _,budget,_,_,.rejected query _ _ => [(budget,query.program?.isSome)]
  | _,budget,_,_,.unsupported query _ _ => [(budget,query.program?.isSome)]
  | _,budget,_,_,.step query _ _ _ tail => (budget,query.program?.isSome) :: tail.observations

def review : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → Bool
  | _,_,_,_,.exhausted => true
  | _,_,domain,reference,.complete receipt _ => Closure.Receipt.review model domain fallback reference receipt
  | _,budget,domain,reference,.unsupported query _ failure =>
    Runtime.review model domain fallback reference budget query && !decide (failure.request ∈ model.source.code.actions)
  | _,budget,domain,reference,.rejected query _ failure =>
    Runtime.review model domain fallback reference budget query &&
      !decide (Selection.holds model domain fallback [reference,selected model fallback query] reference (selected model fallback query) failure.row)
  | _,budget,domain,reference,.step query _ _ _ tail => Runtime.review model domain fallback reference budget query && tail.review

theorem every_new_query_is_independently_reviewable (chain : Chain model fallback fuel budget domain reference) :
    chain.review = true := by
  induction chain with
  | exhausted => rfl
  | complete receipt exact => exact Closure.every_completion_has_independent_source_review model _ fallback _ receipt
  | unsupported query exact failure =>
    simp only [review,Runtime.independently_reviewed,Bool.true_and,Bool.not_eq_true',decide_eq_false_iff_not]
    exact failure.outside
  | rejected query exact failure =>
    simp only [review,Runtime.independently_reviewed,Bool.true_and,Bool.not_eq_true',decide_eq_false_iff_not]
    exact failure.broken
  | step query exact safe supported tail ih => simp only [review,Bool.and_eq_true,Runtime.independently_reviewed,ih,and_self]

def realize : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → Cursor model.source.code →
      Opponent model.source.code → Cursor model.source.code
  | _,_,_,_,.exhausted,point,_ => point
  | _,_,_,reference,.complete _ _,point,environment => after point fallback reference environment 1
  | _,_,_,_,.rejected _ _ _,point,_ => point
  | _,_,_,_,.unsupported _ _ _,point,_ => point
  | _,_,_,_,.step query _ _ _ tail,point,environment =>
    tail.realize (after point fallback (selected model fallback query) environment 1) environment

def finalDomain : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → List (Cursor model.source.code)
  | _,_,domain,_,.exhausted => domain
  | _,_,domain,reference,.complete _ _ => advance domain fallback reference
  | _,_,domain,_,.rejected _ _ _ => domain
  | _,_,domain,_,.unsupported _ _ _ => domain
  | _,_,_,_,.step _ _ _ _ tail => tail.finalDomain

def AllCutsCovered : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,domain,_,.exhausted,point,_ => Covered domain point
  | _,_,domain,reference,.complete _ _,point,environment => Covered domain point ∧
    Covered (advance domain fallback reference) (after point fallback reference environment 1)
  | _,_,domain,_,.rejected _ _ _,point,_ => Covered domain point
  | _,_,domain,_,.unsupported _ _ _,point,_ => Covered domain point
  | _,_,domain,_,.step query _ _ _ tail,point,environment => Covered domain point ∧
    tail.AllCutsCovered (after point fallback (selected model fallback query) environment 1) environment

theorem every_query_uses_its_actual_successor_domain (chain : Chain model fallback fuel budget domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.AllCutsCovered point environment ∧ Covered chain.finalDomain (chain.realize point environment) := by
  induction chain generalizing point with
  | exhausted => exact ⟨covered,covered⟩
  | @complete fuel budget domain reference receipt exact =>
    have next := every_actual_raw_installation_has_a_public_successor _ point covered fallback reference environment
    exact ⟨⟨covered,next⟩,next⟩
  | rejected => exact ⟨covered,covered⟩
  | unsupported => exact ⟨covered,covered⟩
  | step query exact safe supported tail ih =>
    have next := every_actual_raw_installation_has_a_public_successor _ point covered fallback (selected model fallback query) environment
    have continued := ih (after point fallback (selected model fallback query) environment 1) next
    exact ⟨⟨covered,continued.1⟩,continued.2⟩

def AllCutsProtected : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,_,_,.exhausted,_,_ => True
  | _,_,domain,reference,.complete _ _,point,_ => Open.Supported model domain fallback reference ∧
    ∀ rival : Opponent model.source.code,Synthesis.accepts model.source.code (economicAxes point.source point.cut)
      (Finite.actualEvaluation model point fallback reference rival) (Finite.actualEvaluation model point fallback reference rival)
  | _,_,_,_,.rejected _ _ _,_,_ => True
  | _,_,_,_,.unsupported _ _ _,_,_ => True
  | _,_,domain,reference,.step query _ _ _ tail,point,environment =>
    Open.Supported model domain fallback (selected model fallback query) ∧ (∀ rival : Opponent model.source.code,
      Synthesis.accepts model.source.code (economicAxes point.source point.cut)
        (Finite.actualEvaluation model point fallback (selected model fallback query) rival)
        (Finite.actualEvaluation model point fallback reference rival)) ∧
    tail.AllCutsProtected (after point fallback (selected model fallback query) environment 1) environment

private theorem completion_at_actual_cursor (receipt : Closure.Receipt model domain fallback reference budget)
    (point : Cursor model.source.code) (covered : Covered domain point) (rival : Opponent model.source.code) :
    Synthesis.accepts model.source.code (economicAxes point.source point.cut)
      (Finite.actualEvaluation model point fallback reference rival) (Finite.actualEvaluation model point fallback reference rival) := by
  obtain ⟨representative,inside,matched⟩ := covered
  exact (Acceptance.aligned_acceptance model representative point matched rival fallback reference reference).mp
    ((Closure.every_source_generated_completion_covers_the_entire_raw_domain model domain fallback reference receipt).2.1
      ⟨representative,inside⟩ rival)

theorem every_installed_cut_is_accepted_with_its_full_actual_responsibility
    (chain : Chain model fallback fuel budget domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.AllCutsProtected point environment := by
  induction chain generalizing point with
  | exhausted => trivial
  | complete receipt exact =>
    exact ⟨(Closure.every_source_generated_completion_covers_the_entire_raw_domain model _ fallback _ receipt).1,
      completion_at_actual_cursor receipt point covered⟩
  | rejected => trivial
  | unsupported => trivial
  | @step fuel budget domain reference query exact safe supported tail ih =>
    refine ⟨(support_exact model fallback domain _).mp supported,?_,ih (after point fallback (selected model fallback query) environment 1)
      (every_actual_raw_installation_has_a_public_successor _ point covered fallback (selected model fallback query) environment)⟩
    intro rival
    obtain ⟨representative,inside,matched⟩ := covered
    exact (Acceptance.aligned_acceptance model representative point matched rival fallback (selected model fallback query) reference).mp
      ((Selection.acceptable_iff_every_common_external_opponent model domain fallback [reference,selected model fallback query]
        reference (selected model fallback query) (by simp) (by simp)).mp safe ⟨representative,inside⟩ rival)

/-- Replay installed proposals against the actual cursor's own complete finite rows. -/
def replayActual : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference →
      Cursor model.source.code → Opponent model.source.code → Bool
  | _,_,_,_,.exhausted,_,_ => true
  | _,_,_,reference,.complete _ _,point,_ =>
    decide (Selection.acceptable model [point] fallback [reference,reference] reference reference)
  | _,_,_,_,.rejected _ _ _,_,_ => true
  | _,_,_,_,.unsupported _ _ _,_,_ => true
  | _,_,_,reference,.step query _ _ _ tail,point,environment =>
    decide (Selection.acceptable model [point] fallback [reference,selected model fallback query] reference (selected model fallback query)) &&
      tail.replayActual (after point fallback (selected model fallback query) environment 1) environment

theorem every_actual_query_has_an_independent_complete_replay
    (chain : Chain model fallback fuel budget domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) (covered : Covered domain point) :
    chain.replayActual point environment = true := by
  induction chain generalizing point with
  | exhausted => rfl
  | @complete fuel budget domain reference receipt exact =>
    rw [replayActual,decide_eq_true_eq,Selection.acceptable_iff_every_common_external_opponent model [point] fallback
      [reference,reference] reference reference (by simp) (by simp)]
    intro world rival
    have same : world.val = point := List.mem_singleton.mp world.property
    rw [same]
    exact completion_at_actual_cursor receipt point covered rival
  | rejected => rfl
  | unsupported => rfl
  | @step fuel budget domain reference query exact safe supported tail ih =>
    simp only [replayActual,Bool.and_eq_true]
    refine ⟨?_,ih (after point fallback (selected model fallback query) environment 1)
      (every_actual_raw_installation_has_a_public_successor _ point covered fallback (selected model fallback query) environment)⟩
    rw [decide_eq_true_eq,
      Selection.acceptable_iff_every_common_external_opponent model [point] fallback [reference,selected model fallback query]
        reference (selected model fallback query) (by simp) (by simp)]
    intro world rival
    rcases world with ⟨cursor,inside⟩
    have same : cursor = point := List.mem_singleton.mp inside
    subst cursor
    obtain ⟨representative,member,matched⟩ := covered
    exact (Acceptance.aligned_acceptance model representative point matched rival fallback (selected model fallback query) reference).mp
      ((Selection.acceptable_iff_every_common_external_opponent model domain fallback [reference,selected model fallback query]
        reference (selected model fallback query) (by simp) (by simp)).mp safe ⟨representative,member⟩ rival)

def Migrations : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference →
      Cursor model.source.code → Opponent model.source.code → Type
  | _,_,_,_,.exhausted,_,_ => Unit
  | _,_,_,reference,.complete _ _,point,environment => StepNative.Payload model point fallback reference environment
  | _,_,_,_,.rejected _ _ _,_,_ => Unit
  | _,_,_,_,.unsupported _ _ _,_,_ => Unit
  | _,_,_,_,.step query _ _ _ tail,point,environment =>
    StepNative.Payload model point fallback (selected model fallback query) environment ×
      tail.Migrations (after point fallback (selected model fallback query) environment 1) environment

def migrations : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → (chain : Chain model fallback fuel budget domain reference) →
      (point : Cursor model.source.code) → (environment : Opponent model.source.code) → chain.Migrations point environment
  | _,_,_,_,.exhausted,_,_ => ()
  | _,_,_,reference,.complete _ _,point,environment => StepNative.generate model point fallback reference environment
  | _,_,_,_,.rejected _ _ _,_,_ => ()
  | _,_,_,_,.unsupported _ _ _,_,_ => ()
  | _,_,_,_,.step query _ _ _ tail,point,environment =>
    ⟨StepNative.generate model point fallback (selected model fallback query) environment,
      tail.migrations (after point fallback (selected model fallback query) environment 1) environment⟩

theorem realization_is_the_original_paid_fold (chain : Chain model fallback fuel budget domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) :
    chain.realize point environment = Counted.Installation.Chain.fold (fallback := fallback) point environment chain.rules := by
  induction chain generalizing point with
  | exhausted => rfl
  | complete => rfl
  | rejected => rfl
  | unsupported => rfl
  | step query exact safe supported tail ih => exact ih (after point fallback (selected model fallback query) environment 1)

def InstalledPrefixes : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → Cursor model.source.code →
      Opponent model.source.code → Prop
  | _,_,_,_,.exhausted,_,_ => True
  | _,_,_,_,.complete _ _,_,_ => True
  | _,_,_,_,.rejected _ _ _,_,_ => True
  | _,_,_,_,.unsupported _ _ _,_,_ => True
  | _,_,_,_,.step query _ _ _ tail,point,environment =>
    (∀ (current : RawCurrent Party Good (Mandate.State Party Technology) Instrument),
      current.round-model.source.code.initial.round-1 < point.history.length+1+(point.cut+1) →
        (tail.realize (after point fallback (selected model fallback query) environment 1) environment).source.body current =
          (after point fallback (selected model fallback query) environment 1).source.body current) ∧
    tail.InstalledPrefixes (after point fallback (selected model fallback query) environment 1) environment

theorem all_query_updates_are_kept_by_one_actual_source (chain : Chain model fallback fuel budget domain reference)
    (point : Cursor model.source.code) (environment : Opponent model.source.code) : chain.InstalledPrefixes point environment := by
  induction chain generalizing point with
  | exhausted => trivial
  | complete => trivial
  | rejected => trivial
  | unsupported => trivial
  | step query exact safe supported tail ih =>
    refine ⟨?_,ih (after point fallback (selected model fallback query) environment 1)⟩
    intro current earlier
    rw [realization_is_the_original_paid_fold]
    exact Counted.Installation.Chain.fold_keeps_every_prior_emitter_word
      (after point fallback (selected model fallback query) environment 1) environment tail.rules current earlier

def AllCompletions : {fuel budget : Nat} → {domain : List (Cursor model.source.code)} →
    {reference : Program model.source.code} → Chain model fallback fuel budget domain reference → Prop
  | _,_,_,_,.exhausted | _,_,_,_,.unsupported _ _ _ | _,_,_,_,.rejected _ _ _ => True
  | _,_,domain,reference,.complete _ _ => Open.Supported model domain fallback reference ∧
    Bounds.Accepted model domain fallback reference reference ∧
    ∀ raw : Program model.source.code,Open.Supported model domain fallback raw →
      Bounds.Accepted model domain fallback reference raw → ¬ Open.improves model domain fallback reference raw
  | _,_,_,_,.step _ _ _ _ tail => tail.AllCompletions

theorem every_actual_completion_covers_the_entire_supported_raw_domain
    (chain : Chain model fallback fuel budget domain reference) : chain.AllCompletions := by
  induction chain with
  | exhausted => trivial
  | unsupported => trivial
  | rejected => trivial
  | complete receipt exact => exact Closure.every_source_generated_completion_covers_the_entire_raw_domain model _ fallback _ receipt
  | step query exact safe supported tail ih => exact ih

end Chain
end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Continuation
