import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Execution
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Regression

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Source
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

abbrev code := {Search.Regression.code with
  actions := [Search.Regression.meter]
  bootstrap := Search.Regression.code.bootstrap ++ [Search.Regression.meter]}
abbrev rival : Opponent code := fun _ _ _ => none
def idle : code.Policy := fun _ _ => []
theorem idle_generated : idle ∈ code.policies := by
  apply code.every_local_policy_is_enumerated
  intro key _
  exact (mem_words_iff _ _ _).mpr (by simp [idle])
def cursor (budget : Nat) : Cursor code :=
  ⟨idle,idle_generated,code.publicPrefix,code.public_prefix_is_an_actual_generated_history,
    rival,.original,⟨rival,budget⟩,[],0,code.publicPrefix.length+1⟩
def point (budget : Nat) : View (code := code) := ⟨cursor budget,⟨arrival (cursor budget),by omega⟩⟩
def model (budget : Nat) : Native.Authority.Bound (Party := Bool) (Good := Bool)
    (Port := Budget.Programme.Flow.Regression.Port) (Technology := Unit) (Instrument := Unit) :=
  ⟨Budget.Programme.Flow.Regression.base,Budget.Programme.Flow.Regression.scope,(cursor budget).source,rfl,rfl⟩
abbrev domain (budget : Nat) := [cursor budget]
abbrev original : Rule code := Replay.protocol 0 [Search.Regression.meter] ((mem_words_iff _ _ _).mpr (by simp))
def baseline (budget : Nat) : Program code (horizon (domain budget)) :=
  ⟨List.replicate budget original,by simp only [List.length_replicate];change budget ≤ max budget 0;exact Nat.le_max_left _ _⟩
def task (budget : Nat) : Task (Party := Bool) (Good := Bool)
    (Port := Budget.Programme.Flow.Regression.Port) (Technology := Unit) (Instrument := Unit) where
  model := model budget
  domain := domain budget
  original := original
  baseline := baseline budget
  point := point budget
  rival := rival
  reader := ⟨0,by change 0 < 1;decide⟩
  quote := ⟨[],[Search.Regression.meter]⟩
  vocabulary := ⟨fun _ => none,fun _ => 0,false⟩
  encoding := fun _ => none
  law := ⟨fun _ _ => ⟨0,0,0⟩,1⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (input : Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

/-- The learner starts from every declared public possibility, never a selected actual world. -/
def initialBeliefs : List (View (code := input.model.source.code)) :=
  input.domain.map fun point => ⟨point,⟨arrival point,by omega⟩⟩

inductive Seed where
  | rejected (reason : Selection.Rejection input.model input.domain input.original input.baseline input.baseline)
  | accepted (cache : Cache input) (empty : cache.past = [])
      (programme : cache.programme = input.baseline) (beliefs : cache.beliefs = initialBeliefs input)

/-- The installed verifier decides the full original relation; success constructs the original cache. -/
def seed : Seed input :=
  letI := input.initialVerifier
  if checked : Selection.acceptable input.model input.domain input.original input.baseline input.baseline then
    .accepted {
      past := []
      programme := input.baseline
      beliefs := initialBeliefs input
      within := Nat.zero_le _
      actualWithin := Nat.zero_le _
      retained := rfl
      above := checked
      planner := input.planner} rfl rfl rfl
  else
    match Distributed.inspect (Selection.holds input.model input.domain input.original input.baseline input.baseline)
        (Replanning.rows input.model input.domain) with
    | .rejected row generated broken => .rejected ⟨row,generated,broken⟩
    | .accepted all => False.elim (checked all)

abbrev Response := Sum (Selection.Rejection input.model input.domain input.original input.baseline input.baseline) (Cache input)

abbrev Generated := Sum (Selection.Rejection input.model input.domain input.original input.baseline input.baseline)
  (Cache input × List Report)

/-- The seed, paid walk and reports have one source-owned computation. -/
def generate (rounds : Nat) : Generated input := match seed input with
  | .rejected reason => .inl reason
  | .accepted cache _ _ _ => .inr (Owned.trace input rounds cache)
/-- One source computation owns both success and rejection, not a caller-selected successful cache. -/
structure Occurrence (rounds : Nat) where
  generated : Generated input
  exact_generation : generated = generate input rounds

def occurrence (rounds : Nat) : Occurrence input rounds := ⟨generate input rounds,rfl⟩

namespace Occurrence
variable {input} {rounds : Nat}
abbrev response (made : Occurrence input rounds) : Response input := match made.generated with
  | .inl reason => .inl reason
  | .inr actual => .inr actual.1
abbrev reports (made : Occurrence input rounds) := match made.generated with
  | .inl _ => []
  | .inr actual => actual.2
abbrev controls (made : Occurrence input rounds) := match made.response with
  | .inl _ => []
  | .inr cache => cache.past
end Occurrence

abbrev response (rounds : Nat) : Response input := match generate input rounds with
  | .inl reason => .inl reason
  | .inr actual => .inr actual.1
abbrev reports (rounds : Nat) := match generate input rounds with
  | .inl _ => []
  | .inr actual => actual.2

abbrev controls (rounds : Nat) := match response input rounds with
  | .inl _ => []
  | .inr cache => cache.past
abbrev full (rounds : Nat) := Splice.install input.point.point input.rival (controls input rounds)

theorem the_generated_final_cache_protects_every_original_responsibility (rounds : Nat) :
    match response input rounds with
    | .inl _ => True
    | .inr cache => Selection.acceptable input.model input.domain input.original input.baseline cache.programme := by
  cases made : response input rounds with
  | inl => trivial
  | inr cache => exact cache.above

theorem the_generated_cache_current_is_the_same_actual_source (rounds : Nat) :
    match response input rounds with
    | .inl _ => True
    | .inr cache => (cache.current input.point input.rival).point = full input rounds := by
  cases made : response input rounds with
  | inl => trivial
  | inr cache =>
      change (cache.current input.point input.rival).point = full input rounds
      rw [Paid.State.current_is_the_actual_control_prefix]
      simp only [full,controls,made]

theorem every_generated_feedback_chain_keeps_actual_public_knowledge (rounds : Nat)
    (covered : Knowledge.Contains (initialBeliefs input) input.point) :
    match response input rounds with
    | .inl _ => True
    | .inr cache => Knowledge.Contains cache.beliefs (cache.current input.point input.rival) := by
  unfold response generate
  cases seed input with
  | rejected => trivial
  | accepted cache empty programme beliefs =>
      change Knowledge.Contains (Owned.trace input rounds cache).1.beliefs
        ((Owned.trace input rounds cache).1.current input.point input.rival)
      rw [Owned.trace_is_the_original_run_and_reports]
      apply Owned.the_whole_run_preserves_actual_origin_knowledge
      simpa only [Paid.State.current,empty,Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Observed.Transcript.actualView,List.foldl_nil,beliefs] using covered

theorem the_concrete_public_source_generates_its_own_initial_knowledge (budget : Nat) :
    Knowledge.Contains (initialBeliefs (task budget)) (task budget).point := by
  apply Knowledge.member
  change point budget ∈ [point budget]
  exact List.mem_cons_self

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.Source
