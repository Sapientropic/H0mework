import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Prepaid
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Refinement
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}
  {source : SourceQuota.Generated prepared} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue}
variable (domain : List (Candidate all)) (reference : Candidate all)
def Eligible (candidate : Candidate all) := Distributed.NoWorse (axes all) cost candidate reference
instance (candidate : Candidate all) : Decidable (Eligible reference candidate) := inferInstanceAs (Decidable (Distributed.NoWorse _ _ _ _))
def filtered (items : List (Candidate all)) := items.filter fun candidate => decide (Eligible reference candidate)
private theorem member (candidate : Candidate all) : candidate ∈ filtered reference domain ↔ candidate ∈ domain ∧ Eligible reference candidate := by simp only [filtered,List.mem_filter,decide_eq_true_eq]

structure Resolution where
  private mk ::
  selected : Distributed.Selected (axes all) cost domain
  no_worse : Eligible reference selected.policy

inductive State where
  | gathering (remaining cached : List (Candidate all)) (conserved : cached ++ filtered reference remaining = filtered reference domain)
  | checking (candidate : Candidate all) (rest cached : List (Candidate all))
      (conserved : cached ++ filtered reference (candidate::rest) = filtered reference domain)
      (todo : List (Axis all)) (within : ∀ axis ∈ todo,axis ∈ axes all)
      (passed : (∀ axis ∈ todo,cost candidate axis ≤ cost reference axis) → Eligible reference candidate)
  | searching (cached : List (Candidate all)) (complete : cached = filtered reference domain) (current : Machine.Scanner.Search cached)

def initial : State domain reference := .gathering domain [] rfl
inductive Control | enter | accept | beginSearch
inductive Event where
  | control (operation : Control)
  | yes (candidate : Candidate all) (axis : Axis all) (actual : cost candidate axis ≤ cost reference axis)
  | no (candidate : Candidate all) (axis : Axis all) (actual : ¬ cost candidate axis ≤ cost reference axis)
  | search (cached : List (Candidate all)) (operation : Machine.Scanner.Action (domain := cached))

private theorem pass_cons {candidate : Candidate all} {head : Axis all} {tail : List (Axis all)}
    (passed : cost candidate head ≤ cost reference head) (later : ∀ axis ∈ tail,cost candidate axis ≤ cost reference axis) :
    ∀ axis ∈ head::tail,cost candidate axis ≤ cost reference axis := by
  intro axis inside
  rcases List.mem_cons.mp inside with same | rest
  · subst axis;exact passed
  · exact later axis rest

def move : State domain reference → Option (State domain reference × Event reference)
  | .gathering [] cached conserved =>
      some (.searching cached (by simpa only [filtered,List.filter_nil,List.append_nil] using conserved) (Machine.Scanner.start cached),.control .beginSearch)
  | .gathering (candidate::rest) cached conserved =>
      some (.checking candidate rest cached conserved (axes all) (fun _ inside => inside) (fun checked => checked),.control .enter)
  | .checking candidate rest cached conserved [] _ passed =>
      let valid := passed (by intro axis inside;cases inside)
      some (.gathering rest (cached++[candidate]) (by
          rw [List.append_assoc]
          simpa only [filtered,List.filter_cons,decide_eq_true valid,ite_true,List.singleton_append] using conserved),.control .accept)
  | .checking candidate rest cached conserved (head::tail) within passed =>
      if valid : cost candidate head ≤ cost reference head then
        some (.checking candidate rest cached conserved tail
          (fun axis inside => within axis (List.mem_cons_of_mem _ inside))
          (fun later => passed (pass_cons reference valid later)),.yes candidate head valid)
      else
        let failed : ¬ Eligible reference candidate := fun allowed => valid (allowed head (within head List.mem_cons_self))
        some (.gathering rest cached (by
          simpa only [filtered,List.filter_cons,decide_eq_false failed,Bool.false_eq_true,ite_false] using conserved),.no candidate head valid)
  | .searching cached complete current => match actual : Machine.Scanner.move cached current with
    | none => none
    | some (after,event) => some (.searching cached complete after,.search cached event)

def State.finished : State domain reference → Bool
  | .gathering .. | .checking .. => false
  | .searching cached _ current => current.finished cached
def searchBound := 1+domain.length*(1+domain.length*(2*(axes all).length+3)+2)
def State.rank : State domain reference → Nat
  | .gathering remaining .. => remaining.length*((axes all).length+2)+searchBound domain+2
  | .checking _ rest _ _ todo .. => rest.length*((axes all).length+2)+todo.length+searchBound domain+3
  | .searching cached _ current => current.rank cached

theorem step_progresses {before after : State domain reference} {event : Event reference}
    (actual : move domain reference before = some (after,event)) : after.rank domain reference < before.rank domain reference := by
  cases before with
  | gathering remaining cached conserved =>
    cases remaining with
    | nil =>
      dsimp only [move] at actual;cases Option.some.inj actual
      have equality : cached = filtered reference domain := by simpa only [filtered,List.filter_nil,List.append_nil] using conserved
      have bound : cached.length ≤ domain.length := by rw [equality];exact List.length_filter_le _ _
      have a := Nat.mul_le_mul_right (2*(axes all).length+3) bound
      have b := Nat.mul_le_mul bound (Nat.add_le_add_right (Nat.add_le_add_left a 1) 2)
      simp only [State.rank,Machine.Scanner.start,Machine.Scanner.Search.rank,Machine.Scanner.policies,List.length_attach,Machine.Scanner.innerBound,searchBound,List.length_nil,Nat.zero_mul]
      omega
    | cons candidate rest =>
      dsimp only [move] at actual;cases Option.some.inj actual
      simp only [State.rank,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  | checking candidate rest cached conserved todo within passed =>
    cases todo with
    | nil =>
      dsimp only [move] at actual;cases Option.some.inj actual
      simp only [State.rank,List.length_nil];omega
    | cons head tail =>
      dsimp only [move] at actual;split at actual
      all_goals cases Option.some.inj actual
      all_goals simp only [State.rank,List.length_cons]
      all_goals omega
  | searching cached complete current =>
    dsimp only [move] at actual;split at actual
    · cases actual
    · rename_i after event observed
      cases Option.some.inj actual
      exact Machine.Scanner.each_search_step_decreases_the_source_rank cached observed

theorem stopped_iff_finished (state : State domain reference) : move domain reference state = none ↔ state.finished domain reference = true := by
  cases state with
  | gathering remaining cached conserved => cases remaining <;> simp [move,State.finished]
  | checking candidate rest cached conserved todo within passed =>
    cases todo <;> dsimp only [move,State.finished]
    · simp
    · split <;> simp
  | searching cached complete current =>
    dsimp only [move,State.finished];split
    · rename_i stopped;simp only [true_iff];exact (Machine.Scanner.move_none_iff_finished cached current).mp stopped
    · rename_i after event actual
      simp only [reduceCtorEq,false_iff]
      intro finished
      have stopped := (Machine.Scanner.move_none_iff_finished cached current).mpr finished
      rw [stopped] at actual;cases actual

def State.resolution : State domain reference → Option (Resolution domain reference)
  | .gathering .. | .checking .. => none
  | .searching cached complete current => match current.selection cached with
    | none => none
    | some chosen =>
      let listed := (member domain reference chosen.policy).mp (complete ▸ chosen.original)
      some ⟨⟨chosen.policy,listed.1,by
          intro other inside strict
          apply chosen.maximal other
            (by rw [complete];exact (member domain reference other).mpr ⟨inside,Distributed.noWorse_trans strict.1 listed.2⟩)
          exact strict⟩,listed.2⟩

theorem Resolution.available_strict_improvement_is_actual (answer : Resolution domain reference)
    (available : ∃ other ∈ domain,Distributed.Improves (axes all) cost reference other) :
    Distributed.Improves (axes all) cost reference answer.selected.policy := by
  refine ⟨answer.no_worse,?_⟩
  intro backwards
  obtain ⟨other,inside,strict⟩ := available
  apply answer.selected.maximal other inside
  exact ⟨Distributed.noWorse_trans strict.1 backwards,fun reverse => strict.2 (Distributed.noWorse_trans backwards reverse)⟩

theorem finished_with_listed_reference_has_a_resolution (listed : reference ∈ domain) (state : State domain reference)
    (finished : state.finished domain reference = true) : (state.resolution domain reference).isSome = true := by
  cases state with
  | gathering | checking => cases finished
  | searching cached complete current =>
    cases current with
    | candidates | checking => cases finished
    | released => rfl
    | excluded rejected =>
      have empty := Machine.Scanner.Search.excluded_means_empty cached rejected
      have retained : reference ∈ cached := by
        rw [complete]
        exact (member domain reference reference).mpr ⟨listed,by intro axis _;exact le_refl _⟩
      rw [empty] at retained;cases retained

inductive Trace (domain : List (Candidate all)) (reference : Candidate all) : State domain reference → State domain reference → List (Event reference) → Prop
  | nil (state) : Trace domain reference state state []
  | step {before middle after event work} (actual : move domain reference before = some (middle,event))
      (later : Trace domain reference middle after work) : Trace domain reference before after (event::work)
structure Calculation (domain : List (Candidate all)) (reference : Candidate all) (before : State domain reference) (capacity : Nat) where
  private mk ::
  endpoint : State domain reference
  work : List (Event reference)
  history : Trace domain reference before endpoint work
  fits : work.length ≤ capacity
def execute : (capacity : Nat) → (before : State domain reference) → Calculation domain reference before capacity
  | 0,before => ⟨before,[],.nil before,by rfl⟩
  | capacity+1,before => match actual : move domain reference before with
    | none => ⟨before,[],.nil before,Nat.zero_le _⟩
    | some (after,event) => let later := execute capacity after
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.fits;simpa only [List.length_cons] using Nat.succ_le_succ this⟩
theorem sufficient_source_rank_finishes (capacity : Nat) (before : State domain reference) (enough : before.rank domain reference ≤ capacity) :
    (execute domain reference capacity before).endpoint.finished domain reference = true := by
  induction capacity generalizing before with
  | zero =>
    cases before with
    | gathering | checking => simp only [State.rank] at enough;omega
    | searching cached complete current => exact Machine.Scanner.source_rank_completes_the_entire_domain_search cached 0 current enough
  | succ capacity ih =>
    unfold execute;split
    · rename_i stopped;exact (stopped_iff_finished domain reference before).mp stopped
    · rename_i after event actual
      exact ih after (by have smaller := step_progresses domain reference actual;omega)
theorem unfinished_spends_all (capacity : Nat) (before : State domain reference)
    (unfinished : (execute domain reference capacity before).endpoint.finished domain reference = false) :
    (execute domain reference capacity before).work.length = capacity := by
  induction capacity generalizing before with
  | zero => rfl
  | succ capacity ih =>
    unfold execute at unfinished ⊢;split at unfinished
    · rename_i stopped
      rw [(stopped_iff_finished domain reference before).mp stopped] at unfinished
      cases unfinished
    · rename_i after event actual;exact congrArg Nat.succ (ih after unfinished)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Refinement
