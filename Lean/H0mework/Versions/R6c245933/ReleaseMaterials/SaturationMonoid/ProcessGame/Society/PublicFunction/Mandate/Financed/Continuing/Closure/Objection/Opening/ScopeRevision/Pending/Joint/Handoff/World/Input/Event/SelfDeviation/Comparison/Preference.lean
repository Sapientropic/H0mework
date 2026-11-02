import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
namespace Observation
variable {first : Packet}
def kind (observed : Observation first) := observed.inherited.kind observed.incoming observed.trace
def clock (observed : Observation first) := (current observed.packet.1 observed.packet.2.inputs).clock
end Observation

inductive Domain
  | response
  | paidWindow
  deriving DecidableEq

/-- The paid-window domain checks actual service and the exact clock. The
response domain instead retains each branch's own actual timing. -/
def Compatible {first : Packet} (domain : Domain) (old new : Observation first) : Prop :=
  match domain with
  | .response => True
  | .paidWindow => old.kind = .paid ∧ new.kind = .paid ∧ old.clock = new.clock

instance {first : Packet} (domain : Domain) (old new : Observation first) : Decidable (Compatible domain old new) := by
  cases domain <;> unfold Compatible <;> infer_instance

theorem paid_window_failure_is_exact {first : Packet} (old new : Observation first) :
    ¬ Compatible .paidWindow old new ↔ old.kind ≠ .paid ∨ new.kind ≠ .paid ∨ old.clock ≠ new.clock := by
  classical
  simp only [Compatible,not_and_or]

theorem paid_window_has_actual_service_for_every_original_task {first : Packet} (old new : Observation first)
    (accepted : Compatible .paidWindow old new) :
    Nonempty (InheritedResponse.Paid old.incoming old.trace) ∧
      Nonempty (InheritedResponse.Paid new.incoming new.trace) :=
  ⟨InheritedResponse.Result.paid_has_a_full_inherited_witness old.incoming old.trace old.inherited accepted.1,
    InheritedResponse.Result.paid_has_a_full_inherited_witness new.incoming new.trace new.inherited accepted.2.1⟩

/-- A declared preference reads the complete generated source observation.
It is never an argument to the source, law, input menu or response runtime. -/
abbrev Utility (first : Packet) := Observation first → Bool → ℚ

variable {first : Packet} {epoch : Epoch} (inventory : Inventory epoch) (intent : Input.Intent) (actor : Bool)
  (earlier : Evolution first ⟨epoch,inventory⟩) (domain : Domain) (utility : Utility first)

def profitable : List (Candidate inventory actor) :=
  (candidates inventory actor).filter fun permit => decide (
    Compatible domain (baseline inventory intent actor earlier) (alternative inventory intent actor earlier permit) ∧
      utility (baseline inventory intent actor earlier) actor < utility (alternative inventory intent actor earlier permit) actor)

theorem profitable_exact (permit : Candidate inventory actor) :
    permit ∈ profitable inventory intent actor earlier domain utility ↔
      permit ∈ candidates inventory actor ∧
      Compatible domain (baseline inventory intent actor earlier) (alternative inventory intent actor earlier permit) ∧
      utility (baseline inventory intent actor earlier) actor < utility (alternative inventory intent actor earlier permit) actor := by
  simp only [profitable,List.mem_filter,decide_eq_true_eq]

theorem empty_iff_no_declared_improvement :
    profitable inventory intent actor earlier domain utility = [] ↔
      ∀ permit ∈ candidates inventory actor,
        Compatible domain (baseline inventory intent actor earlier) (alternative inventory intent actor earlier permit) →
          utility (alternative inventory intent actor earlier permit) actor ≤ utility (baseline inventory intent actor earlier) actor := by
  constructor
  · intro empty permit generated compatible
    by_contra denied
    have inside := (profitable_exact inventory intent actor earlier domain utility permit).mpr
      ⟨generated,compatible,lt_of_not_ge denied⟩
    simp only [empty,List.not_mem_nil] at inside
  · intro stable
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro permit inside
    obtain ⟨generated,compatible,strict⟩ := (profitable_exact inventory intent actor earlier domain utility permit).mp inside
    exact (not_lt_of_ge (stable permit generated compatible)) strict

inductive Verdict where
  | private stable (checked : profitable inventory intent actor earlier domain utility = [])
  | private improvement (permit : Candidate inventory actor) (generated : permit ∈ candidates inventory actor)
      (compatible : Compatible domain (baseline inventory intent actor earlier) (alternative inventory intent actor earlier permit))
      (strict : utility (baseline inventory intent actor earlier) actor < utility (alternative inventory intent actor earlier permit) actor)

def classify : Verdict inventory intent actor earlier domain utility :=
  match checked : profitable inventory intent actor earlier domain utility with
  | [] => .stable checked
  | permit :: tail =>
      have inside : permit ∈ profitable inventory intent actor earlier domain utility := by rw [checked]; exact List.mem_cons_self
      let facts := (profitable_exact inventory intent actor earlier domain utility permit).mp inside
      .improvement permit facts.1 facts.2.1 facts.2.2

def Verdict.isStable : Verdict inventory intent actor earlier domain utility → Bool
  | .stable _ => true
  | .improvement .. => false

theorem classified_stability_is_the_computed_empty_list :
    (classify inventory intent actor earlier domain utility).isStable inventory intent actor earlier domain utility = true ↔
      profitable inventory intent actor earlier domain utility = [] := by
  unfold classify
  split
  · simp_all [Verdict.isStable]
  · simp_all [Verdict.isStable]

/-- Single-good declared accounting payoff. All remaining actual consequences
are read by `other`; this declares values, not convertibility or authority. -/
def netPayoff (unit : Good) (other : Utility first) : Utility first :=
  fun observed party => other observed party - observed.netExpense party unit

theorem checked_stability_bounds_actual_net_expense (unit : Good) (other : Utility first)
    (checked : (classify inventory intent actor earlier domain (netPayoff unit other)).isStable inventory intent actor earlier domain (netPayoff unit other) = true)
    (permit : Candidate inventory actor) (generated : permit ∈ candidates inventory actor)
    (compatible : Compatible domain (baseline inventory intent actor earlier) (alternative inventory intent actor earlier permit)) :
    (baseline inventory intent actor earlier).netExpense actor unit ≤
      (alternative inventory intent actor earlier permit).netExpense actor unit +
        other (baseline inventory intent actor earlier) actor - other (alternative inventory intent actor earlier permit) actor := by
  have empty := (classified_stability_is_the_computed_empty_list inventory intent actor earlier domain (netPayoff unit other)).mp checked
  have stable := (empty_iff_no_declared_improvement inventory intent actor earlier domain (netPayoff unit other)).mp empty permit generated compatible
  unfold netPayoff at stable
  linarith

theorem flat_preferences_have_no_profitable_option :
    profitable inventory intent actor earlier domain (fun _ _ => 0) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro permit inside
  have facts := (profitable_exact inventory intent actor earlier domain (fun _ _ => 0) permit).mp inside
  exact (lt_irrefl (0 : ℚ)) facts.2.2

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation.Comparison
