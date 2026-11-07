import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort.Execution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Capture.Contract
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Bounds.System.Envelope

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort

open Source.Program Abolition.Root Abolition.Root.Registered PublicFunction PublicFunction.Repayment
open Redemption (sourceLaw)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))
local notation "Bid" => Position Party Instrument × ℚ

structure Plan (Party Good Port Technology Instrument : Type) where
  preparation : List (Option (Compile.RawInput Party Good Port Technology Instrument))
  tenders : List (Position Party Instrument × ℚ)
  exit : List (Option (Compile.RawInput Party Good Port Technology Instrument))

local notation "Proposal" => Plan Party Good Port Technology Instrument

def fundingStart (source : C) (plan : Proposal) := Execution.endAt source plan.preparation

def allTenders (source : C) (plan : Proposal) := compileBatch (fundingStart source plan) plan.tenders

def paidPrefix (source : C) (plan : Proposal) : Script := plan.preparation ++ allTenders source plan

def chargedPrefix (source : C) (count : Nat) (plan : Proposal) : Script :=
  let front := paidPrefix source plan
  front ++ Execution.originalResponses source front count

def exitStart (source : C) (count : Nat) (plan : Proposal) := Execution.endAt source (chargedPrefix source count plan)

def compile (source : C) (count : Nat) (plan : Proposal) : Script := chargedPrefix source count plan ++ plan.exit

def recipients (plan : Proposal) : List Party := plan.tenders.map fun bid => bid.1.creditor

def PositiveService (task : PublicTaskSpec Party Good) (actor : Party) : Prop :=
  ∃ slot ∈ task.slots, slot.bearer = actor ∧ ∃ lot ∈ slot.goods, 0 < lot.2

def CoversOriginalMembers (source : C) (task : PublicTaskSpec Party Good) (plan : Proposal) : Prop :=
  (∀ actor ∈ source.members, actor ∈ recipients plan) ∧
    (∀ bid ∈ plan.tenders, bid.1.creditor ∈ source.members ∧ bid.1.debtor ∈ source.members) ∧
    (∀ actor ∈ source.members, PositiveService task actor)

inductive PopulationFailure (source : C) (task : PublicTaskSpec Party Good) (plan : Proposal)
  | unpaid (actor : Party) (original : actor ∈ source.members) (absent : actor ∉ recipients plan)
  | unowned (bid : Bid) (original : bid ∈ plan.tenders)
      (absent : ¬ (bid.1.creditor ∈ source.members ∧ bid.1.debtor ∈ source.members))
  | service (actor : Party) (original : actor ∈ source.members) (absent : ¬ PositiveService task actor)

theorem PopulationFailure.refutes {source : C} {task : PublicTaskSpec Party Good} {plan : Proposal}
    (issue : PopulationFailure source task plan) : ¬ CoversOriginalMembers source task plan := by
  intro covered
  cases issue with
  | unpaid actor original absent => exact absent (covered.1 actor original)
  | unowned bid original absent => exact absent (covered.2.1 bid original)
  | service actor original absent => exact absent (covered.2.2 actor original)

private theorem population_failure_has_an_original_bearer
    (source : C) (task : PublicTaskSpec Party Good) (plan : Proposal)
    (failed : ¬ CoversOriginalMembers source task plan) : Nonempty (PopulationFailure source task plan) := by
  classical
  by_cases paid : ∀ actor ∈ source.members, actor ∈ recipients plan
  · by_cases owned : ∀ bid ∈ plan.tenders, bid.1.creditor ∈ source.members ∧ bid.1.debtor ∈ source.members
    · have absent : ¬ ∀ actor ∈ source.members, PositiveService task actor :=
        fun every => failed ⟨paid, owned, every⟩
      obtain ⟨actor, problem⟩ := not_forall.mp absent
      exact ⟨.service actor (Classical.not_imp.mp problem).1 (Classical.not_imp.mp problem).2⟩
    · obtain ⟨bid, problem⟩ := not_forall.mp owned
      exact ⟨.unowned bid (Classical.not_imp.mp problem).1 (Classical.not_imp.mp problem).2⟩
  · obtain ⟨actor, problem⟩ := not_forall.mp paid
    exact ⟨.unpaid actor (Classical.not_imp.mp problem).1 (Classical.not_imp.mp problem).2⟩

def Actionable (source : C) (task : PublicTaskSpec Party Good) (count : Nat) (plan : Proposal) : Prop :=
  CoversOriginalMembers source task plan ∧ FundedBatch (fundingStart source plan) plan.tenders ∧
    (∀ item ∈ Execution.inventory (exitStart source count plan) plan.exit, Independent source [] item) ∧
    Clock.Window.FullyServed (exitStart source count plan) task plan.exit

inductive Issue (source : C) (task : PublicTaskSpec Party Good) (count : Nat) (plan : Proposal)
  | cohort (failed : PopulationFailure source task plan)
  | payment (failed : BatchIssue (fundingStart source plan) plan.tenders)
  | role (item : ExecutionItem Party Good Port Technology Instrument)
      (original : item ∈ Execution.inventory (exitStart source count plan) plan.exit)
      (failed : ¬ Independent source [] item)
  | service (unpaid : Clock.Window.Shortage (exitStart source count plan) task plan.exit)

theorem Issue.refutes {source : C} {task : PublicTaskSpec Party Good} {count : Nat} {plan : Proposal}
    (issue : Issue source task count plan) : ¬ Actionable source task count plan := by
  rintro ⟨cohort, paid, roles, service⟩
  cases issue with
  | cohort missing => exact missing.refutes cohort
  | payment missing => exact missing.refutes paid
  | role item original failed => exact failed (roles item original)
  | service missing => exact missing.refutes service

def inspect (source : C) (task : PublicTaskSpec Party Good) (count : Nat) (plan : Proposal) :
    Option (Issue source task count plan) :=
  letI : Decidable (CoversOriginalMembers source task plan) := by
    unfold CoversOriginalMembers PositiveService
    infer_instance
  if cohort : CoversOriginalMembers source task plan then
    match decideBatch (fundingStart source plan) plan.tenders with
    | .blocked issue => some (.payment issue)
    | .paid _ =>
      match Material.inspectList (Independent source []) (Execution.inventory (exitStart source count plan) plan.exit) with
      | .failure item original failed => some (.role item original failed)
      | .clear _ => (Clock.Window.inspect (exitStart source count plan) task plan.exit).map .service
  else some (.cohort (Classical.choice (population_failure_has_an_original_bearer source task plan cohort)))

theorem inspection_is_exact_for_the_original_population
    (source : C) (task : PublicTaskSpec Party Good) (count : Nat) (plan : Proposal) :
    inspect source task count plan = none ↔ Actionable source task count plan := by
  constructor
  · intro clear
    unfold inspect at clear
    split at clear
    · rename_i cohort
      split at clear
      · contradiction
      · rename_i paid _
        split at clear
        · contradiction
        · rename_i independent _
          have absent := Option.map_eq_none_iff.mp clear
          exact ⟨cohort, paid, independent, (Clock.Window.passes_iff_every_original_service_commits_in_time _ _ _).mp absent⟩
    · contradiction
  · intro completed
    cases actual : inspect source task count plan with
    | none => rfl
    | some issue => exact (issue.refutes completed).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Cohort
