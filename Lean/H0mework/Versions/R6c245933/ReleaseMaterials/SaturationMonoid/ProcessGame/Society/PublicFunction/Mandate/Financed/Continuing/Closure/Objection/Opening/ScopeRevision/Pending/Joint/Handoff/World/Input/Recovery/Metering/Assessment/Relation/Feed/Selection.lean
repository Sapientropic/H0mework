import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
noncomputable section

namespace Selection
variable {epoch : Epoch} (inventory : Inventory epoch)
  (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit))
  (domain : List (Distributed.Recall.Information.Agency.Protocol.Continuation.Cursor model.source.code))
  (reference : Rule model.source.code) {fuel : Nat}
  (tariff : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Tariff
    (Party := Bool) (Good := Good) (Port := Mandate.Source.Port) (Technology := Unit) (Instrument := Unit))
  (requested : List (List Action))

abbrev Row := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.Row model domain
abbrev rows := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.rows model domain

def holds (original program : Whole.Program model.source.code fuel) (row : Row model domain) : Prop :=
  Feed.Accepts model row.world.val reference inventory requested program original
    (Cut.opponent row.world.val.source row.world.val.entry row.world.val.cut row.table.val) tariff

instance (original program : Whole.Program model.source.code fuel) (row : Row model domain) :
    Decidable (holds inventory model domain reference tariff requested original program row) := by
  unfold holds;infer_instance

def acceptable (original program : Whole.Program model.source.code fuel) : Prop :=
  ∀ row ∈ rows model domain,holds inventory model domain reference tariff requested original program row

instance (original program : Whole.Program model.source.code fuel) :
    Decidable (acceptable inventory model domain reference tariff requested original program) := by
  unfold acceptable;infer_instance

theorem retains_original_acceptance (original program : Whole.Program model.source.code fuel)
    (accepted : acceptable inventory model domain reference tariff requested original program) :
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.acceptable
      (tariff := tariff) (requested := requested) model domain reference original program :=
  fun row member => (accepted row member).1.1

structure Candidate (original : Whole.Program model.source.code fuel) where
  previous : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.Candidate
    (tariff := tariff) (requested := requested) model domain reference original
  accepted : acceptable inventory model domain reference tariff requested original previous.protocol

variable {inventory model domain reference tariff requested}
abbrev Candidate.protocol {original : Whole.Program model.source.code fuel}
    (candidate : Candidate inventory model domain reference tariff requested original) := candidate.previous.protocol
variable (inventory model domain reference tariff requested)

def refine (original : Whole.Program model.source.code fuel)
    (previous : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.Candidate
      (tariff := tariff) (requested := requested) model domain reference original) :
    Option (Candidate inventory model domain reference tariff requested original) :=
  if accepted : acceptable inventory model domain reference tariff requested original previous.protocol then
    some ⟨previous,accepted⟩ else none

def candidates (original : Whole.Program model.source.code fuel) :=
  (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.candidates
    (tariff := tariff) (requested := requested) model domain reference original).filterMap
      (refine inventory model domain reference tariff requested original)

theorem every_jointly_accepted_program_is_in_the_original_pool
    (original program : Whole.Program model.source.code fuel)
    (accepted : acceptable inventory model domain reference tariff requested original program) :
    ∃ candidate ∈ candidates inventory model domain reference tariff requested original,candidate.protocol = program := by
  obtain ⟨previous,member,same⟩ :=
    Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.every_acceptable_program_is_generated
      (tariff := tariff) (requested := requested) model domain reference original program
      (retains_original_acceptance inventory model domain reference tariff requested original program accepted)
  have keep : acceptable inventory model domain reference tariff requested original previous.protocol := same.symm ▸ accepted
  refine ⟨⟨previous,keep⟩,List.mem_filterMap.mpr ⟨previous,member,?_⟩,same⟩
  simp only [refine,dif_pos keep]

abbrev axes := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.axes (fuel := fuel) model
abbrev benefit := Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.benefit (fuel := fuel)
  (tariff := tariff) (requested := requested) model domain reference

abbrev Choice (original : Whole.Program model.source.code fuel) := Distributed.Selected (axes (fuel := fuel) model)
  (fun candidate : Candidate inventory model domain reference tariff requested original =>
    benefit model domain reference tariff requested candidate.protocol)
  (candidates inventory model domain reference tariff requested original)

structure Rejection (original program : Whole.Program model.source.code fuel) where
  row : Row model domain
  generated : row ∈ rows model domain
  broken : ¬ holds inventory model domain reference tariff requested original program row

def Rejection.cause {original program : Whole.Program model.source.code fuel}
    (rejected : Rejection inventory model domain reference tariff requested original program) :=
  Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.Family.explain
    (PresentNoWorse model rejected.row.world.val inventory requested)
    (FutureNoWorse model rejected.row.world.val inventory)
    (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Restoration.required model rejected.row.world.val requested)
    (tensor model rejected.row.world.val reference program
      (Cut.opponent rejected.row.world.val.source rejected.row.world.val.entry rejected.row.world.val.cut rejected.row.table.val) inventory tariff)
    (tensor model rejected.row.world.val reference original
      (Cut.opponent rejected.row.world.val.source rejected.row.world.val.entry rejected.row.world.val.cut rejected.row.table.val) inventory tariff)
    rejected.broken

def rejectionFrom (original program : Whole.Program model.source.code fuel)
    (denied : ¬ acceptable inventory model domain reference tariff requested original program) :
    Rejection inventory model domain reference tariff requested original program :=
  match Distributed.inspect (holds inventory model domain reference tariff requested original program) (rows model domain) with
  | .rejected row member broken => ⟨row,member,broken⟩
  | .accepted all => False.elim (denied all)

inductive Outcome (original : Whole.Program model.source.code fuel) where
  | selected (choice : Choice inventory model domain reference tariff requested original)
  | blocked (rejected : ∀ program : Whole.Program model.source.code fuel,
      Rejection inventory model domain reference tariff requested original program)

/-- The original pool and Pareto engine are retained. Full History admission
is checked for every candidate before the engine selects from that pool. -/
def compile (original : Whole.Program model.source.code fuel) : Outcome inventory model domain reference tariff requested original :=
  match selected : Distributed.choose (axes (fuel := fuel) model)
      (fun candidate : Candidate inventory model domain reference tariff requested original =>
        benefit model domain reference tariff requested candidate.protocol)
      (candidates inventory model domain reference tariff requested original) with
  | some choice => .selected choice
  | none => .blocked fun program => rejectionFrom inventory model domain reference tariff requested original program (by
      intro accepted
      obtain ⟨candidate,member,_⟩ := every_jointly_accepted_program_is_in_the_original_pool
        inventory model domain reference tariff requested original program accepted
      rw [Distributed.choose_none_iff_empty] at selected
      simp only [selected,List.not_mem_nil] at member)

theorem selected_is_jointly_admitted_before_selection (original : Whole.Program model.source.code fuel)
    (choice : Choice inventory model domain reference tariff requested original) (row : Row model domain) :
    holds inventory model domain reference tariff requested original choice.policy.protocol row :=
  choice.policy.accepted row
    (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration.every_row_is_generated _ _ _)


def verify (original program : Whole.Program model.source.code fuel) : Bool :=
  decide (acceptable inventory model domain reference tariff requested original program ∧
    ∀ other ∈ candidates inventory model domain reference tariff requested original,
      ¬ Distributed.Improves (axes (fuel := fuel) model)
        (benefit model domain reference tariff requested) program other.protocol)

theorem selected_is_independently_verified (original : Whole.Program model.source.code fuel)
    (choice : Choice inventory model domain reference tariff requested original) :
    verify inventory model domain reference tariff requested original choice.policy.protocol = true := by
  apply decide_eq_true
  refine ⟨choice.policy.accepted,?_⟩
  intro other member
  exact choice.maximal other member

def review (original : Whole.Program model.source.code fuel)
    (outcome : Outcome inventory model domain reference tariff requested original) : Bool :=
  match outcome with
  | .selected choice => verify inventory model domain reference tariff requested original choice.policy.protocol
  | .blocked rejected => (Whole.programs model.source.code fuel).all fun program =>
      !decide (holds inventory model domain reference tariff requested original program (rejected program).row)

theorem every_generated_outcome_has_its_raw_source_review
    (original : Whole.Program model.source.code fuel)
    (outcome : Outcome inventory model domain reference tariff requested original) :
    review inventory model domain reference tariff requested original outcome = true := by
  cases outcome with
  | selected choice => exact selected_is_independently_verified _ _ _ _ _ _ _ choice
  | blocked rejected =>
      apply List.all_eq_true.mpr
      intro program _
      simp only [Bool.not_eq_true',decide_eq_false_iff_not]
      exact (rejected program).broken

end Selection

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed
