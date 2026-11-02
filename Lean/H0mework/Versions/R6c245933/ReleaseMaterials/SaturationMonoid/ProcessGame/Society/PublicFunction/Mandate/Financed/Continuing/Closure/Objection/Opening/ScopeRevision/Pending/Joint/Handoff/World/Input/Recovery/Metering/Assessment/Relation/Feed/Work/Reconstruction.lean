import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Lookup
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Task
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Communication.Capability

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Reconstruction
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit))

abbrev Program := Whole.Program prior.model.source.code (horizon prior.domain)
abbrev Row := Fin (Feed.Selection.rows prior.model prior.domain).length
abbrev row (index : Row prior) := (Feed.Selection.rows prior.model prior.domain)[index]
abbrev queries (index : Row prior) := Restoration.required prior.model (row prior index).world.val prior.futureRequests

structure Axis where
  row : Row prior
  query : Fin (queries prior row).length
  intent : {intent : Intent // intent ∈ ScopeForecast.intents}

def axes : List (Axis prior) :=
  (List.finRange (Feed.Selection.rows prior.model prior.domain).length).flatMap fun row =>
    (List.finRange (queries prior row).length).flatMap fun query =>
      ScopeForecast.intents.attach.map fun intent => ⟨row,query,intent⟩

theorem every_original_axis_is_generated (axis : Axis prior) : axis ∈ axes prior :=
  List.mem_flatMap.mpr ⟨axis.row,List.mem_finRange _,List.mem_flatMap.mpr
    ⟨axis.query,List.mem_finRange _,List.mem_map.mpr ⟨axis.intent,List.mem_attach _ _,rfl⟩⟩⟩

def oldCursor (program : Program prior) (axis : Axis prior) :=
  Feed.continuation prior (row prior axis.row).world.val program
    (Cut.opponent (row prior axis.row).world.val.source (row prior axis.row).world.val.entry
      (row prior axis.row).world.val.cut (row prior axis.row).table.val)

variable {epoch : Epoch} (inventory : Inventory epoch)
  (original : Work.Batch prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing)

def port (program : Program prior) (axis : Axis prior) :=
  ((Lookup.cell original axis.row program).scopeForecast axis.query).read axis.intent.val

abbrev View (program : Program prior) (axis : Axis prior) :=
  TaskSource.Communication.Capability.Snapshot prior
    (port prior inventory original program axis).next.saved.2
    (port prior inventory original program axis).next.pending (oldCursor prior program axis)

def makeView (program : Program prior) (axis : Axis prior) : View prior inventory original program axis :=
  TaskSource.Communication.Capability.generate prior _ _ _

def origin (program : Program prior) (axis : Axis prior) (position : Fin (prior.domain.length+1)) :=
  (oldCursor prior program axis :: prior.domain)[position]

def preparedWindow (program : Program prior) (axis : Axis prior) (position : Fin (prior.domain.length+1)) :
    Window (⟨epoch,inventory⟩ : Packet) :=
  let actual := port prior inventory original program axis
  let old := origin prior program axis position
  ⟨⟨actual.next.saved.1,TaskSource.Communication.Source.saved actual.next.saved.2 old⟩,
    .append (ScopeForecast.after actual).native (TaskSource.Communication.Source.native actual.next.saved.2 old)⟩

/-- The full directory is indexed by the original source positions. Its ports
come from the original cached Reports; no Report or joint response is regenerated. -/
structure Batch where
  private mk ::
  view : (program : Program prior) → (axis : Axis prior) → View prior inventory original program axis
  generated : view = makeView prior inventory original

def execute : Batch prior inventory original := ⟨makeView prior inventory original,rfl⟩

variable {prior inventory original}
def Holds (batch : Batch prior inventory original) (previous program : Program prior) (axis : Axis prior) : Prop :=
  (∀ position ∈ List.finRange (prior.domain.length+1),
    Window.NoWorse (preparedWindow prior inventory original program axis position)
      (preparedWindow prior inventory original previous axis position)) ∧
  TaskSource.Communication.Capability.NoWorse (batch.view program axis) (batch.view previous axis)

instance (batch : Batch prior inventory original) (previous program : Program prior) (axis : Axis prior) :
    Decidable (Holds batch previous program axis) := by unfold Holds;infer_instance

def Accepts (batch : Batch prior inventory original) (previous program : Program prior) : Prop :=
  ∀ axis ∈ axes prior,Holds batch previous program axis

instance (batch : Batch prior inventory original) (previous program : Program prior) :
    Decidable (Accepts batch previous program) := by unfold Accepts;infer_instance

structure Rejection (batch : Batch prior inventory original) (previous program : Program prior) where
  axis : Axis prior
  generated : axis ∈ axes prior
  broken : ¬ Holds batch previous program axis

def rejectionFrom (batch : Batch prior inventory original) (previous program : Program prior)
    (failed : ¬ Accepts batch previous program) : Rejection batch previous program :=
  match Distributed.inspect (Holds batch previous program) (axes prior) with
  | .rejected axis generated broken => ⟨axis,generated,broken⟩
  | .accepted kept => False.elim (failed kept)

theorem accepts_refl (batch : Batch prior inventory original) (program : Program prior) :
    Accepts batch program program := fun _ _ =>
  ⟨fun _ _ => Window.noWorse_refl _,TaskSource.Communication.Capability.noWorse_refl _⟩

theorem every_original_axis_is_preserved (batch : Batch prior inventory original)
    (previous program : Program prior) (accepted : Accepts batch previous program) (axis : Axis prior) :
    Holds batch previous program axis := accepted axis (every_original_axis_is_generated prior axis)

variable (prior)
/-- Declared services: every rebuilt cursor, Task compilation, source admission,
and every original programme assessment. Raw fees stay in preparedWindow. -/
def snapshotServices : Nat := prior.domain.length+1+1+1+
  (TaskSource.Communication.Capability.catalogue prior).length

def comparisonServices : Nat := prior.domain.length+1+1

def queryCount : Nat := ((Replanning.points prior.model prior.domain).map fun world =>
  tableCount world.val * (Restoration.required prior.model world.val prior.futureRequests).length).sum

private theorem queryCount_rows : queryCount prior =
    ((Feed.Selection.rows prior.model prior.domain).map fun row =>
      (Restoration.required prior.model row.world.val prior.futureRequests).length).sum := by
  have one (world : Replanning.Point prior.model prior.domain)
      (pool : List (Replanning.TableAt prior.model prior.domain world)) :
      ((pool.map fun table => (⟨world,table⟩ : Feed.Selection.Row prior.model prior.domain)).map
        fun row => (Restoration.required prior.model row.world.val prior.futureRequests).length).sum =
      pool.length * (Restoration.required prior.model world.val prior.futureRequests).length := by
    induction pool with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
        simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm]
  have all (worlds : List (Replanning.Point prior.model prior.domain)) :
      (worlds.map fun world => tableCount world.val *
        (Restoration.required prior.model world.val prior.futureRequests).length).sum =
      ((worlds.flatMap fun world => (Cut.tables world.val.source world.val.entry world.val.cut).attach.map
        fun table => (⟨world,table⟩ : Feed.Selection.Row prior.model prior.domain)).map
          fun row => (Restoration.required prior.model row.world.val prior.futureRequests).length).sum := by
    induction worlds with
    | nil => rfl
    | cons world later ih =>
        simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,
          one,List.length_attach]
        rw [ih,tableCount_exact]
  exact all _

theorem axes_count : (axes prior).length = queryCount prior * ScopeForecast.intents.length := by
  have inner (count : Nat) :
      ((List.finRange count).map fun _ => ScopeForecast.intents.length).sum =
        count * ScopeForecast.intents.length := by simp
  have indexed : ((List.finRange (Feed.Selection.rows prior.model prior.domain).length).map
      fun index => (queries prior index).length) =
      ((Feed.Selection.rows prior.model prior.domain).map fun row =>
        (Restoration.required prior.model row.world.val prior.futureRequests).length) := by
    rw [←List.ofFn_eq_map]
    exact List.ofFn_getElem_eq_map (Feed.Selection.rows prior.model prior.domain)
      (fun row => (Restoration.required prior.model row.world.val prior.futureRequests).length)
  simp only [axes,List.length_flatMap,List.length_map,List.length_attach,inner]
  rw [List.sum_map_mul_right,indexed,←queryCount_rows]

/-- Each comparison pays both generated snapshots explicitly. The Pi count
quotes every original row without allocating its table values. -/
def units : Nat := (Work.programs prior.model prior.domain).length *
  (queryCount prior * ScopeForecast.intents.length * (2*snapshotServices prior+comparisonServices prior))

theorem units_are_the_complete_reconstruction_directory : units prior =
    (Work.programs prior.model prior.domain).length * ((axes prior).length * (2*snapshotServices prior+comparisonServices prior)) := by
  rw [axes_count]
  rfl

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Reconstruction
