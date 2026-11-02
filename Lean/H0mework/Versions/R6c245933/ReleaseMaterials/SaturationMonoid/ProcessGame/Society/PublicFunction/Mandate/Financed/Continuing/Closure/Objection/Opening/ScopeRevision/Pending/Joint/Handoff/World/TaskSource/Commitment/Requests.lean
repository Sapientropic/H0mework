import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Requests
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Input.Recovery.Metering.Assessment.Relation
noncomputable section

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) {epoch : Epoch} (inventory : Inventory epoch)
  (past : List (Rule prior.model.source.code))

abbrev Program := Commitment.Program prior
abbrev Row := Feed.Work.Reconstruction.Row prior
abbrev queries (row : Feed.Selection.Row prior.model prior.domain) :=
  Restoration.required prior.model row.world.val prior.futureRequests

structure Query where
  row : Row prior
  query : Fin (queries prior (Feed.Selection.rows prior.model prior.domain)[row]).length

def directory : List (Query prior) :=
  (List.finRange (Feed.Selection.rows prior.model prior.domain).length).flatMap fun row =>
    (List.finRange (queries prior (Feed.Selection.rows prior.model prior.domain)[row]).length).map
      fun query => ⟨row,query⟩

theorem every_original_query_is_included (query : Query prior) : query ∈ directory prior :=
  List.mem_flatMap.mpr ⟨query.row,List.mem_finRange _,
    List.mem_map.mpr ⟨query.query,List.mem_finRange _,rfl⟩⟩

def word (query : Query prior) :=
  (queries prior (Feed.Selection.rows prior.model prior.domain)[query.row])[query.query]

def cursor (program : Program prior) := (Commitment.rebuilt prior inventory past program).target

def window (program : Program prior) : Window (⟨epoch,inventory⟩ : Packet) :=
  ⟨(cursor prior inventory past program).saved,
    .append (Commitment.native prior inventory past program) (Commitment.rebuilt prior inventory past program).native⟩

def submitted (program : Program prior) (query : Query prior) :=
  (cursor prior inventory past program).pending ++ word prior query

def submittedQueries (program : Program prior) (row : Feed.Selection.Row prior.model prior.domain) :=
  (queries prior row).map ((cursor prior inventory past program).pending ++ ·)

private theorem original_residual_is_bounded {otherEpoch : Epoch} {saved : Inventory otherEpoch}
    {word : List Action} (report : Input.Recovery.Metering.Assessment.Report saved word) :
    report.residual.length ≤ word.length := by
  have split := congrArg List.length report.original_request_split
  have origins : (Input.Recovery.pending saved word).length ≤ word.length := by
    unfold Input.Recovery.pending Input.Recovery.origins
    rw [List.length_map]
    exact (List.length_filterMap_le _ _).trans (by
      rw [List.length_attach]
      exact le_of_eq ((Mandate.law base otherEpoch.scope).inventory_length _ 0 word))
  simp only [List.length_append] at split
  omega

theorem actual_pending_is_bounded_by_the_original_pending (program : Program prior) :
    (cursor prior inventory past program).pending.length ≤ prior.worldPending.length := by
  change (Commitment.next prior inventory past program).pending.length ≤ prior.worldPending.length
  have bounded := original_residual_is_bounded
    (Writeback.receive (Commitment.full prior past program).source inventory
      (Budget.Programme.Debt.depth prior.point.point) (Commitment.controls prior past program).length
      prior.worldPending).report
  simpa only [Commitment.next,Writeback.next,Input.Challenge.Redress.Shared.Iteration.Requests.Result.next,
    Input.Challenge.Redress.Shared.Iteration.Requests.submitted,List.append_nil] using bounded

/-- Queries keep their original positions, including duplicate words. Each row
owns one retained Reports value; its five ports are not regenerated per intent. -/
inductive Rows (program : Program prior) : List (Feed.Selection.Row prior.model prior.domain) → Type where
  | nil : Rows program []
  | cons {row later} (reports : Feed.Work.Reports inventory (window prior inventory past program) (submittedQueries prior inventory past program row))
      (tail : Rows program later) : Rows program (row::later)

def generateRows (program : Program prior) (rows : List (Feed.Selection.Row prior.model prior.domain)) :
    Rows prior inventory past program rows :=
  let rebuilt := Commitment.rebuilt prior inventory past program
  let target := rebuilt.target
  let actual : Window (⟨epoch,inventory⟩ : Packet) :=
    ⟨target.saved,.append (Commitment.native prior inventory past program) rebuilt.native⟩
  let pending := target.pending
  let rec generate : (items : List (Feed.Selection.Row prior.model prior.domain)) → Rows prior inventory past program items
    | [] => .nil
    | row::later => .cons
        (Feed.Work.reports inventory actual ((queries prior row).map (pending ++ ·))) (generate later)
  generate rows

def Rows.get {program : Program prior} : {rows : List (Feed.Selection.Row prior.model prior.domain)} →
    Rows prior inventory past program rows → (row : Fin rows.length) →
      Feed.Work.Reports inventory (window prior inventory past program) (submittedQueries prior inventory past program rows[row])
  | _,.nil,row => Fin.elim0 row
  | _,.cons reports later,row => by
      cases row using Fin.cases with
      | zero => exact reports
      | succ row => exact later.get row

def Rows.units {program : Program prior} : {rows : List (Feed.Selection.Row prior.model prior.domain)} →
    Rows prior inventory past program rows → Nat
  | _,.nil => 0
  | _,.cons reports later => reports.units + later.units

theorem Rows.units_le_quote {program : Program prior} {rows : List (Feed.Selection.Row prior.model prior.domain)}
    (made : Rows prior inventory past program rows) :
    made.units ≤ (rows.map fun row => ((queries prior row).map fun word =>
      2 + ScopeForecast.services + prior.worldPending.length + word.length).sum).sum := by
  have words (qs : List (List Action)) :
      (((qs.map ((cursor prior inventory past program).pending ++ ·)).map fun word =>
        2 + ScopeForecast.services + word.length).sum) ≤
      (qs.map fun word => 2 + ScopeForecast.services + prior.worldPending.length + word.length).sum := by
    have bound := actual_pending_is_bounded_by_the_original_pending prior inventory past program
    induction qs with
    | nil => simp only [List.map_nil,List.sum_nil,Nat.le_refl]
    | cons head later ih =>
        simp only [List.map_cons,List.sum_cons,List.length_append]
        omega
  induction made with
  | nil => rfl
  | cons reports later ih =>
      rw [Rows.units,Feed.Work.Reports.quoted_units_are_exact]
      exact Nat.add_le_add (words _) ih

structure Batch (program : Program prior) where
  private mk ::
  rows : Rows prior inventory past program (Feed.Selection.rows prior.model prior.domain)
  generated : rows = generateRows prior inventory past program (Feed.Selection.rows prior.model prior.domain)

def execute (program : Program prior) : Batch prior inventory past program :=
  ⟨generateRows prior inventory past program (Feed.Selection.rows prior.model prior.domain),rfl⟩

variable {prior inventory past}
def Batch.reportUnits {program : Program prior} (batch : Batch prior inventory past program) :=
  Rows.units prior inventory past batch.rows

def Batch.entry {program : Program prior} (batch : Batch prior inventory past program) (query : Query prior) :
    Feed.Work.Entry inventory (window prior inventory past program) (submitted prior inventory past program query) := by
  let index : Fin (submittedQueries prior inventory past program
      (Feed.Selection.rows prior.model prior.domain)[query.row]).length :=
    ⟨query.query.val,by simpa only [submittedQueries,List.length_map] using query.query.isLt⟩
  let entry := Feed.Work.Reports.get inventory (Rows.get prior inventory past batch.rows query.row) index
  have same : (submittedQueries prior inventory past program
      (Feed.Selection.rows prior.model prior.domain)[query.row])[index] = submitted prior inventory past program query := by
    change ((queries prior (Feed.Selection.rows prior.model prior.domain)[query.row]).map
      ((cursor prior inventory past program).pending ++ ·))[query.query.val] = _
    rw [List.getElem_map]
    rfl
  exact Eq.mp (congrArg (Feed.Work.Entry inventory (window prior inventory past program)) same) entry

theorem every_report_is_the_same_original_query_at_the_actual_next {program : Program prior}
    (batch : Batch prior inventory past program) (query : Query prior) :
    (batch.entry query).report = Input.Recovery.Metering.Assessment.Runtime.read (cursor prior inventory past program).saved.2
      (submitted prior inventory past program query) := (batch.entry query).generated

theorem every_report_is_the_actual_pending_then_new_request {program : Program prior}
    (batch : Batch prior inventory past program) (query : Query prior) :
    (batch.entry query).report =
      (Input.Challenge.Redress.Shared.Iteration.Requests.produce
        (cursor prior inventory past program) (word prior query)).report :=
  (batch.entry query).generated

theorem pending_precedes_the_unchanged_original_query (program : Program prior) (query : Query prior) :
    submitted prior inventory past program query =
      (cursor prior inventory past program).pending ++ word prior query := rfl

theorem every_submitted_action_is_reserved (program : Program prior) (query : Query prior) :
    (submitted prior inventory past program query).length ≤ prior.worldPending.length + (word prior query).length := by
  rw [submitted,List.length_append]
  exact Nat.add_le_add_right (actual_pending_is_bounded_by_the_original_pending prior inventory past program) _

variable (prior inventory past)
  (original : Feed.Work.Batch prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing)

def Holds (previous program : Program prior) (batch : Batch prior inventory past program) (query : Query prior) : Prop :=
  ScopeForecast.NoWorse (batch.entry query).scopeForecast
    ((Feed.Work.Lookup.cell original query.row previous).scopeForecast query.query)

instance (previous program : Program prior) (batch : Batch prior inventory past program) (query : Query prior) :
    Decidable (Holds prior inventory past original previous program batch query) := by
  unfold Holds
  infer_instance

def Accepts (previous program : Program prior) (batch : Batch prior inventory past program) : Prop :=
  ∀ query ∈ directory prior,Holds prior inventory past original previous program batch query

instance (previous program : Program prior) (batch : Batch prior inventory past program) :
    Decidable (Accepts prior inventory past original previous program batch) := by
  unfold Accepts
  infer_instance

structure Rejection (previous program : Program prior) (batch : Batch prior inventory past program) where
  query : Query prior
  generated : query ∈ directory prior
  broken : ¬ Holds prior inventory past original previous program batch query

def rejectionFrom (previous program : Program prior) (batch : Batch prior inventory past program)
    (failed : ¬ Accepts prior inventory past original previous program batch) :
    Rejection prior inventory past original previous program batch :=
  match Distributed.inspect (Holds prior inventory past original previous program batch) (directory prior) with
  | .rejected query generated broken => ⟨query,generated,broken⟩
  | .accepted kept => False.elim (failed kept)

theorem every_original_query_keeps_its_full_scope_forecast (previous program : Program prior)
    (batch : Batch prior inventory past program)
    (accepted : Accepts prior inventory past original previous program batch) (query : Query prior) :
    ScopeForecast.NoWorse (batch.entry query).scopeForecast
      ((Feed.Work.Lookup.cell original query.row previous).scopeForecast query.query) :=
  accepted query (every_original_query_is_included prior query)

theorem every_original_axis_keeps_its_task_and_residual (previous program : Program prior)
    (batch : Batch prior inventory past program)
    (accepted : Accepts prior inventory past original previous program batch)
    (axis : Feed.Work.Reconstruction.Axis prior) :
    let query : Query prior := ⟨axis.row,axis.query⟩
    ScopeForecast.PortNoWorse ((batch.entry query).scopeForecast.read axis.intent.val)
      (((Feed.Work.Lookup.cell original axis.row previous).scopeForecast axis.query).read axis.intent.val) ∧
    Window.NoWorse (ScopeForecast.taskWindow ((batch.entry query).scopeForecast.read axis.intent.val))
      (ScopeForecast.taskWindow (((Feed.Work.Lookup.cell original axis.row previous).scopeForecast axis.query).read axis.intent.val)) ∧
    TaskSource.Admission.NoWorse ((batch.entry query).scopeForecast.taskAdmission axis.intent.val)
      (((Feed.Work.Lookup.cell original axis.row previous).scopeForecast axis.query).taskAdmission axis.intent.val) :=
  every_original_query_keeps_its_full_scope_forecast prior inventory past original previous program batch
    accepted ⟨axis.row,axis.query⟩ axis.intent.val axis.intent.property

theorem original_task_admission_cannot_disappear (previous program : Program prior)
    (batch : Batch prior inventory past program) (query : Query prior) (intent : Input.Intent)
    (before : (((Feed.Work.Lookup.cell original query.row previous).scopeForecast query.query).taskAdmission intent).passed = true)
    (lost : ((batch.entry query).scopeForecast.taskAdmission intent).passed ≠ true) :
    ¬ Accepts prior inventory past original previous program batch := by
  intro kept
  have full := every_original_query_keeps_its_full_scope_forecast prior inventory past original previous program batch kept query
  exact lost ((full intent (ScopeForecast.every_native_port_is_included intent)).2.2 before)

theorem original_completed_residual_cannot_disappear (previous program : Program prior)
    (batch : Batch prior inventory past program) (query : Query prior) (intent : Input.Intent)
    (before : (((Feed.Work.Lookup.cell original query.row previous).scopeForecast query.query).read intent).report.residual = [])
    (lost : ((batch.entry query).scopeForecast.read intent).report.residual ≠ []) :
    ¬ Accepts prior inventory past original previous program batch := by
  intro kept
  have full := every_original_query_keeps_its_full_scope_forecast prior inventory past original previous program batch kept query
  exact lost ((full intent (ScopeForecast.every_native_port_is_included intent)).1.1 before)

private def pointServices (world : Replanning.Point prior.model prior.domain) : Nat :=
  let qs := Restoration.required prior.model world.val prior.futureRequests
  2 * (qs.length + 1) * (1 + (qs.map fun word =>
    2 + ScopeForecast.services + prior.worldPending.length + word.length).sum) +
    qs.length * (1 + 3 * ScopeForecast.intents.length)

private theorem tableSum_exact :
    ((Replanning.points prior.model prior.domain).map fun world =>
      Feed.tableCount world.val * pointServices prior world).sum =
    ((Feed.Selection.rows prior.model prior.domain).map fun row => pointServices prior row.world).sum := by
  have one (world : Replanning.Point prior.model prior.domain)
      (pool : List (Replanning.TableAt prior.model prior.domain world)) :
      ((pool.map fun table => (⟨world,table⟩ : Feed.Selection.Row prior.model prior.domain)).map
        fun row => pointServices prior row.world).sum = pool.length * pointServices prior world := by
    induction pool with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
        simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm]
  have all (worlds : List (Replanning.Point prior.model prior.domain)) :
      (worlds.map fun world => Feed.tableCount world.val * pointServices prior world).sum =
      ((worlds.flatMap fun world => (Cut.tables world.val.source world.val.entry world.val.cut).attach.map
        fun table => (⟨world,table⟩ : Feed.Selection.Row prior.model prior.domain)).map
          fun row => pointServices prior row.world).sum := by
    induction worlds with
    | nil => rfl
    | cons world later ih =>
        simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,
          one,List.length_attach]
        rw [ih,Feed.tableCount_exact]
  exact all _

/-- Quote the Pi product before constructing any table/function or Report.
Repeated original baseline rows and retained actual Reports are both charged. -/
def perProgrammeUnits : Nat :=
  1 + horizon prior.domain + Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime.actualHorizon prior.point.point +
    Feed.Work.Reconstruction.snapshotServices prior +
    ((Replanning.points prior.model prior.domain).map fun world =>
      Feed.tableCount world.val * pointServices prior world).sum

theorem perProgrammeUnits_is_the_exact_original_row_quote : perProgrammeUnits prior =
  1 + horizon prior.domain + Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Runtime.actualHorizon prior.point.point +
    Feed.Work.Reconstruction.snapshotServices prior +
    ((Feed.Selection.rows prior.model prior.domain).map fun row =>
      2 * ((queries prior row).length + 1) * (1 + ((queries prior row).map fun word =>
        2 + ScopeForecast.services + prior.worldPending.length + word.length).sum) +
      (queries prior row).length * (1 + 3 * ScopeForecast.intents.length)).sum := by
  rw [perProgrammeUnits,tableSum_exact]
  rfl


def units : Nat := (Feed.Work.programs prior.model prior.domain).length * perProgrammeUnits prior

theorem all_actual_query_services_are_reserved (program : Program prior)
    (batch : Batch prior inventory past program) :
    2 * batch.reportUnits ≤ perProgrammeUnits prior := by
  have each (rows : List (Feed.Selection.Row prior.model prior.domain)) :
      2 * (rows.map fun row => ((queries prior row).map fun word =>
        2 + ScopeForecast.services + prior.worldPending.length + word.length).sum).sum ≤
      (rows.map fun row => 2 * ((queries prior row).length + 1) * (1 + ((queries prior row).map fun word =>
        2 + ScopeForecast.services + prior.worldPending.length + word.length).sum) +
        (queries prior row).length * (1 + 3 * ScopeForecast.intents.length)).sum := by
    induction rows with
    | nil => simp only [List.map_nil,List.sum_nil,Nat.mul_zero,Nat.le_refl]
    | cons row later ih =>
        simp only [List.map_cons,List.sum_cons]
        simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc] at *
        omega
  have paid := each (Feed.Selection.rows prior.model prior.domain)
  unfold Batch.reportUnits
  have quote := Rows.units_le_quote prior inventory past batch.rows
  rw [perProgrammeUnits_is_the_exact_original_row_quote]
  omega


def baselineLookupUnits : Nat := ((Feed.Selection.rows prior.model prior.domain).map fun row =>
  (queries prior row).length * (1 + ((queries prior row).map fun word =>
    2 + ScopeForecast.services + word.length).sum)).sum

theorem all_actual_and_repeated_original_services_are_jointly_reserved (program : Program prior)
    (batch : Batch prior inventory past program) :
    2 * batch.reportUnits + 2 * baselineLookupUnits prior ≤ perProgrammeUnits prior := by
  have perRow (n oldCost newCost portCost : Nat) (bounded : oldCost ≤ newCost) :
      2 * newCost + 2 * (n * (1 + oldCost)) ≤ 2 * (n + 1) * (1 + newCost) + n * portCost := by
    calc
      _ ≤ 2 * newCost + 2 * (n * (1 + newCost)) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left n (Nat.add_le_add_left bounded 1))) _
      _ ≤ _ := by
        simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.mul_assoc]
        omega
  have words (qs : List (List Action)) :
      (qs.map fun word => 2 + ScopeForecast.services + word.length).sum ≤
      (qs.map fun word => 2 + ScopeForecast.services + prior.worldPending.length + word.length).sum := by
    induction qs with
    | nil => exact le_rfl
    | cons head later ih => simp only [List.map_cons,List.sum_cons];omega
  have rows (xs : List (Feed.Selection.Row prior.model prior.domain)) :
      2 * (xs.map fun row => ((queries prior row).map fun word =>
        2 + ScopeForecast.services + prior.worldPending.length + word.length).sum).sum +
      2 * (xs.map fun row => (queries prior row).length * (1 + ((queries prior row).map fun word =>
        2 + ScopeForecast.services + word.length).sum)).sum ≤
      (xs.map fun row => 2 * ((queries prior row).length + 1) * (1 + ((queries prior row).map fun word =>
        2 + ScopeForecast.services + prior.worldPending.length + word.length).sum) +
        (queries prior row).length * (1 + 3 * ScopeForecast.intents.length)).sum := by
    induction xs with
    | nil => exact le_rfl
    | cons row later ih =>
        have head := perRow (queries prior row).length _ _ (1 + 3 * ScopeForecast.intents.length)
          (words (queries prior row))
        simp only [List.map_cons,List.sum_cons]
        convert Nat.add_le_add head ih using 1; ring
  have reserved := rows (Feed.Selection.rows prior.model prior.domain)
  have actual := Rows.units_le_quote prior inventory past batch.rows
  unfold Batch.reportUnits baselineLookupUnits
  rw [perProgrammeUnits_is_the_exact_original_row_quote]
  omega

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Requests
