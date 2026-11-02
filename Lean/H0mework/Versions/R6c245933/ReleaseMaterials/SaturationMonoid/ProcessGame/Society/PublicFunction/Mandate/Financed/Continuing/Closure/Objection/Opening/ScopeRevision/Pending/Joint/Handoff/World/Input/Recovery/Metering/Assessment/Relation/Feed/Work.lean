import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Counting

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable (model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit))
  (domain : List (Continuation.Cursor model.source.code)) (original : Rule model.source.code)
  (requested : List (List Action))

/-- This directory is generated before any World window or report is evaluated.
Duplicate source positions retain separate service allocations. -/
structure Job where
  row : Feed.Selection.Row model domain
  program : Whole.Program model.source.code (horizon domain)

def programs := Whole.programs model.source.code (horizon domain)

def jobs : List (Job model domain) :=
  (Feed.Selection.rows model domain).flatMap fun row =>
    (programs model domain).map fun program => ⟨row,program⟩

def positions : Nat := (programs model domain).length * rowCount model domain

theorem positions_exact : positions model domain = (jobs model domain).length := by
  have count (rows : List (Feed.Selection.Row model domain)) :
      (rows.flatMap fun row => (programs model domain).map fun program => (⟨row,program⟩ : Job model domain)).length =
        rows.length * (programs model domain).length := by
    induction rows with
    | nil => simp
    | cons head tail ih => simp only [List.flatMap_cons, List.length_append, List.length_map,
        ih, List.length_cons, Nat.add_mul, Nat.one_mul, Nat.add_comm]
  unfold positions
  rw [rowCount_exact]
  exact (Nat.mul_comm _ _).trans (count _).symm

variable {model domain}
abbrev Job.queries (job : Job model domain) : List (List Action) :=
  Restoration.required model job.row.world.val requested

/-- One complete window service, then report and joint disposition services plus raw request
positions per query. These are declared service units, not a CPU-time bound. -/
def Job.units (job : Job model domain) : Nat :=
  1 + ((job.queries requested).map fun word => 2 + ScopeForecast.services + word.length).sum

variable (model domain)
def pointUnits (world : Replanning.Point model domain) : Nat :=
  1 + ((Restoration.required model world.val requested).map fun word => 2 + ScopeForecast.services + word.length).sum

def rowUnits (row : Feed.Selection.Row model domain) : Nat := pointUnits model domain requested row.world

/-- The exact old Cartesian allocation is counted by its Pi product, without
materialising function tables or row/program cells merely to quote them. -/
def units : Nat :=
  (programs model domain).length * ((Replanning.points model domain).map fun world =>
    tableCount world.val * pointUnits model domain requested world).sum

private theorem row_units_factor :
    ((Replanning.points model domain).map fun world => tableCount world.val * pointUnits model domain requested world).sum =
      ((Feed.Selection.rows model domain).map (rowUnits model domain requested)).sum := by
  have one (world : Replanning.Point model domain) (pool : List (Replanning.TableAt model domain world)) :
      ((pool.map fun table => (⟨world,table⟩ : Feed.Selection.Row model domain)).map
        (rowUnits model domain requested)).sum = pool.length * pointUnits model domain requested world := by
    induction pool with
    | nil => simp
    | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      change pointUnits model domain requested world + tail.length * pointUnits model domain requested world = _
      simp only [Nat.add_mul, Nat.one_mul, Nat.add_comm]
  have all (worlds : List (Replanning.Point model domain)) :
      (worlds.map fun world => tableCount world.val * pointUnits model domain requested world).sum =
      ((worlds.flatMap fun world => (Cut.tables world.val.source world.val.entry world.val.cut).attach.map
        fun table => (⟨world,table⟩ : Feed.Selection.Row model domain)).map (rowUnits model domain requested)).sum := by
    induction worlds with
    | nil => rfl
    | cons world tail ih =>
      simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
        one, List.length_attach]
      rw [ih, tableCount_exact]
  exact all _

theorem units_are_exact_directory : units model domain requested =
    ((jobs model domain).map fun job => job.units requested).sum := by
  have perRow (row : Feed.Selection.Row model domain)
      (pool : List (Whole.Program model.source.code (horizon domain))) :
      ((pool.map fun program => (⟨row,program⟩ : Job model domain)).map
        fun job => job.units requested).sum = pool.length * rowUnits model domain requested row := by
    induction pool with
    | nil => simp
    | cons head tail ih =>
        simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
        change rowUnits model domain requested row + tail.length * rowUnits model domain requested row = _
        simp only [Nat.add_mul,Nat.one_mul,Nat.add_comm]
  have all (rows : List (Feed.Selection.Row model domain)) :
      ((rows.flatMap fun row => (programs model domain).map fun program =>
        (⟨row,program⟩ : Job model domain)).map fun job => job.units requested).sum =
      (programs model domain).length * (rows.map (rowUnits model domain requested)).sum := by
    induction rows with
    | nil => simp
    | cons head tail ih =>
        rw [List.flatMap_cons,List.map_append,List.sum_append,perRow,ih]
        simp only [List.map_cons,List.sum_cons,Nat.mul_add]
  unfold units
  rw [row_units_factor]
  exact (all (Feed.Selection.rows model domain)).symm

theorem every_original_pool_position_has_a_job
    (row : Feed.Selection.Row model domain) (program : Whole.Program model.source.code (horizon domain))
    (listed : program ∈ programs model domain) :
    (⟨row,program⟩ : Job model domain) ∈ jobs model domain := by
  apply List.mem_flatMap.mpr
  refine ⟨row,Selection.Restoration.every_row_is_generated _ _ _,?_⟩
  exact List.mem_map.mpr ⟨program,listed,rfl⟩

variable {model domain}
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch)
  (tariff : Restoration.Tariff (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit))

/-- Report and funding are read from this one generated object. -/
structure Entry (actual : Window (⟨epoch,inventory⟩ : Packet)) (word : List Action) where
  private mk ::
  report : Report actual.packet.2 word
  generated : report = Runtime.read actual.packet.2 word
  disposition : Challenge.Redress.Shared.Iteration.Step report.packet.2
  disposition_generated : disposition = Challenge.Redress.Shared.Iteration.produce report.packet.2
  forecast : ScopeForecast.Forecast (jointWindowWith actual word report disposition) report.residual
  forecast_generated : forecast = ScopeForecast.generate (jointWindowWith actual word report disposition) report.residual

def Entry.funding {actual : Window (⟨epoch,inventory⟩ : Packet)} {word : List Action}
    (entry : Entry inventory actual word) := entry.report.funding

inductive Reports (actual : Window (⟨epoch,inventory⟩ : Packet)) : List (List Action) → Type where
  | private nil : Reports actual []
  | private cons {word tail} (entry : Entry inventory actual word)
      (later : Reports actual tail) : Reports actual (word::tail)

def reports (actual : Window (⟨epoch,inventory⟩ : Packet)) :
    (queries : List (List Action)) → Reports inventory actual queries
  | [] => .nil
  | word::tail =>
      let report := Runtime.read actual.packet.2 word
      let disposition := Challenge.Redress.Shared.Iteration.produce report.packet.2
      .cons ⟨report,rfl,disposition,rfl,
        ScopeForecast.generate (jointWindowWith actual word report disposition) report.residual,rfl⟩ (reports actual tail)

def Reports.length {actual : Window (⟨epoch,inventory⟩ : Packet)} :
    {queries : List (List Action)} → Reports inventory actual queries → Nat
  | _,.nil => 0
  | _,.cons _ later => 1 + later.length

def Reports.units {actual : Window (⟨epoch,inventory⟩ : Packet)} :
    {queries : List (List Action)} → Reports inventory actual queries → Nat
  | [],.nil => 0
  | word::_,.cons _ later => 2 + ScopeForecast.services + word.length + later.units

theorem Reports.quoted_units_are_exact
    {actual : Window (⟨epoch,inventory⟩ : Packet)} {queries : List (List Action)}
    (made : Reports inventory actual queries) :
    made.units = (queries.map fun word => 2 + ScopeForecast.services + word.length).sum := by
  induction made <;> simp_all only [Reports.units,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil]

theorem Reports.all_original_query_positions_are_executed
    {actual : Window (⟨epoch,inventory⟩ : Packet)} {queries : List (List Action)}
    (made : Reports inventory actual queries) : made.length = queries.length := by
  induction made <;> simp_all only [Reports.length,List.length_cons,List.length_nil,Nat.add_comm]

def Reports.get {actual : Window (⟨epoch,inventory⟩ : Packet)} :
    {queries : List (List Action)} → (made : Reports inventory actual queries) →
      (index : Fin queries.length) → Entry inventory actual queries[index]
  | _,.nil,index => Fin.elim0 index
  | _,.cons entry later,index => by
      cases index using Fin.cases with
      | zero => exact entry
      | succ index => exact later.get index

structure Cell (job : Job model domain) where
  private mk ::
  actual : Feed.Present model job.row.world.val inventory
  generated : actual = Feed.present model job.row.world.val original job.program
    (Cut.opponent job.row.world.val.source job.row.world.val.entry job.row.world.val.cut job.row.table.val)
    inventory tariff
  reports : Reports inventory actual.2 (job.queries requested)

def evaluate (job : Job model domain) : Cell original requested inventory tariff job :=
  let actual := Feed.present model job.row.world.val original job.program
    (Cut.opponent job.row.world.val.source job.row.world.val.entry job.row.world.val.cut job.row.table.val)
    inventory tariff
  ⟨actual,rfl,reports inventory actual.2 (job.queries requested)⟩

variable {original requested inventory tariff}

def Cell.report {job : Job model domain} (cell : Cell original requested inventory tariff job)
    (index : Fin (job.queries requested).length) := (Reports.get inventory cell.reports index).report

def Cell.funding {job : Job model domain} (cell : Cell original requested inventory tariff job)
    (index : Fin (job.queries requested).length) := Entry.funding inventory (Reports.get inventory cell.reports index)

def Cell.jointWindow {job : Job model domain} (cell : Cell original requested inventory tariff job)
    (index : Fin (job.queries requested).length) :=
  let entry := Reports.get inventory cell.reports index
  Relation.jointWindowWith cell.actual.2 (job.queries requested)[index] entry.report entry.disposition

theorem Cell.every_joint_window_is_the_original_source_call {job : Job model domain}
    (cell : Cell original requested inventory tariff job) (index : Fin (job.queries requested).length) :
    cell.jointWindow index = Relation.jointWindow cell.actual.2 (job.queries requested)[index]
      (Runtime.read cell.actual.2.packet.2 (job.queries requested)[index]) := by
  dsimp only [Cell.jointWindow,Relation.jointWindow]
  rw [(Reports.get inventory cell.reports index).disposition_generated,
    (Reports.get inventory cell.reports index).generated]

def Entry.scopeForecast {actual : Window (⟨epoch,inventory⟩ : Packet)} {word : List Action}
    (entry : Entry inventory actual word) :
    ScopeForecast.Forecast (Relation.jointWindow actual word entry.report) entry.report.residual :=
  Eq.mp (congrArg (fun disposition =>
    ScopeForecast.Forecast (jointWindowWith actual word entry.report disposition) entry.report.residual)
    entry.disposition_generated) entry.forecast

theorem Entry.scopeForecast_exact {actual : Window (⟨epoch,inventory⟩ : Packet)} {word : List Action}
    (entry : Entry inventory actual word) : entry.scopeForecast = Relation.scopeForecast actual word entry.report := by
  rcases entry with ⟨report,generated,disposition,same,forecast,exactForecast⟩
  cases same
  cases exactForecast
  rfl

def Cell.scopeForecast {job : Job model domain} (cell : Cell original requested inventory tariff job)
    (index : Fin (job.queries requested).length) := (Reports.get inventory cell.reports index).scopeForecast

theorem Cell.every_forecast_is_the_original_scope_call {job : Job model domain}
    (cell : Cell original requested inventory tariff job) (index : Fin (job.queries requested).length) :
    cell.scopeForecast index = Relation.scopeForecast cell.actual.2 (job.queries requested)[index]
      (cell.report index) := (Reports.get inventory cell.reports index).scopeForecast_exact

theorem Cell.funding_uses_the_same_generated_report {job : Job model domain}
    (cell : Cell original requested inventory tariff job) (index : Fin (job.queries requested).length) :
    cell.funding index = (cell.report index).funding := rfl

theorem Cell.every_report_is_the_original_source_call {job : Job model domain}
    (cell : Cell original requested inventory tariff job) (index : Fin (job.queries requested).length) :
    cell.report index = Runtime.read cell.actual.2.packet.2 (job.queries requested)[index] :=
  (Reports.get inventory cell.reports index).generated

variable (model domain original requested inventory tariff)
/-- Quiet sources share one actual controller across their external tables.
The indexed form allocates each dependent cell when its original comparison
consumes it; the eager form retains the original explicit execution. -/
inductive Storage where
  | eager (cells : List (Sigma fun job : Job model domain => Cell original requested inventory tariff job))
      (directory : cells.map Sigma.fst = jobs model domain)
  | quiet (checked : Budget.Programme.Debt.Information.Inquiry.Replay.PublicDomain.quiet (code := model.source.code) = true)
      (make : (job : Job model domain) → Cell original requested inventory tariff job)

structure Batch where
  private mk ::
  storage : Storage model domain original requested inventory tariff

variable {model domain original requested inventory tariff}

/-- Compatibility expansion preserves every original position. Runtime
selection uses indexed cells directly instead of materialising this list. -/
def Batch.cells (batch : Batch model domain original requested inventory tariff) :
    List (Sigma fun job : Job model domain => Cell original requested inventory tariff job) :=
  match batch.storage with
  | .eager cells _ => cells
  | .quiet _ make => (jobs model domain).map fun job => ⟨job,make job⟩

theorem Batch.directory (batch : Batch model domain original requested inventory tariff) :
    batch.cells.map Sigma.fst = jobs model domain := by
  rcases batch with ⟨storage⟩
  cases storage with
  | eager cells exactDirectory => exact exactDirectory
  | quiet _ make =>
    simp only [Batch.cells, List.map_map, Function.comp_def]
    change (jobs model domain).map id = _
    exact List.map_id _

def Batch.indexed (batch : Batch model domain original requested inventory tariff) : Bool :=
  match batch.storage with | .quiet .. => true | .eager .. => false

def Batch.units (batch : Batch model domain original requested inventory tariff) : Nat :=
  (batch.cells.map fun cell => 1 + cell.2.reports.units).sum

theorem Batch.every_charged_unit_is_an_actual_execution_position
    (batch : Batch model domain original requested inventory tariff) :
    batch.units = Work.units model domain requested := by
  have amounts : (fun cell : Sigma fun job : Job model domain => Cell original requested inventory tariff job =>
      1 + cell.2.reports.units) = (fun cell => cell.1.units requested) := by
    funext cell
    exact congrArg (1 + ·) cell.2.reports.quoted_units_are_exact
  unfold Batch.units
  rw [amounts]
  have mapped := congrArg (fun directory : List (Job model domain) =>
    (directory.map fun job => job.units requested).sum) batch.directory
  rw [units_are_exact_directory]
  simpa only [List.map_map,Function.comp_def] using mapped

theorem Batch.quoted_report_calls_are_exact
    (batch : Batch model domain original requested inventory tariff) :
    (batch.cells.map fun cell => cell.2.reports.length).sum =
      ((jobs model domain).map fun job => (job.queries requested).length).sum := by
  have lengths : (fun cell : Sigma fun job : Job model domain => Cell original requested inventory tariff job =>
      cell.2.reports.length) = (fun cell => (cell.1.queries requested).length) := by
    funext cell
    exact cell.2.reports.all_original_query_positions_are_executed
  rw [lengths]
  have mapped := congrArg (fun directory : List (Job model domain) =>
    (directory.map fun job => (job.queries requested).length).sum) batch.directory
  simpa only [List.map_map,Function.comp_def] using mapped

variable (model domain original requested inventory tariff)

def executeEager : Batch model domain original requested inventory tariff :=
  ⟨.eager ((jobs model domain).map fun job => ⟨job,evaluate original requested inventory tariff job⟩)
    (by
      rw [List.map_map]
      have erase (directory : List (Job model domain)) :
          directory.map (Sigma.fst ∘ fun job =>
            (⟨job,evaluate original requested inventory tariff job⟩ :
              Sigma fun job => Cell original requested inventory tariff job)) = directory := by
        induction directory with
        | nil => rfl
        | cons head tail ih => exact congrArg (head :: ·) ih
      exact erase _)⟩


/-- Default quiet compression changes no directory, quote or source relation.
Nonquiet execution and the explicit eager entry retain their original path. -/
def execute : Batch model domain original requested inventory tariff :=
  if checked : Budget.Programme.Debt.Information.Inquiry.Replay.PublicDomain.quiet (code := model.source.code) = true then
    ⟨.quiet checked (evaluate original requested inventory tariff)⟩
  else executeEager model domain original requested inventory tariff

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work
