import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Exit.Grant.Plan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "Req" => Request Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ

abbrev floorCells (baseline : C) (residents : List Party) : List Cell :=
  (Quantities.Demand.requirements baseline).filter (fun cell => decide (cell.1 ∈ residents))

def deliveredAt (current : C) (word : Word) (cell : Cell) : ℚ :=
  Quantities.Demand.delivered current (Quantities.Execution.primitiveScript word)
    cell.1 cell.2.1 cell.2.2.1

def floorPaid (baseline current : C) (residents : List Party) (word : Word) : Prop :=
  ∀ cell ∈ floorCells baseline residents, cell.2.2.2 ≤ deliveredAt current word cell

abbrev actualItems (current : C) (word : Word) :=
  Quantities.Execution.inventory current (Quantities.Execution.primitiveScript word)

/-- The residents' floor is fixed at the original cut. Every original cell
is paid in one actual continuation at the generated successor. -/
structure ExitFloorAt (baseline current : C) (residents : List Party) (word : Word) : Prop where
  paid : Root.Paid current word
  independent : ∀ item ∈ actualItems current word, Quantities.Exit.Grant.Independent current [] item
  floor : floorPaid baseline current residents word

inductive ExitFailure (baseline current : C) (residents : List Party) (word : Word)
  | execution (issue : Root.Failure current word)
  | dependence (item : Item) (original : item ∈ actualItems current word)
      (failed : ¬ Quantities.Exit.Grant.Independent current [] item)
  | shortage (cell : Cell) (original : cell ∈ floorCells baseline residents)
      (short : deliveredAt current word cell < cell.2.2.2)

inductive ExitDecision (baseline current : C) (residents : List Party) (word : Word)
  | preserved (exit : ExitFloorAt baseline current residents word)
  | refused (failure : ExitFailure baseline current residents word)

def inspectExit (baseline current : C) (residents : List Party) (word : Word) :
    ExitDecision baseline current residents word :=
  match Root.inspect current word with
  | .rejected issue => .refused (.execution issue)
  | .paid paid =>
      match Material.inspectList (Quantities.Exit.Grant.Independent current []) (actualItems current word) with
      | .failure item listed failed => .refused (.dependence item listed failed)
      | .clear independent =>
          match Material.inspectList (fun cell : Cell => cell.2.2.2 ≤ deliveredAt current word cell)
              (floorCells baseline residents) with
          | .failure cell original failed => .refused (.shortage cell original (lt_of_not_ge failed))
          | .clear floor =>
              .preserved ⟨paid, fun item original => independent item original, fun cell original => floor cell original⟩

private def selfUse (current : C) (bearer : Party) (purpose : Use) (bundle : Bundle Good) :
    Option Req :=
  bundle.head?.map fun first =>
    ⟨bearer, [], current.native.input.law.stockPort current.raw.technology bearer first.1, [],
      .use bearer bundle purpose⟩

/-- One source proposal for the next independent life and maintenance
payments, including every member on the original roll. -/
def originalExitWord (baseline current : C) : Word :=
  let law := current.native.input.law
  (baseline.members ++ current.members).dedup.flatMap fun bearer =>
    (selfUse current bearer .necessity (law.necessities current.raw bearer)).toList ++
      (selfUse current bearer .maintenance (law.mandatoryMaintenance current.raw bearer)).toList

theorem every_original_cell_survives {baseline current : C} {residents : List Party} {word : Word}
    (exit : ExitFloorAt baseline current residents word) (cell : Cell)
    (original : cell ∈ Quantities.Demand.requirements baseline) (standing : cell.1 ∈ residents) :
    cell.2.2.2 ≤ deliveredAt current word cell :=
  exit.floor cell (List.mem_filter.mpr ⟨original, decide_eq_true standing⟩)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary
