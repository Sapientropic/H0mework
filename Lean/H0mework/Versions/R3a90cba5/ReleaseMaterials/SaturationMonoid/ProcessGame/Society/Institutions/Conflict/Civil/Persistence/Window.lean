import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Boundary.Actual.Incidence
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Exit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening

noncomputable section

abbrev Script (Party Good Port Technology Instrument : Type) :=
  List (Option (Compile.RawInput Party Good Port Technology Instrument))

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Option (Compile.RawInput Party Good Port Technology Instrument)
local notation "Word" => Script Party Good Port Technology Instrument
local notation "Cell" => Party × Use × Good × ℚ
local notation "Item" => ExecutionItem Party Good Port Technology Instrument
local notation "endAt" => Quantities.Execution.endAt

/-- The open service interval is a suffix of the one actual history. Its cut
and pending material receipts are derived by the original epoch fold. -/
structure Window (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] where
  opened : Root.Cut Party Good Port Technology Instrument
  pending : Script Party Good Port Technology Instrument

local notation "W" => Window Party Good Port Technology Instrument

def Window.at (cut : C) : W := ⟨cut, []⟩

def Window.current (window : W) : C := endAt window.opened window.pending

def Window.nextCut (window : W) (input : Input) : C :=
  Quantities.Execution.next window.current input

def Window.crosses (window : W) (input : Input) : Prop :=
  window.current.raw.clock < (window.nextCut input).raw.clock

instance (window : W) (input : Input) : Decidable (window.crosses input) := by
  unfold Window.crosses
  infer_instance

def Window.write (window : W) (input : Input) : W :=
  if window.crosses input then .at (window.nextCut input)
  else ⟨window.opened, window.pending ++ [input]⟩

theorem Window.write_current (window : W) (input : Input) :
    (window.write input).current = window.nextCut input := by
  unfold Window.write
  split
  · rfl
  · exact Quantities.Execution.endAt_append window.opened window.pending [input]

def Window.run : W → Word → W
  | window, [] => window
  | window, input :: rest => (window.write input).run rest

theorem Window.run_current (window : W) (word : Word) :
    (window.run word).current = endAt window.current word := by
  induction word generalizing window with
  | nil => rfl
  | cons input rest ih =>
    rw [Window.run, ih, Window.write_current]
    rfl

theorem Window.run_append (window : W) (first second : Word) :
    window.run (first ++ second) = (window.run first).run second := by
  induction first generalizing window with
  | nil => rfl
  | cons input rest ih =>
    simp only [List.cons_append, Window.run, ih]

/-- The opening duration is taken from the native law at the actual window
opening. A later edit of technology cannot move this original due address. -/
def Window.deadline (window : W) : ℚ :=
  window.opened.raw.clock + max 0 ((Boundary.Actual.materialLaw window.opened).duration window.opened.raw)

/-- A civilian payment uses an independent item admitted at its own cut. -/
def OwnMaterial (cut : C) (command : List Party) (item : Item) : Prop :=
  Quantities.Exit.Grant.Independent cut command item ∧ cut.native.input.law.Valid item.before item.request

instance (cut : C) (command : List Party) (item : Item) :
    Decidable (OwnMaterial cut command item) := by
  unfold OwnMaterial
  infer_instance

/-- Independence and authority are read at each material item's own
submission cut. A resident's later admission cannot backdate a payment. -/
def timelyUses (deadline : ℚ) (command : List Party) (cell : Cell) : C → Word → ℚ
  | _, [] => 0
  | cut, input :: rest =>
    let reached := Quantities.Execution.next cut input
    let delivered := if reached.raw.clock ≤ deadline then
      let own := (Boundary.Actual.items cut input).filter fun item => decide (OwnMaterial cut command item)
      (own.map fun item => flowAt (Optimality.Cost.actualPart cut.native.handlerFace.rootRead
        item.before item.request (.use cell.2.1)) cell.1 cell.2.2.1).sum
      else 0
    delivered + timelyUses deadline command cell reached rest

def Window.timely (window : W) (command : List Party) (input : Input) (cell : Cell) : ℚ :=
  timelyUses window.deadline command cell window.opened (window.pending ++ [input])

def Window.residents (origin : C) (command : List Party) (window : W) : List Party :=
  (Civil.protectedMembers origin command ++ Civil.protectedMembers window.opened command ++
    Civil.protectedMembers window.current command).dedup

theorem Window.includes_current_resident (origin : C) (command : List Party) (window : W)
    {person : Party} (present : person ∈ Civil.protectedMembers window.current command) :
    person ∈ window.residents origin command :=
  List.mem_dedup.mpr (List.mem_append_right _ present)

def Window.cells (origin : C) (command : List Party) (window : W) : List Cell :=
  let residents := window.residents origin command
  (Boundary.floorCells origin residents ++ Boundary.floorCells window.opened residents ++
    Boundary.floorCells window.current residents).dedup

theorem Window.includes_current_need (origin : C) (command : List Party) (window : W)
    {cell : Cell} (due : cell ∈ Quantities.Demand.requirements window.current)
    (present : cell.1 ∈ Civil.protectedMembers window.current command) :
    cell ∈ window.cells origin command :=
  List.mem_dedup.mpr (List.mem_append_right _
    (List.mem_filter.mpr ⟨due, decide_eq_true (Window.includes_current_resident origin command window present)⟩))

def Window.Pays (origin : C) (command : List Party) (window : W) (input : Input) : Prop :=
  ∀ cell ∈ window.cells origin command, cell.2.2.2 ≤ window.timely command input cell

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
