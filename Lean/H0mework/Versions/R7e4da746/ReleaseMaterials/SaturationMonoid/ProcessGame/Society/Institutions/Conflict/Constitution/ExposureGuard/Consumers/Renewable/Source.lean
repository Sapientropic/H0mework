import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Installed.Source
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers.Legacy

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable

open Capitalism.Universal.Source.Program Capitalism.Universal.Root Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Accounting
open Capitalism.Universal.Abolition.Accounting.Quantifiers Joint
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation
open PublicFunction
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Installed (Port Tech Raw Req releasedTech initial past response liftRequest scope)
open Financial.Installation

noncomputable section

def base : RawLaw Bool Bool Port Unit Unit :=
  { Installed.base with
    technique := fun technology person =>
      let original := Transition.Handoff.Consumers.law.technique technology person
      ⟨original.inputs, original.outputs, original.maintenance, original.requiredPorts.map .ordinary⟩ }

abbrev law := PublicFunction.Mandate.law base scope

abbrev code : Distributed.Code Bool Bool Port Tech Unit :=
  { Installed.code with law := law, initial := law.next initial [] }

def mechanism : Trials.Mechanism Bool Bool Port Tech Unit :=
  { Installed.mechanism with code := code, funding := Installed.mechanism.funding.drop 1 }

def nature : mechanism.Nature := Installed.nature
def originalWord := Control.responseWord mechanism past nature response

def input : ProgrammeSource.Input Bool Bool Port Tech Unit :=
  { Installed.input with law := law, instructions := originalWord }

theorem original_gap :
    Responsibility.partyLoss mechanism past nature response false false = 18 ∧
      Responsibility.controllerCohort mechanism past nature response = [true] := by
  decide +kernel

def productiveClaim : Responsibility.Family.Claim mechanism past nature response :=
  (Responsibility.Family.assess mechanism past nature response).get (by decide +kernel)

def count : Nat := 2 * (input.instructions.length + 2) + 1

private theorem capacity_read (state : Cursor.State input) : Cursor.capacity input state = 7 := by
  rw [Cursor.fixed_capacity input state rfl]
  decide +kernel

private abbrev Coordinates := Cursor.Phase × Nat × Nat × Nat

private def coords (state : Cursor.State input) : Coordinates :=
  (state.phase, state.cycle, state.position, state.ahead)

private def advanceCoordinates : Coordinates → Coordinates
  | (.entering, cycle, position, ahead) => (.accounting, cycle, position, ahead + 1)
  | (.accounting, cycle, position, ahead) =>
      (.accounting, if position < 7 then cycle else cycle + 1,
       if position < 7 then position + 1 else 0, if position = 0 then ahead - 1 else ahead)

private theorem coordinate_step (state : Cursor.State input) :
    coords (Cursor.next input state) = advanceCoordinates (coords state) := by
  cases phase : state.phase <;> simp [coords, Cursor.next, advanceCoordinates, phase, capacity_read state]

private def coordinatesAt : Nat → Coordinates
  | 0 => (.accounting, 0, 0, 2)
  | n + 1 => advanceCoordinates (coordinatesAt n)

private theorem original_coordinates (n : Nat) :
    coords (Financial.Installation.Runtime.cursorAt input 0 n) = coordinatesAt n := by
  induction n with
  | zero => rfl
  | succ n prior =>
    change coords (Cursor.next input (Financial.Installation.Runtime.cursorAt input 0 n)) =
      advanceCoordinates (coordinatesAt n)
    rw [coordinate_step, prior]

def original := Financial.Installation.Runtime.frames input 0 count
def visit : SourceNativeTemporalVisitAt original.native.root.toAuthoritativeRoot.toLedgerRoot :=
  original.temporal input

theorem cursor_eq : original.cursor input = Financial.Installation.Runtime.cursorAt input 0 count :=
  Financial.Installation.Runtime.frames_cursor input 0 count

theorem consumed :
    Financial.Installation.Cursor.lastExecutedIndex input (Financial.Installation.Runtime.cursorAt input 0 count) = 1 ∧
      Financial.Installation.Cursor.pending input (Financial.Installation.Runtime.cursorAt input 0 count) = [] := by
  let state := Financial.Installation.Runtime.cursorAt input 0 count
  have located : coords state = (.accounting, 1, 7, 0) := by
    rw [show coords state = coordinatesAt count from original_coordinates count]
    decide +kernel
  have moved : coords (Cursor.next input state) = (.accounting, 2, 0, 0) := by
    rw [coordinate_step, located]
    rfl
  have position : state.position = 7 := congrArg (fun p : Coordinates => p.2.2.1) located
  have ahead : state.ahead = 0 := congrArg (fun p : Coordinates => p.2.2.2) located
  constructor
  · change Cursor.lastExecutedIndex input state = 1
    unfold Cursor.lastExecutedIndex Cursor.physicalVisitIndex
    rw [show (Cursor.next input state).cycle = 2 from congrArg (fun p : Coordinates => p.2.1) moved,
      show (Cursor.next input state).position = 0 from congrArg (fun p : Coordinates => p.2.2.1) moved,
      show (Cursor.next input state).ahead = 0 from congrArg (fun p : Coordinates => p.2.2.2) moved]
    decide +kernel
  · change Cursor.pending input state = []
    have empty : Cursor.currentPending input state = [] := by
      unfold Cursor.currentPending
      apply List.drop_eq_nil_of_le
      change Cursor.capacity input state ≤ state.position
      rw [capacity_read, position]
    simp [Cursor.pending, empty, Cursor.queuedCount, ahead]

theorem origin : Capitalism.Universal.Abolition.Accounting.Root.Source.OriginAt
    input original.native visit productiveClaim where
  law := rfl
  before := by
    change mechanism.code.initial = ProgrammeSource.rawCurrent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [consumed.1]
    rfl
  word := by
    change originalWord = ProgrammeSource.rawEvent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [consumed.1]
    rfl
  history := by
    change past = (List.range (Financial.Installation.Cursor.lastExecutedIndex input (original.cursor input))).map
      (fun index => ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input index).current)
    rw [cursor_eq, consumed.1]
    rfl
  accounted := by
    change Financial.Installation.Cursor.pending input (original.cursor input) = []
    rw [cursor_eq]
    exact consumed.2

def seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response) :=
  ⟨input, 0, count, productiveClaim, origin, []⟩

private def measuredCells (raw : Raw) (word : List Req) : List ((Bool × Bool × Bool) × ℚ) :=
  (Entitlement.Source.legs law raw word).filterMap fun leg =>
    if Entitlement.Source.ControlledReturn leg then
      some ((leg.sender, leg.recipient, leg.good), leg.quantity)
    else none

set_option backward.isDefEq.respectTransparency false in
theorem original_gross_cells :
    (Entitlement.Source.demands (window seed)).map
      (fun demand => (Entitlement.Duty.demandKey (window seed) demand, demand.quantity)) =
        [((false, true, false), 100)] := by
  have before : (window seed).before = mechanism.code.initial := origin.before.symm
  have word : (window seed).word = originalWord := origin.word.symm
  calc
    _ = measuredCells (window seed).before (window seed).word := by
      change List.map _ (List.filterMap (Entitlement.Source.readDemand (window seed)) (window seed).legs) =
        (window seed).legs.filterMap (fun leg => if Entitlement.Source.ControlledReturn leg then
          some ((leg.sender, leg.recipient, leg.good), leg.quantity) else none)
      rw [List.map_filterMap]
      congr 1
      funext leg
      unfold Entitlement.Source.readDemand
      split <;> rfl
    _ = _ := by
      rw [before, word]
      decide +kernel

theorem gross_quantity : (Entitlement.Source.demands (window seed)).map Entitlement.Source.Demand.quantity = [100] := by
  have calculated := congrArg (List.map Prod.snd) original_gross_cells
  simpa only [List.map_map, Function.comp_def, List.map_cons, List.map_nil] using calculated

def grossClaim : Entitlement.Source.Claim (window seed) :=
  (Entitlement.Source.assess (window seed)).get (by
    have nonempty : Entitlement.Source.demands (window seed) ≠ [] := by
      intro empty
      have amount := gross_quantity
      rw [empty] at amount
      cases amount
    simp [Entitlement.Source.assess, dif_pos (original_cause_is_accounted seed), dif_pos nonempty, Option.isSome_some])

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Consumers.Renewable
