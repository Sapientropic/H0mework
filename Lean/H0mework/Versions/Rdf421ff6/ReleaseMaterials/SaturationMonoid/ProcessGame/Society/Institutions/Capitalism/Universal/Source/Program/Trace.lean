import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Step

/-!
# The finite source execution and its original affected inventory

Each inventory item is an original requested instruction with the intermediate
current computed by preceding instructions.  Rejection keeps that item and
its bearer visible.  No receipt registry or completed history is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

structure ExecutionItem (Party Good Port Technology Instrument : Type u) where
  index : Nat
  before : RawCurrent Party Good Technology Instrument
  request : Request Party Good Port Technology Instrument

structure ExecutionResult (Party Good Port Technology Instrument : Type u) where
  final : RawCurrent Party Good Technology Instrument
  items : List (ExecutionItem Party Good Port Technology Instrument)

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument)

def execute (current : RawCurrent Party Good Technology Instrument) :
    Nat → RawEvent Party Good Port Technology Instrument →
      ExecutionResult Party Good Port Technology Instrument
  | _, [] => ⟨current, []⟩
  | index, request :: tail =>
      let remaining := execute (law.step current request) (index + 1) tail
      ⟨remaining.final, ⟨index, current, request⟩ :: remaining.items⟩

def rawItems (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument) :
    List (ExecutionItem Party Good Port Technology Instrument) :=
  (law.execute current 0 event).items

def next (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument) :
    RawCurrent Party Good Technology Instrument :=
  { (law.execute current 0 event).final with
    clock := current.clock + max 0 (law.duration current)
    round := current.round + 1 }

def totalDebit (items : List (ExecutionItem Party Good Port Technology Instrument))
    (party : Party) (good : Good) : ℚ :=
  (items.map (fun item => flowAt (law.actualDebit item.before item.request) party good)).sum

def totalCredit (items : List (ExecutionItem Party Good Port Technology Instrument))
    (party : Party) (good : Good) : ℚ :=
  (items.map (fun item => flowAt (law.actualCredit item.before item.request) party good)).sum

theorem inventory_length (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument) :
    (law.execute current index event).items.length = event.length := by
  induction event generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simpa only [execute, List.length_cons] using
        congrArg Nat.succ (ih (law.step current request) (index + 1))

/-- Original requested commands survive even when their effects are refused. -/
theorem inventory_requests_exact (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument) :
    ((law.execute current index event).items.map ExecutionItem.request) = event := by
  induction event generalizing current index with
  | nil => rfl
  | cons request tail ih => simp only [execute, List.map_cons, ih]

theorem execute_append (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (first second : RawEvent Party Good Port Technology Instrument) :
    law.execute current index (first ++ second) =
      let front := law.execute current index first
      let back := law.execute front.final (index + first.length) second
      ⟨back.final, front.items ++ back.items⟩ := by
  induction first generalizing current index with
  | nil => simp [execute]
  | cons request tail ih =>
      simp only [List.cons_append, execute, ih, List.length_cons, List.cons_append]
      have same : index + 1 + tail.length = index + (tail.length + 1) := by omega
      rw [same]

theorem execute_material_balance (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (event : RawEvent Party Good Port Technology Instrument)
    (party : Party) (good : Good) :
    (law.execute current index event).final.stock party good +
        law.totalDebit (law.execute current index event).items party good =
      current.stock party good + law.totalCredit (law.execute current index event).items party good := by
  induction event generalizing current index with
  | nil => simp [execute, totalDebit, totalCredit]
  | cons request tail ih =>
      have first := law.material_step_balance current request party good
      have later := ih (law.step current request) (index + 1)
      simp only [execute, totalDebit, totalCredit, List.map_cons, List.sum_cons]
      simp only [totalDebit, totalCredit] at later
      linarith

theorem actual_next_material_balance (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument) (party : Party) (good : Good) :
    (law.next current event).stock party good + law.totalDebit (law.rawItems current event) party good =
      current.stock party good + law.totalCredit (law.rawItems current event) party good :=
  law.execute_material_balance current 0 event party good

theorem next_clock_nondecreasing (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument) :
    current.clock ≤ (law.next current event).clock := by
  exact le_add_of_nonneg_right (le_max_left _ _)

theorem next_round_fresh (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument) :
    current.round < (law.next current event).round := Nat.lt_succ_self _

theorem two_nonidentical_currents (current : RawCurrent Party Good Technology Instrument)
    (event : RawEvent Party Good Port Technology Instrument) : law.next current event ≠ current := by
  intro same
  have strict := law.next_round_fresh current event
  rw [same] at strict
  exact Nat.lt_irrefl _ strict

end RawLaw

/-- The emitted request is computed afresh from the current local source.
The body is programme code, not an indexed table of successful histories. -/
structure RawProgram (Party Good Port Technology Instrument : Type u) where
  law : RawLaw Party Good Port Technology Instrument
  initial : RawCurrent Party Good Technology Instrument
  body : RawCurrent Party Good Technology Instrument → RawEvent Party Good Port Technology Instrument

namespace RawProgram

variable (program : RawProgram Party Good Port Technology Instrument)

def emit (current : RawCurrent Party Good Technology Instrument) :
    RawEvent Party Good Port Technology Instrument := program.body current

def tick (current : RawCurrent Party Good Technology Instrument) :
    RawCurrent Party Good Technology Instrument := program.law.next current (program.emit current)

def currentAt : Nat → RawCurrent Party Good Technology Instrument
  | 0 => program.initial
  | n + 1 => program.tick (currentAt n)

theorem currentAt_round (n : Nat) : (program.currentAt n).round = program.initial.round + n := by
  induction n with
  | zero => simp [currentAt]
  | succ n ih =>
      change (program.currentAt n).round + 1 = program.initial.round + (n + 1)
      omega

end RawProgram

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
