import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Vector
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Exposure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Visits

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

abbrev Window := Financial.Family.Migration.Exposure.Window sources

def window (index : Index) (ordinal : Nat) : Window sources :=
  ⟨index, ProgrammeHistory.visitAt (sources index) ordinal⟩

def rawAt (index : Index) (ordinal : Nat) :=
  ProgrammeSource.rawCurrent (sources index) (ProgrammeHistory.visitAt (sources index) ordinal).current

def atVisit (entry : Window sources) (bearer : Party) : CostVector Good :=
  wordCost (sources entry.1).law (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
    (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) bearer

def creditAt (entry : Window sources) (bearer : Party) (good : Good) : ℚ :=
  (sources entry.1).law.totalCredit
    ((sources entry.1).law.rawItems (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
      (ProgrammeSource.rawEvent (sources entry.1) entry.2.current)) bearer good

def total : List (Window sources) → Party → CostVector Good
  | [], _ => 0
  | entry :: rest, bearer => atVisit sources entry bearer + total rest bearer

def credits : List (Window sources) → Party → Good → ℚ
  | [], _, _ => 0
  | entry :: rest, bearer, good => creditAt sources entry bearer good + credits rest bearer good

theorem total_append (left right : List (Window sources)) (bearer : Party) :
    total sources (left ++ right) bearer = total sources left bearer + total sources right bearer := by
  induction left with
  | nil => simp only [List.nil_append, total, zero_add]
  | cons entry rest ih => simp only [List.cons_append, total, ih, add_assoc]

theorem credits_append (left right : List (Window sources)) (bearer : Party) (good : Good) :
    credits sources (left ++ right) bearer good = credits sources left bearer good + credits sources right bearer good := by
  induction left with
  | nil => simp only [List.nil_append, credits, zero_add]
  | cons entry rest ih => simp only [List.cons_append, credits, ih, add_assoc]

def interval (index : Index) (start : Nat) : Nat → List (Window sources)
  | 0 => []
  | count + 1 => window sources index start :: interval index (start + 1) count

theorem interval_length (index : Index) (start count : Nat) :
    (interval sources index start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simpa only [interval, List.length_cons] using congrArg Nat.succ (ih (start + 1))

theorem raw_next (index : Index) (ordinal : Nat) :
    rawAt sources index (ordinal + 1) = (sources index).law.next (rawAt sources index ordinal)
      (ProgrammeSource.rawEvent (sources index) (ProgrammeHistory.visitAt (sources index) ordinal).current) :=
  ProgrammeSource.actual_raw_next (sources index) _

theorem step_material (index : Index) (ordinal : Nat) (bearer : Party) (good : Good) :
    (rawAt sources index (ordinal + 1)).stock bearer good +
      atVisit sources (window sources index ordinal) bearer (.operating good) +
      atVisit sources (window sources index ordinal) bearer (.debtPayment good) =
    (rawAt sources index ordinal).stock bearer good + creditAt sources (window sources index ordinal) bearer good := by
  have balance := (sources index).law.actual_next_material_balance (rawAt sources index ordinal)
    (ProgrammeSource.rawEvent (sources index) (ProgrammeHistory.visitAt (sources index) ordinal).current) bearer good
  have partition := wordCost_partitions_actual_debit (sources index).law (rawAt sources index ordinal)
    (ProgrammeSource.rawEvent (sources index) (ProgrammeHistory.visitAt (sources index) ordinal).current) bearer good
  rw [← raw_next sources index ordinal] at balance
  change atVisit sources (window sources index ordinal) bearer (.operating good) +
    atVisit sources (window sources index ordinal) bearer (.debtPayment good) = _ at partition
  change _ = (rawAt sources index ordinal).stock bearer good + creditAt sources (window sources index ordinal) bearer good at balance
  linarith

theorem step_elapsed (index : Index) (ordinal : Nat) (bearer : Party) :
    atVisit sources (window sources index ordinal) bearer .elapsed =
      (rawAt sources index (ordinal + 1)).clock - (rawAt sources index ordinal).clock := by
  rw [raw_next]
  simp only [atVisit, window, wordCost, RawLaw.next, rawAt]
  ring

theorem interval_material (index : Index) (start count : Nat) (bearer : Party) (good : Good) :
    (rawAt sources index (start + count)).stock bearer good +
      total sources (interval sources index start count) bearer (.operating good) +
      total sources (interval sources index start count) bearer (.debtPayment good) =
    (rawAt sources index start).stock bearer good + credits sources (interval sources index start count) bearer good := by
  induction count generalizing start with
  | zero => simp only [interval, total, credits, Pi.zero_apply, add_zero]
  | succ count ih =>
      have front := step_material sources index start bearer good
      have tail := ih (start + 1)
      rw [show start + (count + 1) = start + 1 + count by omega]
      change _ + (atVisit sources (window sources index start) bearer (.operating good) + _) +
        (atVisit sources (window sources index start) bearer (.debtPayment good) + _) =
        _ + (creditAt sources (window sources index start) bearer good + _)
      linarith

theorem interval_elapsed (index : Index) (start count : Nat) (bearer : Party) :
    total sources (interval sources index start count) bearer .elapsed =
      (rawAt sources index (start + count)).clock - (rawAt sources index start).clock := by
  induction count generalizing start with
  | zero => simp only [Nat.add_zero, interval, total, Pi.zero_apply, sub_self]
  | succ count ih =>
      have front := step_elapsed sources index start bearer
      have tail := ih (start + 1)
      rw [show start + (count + 1) = start + 1 + count by omega]
      change atVisit sources (window sources index start) bearer .elapsed + _ = _
      linarith

theorem total_nonnegative (entries : List (Window sources)) (bearer : Party) :
    BoundedBy 0 (total sources entries bearer) := by
  induction entries with
  | nil => exact fun _ => le_rfl
  | cons entry rest ih =>
      intro coordinate
      exact add_nonneg (wordCost_nonnegative (sources entry.1).law
        (ProgrammeSource.rawCurrent (sources entry.1) entry.2.current)
        (ProgrammeSource.rawEvent (sources entry.1) entry.2.current) bearer coordinate) (ih coordinate)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Costs.Visits
