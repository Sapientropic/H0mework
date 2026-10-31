import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.CursorProgress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Financial.Installation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def cycleCost (cycle : Nat) : Nat := (Financial.inventoryAt input (ProgrammeHistory.visitAt input cycle)).length + 1

def queuedCost (cycle : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => cycleCost input cycle + queuedCost (cycle + 1) count

/-- Only the already occurred queue is counted. The final unit of each cycle
is the original cursor's boundary step, which changes no physical state. -/
def budget (cursor : Cursor.State input) : Nat :=
  if Cursor.FreshBody input cursor then 0
  else cycleCost input cursor.cycle - cursor.position + queuedCost input (cursor.cycle + 1) (Cursor.queuedCount input cursor)

theorem cycleCost_eq (cursor : Cursor.State input) :
    cycleCost input cursor.cycle = Cursor.capacity input cursor + 1 := rfl

theorem bookkeeping_uses_one_unit (cursor : Cursor.State input)
    (accounting : cursor.phase = .accounting)
    (bounded : cursor.position ≤ Cursor.capacity input cursor)
    (old : ¬ Cursor.FreshBody input cursor) :
    budget input (Cursor.next input cursor) + 1 = budget input cursor := by
  have capacity := Cursor.capacity_positive input cursor
  by_cases first : cursor.position = 0
  · have ahead : 0 < cursor.ahead := by
      by_contra missing
      have zero : cursor.ahead = 0 := by omega
      exact old (Or.inr ⟨first, zero⟩)
    have available : cursor.position < Cursor.capacity input cursor := by omega
    have nextOld : ¬ Cursor.FreshBody input (Cursor.next input cursor) := by
      simp only [Cursor.FreshBody, Cursor.next, accounting, if_pos available]
      simp [first]
    have c := cycleCost_eq input cursor
    simp only [budget, if_neg old, if_neg nextOld]
    simp only [Cursor.next, accounting, if_pos available, Cursor.queuedCount]
    simp [first]
    omega
  · have positive : 0 < cursor.position := Nat.pos_of_ne_zero first
    by_cases available : cursor.position < Cursor.capacity input cursor
    · have nextOld : ¬ Cursor.FreshBody input (Cursor.next input cursor) := by
        simp only [Cursor.FreshBody, Cursor.next, accounting, if_pos available, if_neg first]
        simp
      have c := cycleCost_eq input cursor
      simp only [budget, if_neg old, if_neg nextOld]
      simp [Cursor.next, accounting, available, first, Cursor.queuedCount]
      omega
    · have exhausted : cursor.position = Cursor.capacity input cursor := by omega
      by_cases empty : cursor.ahead = 0
      · have fresh : Cursor.FreshBody input (Cursor.next input cursor) := by
          exact Or.inr ⟨by simp only [Cursor.next, accounting, if_neg available],
            by simp only [Cursor.next, accounting, if_neg first, empty]⟩
        simp only [budget, if_pos fresh, if_neg old, Cursor.queuedCount, if_neg first, empty,
          Nat.sub_zero, queuedCost, Nat.add_zero, Nat.zero_add]
        rw [cycleCost_eq]
        omega
      · obtain ⟨remaining, successor⟩ := Nat.exists_eq_succ_of_ne_zero empty
        have nextOld : ¬ Cursor.FreshBody input (Cursor.next input cursor) := by
          simp only [Cursor.FreshBody, Cursor.next, accounting, if_neg available, if_neg first]
          simp [empty]
        have c := cycleCost_eq input cursor
        simp only [budget, if_neg old, if_neg nextOld]
        simp [Cursor.next, accounting, available, first, Cursor.queuedCount, successor, queuedCost]
        omega

theorem bookkeeping_decreases (cursor : Cursor.State input)
    (accounting : cursor.phase = .accounting)
    (bounded : cursor.position ≤ Cursor.capacity input cursor)
    (old : ¬ Cursor.FreshBody input cursor) :
    budget input (Cursor.next input cursor) < budget input cursor := by
  have exactDebit := bookkeeping_uses_one_unit input cursor accounting bounded old
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.PendingDrain
