import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Productive.Clearance.Joint.Revision.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution (endAt)
open Reparation.Actual (Occurrence Script)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (loss : Occurrence seed community) (word : Script Party Good Port Technology Instrument)

private def needAt (cut : InventoryRead Party Good Technology Instrument) (person : Party) (good : Good) : ℚ :=
  atRaw seed.native.input.law (originalRaw loss) cut.raw person good

structure NeedShortage where
  position : Fin (inventoryTrace loss word).length
  person : Party
  good : Good
  short : let cut := (inventoryTrace loss word)[position]
    cut.raw.stock person good < needAt loss cut person good
  first : ∀ earlier : Fin (inventoryTrace loss word).length, earlier < position →
    ∀ p g, let cut := (inventoryTrace loss word)[earlier]
    needAt loss cut p g ≤ cut.raw.stock p g

def NeedShortage.address (shortage : NeedShortage loss word) :=
  let cut := (inventoryTrace loss word)[shortage.position]
  (cut.visit, cut.item, shortage.person, shortage.good)

def NeedShortage.amount (shortage : NeedShortage loss word) : ℚ :=
  let cut := (inventoryTrace loss word)[shortage.position]
  needAt loss cut shortage.person shortage.good - cut.raw.stock shortage.person shortage.good

theorem NeedShortage.amount_pos (shortage : NeedShortage loss word) :
    0 < shortage.amount loss word := sub_pos.mpr shortage.short

theorem NeedShortage.refutes (shortage : NeedShortage loss word) : ¬ ProtectsNeeds loss word :=
  fun protects => (not_le_of_gt shortage.short)
    (protects _ (List.getElem_mem shortage.position.isLt) shortage.person shortage.good)

/-- Recompute the obligation at every original material position. A
technology or stock change can raise the need for the next position. -/
def inspectNeeds : NeedShortage loss word ⊕ PLift (ProtectsNeeds loss word) := by
  classical
  by_cases failed : ∃ n, ∃ inside : n < (inventoryTrace loss word).length,
      ∃ person good, let cut := (inventoryTrace loss word)[n]'inside
        cut.raw.stock person good < needAt loss cut person good
  · let n := Nat.find failed
    have first := Nat.find_spec failed
    let inside := Classical.choose first
    let pair := Classical.choose_spec first
    let person := Classical.choose pair
    let good := Classical.choose (Classical.choose_spec pair)
    refine .inl ⟨⟨n, inside⟩, person, good, Classical.choose_spec (Classical.choose_spec pair), ?_⟩
    intro i earlier p g
    exact le_of_not_gt (fun short => Nat.find_min failed earlier ⟨i.isLt, p, g, short⟩)
  · refine .inr ⟨?_⟩
    intro cut present person good
    obtain ⟨n, inside, rfl⟩ := List.getElem_of_mem present
    exact le_of_not_gt (fun short => failed ⟨n, inside, person, good, short⟩)

theorem inspectNeeds_passes_iff :
    (∃ accepted, inspectNeeds loss word = .inr accepted) ↔ ProtectsNeeds loss word := by
  constructor
  · rintro ⟨accepted, _⟩
    exact accepted.down
  · intro safe
    cases inspectNeeds loss word with
    | inl shortage => exact (shortage.refutes loss word safe).elim
    | inr accepted => exact ⟨accepted, rfl⟩

theorem a_failed_need_check_names_the_first_shortage (failed : ¬ ProtectsNeeds loss word) :
    ∃ shortage, inspectNeeds loss word = .inl shortage := by
  cases inspectNeeds loss word with
  | inl shortage => exact ⟨shortage, rfl⟩
  | inr safe => exact (failed safe.down).elim

theorem ProtectsNeeds.of_prefix {earlier later : Script Party Good Port Technology Instrument}
    (protects : ProtectsNeeds loss later) (initial : earlier.IsPrefix later) : ProtectsNeeds loss earlier := by
  obtain ⟨tail, rfl⟩ := initial
  intro cut present person good
  apply protects cut _ person good
  obtain ⟨n, within, listed⟩ := List.mem_flatMap.mp present
  have early : n ≤ earlier.length := Nat.le_of_lt_succ (List.mem_range.mp within)
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_range.mpr (by rw [List.length_append]; omega), ?_⟩
  simp only [List.take_append_of_le_length early]
  rcases List.mem_cons.mp listed with head | material
  · exact List.mem_cons.mpr (Or.inl head)
  · apply List.mem_cons.mpr
    apply Or.inr
    by_cases inside : n < earlier.length
    · have extended : n < (earlier ++ tail).length := by rw [List.length_append]; omega
      rw [dif_pos inside] at material
      rw [dif_pos extended, List.getElem_append_left inside]
      exact material
    · rw [dif_neg inside] at material
      exact (List.not_mem_nil material).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.Clearance.Joint.SourceReserve
