import H0mework.Physics.MotherProgrammesFormationProgrammes.Entry
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammes

open Stage9C.Revision MotherFamilyOccurrence StageEightDiscreteFormation MotherCoordinateCompletion
open RationalSourceFormation

noncomputable section

def entryAddress (visit : MotherVisit) : Fin (codeOf visit).unpair.1 → ℕ :=
  unpack (codeOf visit).unpair.1 (codeOf visit).unpair.2

def entryVisit (visit : MotherVisit) (slot : Fin (codeOf visit).unpair.1) : MotherVisit :=
  pastVisit visit (entryAddress visit slot)

/-- Length, entry addresses and both inputs of each entry are read from
the current mother history. The result is a finite calculation programme. -/
private def readProgramme (visit : MotherVisit) (shape : ℕ × ℕ) : List Entry :=
  List.ofFn (fun slot : Fin shape.1 => entryAt (pastVisit visit (unpack shape.1 shape.2 slot)))

def programmeAt (visit : MotherVisit) : List Entry :=
  readProgramme visit (codeOf visit).unpair

theorem programme_length (visit : MotherVisit) :
    (programmeAt visit).length = (codeOf visit).unpair.1 := List.length_ofFn

theorem entry_address_le (visit : MotherVisit) (slot : Fin (codeOf visit).unpair.1) :
    entryAddress visit slot ≤ codeOf visit :=
  (unpack_le _ _ slot).trans (Nat.unpair_right_le _)

theorem entry_visit_code (visit : MotherVisit) (slot : Fin (codeOf visit).unpair.1) :
    codeOf (entryVisit visit slot) = entryAddress visit slot :=
  past_code _ _ (entry_address_le visit slot)

theorem programme_prefixes (visit : MotherVisit) (entry : Entry) (member : entry ∈ programmeAt visit) :
    temporalDepth entry.discreteVisit.history ≤ temporalDepth visit.history ∧
      temporalDepth entry.coordinateVisit.history ≤ temporalDepth visit.history ∧
      ∀ slot : Fin (65 * 4),
        temporalDepth (MotherCoordinateCompletion.sample (65 * 4) entry.coordinateVisit slot).history ≤
          temporalDepth visit.history := by
  obtain ⟨slot, rfl⟩ := List.mem_ofFn.mp member
  have nested := entry_prefixes (entryVisit visit slot)
  have past : temporalDepth (entryVisit visit slot).history ≤ temporalDepth visit.history := past_depth_le _ _
  exact ⟨nested.1.trans past, nested.2.1.trans past, fun slot => (nested.2.2 slot).trans past⟩

theorem programme_data_packed {count : ℕ} (codes : Fin count → ℕ) :
    (programmeAt (SpinPair.visit (10 + Nat.pair count (pack codes)))).map Entry.data =
      List.ofFn (fun slot => (entryAt (SpinPair.visit (10 + codes slot))).data) := by
  rw [programmeAt, code_at, Nat.unpair_pair]
  simp only [readProgramme, unpack_pack, List.map_ofFn]
  apply congrArg List.ofFn
  funext slot
  apply entry_data_same_code
  have bound : codes slot ≤ Nat.pair count (pack codes) := by
    have inner : codes slot ≤ pack codes := by
      simpa only [unpack_pack] using unpack_le count (pack codes) slot
    exact inner.trans (Nat.right_le_pair _ _)
  rw [past_code _ _ (by simpa only [code_at] using bound), code_at]

/-- The target is confined to coverage: the unchanged reader already
generates every finite list of complete discrete material and rational coordinates. -/
theorem every_programme (targets : List Datum) :
    ∃ code, (programmeAt (SpinPair.visit (10 + code))).map Entry.data = targets := by
  have each : ∀ slot : Fin targets.length, ∃ code,
      (entryAt (SpinPair.visit (10 + code))).data = targets.get slot :=
    fun slot => every_entry (targets.get slot)
  choose codes generated using each
  refine ⟨Nat.pair targets.length (pack codes), ?_⟩
  rw [programme_data_packed]
  rw [show (fun slot => (entryAt (SpinPair.visit (10 + codes slot))).data) = targets.get from
    funext generated]
  exact List.ofFn_get targets

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammes
