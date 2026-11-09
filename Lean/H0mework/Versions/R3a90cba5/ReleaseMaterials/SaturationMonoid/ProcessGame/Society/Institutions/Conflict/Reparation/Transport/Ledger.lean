import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Entries
import Mathlib.Data.Finite.Sum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Shape

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Capitalism.Universal.Root.Financial.Installation (KeepsKeys)

variable {law : DebtActivationLaw} {base joint : WorldRelationNetwork}
  (shape : Shape law base joint) {before after : base.Support} {first last : law.DebtState}
  (motion : Motion law first last) (original : LedgerWriteEvolutionAt base ⟨before⟩ ⟨after⟩)
  (owner : OpenResponsibilityAt base before)

private def readFibre {A B : Type} (presentation : A ≃ B) {P : B → Type}
    (generate : ∀ a, P (presentation a)) (value : B) : P value :=
  presentation.apply_symm_apply value ▸ generate (presentation.symm value)

@[simp] private theorem readFibre_forward {A B : Type} (presentation : A ≃ B) {P : B → Type}
    (generate : ∀ a, P (presentation a)) (value : A) :
    readFibre presentation generate (presentation value) = generate value := by
  let castAlong {a b : A} (equal : a = b) (witness : presentation a = presentation b) :
      witness ▸ generate a = generate b := by cases equal; rfl
  exact castAlong (presentation.symm_apply_apply value) (presentation.apply_symm_apply (presentation value))

private def destinationOn (entry : OpenResponsibilityAt base before ⊕ Unit) :
    Σ target : OpenResponsibilityAt joint (shape.support after last),
      LedgerEntryEvolutionAt joint (shape.rows before first entry) target :=
  match entry with
  | .inl old => let moved := original.destination old
    ⟨shape.original moved.1, shape.oldEvolution motion moved.2⟩
  | .inr _ => ⟨shape.repair after last, shape.repairEvolution motion original owner⟩

private def originOn (entry : OpenResponsibilityAt base after ⊕ Unit) :
    Σ start : OpenResponsibilityAt joint (shape.support before first),
      LedgerEntryEvolutionAt joint start (shape.rows after last entry) :=
  match entry with
  | .inl old => let moved := original.origin old
    ⟨shape.original moved.1, shape.oldEvolution motion moved.2⟩
  | .inr _ => ⟨shape.repair before first, shape.repairEvolution motion original owner⟩

/-- Lift the whole original write, including the target-origin map. -/
def lift : LedgerWriteEvolutionAt joint ⟨shape.support before first⟩ ⟨shape.support after last⟩ where
  destination := readFibre (shape.rows before first) (destinationOn shape motion original owner)
  origin := readFibre (shape.rows after last) (originOn shape motion original owner)

theorem lift_destination_original (entry : OpenResponsibilityAt base before) :
    (shape.lift motion original owner |>.destination (shape.original (r := first) entry)).1 =
      shape.original (r := last) (original.destination entry).1 := by
  simp only [lift, readFibre_forward, destinationOn]

theorem lift_origin_original (entry : OpenResponsibilityAt base after) :
    (shape.lift motion original owner |>.origin (shape.original (r := last) entry)).1 =
      shape.original (r := first) (original.origin entry).1 := by
  simp only [lift, readFibre_forward, originOn]

theorem lift_destination_repair :
    (shape.lift motion original owner |>.destination (shape.repair before first)).1 =
      shape.repair after last := by
  simp only [lift, readFibre_forward, destinationOn]

theorem lift_origin_repair :
    (shape.lift motion original owner |>.origin (shape.repair after last)).1 =
      shape.repair before first := by
  simp only [lift, readFibre_forward, originOn]

theorem lift_keeps_keys (keys : KeepsKeys original) : KeepsKeys (shape.lift motion original owner) := by
  constructor
  · intro entry
    obtain ⟨old | repair, rfl⟩ := (shape.rows before first).surjective entry
    · rw [show shape.rows before first (.inl old) = shape.original (r := first) old from rfl,
        shape.lift_destination_original, shape.old_key, shape.old_key, keys.1]
    · cases repair
      rw [show shape.rows before first (.inr ()) = shape.repair before first from rfl,
        shape.lift_destination_repair, shape.repair_key, shape.repair_key]
  · intro entry
    obtain ⟨old | repair, rfl⟩ := (shape.rows after last).surjective entry
    · rw [show shape.rows after last (.inl old) = shape.original (r := last) old from rfl,
        shape.lift_origin_original, shape.old_key, shape.old_key, keys.2]
    · cases repair
      rw [show shape.rows after last (.inr ()) = shape.repair after last from rfl,
        shape.lift_origin_repair, shape.repair_key, shape.repair_key]

theorem finiteRows (s : base.Support) (r : law.DebtState) (finite : Finite (OpenResponsibilityAt base s)) :
    Finite (OpenResponsibilityAt joint (shape.support s r)) := by
  let := finite
  exact Finite.of_equiv _ (shape.rows s r)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Shape
