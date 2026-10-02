import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Lists

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle
open scoped Classical
noncomputable section

abbrev Sorts := Fin 12 → Type

def sortsOf (v : ResponsibilityLifecycle.Vocabulary.{0}) : Sorts
  | 0 => v.SourceEvent
  | 1 => v.Content
  | 2 => v.Residual
  | 3 => v.Bearer
  | 4 => v.ProtectedInterest
  | 5 => v.Scope
  | 6 => v.Lineage
  | 7 => v.Incidence
  | 8 => v.SourceObservation.Carrier
  | 9 => v.NextActorSignal
  | 10 => v.AgeSignal
  | 11 => v.TransferOfferSignal

def formedSorts (material : M) : Sorts := fun index => {code : B // bit material index.val code}

namespace SortEncoding
variable (sorts : Sorts) (encode : (Σ i, sorts i) ↪ B)

def reader (code : B) (tag : Nat) : ℝ :=
  if ∃ (index : Fin 12) (value : sorts index), index.val = tag ∧ encode ⟨index, value⟩ = code then 0 else 1

def equivalence {material : M} (hm : MotherHigherLawFormation.read material = reader sorts encode)
    (index : Fin 12) : sorts index ≃ formedSorts material index :=
  MotherNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk index).trans encode)
    (bit material index.val) (by
      intro code
      change (MotherHigherLawFormation.read material code index.val = 0) ↔ _
      rw [hm]
      simp only [reader, ite_eq_left_iff, one_ne_zero, imp_false, not_not]
      constructor
      · rintro ⟨other, value, same, encoded⟩
        have same : other = index := Fin.ext same
        cases same
        exact ⟨value, encoded⟩
      · rintro ⟨value, encoded⟩
        exact ⟨index, value, rfl, encoded⟩)
end SortEncoding

theorem every_sorts (sorts : Sorts) (encode : (Σ i, sorts i) ↪ B) :
    ∃ material : M, Nonempty ((i : Fin 12) → sorts i ≃ formedSorts material i) := by
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective (SortEncoding.reader sorts encode)
  exact ⟨material, ⟨SortEncoding.equivalence sorts encode hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
