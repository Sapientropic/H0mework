import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRestructuringVocabulary.Lists
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
open MotherArenaNetwork MotherRestructuringOrigin
open ResponsibilityLifecycle
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def formedSorts (material : M) : Sorts := fun index => {code : B // bit material index.val code}

namespace SortEncoding
variable (sorts : Sorts) (encode : (Σ i, sorts i) ↪ MotherArenaHigher.Base rank)

def reader (code : B) (tag : Nat) : ℝ :=
  if ∃ (index : Fin 12) (value : sorts index), index.val = tag ∧ encode ⟨index, value⟩ = code then 0 else 1

def equivalence {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader sorts encode)
    (index : Fin 12) : sorts index ≃ formedSorts material index :=
  MotherArenaNetworkOrigin.imageEquiv ((Function.Embedding.sigmaMk index).trans encode)
    (bit material index.val) (by
      intro code
      change ((MotherArenaHigher.read rank) material code index.val = 0) ↔ _
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
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank) (SortEncoding.reader sorts encode)
  exact ⟨material, ⟨SortEncoding.equivalence sorts encode hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
