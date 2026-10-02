import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRestructuringVocabulary.Schema
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
open MotherArenaNetwork MotherRestructuringOrigin
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

namespace FamilyEncoding
variable (base : MotherArenaHigher.Material rank) (old : Families (formedSorts base)) (encode : FamilyTotal old ↪ MotherArenaHigher.Base rank)

def argumentAddress (index : Fin 31) : Args (formedSorts base) (signature index) ↪ B :=
  argsEmbedding (formedSorts base) (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩) (signature index)

def reader (code : B) (tag : Nat) : ℝ :=
  let pair := (MotherArenaHigher.unpair rank) code
  if ∃ index args value, index.val = tag ∧ argumentAddress base index args = pair.1 ∧ encode ⟨index, args, value⟩ = pair.2 then 0 else 1

def equivalence {material : MotherArenaHigher.Material rank} (hm : (MotherArenaHigher.read rank) material = reader base old encode)
    (index : Fin 31) (args : Args (formedSorts base) (signature index)) : old index args ≃ formedFamilies base material index args :=
  MotherArenaNetworkOrigin.imageEquiv
    ((Function.Embedding.sigmaMk args).trans ((Function.Embedding.sigmaMk index).trans encode))
    (fun code => r2 material index.val (argumentAddress base index args) code) (by
      intro code
      change ((MotherArenaHigher.read rank) material ((MotherArenaHigher.pair rank) (argumentAddress base index args, code)) index.val = 0) ↔ _
      rw [hm]
      simp only [reader, MotherArenaHigher.unpair_pair, ite_eq_left_iff, one_ne_zero, imp_false, not_not]
      constructor
      · rintro ⟨other, values, value, indexEq, argsEq, codeEq⟩
        have same : other = index := Fin.ext indexEq
        cases same
        have same := (argumentAddress base index).injective argsEq
        cases same
        exact ⟨value, codeEq⟩
      · rintro ⟨value, codeEq⟩
        exact ⟨index, args, value, rfl, rfl, codeEq⟩)
end FamilyEncoding

theorem every_families (base : M) (old : Families (formedSorts base)) (encode : FamilyTotal old ↪ B) :
    ∃ material : M, Nonempty ((index : Fin 31) → (args : Args (formedSorts base) (signature index)) →
      old index args ≃ formedFamilies base material index args) := by
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank) (FamilyEncoding.reader base old encode)
  exact ⟨material, ⟨FamilyEncoding.equivalence base old encode hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
