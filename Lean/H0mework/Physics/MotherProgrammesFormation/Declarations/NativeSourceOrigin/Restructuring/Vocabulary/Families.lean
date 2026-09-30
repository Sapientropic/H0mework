import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Vocabulary

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open MotherNetworkFactory
open scoped Classical
noncomputable section

def listEquiv {A C : Type} (e : A ≃ C) : List A ≃ List C where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv := by
    intro values
    induction values with
    | nil => rfl
    | cons value rest ih => simp only [List.map_cons, Equiv.symm_apply_apply, ih]
  right_inv := by
    intro values
    induction values with
    | nil => rfl
    | cons value rest ih => simp only [List.map_cons, Equiv.apply_symm_apply, ih]

def Slot.equiv {old generated : Sorts} (e : ∀ i, old i ≃ generated i) : (slot : Slot) → slot.carrier old ≃ slot.carrier generated
  | .atom index => e index
  | .list index => listEquiv (e index)

def argsEquiv {old generated : Sorts} (e : ∀ i, old i ≃ generated i) :
    (slots : List Slot) → Args old slots ≃ Args generated slots :=
  List.rec (motive := fun slots => Args old slots ≃ Args generated slots)
    (Equiv.refl _) (fun first _ tail => Equiv.prodCongr (first.equiv e) tail)

def transportFamilies {old generated : Sorts} (e : ∀ i, old i ≃ generated i) (family : Families old) : Families generated :=
  fun index args => family index ((argsEquiv e (signature index)).symm args)

def transportedMember {old generated : Sorts} (e : ∀ i, old i ≃ generated i) (family : Families old)
    (index : Fin 31) (args : Args old (signature index)) :
    family index args ≃ transportFamilies e family index (argsEquiv e (signature index) args) :=
  Equiv.cast (congrArg (family index) ((argsEquiv e (signature index)).symm_apply_apply args).symm)

abbrev FamilyTotal {sorts : Sorts} (family : Families sorts) :=
  Σ index : Fin 31, Σ args : Args sorts (signature index), family index args

def familyTotalEquiv {old generated : Sorts} (e : ∀ i, old i ≃ generated i) (family : Families old) :
    FamilyTotal family ≃ FamilyTotal (transportFamilies e family) :=
  Equiv.sigmaCongrRight (fun index => Equiv.sigmaCongr (argsEquiv e (signature index)) (transportedMember e family index))

namespace FamilyEncoding
variable (base : M) (old : Families (formedSorts base)) (encode : FamilyTotal old ↪ B)

def argumentAddress (index : Fin 31) : Args (formedSorts base) (signature index) ↪ B :=
  argsEmbedding (formedSorts base) (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩) (signature index)

def reader (code : B) (tag : Nat) : ℝ :=
  let pair := MotherHigherLawFamily.unpair code
  if ∃ index args value, index.val = tag ∧ argumentAddress base index args = pair.1 ∧ encode ⟨index, args, value⟩ = pair.2 then 0 else 1

def equivalence {material : M} (hm : MotherHigherLawFormation.read material = reader base old encode)
    (index : Fin 31) (args : Args (formedSorts base) (signature index)) : old index args ≃ formedFamilies base material index args :=
  MotherNetworkOrigin.imageEquiv
    ((Function.Embedding.sigmaMk args).trans ((Function.Embedding.sigmaMk index).trans encode))
    (fun code => r2 material index.val (argumentAddress base index args) code) (by
      intro code
      change (MotherHigherLawFormation.read material (MotherHigherLawFamily.pair (argumentAddress base index args, code)) index.val = 0) ↔ _
      rw [hm]
      simp only [reader, MotherHigherLawFamily.unpair_pair, ite_eq_left_iff, one_ne_zero, imp_false, not_not]
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
  obtain ⟨material, hm⟩ := MotherHigherLawFormation.read_surjective (FamilyEncoding.reader base old encode)
  exact ⟨material, ⟨FamilyEncoding.equivalence base old encode hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
