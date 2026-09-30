import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Sorts

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open MotherNetworkFactory
noncomputable section

inductive Slot
  | atom (sort : Fin 12)
  | list (sort : Fin 12)

def Slot.carrier (sorts : Sorts) : Slot → Type
  | .atom sort => sorts sort
  | .list sort => List (sorts sort)

def Args (sorts : Sorts) : List Slot → Type :=
  List.rec PUnit (fun first _ tail => first.carrier sorts × tail)

/-- The 26 original lifecycle evidence families followed by the five
restructuring families. Their real argument lists fix this schema. -/
def signature : Fin 31 → List Slot
  | 0 => [.atom 0]
  | 1 | 2 | 3 | 4 | 5 => [.atom 0, .atom 1]
  | 6 => [.atom 0, .atom 5]
  | 7 | 8 => [.atom 3, .atom 0, .atom 5]
  | 9 => [.atom 1, .atom 5]
  | 10 => [.atom 0, .atom 1, .atom 2, .atom 2]
  | 11 | 12 => [.atom 0, .atom 1, .atom 5]
  | 13 => [.atom 0, .atom 5, .atom 5]
  | 14 => [.atom 0, .atom 3, .atom 3, .atom 5]
  | 15 | 16 | 17 | 18 | 19 => [.atom 0, .atom 1, .atom 5]
  | 20 | 21 => [.atom 0, .atom 7, .atom 1, .atom 7, .atom 1, .atom 5, .atom 5]
  | 22 | 23 | 24 | 25 => [.atom 0, .atom 1, .atom 5]
  | 26 => [.atom 0, .atom 7, .atom 1, .atom 7, .atom 1]
  | 27 => [.atom 0, .atom 1, .list 1]
  | 28 => [.atom 0, .list 1, .atom 1]
  | 29 | 30 => [.atom 0, .atom 1, .atom 1]
  | ⟨index + 31, bound⟩ => False.elim (by omega)

def Slot.embedding (sorts : Sorts) (encode : ∀ i, sorts i ↪ B) : (slot : Slot) → slot.carrier sorts ↪ B
  | .atom sort => encode sort
  | .list sort => listEmbedding (encode sort)

def argsEmbedding (sorts : Sorts) (encode : ∀ i, sorts i ↪ B) : (slots : List Slot) → Args sorts slots ↪ B :=
  List.rec (motive := fun slots => Args sorts slots ↪ B)
    ⟨fun _ => natTag 0, fun left right _ => @Subsingleton.elim PUnit inferInstance left right⟩
    (fun slot _ tail => {
      toFun := fun args => MotherHigherLawFamily.pair (slot.embedding sorts encode args.1, tail args.2)
      inj' := by
        intro left right same
        have pairEq := MotherHigherLawFamily.pair_injective same
        exact Prod.ext ((slot.embedding sorts encode).injective (congrArg Prod.fst pairEq))
          (tail.injective (congrArg Prod.snd pairEq)) })

abbrev Families (sorts : Sorts) := (index : Fin 31) → Args sorts (signature index) → Type

def formedFamilies (base material : M) : Families (formedSorts base) :=
  fun index args => {code : B // r2 material index.val
    (argsEmbedding (formedSorts base) (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩) (signature index) args) code}

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
