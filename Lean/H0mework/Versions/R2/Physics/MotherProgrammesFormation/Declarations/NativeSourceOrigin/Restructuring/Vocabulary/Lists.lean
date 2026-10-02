import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Projection.Consumer
import H0mework.Versions.R2.Physics.MotherDeclarationsSource.TypeOriginNative

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
open MotherNetworkFactory
noncomputable section

def natTag (n : Nat) : B := MotherHigherLawValue.readBase (MotherHigherLawValue.scalar n)

theorem natTag_injective : Function.Injective natTag := by
  intro a b same
  have seen := congrArg (fun law => MotherPhysicalLaws.lawRead law (MotherSourceTypeOrigin.baseCurrent, 0) 0) same
  simp only [natTag, MotherHigherLawValue.readBase_read, MotherHigherLawValue.scalar_read] at seen
  exact_mod_cast seen

/-- Original finite child lists keep length, order and repetitions. The tags
separate nil from cons even though the mother pair operation is surjective. -/
def listAddress : List B → B :=
  List.rec (MotherHigherLawFamily.pair (natTag 0, natTag 0))
    (fun value _ encoded => MotherHigherLawFamily.pair (natTag 1, MotherHigherLawFamily.pair (value, encoded)))

theorem listAddress_injective : Function.Injective listAddress := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons value rest =>
          have bad := natTag_injective (congrArg Prod.fst (MotherHigherLawFamily.pair_injective same))
          cases bad
  | cons value rest ih =>
      intro right same
      cases right with
      | nil =>
          have bad := natTag_injective (congrArg Prod.fst (MotherHigherLawFamily.pair_injective same))
          cases bad
      | cons other tail =>
          have pairEq := MotherHigherLawFamily.pair_injective (congrArg Prod.snd (MotherHigherLawFamily.pair_injective same))
          exact congrArg₂ List.cons (congrArg Prod.fst pairEq) (ih (congrArg Prod.snd pairEq))

def listEmbedding {A : Type} (encode : A ↪ B) : List A ↪ B where
  toFun := fun values => listAddress (values.map encode)
  inj' := by
    intro left right encoded
    have same : left.map encode = right.map encode := listAddress_injective encoded
    clear encoded
    induction left generalizing right with
    | nil => cases right <;> first | rfl | cases same
    | cons head rest ih =>
        cases right with
        | nil => cases same
        | cons other tail =>
            have pairEq := List.cons.inj same
            exact congrArg₂ List.cons (encode.injective pairEq.1) (ih pairEq.2)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringOrigin
