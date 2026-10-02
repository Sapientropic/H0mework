import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaFormation.NetworkCoverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
open MotherArenaNetwork MotherRestructuringOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def natTag (n : Nat) : B := (MotherArenaHigher.baseReadEquiv rank).symm (fun _ _ => (n : ℝ))

theorem natTag_injective : Function.Injective (natTag (rank := rank)) := by
  intro a b same
  have seen := congrFun (congrFun (congrArg (MotherArenaHigher.baseReadEquiv rank) same) (Sum.inl ())) 0
  simp only [natTag, Equiv.apply_symm_apply] at seen
  exact_mod_cast seen

/-- Original finite child lists keep length, order and repetitions. The tags
separate nil from cons even though the mother pair operation is surjective. -/
def listAddress : List B → B :=
  List.rec ((MotherArenaHigher.pair rank) (natTag 0, natTag 0))
    (fun value _ encoded => (MotherArenaHigher.pair rank) (natTag 1, (MotherArenaHigher.pair rank) (value, encoded)))

theorem listAddress_injective : Function.Injective (listAddress (rank := rank)) := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons value rest =>
          have bad := natTag_injective (congrArg Prod.fst ((MotherArenaHigher.pairEquiv rank).injective same))
          cases bad
  | cons value rest ih =>
      intro right same
      cases right with
      | nil =>
          have bad := natTag_injective (congrArg Prod.fst ((MotherArenaHigher.pairEquiv rank).injective same))
          cases bad
      | cons other tail =>
          have pairEq := (MotherArenaHigher.pairEquiv rank).injective (congrArg Prod.snd ((MotherArenaHigher.pairEquiv rank).injective same))
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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
