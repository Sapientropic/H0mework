import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRestructuringVocabulary.Sorts
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
open MotherArenaNetwork MotherRestructuringOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def slotEmbedding (sorts : Sorts) (encode : ∀ i, sorts i ↪ B) : (slot : Slot) → slot.carrier sorts ↪ B
  | .atom sort => encode sort
  | .list sort => listEmbedding (encode sort)

def argsEmbedding (sorts : Sorts) (encode : ∀ i, sorts i ↪ B) : (slots : List Slot) → Args sorts slots ↪ B :=
  List.rec (motive := fun slots => Args sorts slots ↪ B)
    ⟨fun _ => natTag 0, fun left right _ => @Subsingleton.elim PUnit inferInstance left right⟩
    (fun slot _ tail => {
      toFun := fun args => (MotherArenaHigher.pair rank) (slotEmbedding sorts encode slot args.1, tail args.2)
      inj' := by
        intro left right same
        have pairEq := (MotherArenaHigher.pairEquiv rank).injective same
        exact Prod.ext ((slotEmbedding sorts encode slot).injective (congrArg Prod.fst pairEq))
          (tail.injective (congrArg Prod.snd pairEq)) })

def formedFamilies (base material : M) : Families (formedSorts base) :=
  fun index args => {code : B // r2 material index.val
    (argsEmbedding (formedSorts base) (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩) (signature index) args) code}

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
