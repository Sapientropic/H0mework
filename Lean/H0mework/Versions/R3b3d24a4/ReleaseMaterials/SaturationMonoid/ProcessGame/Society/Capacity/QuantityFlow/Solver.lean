import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Fast
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.GridSearch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]

private def indexIn {Key : Type*} [DecidableEq Key] (keys : List Key) (key : Key)
    (member : key ∈ keys) : Fin keys.length :=
  ⟨keys.idxOf key, List.idxOf_lt_length_iff.mpr member⟩

private def fastListed (network : Network L R)
    (slots : List L) (items : List R) (allSlots : ∀ slot, slot ∈ slots) (allItems : ∀ item, item ∈ items) :
    Option (network.Certificate) :=
  let numeric : Network (Fin slots.length) (Fin items.length) :=
    { need := fun slot => network.need (slots.get slot)
      capacity := fun item => network.capacity (items.get item)
      allows := fun slot item => network.allows (slots.get slot) (items.get item)
      need_nonnegative := fun slot => network.need_nonnegative (slots.get slot)
      capacity_nonnegative := fun item => network.capacity_nonnegative (items.get item) }
  match numeric.fast with
  | none => none
  | some receipt =>
    let slotIndex := fun slot => indexIn slots slot (allSlots slot)
    let itemIndex := fun item => indexIn items item (allItems item)
    let allocation := fun slot item => receipt.allocation (slotIndex slot) (itemIndex item)
    let group := Finset.univ.filter fun slot => slotIndex slot ∈ receipt.group
    network.check allocation group

/-- Shortest augmenting paths are the ordinary producer. The finite exact
grid gives totality even if a proposed result fails the independent check. -/
def solveListed (network : Network L R)
    (slots : List L) (items : List R) (allSlots : ∀ slot, slot ∈ slots) (allItems : ∀ item, item ∈ items) :
    network.Certificate :=
  match network.fastListed slots items allSlots allItems with
  | some receipt => receipt
  | none => (network.gridSearch slots items).get (network.gridSearch_returns_an_exact_certificate
      slots items allSlots allItems)

end SaturationMonoid.ProcessGame.Society.Capacity.QuantityFlow.Network
