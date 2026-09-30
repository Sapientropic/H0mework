import H0mework.Physics.ReceiverActuation.CommonLoad

/-! # Exact command-load incidence in the receiver's eleven literal output ports -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable (hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource) (clockMax : Nat)

def outputLoadNode (channel : FiniteEmbodimentChannel) :
    Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size :=
  let entry := receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)
  ⟨((aigOutputBank entry).vec.get (outputLoadPort channel).val (outputLoadPort channel).isLt).gate,
    ((aigOutputBank entry).vec.get (outputLoadPort channel).val (outputLoadPort channel).isLt).hgate⟩

theorem outputLoadNode_val (channel : FiniteEmbodimentChannel) :
    (outputLoadNode hardware clockMax channel).val =
      (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size +
        (finiteADCChannelEquivFin channel).val + 1 := by
  change ((aigOutputBank _).vec.get _ _).gate = _
  rw [aigOutputBank_ref_gate]
  change _ + ((finiteADCChannelEquivFin channel).val + 1) = _
  omega

/-- The inverse uses only the original channel equivalence and the literal declaration offset. -/
def outputLoadChannel? (node : Fin (aigOutputBank
    (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size) (polarity : Bool) :
    Option FiniteEmbodimentChannel :=
  if loaded : (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size < node.val ∧
      polarity = false then
    have bounded : node.val - (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size - 1 < 10 := by
      have bound := node.isLt
      have size := aigOutputBank_size (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
      omega
    some (finiteADCChannelEquivFin.symm ⟨node.val -
      (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size - 1, bounded⟩)
  else none

private theorem channel_of_offset (size node : Nat) (channel : FiniteEmbodimentChannel)
    (bounded : node - size - 1 < 10) (same : node = size + (finiteADCChannelEquivFin channel).val + 1) :
    some (finiteADCChannelEquivFin.symm ⟨node - size - 1, bounded⟩) = some channel := by
  have index_eq : (⟨node - size - 1, bounded⟩ : Fin 10) = finiteADCChannelEquivFin channel := by
    apply Fin.ext
    dsimp only
    omega
  exact congrArg some ((congrArg finiteADCChannelEquivFin.symm index_eq).trans
    (finiteADCChannelEquivFin.symm_apply_apply channel))

theorem outputLoadChannel?_command (channel : FiniteEmbodimentChannel) :
    outputLoadChannel? hardware clockMax (outputLoadNode hardware clockMax channel) false = some channel := by
  have index := outputLoadNode_val hardware clockMax channel
  have eligible : (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size <
      (outputLoadNode hardware clockMax channel).val ∧ false = false := ⟨by omega, rfl⟩
  rw [outputLoadChannel?, dif_pos eligible]
  exact channel_of_offset _ _ channel _ index

/-- Each accepted coordinate is exactly one command's positive output; no source address is guessed. -/
theorem outputLoadChannel?_some_iff
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (polarity : Bool) (channel : FiniteEmbodimentChannel) :
    outputLoadChannel? hardware clockMax node polarity = some channel ↔
      node = outputLoadNode hardware clockMax channel ∧ polarity = false := by
  constructor
  · intro selected
    unfold outputLoadChannel? at selected
    split at selected
    · rename_i eligible
      have same := congrArg finiteADCChannelEquivFin (Option.some.inj selected)
      rw [Equiv.apply_symm_apply] at same
      have values := congrArg Fin.val same
      refine ⟨Fin.ext ?_, eligible.2⟩
      have address := outputLoadNode_val hardware clockMax channel
      dsimp only at values
      omega
    · contradiction
  · rintro ⟨rfl, rfl⟩
    exact outputLoadChannel?_command hardware clockMax channel

theorem outputLoadNode_injective : Function.Injective (outputLoadNode hardware clockMax) := by
  intro left right same
  have received := outputLoadChannel?_command hardware clockMax left
  rw [same, outputLoadChannel?_command] at received
  exact (Option.some.inj received).symm

def outputLoadAddress (channel : FiniteEmbodimentChannel) :
    AIGCapacitorAddress (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig :=
  ⟨(outputLoadNode hardware clockMax channel, false), by
    have selected := aigOutputBank_decl (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
      (outputLoadPort channel)
    simp only [aigNodeHasCapacitor, outputLoadNode, selected]⟩

theorem outputLoadAddress_injective : Function.Injective (outputLoadAddress hardware clockMax) := by
  intro left right same
  exact outputLoadNode_injective hardware clockMax
    (congrArg (fun address => address.val.1) same)

theorem outputLoadChannel?_address_iff
    (address : AIGCapacitorAddress (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig)
    (channel : FiniteEmbodimentChannel) :
    outputLoadChannel? hardware clockMax address.val.1 address.val.2 = some channel ↔
      address = outputLoadAddress hardware clockMax channel := by
  rw [outputLoadChannel?_some_iff]
  constructor
  · rintro ⟨sameNode, samePolarity⟩
    exact Subtype.ext (Prod.ext sameNode samePolarity)
  · intro same
    exact ⟨congrArg (fun a => a.val.1) same, congrArg (fun a => a.val.2) same⟩

theorem outputLoadAddresses_card :
    (Finset.univ.image (outputLoadAddress hardware clockMax)).card = 10 := by
  rw [Finset.card_image_of_injective _ (outputLoadAddress_injective hardware clockMax), Finset.card_univ]
  exact Fintype.card_congr finiteADCChannelEquivFin

theorem outputLoadChannel?_negative
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size) :
    outputLoadChannel? hardware clockMax node true = none := by
  simp only [outputLoadChannel?, Bool.true_eq_false, and_false, ↓reduceDIte]

theorem outputLoadChannel?_old
    (node : Fin (aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).aig.decls.size)
    (old : node.val < (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)).aig.decls.size)
    (polarity : Bool) : outputLoadChannel? hardware clockMax node polarity = none := by
  exact dif_neg (fun eligible => (lt_asymm old eligible.1))

theorem outputLoadChannel?_validity :
    outputLoadChannel? hardware clockMax
      ⟨((aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).vec.get 0 (by decide)).gate,
        ((aigOutputBank (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))).vec.get 0 (by decide)).hgate⟩ false = none := by
  apply dif_neg
  intro eligible
  have address := aigOutputBank_ref_gate (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1)) (0 : Fin 11)
  dsimp only at eligible
  simp only [Fin.val_zero, Nat.add_zero] at address
  omega

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
