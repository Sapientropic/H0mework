import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Current
import H0mework.Versions.R2.Physics.YangMillsFlatQuantum.PairingResponse

/-! The occupied spectral preparation acts on the complete mother carrier.
The original spin exchange is retained in its temporal-charge response. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 500000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing
open scoped InnerProductSpace Matrix
noncomputable section

/-- Spin selection extends to every internal mother component; no internal compression is inserted. -/
def preparation : Mother where
  toFun matter spin := if spin.val < 2 then 0 else (spinScale : ℂ) • matter spin
  map_add' first second := by
    funext spin
    change (if spin.val < 2 then 0 else (spinScale : ℂ) • (first spin + second spin)) =
      (if spin.val < 2 then 0 else (spinScale : ℂ) • first spin) +
        (if spin.val < 2 then 0 else (spinScale : ℂ) • second spin)
    split_ifs <;> simp only [smul_add, zero_add]
  map_smul' coefficient matter := by
    funext spin
    change (if spin.val < 2 then 0 else (spinScale : ℂ) • (coefficient • matter spin)) =
      coefficient • (if spin.val < 2 then 0 else (spinScale : ℂ) • matter spin)
    split_ifs <;> simp only [smul_zero, smul_smul, mul_comm]

theorem preparation_embed (point : BasePoint) :
    preparation (embed (Source.vector point)) = embed (prepared point) := by
  funext spin
  change (if spin.val < 2 then 0 else (spinScale : ℂ) •
    sourceColorDiracMatter (fun s c => Source.vector point (s,c)) spin) =
      sourceColorDiracMatter (fun s c => prepared point (s,c)) spin
  simp only [sourceColorDiracMatter, prepared_value]
  split_ifs
  · simp only [zero_smul, Finset.sum_const_zero]
  · rw [Finset.smul_sum]
    simp only [smul_smul]

theorem full_prepared (point : BasePoint) :
    operator preparation (YangMills.FullPairing.prepared point) =
      naturalCoordinates (embed (prepared point)) := by
  rw [YangMills.FullPairing.prepared, operator_coordinates, preparation_embed]

theorem full_prepared_inner (point : BasePoint) :
    inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
      (operator preparation (YangMills.FullPairing.prepared point)) = 1 := by
  rw [full_prepared, inner_embed, coordinates_embed]
  exact prepared_norm point

/-- The physical inner-product readout of the original temporal current. -/
def chargeMother : Mother :=
  flipMatter.comp (currentAction 0 HyperchargeResponse.chargeDirection)

theorem charge_coordinates (values : Source.Index → ℂ) (index : Source.Index) :
    coordinates (chargeMother (embed values)) index = (charge *ᵥ values) index := by
  exact (responseMatrix_mulVec (currentAction 0 HyperchargeResponse.chargeDirection) values index).symm

theorem full_charge_pair (point : BasePoint) :
    inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
      (operator chargeMother (operator preparation (YangMills.FullPairing.prepared point))) = -1 := by
  rw [full_prepared, operator_coordinates, inner_embed]
  simp_rw [charge_coordinates, prepared_charge, Pi.neg_apply, mul_neg]
  rw [Finset.sum_neg_distrib, prepared_norm]

theorem source_charge (point : BasePoint) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (responseMatrix (pairedMother preparation (chargeMother.comp preparation))) = -1 := by
  rw [source_gram]
  have compose : operator (chargeMother.comp preparation) (YangMills.FullPairing.prepared point) =
      operator chargeMother (operator preparation (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared, operator_coordinates]
  rw [compose, full_charge_pair]

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation
