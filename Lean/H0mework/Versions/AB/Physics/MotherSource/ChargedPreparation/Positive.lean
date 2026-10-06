import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Classical

/-! The same source current produces the complementary positive-charge preparation. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
namespace SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.Positive
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing
open scoped InnerProductSpace Matrix
noncomputable section

def vector (point : BasePoint) : Source.Index → ℂ :=
  (spinScale : ℂ) • Source.vector point-ChargedPreparation.prepared point

theorem vector_value (point : BasePoint) (index : Source.Index) :
    vector point index = if index.1.val < 2 then (spinScale : ℂ)*Source.vector point index else 0 := by
  simp only [vector, Pi.sub_apply, Pi.smul_apply, prepared_value, smul_eq_mul]
  split_ifs <;> ring

theorem vector_charge (point : BasePoint) : charge *ᵥ vector point = vector point := by
  funext index
  rw [charge_mulVec, vector_value]
  simp only [sign]
  split_ifs <;> ring

theorem vector_norm (point : BasePoint) :
    (∑ index : Source.Index, star (vector point index)*vector point index) = 1 := by
  simp only [Fintype.sum_prod_type]
  simp [vector_value, Source.vector, Source.amplitude, spinPairCoefficients,
    Fin.sum_univ_four, Fin.sum_univ_two]
  have phase := Source.phase_star_mul frequency point
  have scale : (spinScale : ℂ)^2 = 2 := by exact_mod_cast spinScale_sq
  dsimp only [upperPhase] at *
  change (starRingEnd ℂ) (Stage9C.Material.SpinPair.phase frequency point) *
    Stage9C.Material.SpinPair.phase frequency point = 1 at phase
  norm_num only [map_ofNat]
  linear_combination ((spinScale : ℂ)^2/2)*phase + scale/2

def preparation : Mother := (spinScale : ℂ) • (1 : Mother)-ChargedPreparation.preparation

theorem preparation_embed (point : BasePoint) :
    preparation (embed (Source.vector point)) = embed (vector point) := by
  simp only [preparation, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
    ChargedPreparation.preparation_embed, vector, map_sub, map_smul]

theorem full_prepared (point : BasePoint) :
    operator preparation (YangMills.FullPairing.prepared point) = naturalCoordinates (embed (vector point)) := by
  rw [YangMills.FullPairing.prepared, operator_coordinates, preparation_embed]

theorem full_charge_pair (point : BasePoint) :
    inner ℂ (operator preparation (YangMills.FullPairing.prepared point))
      (operator chargeMother (operator preparation (YangMills.FullPairing.prepared point))) = 1 := by
  rw [full_prepared, operator_coordinates, inner_embed]
  simp_rw [charge_coordinates, vector_charge]
  exact vector_norm point

def dualPreparation : Mother :=
  flipMatter.comp ((fromOperator (operator preparation).adjoint).comp flipMatter)

theorem paired_charge (matter : DiracExteriorMatterCarrier) :
    pairedMother preparation (chargeMother.comp preparation) matter =
      dualPreparation (currentAction 0 HyperchargeResponse.chargeDirection (preparation matter)) := by
  simp [pairedMother, dualPreparation, chargeMother, fromOperator, operator]

theorem classical_current (point : BasePoint) :
    actual.conjugateMatter point
      (dualPreparation (currentAction 0 HyperchargeResponse.chargeDirection
        (preparation (actual.matter point)))) = 4*(spinScale : ℂ) := by
  rw [← paired_charge, dual_gram]
  have compose : operator (chargeMother.comp preparation) (YangMills.FullPairing.prepared point) =
      operator chargeMother (operator preparation (YangMills.FullPairing.prepared point)) := by
    simp [YangMills.FullPairing.prepared, operator_coordinates]
  rw [compose, full_charge_pair, mul_one]

def amountAmplitude (amount : ℕ) : ℂ := (Real.sqrt (amount : ℝ) : ℂ)

def amountMatter (amount : ℕ) (point : BasePoint) : DiracExteriorMatterCarrier :=
  amountAmplitude amount • preparation (actual.matter point)

def amountDual (amount : ℕ) (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  amountAmplitude amount • (actual.conjugateMatter point).comp dualPreparation

theorem amount_current (amount : ℕ) (point : BasePoint) :
    amountDual amount point (currentAction 0 HyperchargeResponse.chargeDirection (amountMatter amount point)) =
      4*(spinScale : ℂ)*(amount : ℂ) := by
  have square : (amountAmplitude amount)^2 = (amount : ℂ) := by
    unfold amountAmplitude
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg amount : 0 ≤ (amount : ℝ))
  simp only [amountDual, amountMatter, LinearMap.smul_apply, LinearMap.comp_apply, map_smul,
    smul_eq_mul, classical_current]
  linear_combination (4*(spinScale : ℂ))*square

end
end SaturationMonoid.PhysicsCore.Stage10.ChargedPreparation.Positive
