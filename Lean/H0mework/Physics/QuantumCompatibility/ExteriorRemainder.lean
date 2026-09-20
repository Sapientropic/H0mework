import H0mework.Physics.QuantumCompatibility.ExteriorJet

/-! A source-sized error bound for the actual exterior transport and its
Stage 8 jet. The multilinear estimate is applied before reading coordinates. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open StageNineP286GaugeConnectionVariation StageNineExteriorMotherLieRepresentation
open DiracExteriorMatterLocalGaugeLink
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

def fundamentalTupleLinear (degree : ℕ) (vectors : Fin degree → SU7FundamentalCarrier) :
    FundamentalMatrix →ₗ[ℝ] (Fin degree → SU7FundamentalCarrier) where
  toFun matrix slot := matrix *ᵥ vectors slot
  map_add' := by intros; ext slot; simp [Matrix.add_mulVec]
  map_smul' := by intros; ext slot; simp [Matrix.smul_mulVec]

def fundamentalTuple (degree : ℕ) (vectors : Fin degree → SU7FundamentalCarrier) :
    FundamentalMatrix →L[ℝ] (Fin degree → SU7FundamentalCarrier) :=
  (fundamentalTupleLinear degree vectors).toContinuousLinearMap

def exteriorWedgeErrorScale (point : BasePoint) (direction : LorentzianIndex) (degree : ℕ)
    (vectors : Fin degree → SU7FundamentalCarrier) (coordinate : ExteriorBasisIndex degree)
    (duration : ℝ) : ℝ :=
  ‖exteriorCoordinateForm degree coordinate‖ * degree *
    (‖fundamentalTuple degree vectors‖ * (1 + duration * ‖connectionGenerator point direction‖)) ^ (degree - 1) *
      ‖fundamentalTuple degree vectors‖ * ‖connectionGenerator point direction‖ ^ 2

theorem exteriorTransport_wedge_remainder
    (point : BasePoint) (direction : LorentzianIndex) (degree : ℕ)
    (vectors : Fin degree → SU7FundamentalCarrier) (coordinate : ExteriorBasisIndex degree)
    (duration : ℝ) (nonnegative : 0 ≤ duration) :
    ‖(su7ExteriorBasis degree).repr
        (exteriorLinkAction degree (connectionTransport point direction duration)
          ((exteriorPower.ιMulti ℂ degree) vectors)) coordinate -
      (su7ExteriorBasis degree).repr
        (exteriorLinkAction degree (connectionJet point direction duration)
          ((exteriorPower.ιMulti ℂ degree) vectors)) coordinate‖ ≤
      exteriorWedgeErrorScale point direction degree vectors coordinate duration * duration ^ 2 := by
  let action := fundamentalTuple degree vectors
  let generator := connectionGenerator point direction
  let transport := connectionTransport point direction duration
  let jet := connectionJet point direction duration
  have unitNorm : ‖transport‖ = 1 := CStarRing.norm_of_mem_unitary
    (connectionTransport_unitary point direction duration)
  have jetNorm : ‖jet‖ ≤ 1 + duration * ‖generator‖ := by
    dsimp only [jet]
    rw [connectionJet_eq]
    exact (norm_add_le _ _).trans_eq (by rw [norm_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg nonnegative])
  have one_le : 1 ≤ 1 + duration * ‖generator‖ := le_add_of_nonneg_right (mul_nonneg nonnegative (norm_nonneg _))
  have maxBound : max ‖action transport‖ ‖action jet‖ ≤ ‖action‖ * (1 + duration * ‖generator‖) := by
    apply max_le
    · exact (action.le_opNorm transport).trans (by rw [unitNorm]; exact mul_le_mul_of_nonneg_left one_le (norm_nonneg _))
    · exact (action.le_opNorm jet).trans (mul_le_mul_of_nonneg_left jetNorm (norm_nonneg _))
  have difference : ‖action transport - action jet‖ ≤ ‖action‖ * (‖generator‖ ^ 2 * duration ^ 2) := by
    rw [← map_sub]
    exact (action.le_opNorm (transport - jet)).trans
      (mul_le_mul_of_nonneg_left (connectionTransport_remainder point direction duration nonnegative) (norm_nonneg _))
  have estimate := (exteriorCoordinateForm degree coordinate).norm_image_sub_le
    (action transport) (action jet)
  have powerBound := pow_le_pow_left₀ (by positivity : 0 ≤ max ‖action transport‖ ‖action jet‖) maxBound (degree - 1)
  have bound := mul_le_mul
    (mul_le_mul_of_nonneg_left powerBound (by positivity : 0 ≤ ‖exteriorCoordinateForm degree coordinate‖ * degree))
    difference (norm_nonneg _) (by positivity)
  have result := estimate.trans (by simpa only [Fintype.card_fin] using bound)
  simp only [exteriorLinkAction, exteriorPower.map_apply_ιMulti]
  change ‖(exteriorCoordinateForm degree coordinate) (action transport) -
    (exteriorCoordinateForm degree coordinate) (action jet)‖ ≤ _
  simpa only [exteriorWedgeErrorScale, action, generator, mul_assoc] using result

def exteriorErrorScale (point : BasePoint) (direction : LorentzianIndex) (degree : ℕ)
    (matter : ⋀[ℂ]^degree SU7FundamentalCarrier) (coordinate : ExteriorBasisIndex degree)
    (duration : ℝ) : ℝ :=
  ∑ input, ‖(su7ExteriorBasis degree).repr matter input‖ *
    exteriorWedgeErrorScale point direction degree (exteriorBasisInput degree input) coordinate duration

theorem exteriorTransport_remainder
    (point : BasePoint) (direction : LorentzianIndex) (degree : ℕ)
    (matter : ⋀[ℂ]^degree SU7FundamentalCarrier) (coordinate : ExteriorBasisIndex degree)
    (duration : ℝ) (nonnegative : 0 ≤ duration) :
    ‖(su7ExteriorBasis degree).repr
        (exteriorLinkAction degree (connectionTransport point direction duration) matter) coordinate -
      (su7ExteriorBasis degree).repr
        (exteriorLinkAction degree (connectionJet point direction duration) matter) coordinate‖ ≤
      exteriorErrorScale point direction degree matter coordinate duration * duration ^ 2 := by
  have inputBound (input : ExteriorBasisIndex degree) :=
    exteriorTransport_wedge_remainder point direction degree (exteriorBasisInput degree input)
      coordinate duration nonnegative
  simp only [exteriorBasisInput_wedge_eq_basis_slot] at inputBound
  conv_lhs => rw [← (su7ExteriorBasis degree).sum_repr matter]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ input : ExteriorBasisIndex degree,
        ‖(su7ExteriorBasis degree).repr matter input *
          ((su7ExteriorBasis degree).repr
              (exteriorLinkAction degree (connectionTransport point direction duration)
                (su7ExteriorBasis degree input)) coordinate -
            (su7ExteriorBasis degree).repr
              (exteriorLinkAction degree (connectionJet point direction duration)
                (su7ExteriorBasis degree input)) coordinate)‖ := norm_sum_le _ _
    _ ≤ ∑ input : ExteriorBasisIndex degree,
        ‖(su7ExteriorBasis degree).repr matter input‖ *
          (exteriorWedgeErrorScale point direction degree (exteriorBasisInput degree input)
            coordinate duration * duration ^ 2) := by
      apply Finset.sum_le_sum
      intro input _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (inputBound input) (norm_nonneg _)
    _ = _ := by simp only [exteriorErrorScale, Finset.sum_mul, mul_assoc]

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
