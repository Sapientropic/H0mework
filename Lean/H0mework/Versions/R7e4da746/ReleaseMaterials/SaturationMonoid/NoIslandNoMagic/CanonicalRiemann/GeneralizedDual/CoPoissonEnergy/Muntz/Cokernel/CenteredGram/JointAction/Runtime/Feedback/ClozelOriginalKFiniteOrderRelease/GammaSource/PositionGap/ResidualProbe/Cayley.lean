import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe

open BurnolPhysicalState MeasureTheory Set Finset
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped BigOperators

open private anchor_right from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedWordSeparation
open private shiftedAction shifted_right from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe
open private cayley_binomial cayley_power_norm from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.FinitePowerWindow.Geometric

local notation "R" => burnolDirectRightResolventCLM
local notation "S" => burnolDirectRightResolvent
local notation "U" => sourceCayley
local notation "δ" => sourceDamping
local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)

def discount (c : BurnolCompletedMellinCoordinate) (x : ℝ) : ℝ :=
  x/(δ c+x)

theorem discount_nonneg (c : BurnolCompletedMellinCoordinate) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ discount c x :=
  div_nonneg hx ((sourceDamping_pos c).le.trans (le_add_of_nonneg_right hx))

theorem discount_lt_one (c : BurnolCompletedMellinCoordinate) {x : ℝ} (hx : 0 ≤ x) :
    discount c x < 1 :=
  (div_lt_one (add_pos_of_pos_of_nonneg (sourceDamping_pos c) hx)).mpr
    (lt_add_of_pos_left _ (sourceDamping_pos c))

theorem discount_monotone (c : BurnolCompletedMellinCoordinate) {x y : ℝ}
    (hx : 0 ≤ x) (before : x ≤ y) : discount c x ≤ discount c y := by
  unfold discount
  apply (div_le_div_iff₀ (add_pos_of_pos_of_nonneg (sourceDamping_pos c) hx)
    (add_pos_of_pos_of_nonneg (sourceDamping_pos c) (hx.trans before))).mpr
  nlinarith [mul_le_mul_of_nonneg_left before (sourceDamping_pos c).le]

private theorem shifted_norm (c : BurnolCompletedMellinCoordinate) {x : ℝ} (hx : 0 ≤ x) (v : BurnolL2) :
    ‖S (c.value/2+(x:ℂ)) v‖ ≤ (2/δ c)*‖v‖ := by
  let z := c.value/2+(x:ℂ)
  have rate : z.re-1/4 = δ c/2+x := by
    dsimp only [z,sourceDamping]
    rw [Complex.add_re,Complex.ofReal_re,Complex.div_re]
    norm_num
    ring
  have positive : 0 < δ c/2 := half_pos (sourceDamping_pos c)
  have damped : 0 < δ c/2+x := add_pos_of_pos_of_nonneg positive hx
  change ‖S z v‖ ≤ _
  rw [burnolDirectRightResolvent,norm_neg]
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖burnolDirectRightResolventIntegrand z v t‖ :=
      norm_integral_le_integral_norm _
    _ = (δ c/2+x)⁻¹*‖v‖ := by
      simp only [burnolDirectRightResolventIntegrand,norm_smul,
        (burnolMultiplicativeDilation _).norm_map,norm_positiveMellinQuarterRightResolventWeight,rate]
      rw [integral_mul_const,integral_exp_mul_Ioi (neg_lt_zero.mpr damped) 0]
      simp only [mul_zero,Real.exp_zero,neg_div_neg_eq,one_div]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [show 2/δ c = (δ c/2)⁻¹ by rw [inv_div]]
      exact inv_anti₀ positive (le_add_of_nonneg_right hx)

private def shiftedCLM (c : BurnolCompletedMellinCoordinate) (x : ℝ) (hx : 0 ≤ x) : End :=
  (shiftedAction c x hx).mkContinuous (2/δ c) (shifted_norm c hx)

private theorem actual_transfer (c : BurnolCompletedMellinCoordinate) (x : ℝ) (hx : 0 ≤ x) :
    shiftedCLM c x hx * (1-(discount c x:ℂ) • U c) = (1-(discount c x:ℂ)) • R c := by
  let H := shiftedCLM c x hx
  let ρ : ℂ := discount c x
  have paid (v : BurnolL2) : H v - R c v = (x:ℂ) • H (R c v) := by
    have source := burnolDirectRightResolvent_identity (c.value/2+(x:ℂ)) (c.value/2)
      (shifted_right c hx) (anchor_right c) v
    change H v - R c v = (c.value/2+(x:ℂ)-c.value/2) • H (R c v) at source
    rwa [show c.value/2+(x:ℂ)-c.value/2 = (x:ℂ) by ring] at source
  have scale : ρ*(δ c:ℂ) = (1-ρ)*(x:ℂ) := by
    have balance : discount c x*δ c = (1-discount c x)*x := by
      unfold discount
      field_simp [(add_pos_of_pos_of_nonneg (sourceDamping_pos c) hx).ne']
      ring
    change (discount c x:ℂ)*(δ c:ℂ) = (1-(discount c x:ℂ))*(x:ℂ)
    exact_mod_cast balance
  apply ContinuousLinearMap.ext
  intro v
  change H (v - ρ • (v+(δ c:ℂ) • R c v)) = (1-ρ) • R c v
  simp only [map_sub,map_smul,map_add,smul_add,smul_smul,scale]
  linear_combination (norm := module) (1-ρ) • paid v

/-- All coefficients of the finite rightward probe multiply strictly positive original R powers. -/
def rightWeight (c : BurnolCompletedMellinCoordinate) (x : ℝ) (k j : Nat) : ℂ :=
  (1-(discount c x:ℂ)) * (discount c x:ℂ)^k * (k.choose j:ℂ) * (δ c:ℂ)^j

def finiteShift (c : BurnolCompletedMellinCoordinate) (x : ℝ) (fuel : Nat) : End :=
  ∑ k ∈ range fuel, ∑ j ∈ range (k+1), rightWeight c x k j • (R c)^(j+1)

private theorem finite_geometric (c : BurnolCompletedMellinCoordinate) (x : ℝ) (fuel : Nat) :
    finiteShift c x fuel = (1-(discount c x:ℂ)) •
      (R c * ∑ k ∈ range fuel, ((discount c x:ℂ) • U c)^k) := by
  unfold finiteShift
  simp only [Finset.mul_sum,Finset.smul_sum]
  apply sum_congr rfl
  intro k _
  simp only [smul_pow,cayley_binomial,mul_smul_comm,Finset.mul_sum,Finset.smul_sum]
  apply sum_congr rfl
  intro j _
  rw [← pow_succ',smul_smul,smul_smul]
  congr 1
  unfold rightWeight
  ring

/-- The finite word and its literal remainder are generated by the same original resolvent identity. -/
theorem actual_shift_remainder (c : BurnolCompletedMellinCoordinate) (x : ℝ) (hx : 0 ≤ x)
    (fuel : Nat) (v : BurnolL2) :
    S (c.value/2+(x:ℂ)) v - finiteShift c x fuel v =
      S (c.value/2+(x:ℂ)) ((((discount c x:ℂ) • U c)^fuel) v) := by
  let A := (discount c x:ℂ) • U c
  let H := shiftedCLM c x hx
  have source := congrArg (fun T : End => T * ∑ k ∈ range fuel, A^k) (actual_transfer c x hx)
  change H * (1-A) * (∑ k ∈ range fuel, A^k) =
    ((1-(discount c x:ℂ)) • R c) * (∑ k ∈ range fuel, A^k) at source
  rw [mul_assoc,mul_neg_geom_sum,mul_sub,mul_one,smul_mul_assoc,← finite_geometric] at source
  have result : H - finiteShift c x fuel = H*A^fuel := by linear_combination (norm := module) source
  exact congrArg (fun T : End => T v) result

theorem actual_shift_error (c : BurnolCompletedMellinCoordinate) (x : ℝ) (hx : 0 ≤ x)
    (fuel : Nat) (v : BurnolL2) :
    ‖S (c.value/2+(x:ℂ)) v - finiteShift c x fuel v‖ ≤
      ((2/δ c)*‖v‖) * (discount c x)^fuel := by
  rw [actual_shift_remainder c x hx,smul_pow,_root_.smul_apply]
  have error := shifted_norm c hx ((discount c x:ℂ)^fuel • ((U c)^fuel) v)
  simp only [norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (discount_nonneg c hx),cayley_power_norm] at error
  calc
    _ ≤ (2/δ c)*((discount c x)^fuel*‖v‖) := error
    _ = _ := by ring

theorem finite_shift_read (c : BurnolCompletedMellinCoordinate) (x : ℝ) (fuel : Nat)
    (read : Read) (v : BurnolL2) :
    read (finiteShift c x fuel v) =
      ∑ k ∈ range fuel, ∑ j ∈ range (k+1), rightWeight c x k j * read (((R c)^(j+1)) v) := by
  simp only [finiteShift,_root_.sum_apply,_root_.smul_apply,map_sum,map_smul,smul_eq_mul]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
