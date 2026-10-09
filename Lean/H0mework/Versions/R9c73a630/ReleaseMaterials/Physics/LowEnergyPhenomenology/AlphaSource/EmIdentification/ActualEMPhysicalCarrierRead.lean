import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierEnergy
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierGreen

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMPhysicalCarrier
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction
open StageNineP286GaugeAuxiliaryVariation StageNineCoframeLocalDifferentiability
open StageNineCanonicalCauchyState StageNineFormNativeP286GaugeGeometricFirstVariation
open Stage9C.Material.SpinPair Stage10 TemporalGauge CanonicalGauss PhysicalEMGaugeRealization
open scoped BigOperators Matrix
attribute [local irreducible] Stage10.Runtime.configuration Stage10.Runtime.source

def gaussFrame : Fin 3 ⊕ Fin 1 → P286LieBlockData :=
  Sum.elim sourceColorP286Generator (fun _ => HyperchargeResponse.chargeDirection)

def gaussFourierLie (a b : P286LieBlockData) (k : Fin 3 → ℝ) : ℂ :=
  (p286LiePairing a (gaussSymbolReal b k):ℂ)+Complex.I*(p286LiePairing a (gaussSymbolImag b k):ℂ)

def gaussOriginalFourierMatrix (k : Fin 3 → ℝ) :
    Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℂ :=
  fun i j => ((2*lapse:ℝ):ℂ)*gaussFourierLie (gaussFrame i) (gaussFrame j) k

private theorem color_pair (i j : Fin 3) :
    p286LiePairing (sourceColorP286Generator i) (sourceColorP286Generator j) =
      if i = j then 1/2 else 0 := by
  rw [sourceColorP286Generator_pairing, sourceColorP286Generator_color]
  fin_cases i <;> fin_cases j <;> norm_num [sourceColorRaw, Fin.ext_iff]

private theorem color_y (i : Fin 3) :
    p286LiePairing (sourceColorP286Generator i) HyperchargeResponse.chargeDirection = 0 := by
  rw [sourceColorP286Generator_pairing]
  fin_cases i <;> norm_num [HyperchargeResponse.chargeDirection]

private theorem y_color (i : Fin 3) :
    p286LiePairing HyperchargeResponse.chargeDirection (sourceColorP286Generator i) = 0 := by
  rw [p286LiePairing_symmetric, color_y]

private theorem vec3_last {α : Type} (a b c : α) : (![a,b,c] : Fin 3 → α) 2 = c := rfl

private theorem pair_zero (a : P286LieBlockData) : p286LiePairing a 0 = 0 := by
  simp [p286LiePairing, specialUnitaryLiePairing, hyperchargeLiePairing]

/-- The metric in the current equation is the original P286 bilinear form, not a normalization choice. -/
theorem gauss_frame_pairing (i j : Fin 3 ⊕ Fin 1) :
    (p286LiePairing (gaussFrame i) (gaussFrame j):ℂ) = gaussCurrentMetric i j := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [gaussFrame, Sum.elim_inl, color_pair, gaussCurrentMetric, Matrix.diagonal_apply]
      by_cases h : i = j <;> simp [h]
    | inr j => simp [gaussFrame, color_y, gaussCurrentMetric]
  | inr i =>
    cases j with
    | inl j => simp [gaussFrame, y_color, gaussCurrentMetric]
    | inr j =>
      fin_cases i
      fin_cases j
      simp [gaussFrame, charge_pairing, gaussCurrentMetric]

/-- This is the complete four-dimensional symbol of the original Cauchy Gauss equation. -/
theorem gauss_original_fourier_matrix (k : Fin 3 → ℝ) :
    gaussOriginalFourierMatrix k = ((2*lapse:ℝ):ℂ) • (gaussCurrentMetric*gaussFullBlock k) := by
  have imag (j : Fin 3) := congrFun (gauss_color_imag k) j
  ext i j
  simp only [gaussOriginalFourierMatrix, Matrix.smul_apply, smul_eq_mul]
  congr 1
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp only [gaussFourierLie, gaussFrame, Sum.elim_inl, gauss_color_real, imag,
        gaussCurrentMetric, Matrix.diagonal_mul, gaussFullBlock, Matrix.fromBlocks_apply₁₁,
        Sum.elim_inl, gaussColorBlock]
      fin_cases i <;> fin_cases j <;>
        norm_num [p286LiePairing_add_right, p286LiePairing_smul_right, color_pair,
          gaussColorDiagonal, gaussColorCross, Matrix.cons_val_zero, Matrix.cons_val_one,
          vec3_last, Matrix.cons_val, Fin.ext_iff] <;> ring
    | inr j =>
      simp [gaussFourierLie, gaussFrame, (gauss_y_symbol k).1, (gauss_y_symbol k).2,
        p286LiePairing_smul_right, color_y, gaussCurrentMetric, Matrix.diagonal_mul,
        gaussFullBlock, pair_zero]
  | inr i =>
    cases j with
    | inl j =>
      simp only [gaussFourierLie, gaussFrame, Sum.elim_inl, Sum.elim_inr, gauss_color_real, imag,
        gaussCurrentMetric, Matrix.diagonal_mul, gaussFullBlock, Matrix.fromBlocks_apply₂₁,
        Sum.elim_inr]
      fin_cases j <;>
        norm_num [p286LiePairing_add_right, p286LiePairing_smul_right, y_color,
          Matrix.cons_val_zero, Matrix.cons_val_one, vec3_last]
    | inr j =>
      fin_cases i
      fin_cases j
      simp [gaussFourierLie, gaussFrame, (gauss_y_symbol k).1, (gauss_y_symbol k).2,
        p286LiePairing_smul_right, charge_pairing, gaussCurrentMetric, Matrix.diagonal_mul,
        gaussFullBlock, pair_zero]

def gaussOriginalCurrent (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint) :
    Fin 3 ⊕ Fin 1 → ℂ :=
  fun i => (emCauchyMatterRead matter dual x (gaussFrame i):ℂ)

/-- The full four-current is inserted with its own original normalization. -/
theorem gauss_original_current_response (k : Fin 3 → ℝ) (hk : gaussSquare k ≠ 0)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint) :
    gaussOriginalFourierMatrix k *ᵥ (gaussCurrentGreen k *ᵥ gaussOriginalCurrent matter dual x) =
      -gaussOriginalCurrent matter dual x := by
  rw [gauss_original_fourier_matrix, Matrix.mulVec_mulVec, gauss_current_green_equation k hk,
    Matrix.neg_mulVec, Matrix.one_mulVec]



/-- The source bilinear form generates the four-direction projection and retains its complement. -/
def gaussLieProjection (a : P286LieBlockData) : P286LieBlockData :=
  (∑ i : Fin 3, (2*p286LiePairing (sourceColorP286Generator i) a) • sourceColorP286Generator i) +
    p286LiePairing HyperchargeResponse.chargeDirection a • HyperchargeResponse.chargeDirection

def gaussLieRemainder (a : P286LieBlockData) : P286LieBlockData := a-gaussLieProjection a

private theorem projection_color (a : P286LieBlockData) (j : Fin 3) :
    p286LiePairing (sourceColorP286Generator j) (gaussLieProjection a) =
      p286LiePairing (sourceColorP286Generator j) a := by
  unfold gaussLieProjection
  rw [Fin.sum_univ_three]
  simp only [p286LiePairing_add_right, p286LiePairing_smul_right, color_pair, color_y]
  fin_cases j <;> norm_num [Fin.ext_iff] <;> first | rfl | ring
  apply congrArg (fun i : Fin 3 => p286LiePairing (sourceColorP286Generator i) a)
  apply Fin.ext
  norm_num

private theorem projection_y (a : P286LieBlockData) :
    p286LiePairing HyperchargeResponse.chargeDirection (gaussLieProjection a) =
      p286LiePairing HyperchargeResponse.chargeDirection a := by
  unfold gaussLieProjection
  rw [Fin.sum_univ_three]
  simp [p286LiePairing_add_right, p286LiePairing_smul_right, y_color, charge_pairing]

theorem gauss_remainder_frame (a : P286LieBlockData) (i : Fin 3 ⊕ Fin 1) :
    p286LiePairing (gaussLieRemainder a) (gaussFrame i) = 0 := by
  rw [p286LiePairing_symmetric]
  have rem : gaussLieRemainder a = a+(-1:ℝ) • gaussLieProjection a := by
    unfold gaussLieRemainder
    module
  rw [rem, p286LiePairing_add_right, p286LiePairing_smul_right]
  cases i <;> simp [gaussFrame, projection_color, projection_y]

private theorem remainder_color (a : P286LieBlockData) (j : Fin 3) :
    p286LiePairing (gaussLieRemainder a) (sourceColorP286Generator j) = 0 :=
  gauss_remainder_frame a (.inl j)

private theorem remainder_y (a : P286LieBlockData) :
    p286LiePairing (gaussLieRemainder a) HyperchargeResponse.chargeDirection = 0 :=
  gauss_remainder_frame a (.inr 0)

/-- The other native Lie tests retain their matter current; the four-mode inverse does not delete it. -/
theorem gauss_fourier_complement (a : P286LieBlockData) (k : Fin 3 → ℝ)
    (j : Fin 3 ⊕ Fin 1) : gaussFourierLie (gaussLieRemainder a) (gaussFrame j) k = 0 := by
  cases j with
  | inl j =>
    have imag := congrFun (gauss_color_imag k) j
    simp only [gaussFourierLie, gaussFrame, Sum.elim_inl, gauss_color_real, imag]
    fin_cases j <;>
      simp [p286LiePairing_add_right, p286LiePairing_smul_right, remainder_color,
        Matrix.cons_val_zero, Matrix.cons_val_one, vec3_last]
  | inr j =>
    simp [gaussFourierLie, gaussFrame, (gauss_y_symbol k).1, (gauss_y_symbol k).2,
      p286LiePairing_smul_right, remainder_y, pair_zero]

/-- An exact original Euler residual, without any assumption of complementary-current neutrality. -/
theorem em_cauchy_complement_current (V : BasePoint → ℝ) (hV : ScalarRegular V)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint)
    (a : P286LieBlockData) :
    emCauchyGaussRead V matter dual x (gaussLieRemainder a) =
      emCauchyMatterRead matter dual x (gaussLieRemainder a) := by
  unfold emCauchyGaussRead
  rw [em_cauchy_gauss V hV]
  have em : emDirection = (-1:ℝ) • sourceColorP286Generator 2 +
      (-1/2:ℝ) • HyperchargeResponse.chargeDirection := by
    unfold emDirection
    module
  simp only [em, p286LiePairing_add_right, p286LiePairing_smul_right, remainder_color, remainder_y]
  simp only [mul_zero, add_zero, zero_add]
  rfl

end LowEnergy.GaussComposite.ActualEMPhysicalCarrier
