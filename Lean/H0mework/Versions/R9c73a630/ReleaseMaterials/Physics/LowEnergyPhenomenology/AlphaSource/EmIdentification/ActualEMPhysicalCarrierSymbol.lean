import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierGauss

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMPhysicalCarrier
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SU7MotherLieAlgebra SU7MotherGaugeTheory StageNineP286GaugeAuxiliaryVariation
open StageNineCoframeLocalDifferentiability Stage9C.Material.SpinPair
open Stage10 TemporalGauge CanonicalGauss PhysicalEMGaugeRealization
open scoped BigOperators

def gaussMomentum (k : Fin 3 → ℝ) : BasePoint →L[ℝ] ℝ :=
  ∑ i : Fin 3, k i • EuclideanSpace.proj i.succ

def gaussCos (k : Fin 3 → ℝ) (x : BasePoint) : ℝ := Real.cos (gaussMomentum k x)
def gaussSin (k : Fin 3 → ℝ) (x : BasePoint) : ℝ := Real.sin (gaussMomentum k x)
def gaussSquare (k : Fin 3 → ℝ) : ℝ := ∑ i, (k i)^2

private theorem momentum_coordinate (k : Fin 3 → ℝ) (i : Fin 3) :
    gaussMomentum k (coordinateDirection i.succ) = k i := by
  simp [gaussMomentum, coordinateDirection]

private theorem cos_derivative (k : Fin 3 → ℝ) (x : BasePoint) (i : Fin 3) :
    fieldDirectionalDerivative (gaussCos k) x i.succ = -k i*gaussSin k x := by
  unfold fieldDirectionalDerivative gaussCos
  rw [(gaussMomentum k).hasFDerivAt.cos.fderiv]
  simp only [smul_apply, smul_eq_mul, momentum_coordinate, gaussSin]
  ring

private theorem sin_derivative (k : Fin 3 → ℝ) (x : BasePoint) (i : Fin 3) :
    fieldDirectionalDerivative (gaussSin k) x i.succ = k i*gaussCos k x := by
  unfold fieldDirectionalDerivative gaussSin
  rw [(gaussMomentum k).hasFDerivAt.sin.fderiv]
  simp only [smul_apply, smul_eq_mul, momentum_coordinate, gaussCos]
  ring

private theorem cos_regular (k : Fin 3 → ℝ) : ScalarRegular (gaussCos k) := by
  refine ⟨(gaussMomentum k).differentiable.cos, ?_⟩
  intro i
  simp only [cos_derivative]
  exact ((gaussMomentum k).differentiable.sin).const_mul _

private theorem sin_regular (k : Fin 3 → ℝ) : ScalarRegular (gaussSin k) := by
  refine ⟨(gaussMomentum k).differentiable.sin, ?_⟩
  intro i
  simp only [sin_derivative]
  exact ((gaussMomentum k).differentiable.cos).const_mul _

private theorem cos_laplacian (k : Fin 3 → ℝ) (x : BasePoint) :
    spatialLaplacian (gaussCos k) x = -gaussSquare k*gaussCos k x := by
  unfold spatialLaplacian
  simp only [cos_derivative]
  have term (i : Fin 3) : fieldDirectionalDerivative (fun p => -k i*gaussSin k p) x i.succ =
      -(k i)^2*gaussCos k x := by
    unfold fieldDirectionalDerivative
    rw [fderiv_const_mul (a := gaussSin k) (b := -k i) ((gaussMomentum k).differentiable.sin x)]
    change -k i * fieldDirectionalDerivative (gaussSin k) x i.succ = _
    rw [sin_derivative]
    ring
  simp only [term]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  rfl

private theorem sin_laplacian (k : Fin 3 → ℝ) (x : BasePoint) :
    spatialLaplacian (gaussSin k) x = -gaussSquare k*gaussSin k x := by
  unfold spatialLaplacian
  simp only [sin_derivative]
  have term (i : Fin 3) : fieldDirectionalDerivative (fun p => k i*gaussCos k p) x i.succ =
      -(k i)^2*gaussSin k x := by
    unfold fieldDirectionalDerivative
    rw [fderiv_const_mul (a := gaussCos k) (b := k i) ((gaussMomentum k).differentiable.cos x)]
    change k i * fieldDirectionalDerivative (gaussCos k) x i.succ = _
    rw [cos_derivative]
    ring
  simp only [term]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  rfl

/-- Real and imaginary Fourier coefficients are read from the original covariant differential operator. -/
def gaussSymbolReal (a : P286LieBlockData) (k : Fin 3 → ℝ) : P286LieBlockData :=
  gaussSquare k • a - ∑ i : Fin 3, backgroundAdjoint (backgroundAdjoint a i) i

def gaussSymbolImag (a : P286LieBlockData) (k : Fin 3 → ℝ) : P286LieBlockData :=
  ∑ i : Fin 3, (-2*k i) • backgroundAdjoint a i

/-- The two quadratures generate the Fourier sign and preserve the original Cauchy Gauss operator. -/
theorem gauss_cos_symbol (a : P286LieBlockData) (k : Fin 3 → ℝ) (x : BasePoint) :
    divergence (directionalPotential a (gaussCos k)) x =
      gaussCos k x • gaussSymbolReal a k - gaussSin k x • gaussSymbolImag a k := by
  rw [directional_divergence a _ (cos_regular k), cos_laplacian]
  simp only [cos_derivative, gaussSymbolReal, gaussSymbolImag, Fin.sum_univ_three]
  module

theorem gauss_sin_symbol (a : P286LieBlockData) (k : Fin 3 → ℝ) (x : BasePoint) :
    divergence (directionalPotential a (gaussSin k)) x =
      gaussSin k x • gaussSymbolReal a k + gaussCos k x • gaussSymbolImag a k := by
  rw [directional_divergence a _ (sin_regular k), sin_laplacian]
  simp only [sin_derivative, gaussSymbolReal, gaussSymbolImag, Fin.sum_univ_three]
  module

private theorem background_color (i j : Fin 3) :
    backgroundAdjoint (sourceColorP286Generator j) i =
      gaugeScale • p286LieBracket (sourceColorP286Generator i) (sourceColorP286Generator j) := by
  rw [backgroundAdjoint, p286LieBracket_smul_left]

theorem gauss_color_real (k : Fin 3 → ℝ) (j : Fin 3) :
    gaussSymbolReal (sourceColorP286Generator j) k =
      (gaussSquare k+2*gaugeScale^2) • sourceColorP286Generator j := by
  have neg_right (u v : P286LieBlockData) : p286LieBracket u (-v) = -p286LieBracket u v := by
    rw [← neg_one_smul ℝ v, p286LieBracket_smul_right]
    module
  unfold gaussSymbolReal
  simp only [backgroundAdjoint, p286LieBracket_smul_left, p286LieBracket_smul_right,
    Fin.sum_univ_three]
  fin_cases j <;>
    simp [sourceColorP286Generator_bracket, neg_right, bracket_zero_right, smul_smul]
  all_goals module

theorem gauss_color_imag (k : Fin 3 → ℝ) :
    (fun j : Fin 3 => gaussSymbolImag (sourceColorP286Generator j) k) =
      ![(2*gaugeScale*k 2) • sourceColorP286Generator 1 + (-2*gaugeScale*k 1) • sourceColorP286Generator 2,
        (-2*gaugeScale*k 2) • sourceColorP286Generator 0 + (2*gaugeScale*k 0) • sourceColorP286Generator 2,
        (2*gaugeScale*k 1) • sourceColorP286Generator 0 + (-2*gaugeScale*k 0) • sourceColorP286Generator 1] := by
  funext j
  unfold gaussSymbolImag
  simp only [background_color, Fin.sum_univ_three]
  fin_cases j <;> simp [sourceColorP286Generator_bracket, smul_smul] <;> module

theorem gauss_y_symbol (k : Fin 3 → ℝ) :
    gaussSymbolReal HyperchargeResponse.chargeDirection k =
      gaussSquare k • HyperchargeResponse.chargeDirection ∧
    gaussSymbolImag HyperchargeResponse.chargeDirection k = 0 := by
  have central (i : Fin 3) : backgroundAdjoint HyperchargeResponse.chargeDirection i = 0 := by
    have paid := CanonicalGauss.central_right 1 (gaugeScale • sourceColorP286Generator i)
    simpa only [one_smul, backgroundAdjoint] using paid
  unfold gaussSymbolReal gaussSymbolImag
  simp_rw [central]
  simp [backgroundAdjoint, bracket_zero_right]

end LowEnergy.GaussComposite.ActualEMPhysicalCarrier
