import H0mework.Versions.X.NavierStokes.MaterialAction.CoframeAction
import H0mework.NavierStokes.MaterialAction.DiagonalCoframe

set_option autoImplicit false
open scoped Matrix BigOperators

namespace SaturationMonoid.NavierStokes.NativeCoframeSpin

open PhysicsCore DiracCliffordRepresentation PointwiseDiracSpinConnectionLift
open DiracExteriorMatterAction SU7ExteriorBreakingYukawa
open StageNineP286GaugeConnectionVariationDensity
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliMotherAction NativePauliCoframeAction

noncomputable section

def weight : Fin 4 → ℝ := ![2, -1, -1, -1]

def jet (velocity : PhysicalSpace) (logDerivative : Fin 4 → ℝ) : PointwiseLorentzianCoframeJet :=
  NativeDiagonalCoframe.jet (NativeCanonicalFluidCoframe.diagonal velocity)
    (fun direction internal => weight internal * NativeCanonicalFluidCoframe.diagonal velocity internal *
      logDerivative direction)

theorem jet_coframe (velocity : PhysicalSpace) (logDerivative : Fin 4 → ℝ) :
    (jet velocity logDerivative).coframe = NativeCanonicalFluidCoframe.coframe velocity := rfl

def ratio (density : ℝ) (first second : Fin 4) : ℝ :=
  if first = 0 then (if second = 0 then 1 else density)
  else (if second = 0 then density⁻¹ else 1)

theorem diagonal_ratio (velocity : PhysicalSpace) (first second : Fin 4) :
    NativeCanonicalFluidCoframe.diagonal velocity first /
      NativeCanonicalFluidCoframe.diagonal velocity second =
      ratio (NativeCanonicalFluidCoframe.density velocity) first second := by
  fin_cases first <;> fin_cases second <;>
    simp [NativeCanonicalFluidCoframe.diagonal, ratio,
      ← NativeCanonicalFluidCoframe.scale_cube velocity,
      (NativeCanonicalFluidCoframe.scale_pos velocity).ne'] <;> field_simp

def connection (density : ℝ) (logDerivative : Fin 4 → ℝ) : PointwiseLorentzSpinConnection :=
  fun direction first second =>
    (if direction = first then weight first * ratio density first second * logDerivative second else 0) -
      (if direction = second then minkowskiInternalSign first * minkowskiInternalSign second *
        weight second * ratio density second first * logDerivative first else 0)

theorem jet_connection (velocity : PhysicalSpace) (logDerivative : Fin 4 → ℝ) :
    (jet velocity logDerivative).lorentzSpinConnection =
      connection (NativeCanonicalFluidCoframe.density velocity) logDerivative := by
  have nonzero (index : Fin 4) : NativeCanonicalFluidCoframe.diagonal velocity index ≠ 0 := by
    fin_cases index <;> simp [NativeCanonicalFluidCoframe.diagonal,
      (NativeCanonicalFluidCoframe.scale_pos velocity).ne']
  rw [jet, NativeDiagonalCoframe.spin_connection _ _ nonzero]
  funext direction first second
  simp only [NativeDiagonalCoframe.spinConnection, connection, ← diagonal_ratio, div_eq_mul_inv]
  split_ifs <;> ring

def spinLiftFormula (density : ℝ) (z : Fin 4 → ℝ) : Fin 4 → DiracMatrix :=
  ![(-(density * z 1) : ℂ) • (diracGamma 0 * diracGamma 1) +
      (-(density * z 2) : ℂ) • (diracGamma 0 * diracGamma 2) +
      (-(density * z 3) : ℂ) • (diracGamma 0 * diracGamma 3),
    (z 0 / (2 * density) : ℂ) • (diracGamma 0 * diracGamma 1) +
      (z 3 / 2 : ℂ) • (diracGamma 3 * diracGamma 1) -
      (z 2 / 2 : ℂ) • (diracGamma 1 * diracGamma 2),
    (z 0 / (2 * density) : ℂ) • (diracGamma 0 * diracGamma 2) -
      (z 3 / 2 : ℂ) • (diracGamma 2 * diracGamma 3) +
      (z 1 / 2 : ℂ) • (diracGamma 1 * diracGamma 2),
    (z 0 / (2 * density) : ℂ) • (diracGamma 0 * diracGamma 3) +
      (z 2 / 2 : ℂ) • (diracGamma 2 * diracGamma 3) -
      (z 1 / 2 : ℂ) • (diracGamma 3 * diracGamma 1)]

theorem spinLift_eq (density : ℝ) (z : Fin 4 → ℝ) (direction : Fin 4) :
    diracSpinConnectionLift (connection density z) direction = spinLiftFormula density z direction := by
  fin_cases direction <;>
    simp [diracSpinConnectionLift, loweredLorentzConnectionCoefficient, connection, ratio, weight,
      lorentzBivectorFirst, lorentzBivectorSecond, minkowskiInternalSign, spinLiftFormula,
      Fin.sum_univ_succ] <;> module

def normalizedSpin (density : ℝ) (logDerivative : Fin 4 → ℝ) : DiracMatrix :=
  ∑ direction, (ratio density 0 direction : ℂ) •
    (spinActionMatrix direction * diracSpinConnectionLift (connection density logDerivative) direction)

private theorem spatialSquare (index : Fin 4) (spatial : index ≠ 0) :
    diracGamma index * diracGamma index = 1 := by
  fin_cases index <;> simp_all [diracGamma]

private theorem gamma_swap (first second : Fin 4) (different : first ≠ second) :
    diracGamma first * diracGamma second = -(diracGamma second * diracGamma first) := by
  apply add_eq_zero_iff_eq_neg.mp
  rw [diracGamma_clifford]
  simp [complexMinkowskiEntry, minkowskiInternalMetric, different]

private theorem spatialMiddle (index other : Fin 4) (spatial : index ≠ 0) (different : index ≠ other) :
    diracGamma index * (diracGamma other * diracGamma index) = -diracGamma other := by
  rw [← mul_assoc, gamma_swap index other different, neg_mul, mul_assoc, spatialSquare index spatial, mul_one]

private theorem spatialLeft (index other : Fin 4) (spatial : index ≠ 0) :
    diracGamma index * (diracGamma index * diracGamma other) = diracGamma other := by
  rw [← mul_assoc, spatialSquare index spatial, one_mul]

/-- The spatial connection terms cancel in the original Dirac lift of this generated frame. -/
theorem normalizedSpin_eq (density : ℝ) (positive : 0 < density) (logDerivative : Fin 4 → ℝ) :
    normalizedSpin density logDerivative = (-(3 / 2 : ℝ) * logDerivative 0 : ℂ) • 1 := by
  simp only [normalizedSpin, spinLift_eq, Fin.sum_univ_four]
  dsimp only [spinLiftFormula, spinActionMatrix]
  simp only [Matrix.cons_val, mul_add, mul_sub, Matrix.mul_smul]
  simp [ratio, neg_mul, mul_assoc, spatialMiddle, spatialLeft, smul_add, smul_smul]
  have cancel : (density : ℂ) * ((logDerivative 0 : ℂ) / (2 * density)) = logDerivative 0 / 2 := by
    field_simp [positive.ne']
  rw [cancel, show diracGamma 0 * diracGamma 0 = -(1 : DiracMatrix) from diracGammaZero_sq]
  module

theorem ratio_eq_compensation (velocity : PhysicalSpace) (direction : Fin 4) :
    ratio (NativeCanonicalFluidCoframe.density velocity) 0 direction =
      (NativePauliCoframeAction.compensation velocity direction)⁻¹ := by
  fin_cases direction <;> simp [ratio, NativePauliCoframeAction.compensation]

/-- The complete geometric response is computed through the original spin lift and matter action. -/
theorem spin_response (velocity : PhysicalSpace) (logDerivative : Fin 4 → ℝ)
    (matter : DiracExteriorMatterCarrier) :
    normalizedDerivative velocity (fun direction => diracMatrixMatterAction
      (diracSpinConnectionLift (jet velocity logDerivative).lorentzSpinConnection direction) matter) =
      (-(3 / 2 : ℝ) * logDerivative 0 : ℂ) • matter := by
  have ratio_complex (direction : Fin 4) : (compensation velocity direction : ℂ)⁻¹ =
      (ratio (NativeCanonicalFluidCoframe.density velocity) 0 direction : ℂ) := by
    exact_mod_cast (ratio_eq_compensation velocity direction).symm
  simp only [normalizedDerivative, ratio_complex, jet_connection,
    ← LinearMap.comp_apply, ← diracMatrixMatterAction_mul, ← diracMatrixMatterAction_smul_matrix,
    Fin.sum_univ_four, ← diracMatrixMatterAction_add_matrix]
  have evaluated := congrArg (fun matrix : DiracMatrix => diracMatrixMatterAction matrix matter)
    (normalizedSpin_eq _ (NativeCanonicalFluidCoframe.density_pos velocity) logDerivative)
  have identity : diracMatrixMatterAction 1 matter = matter := by
    funext spin
    simp [diracMatrixMatterAction, Matrix.one_apply]
  simpa only [normalizedSpin, Fin.sum_univ_four, diracMatrixMatterAction_smul_matrix,
    identity] using evaluated

end
end SaturationMonoid.NavierStokes.NativeCoframeSpin
