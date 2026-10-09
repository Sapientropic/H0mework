import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeElectricCurrentEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceInverseElectricCurrentGrowth
open GaussCoreHilbert GaussCoreDifferential GaussMatterCore GaussNativePotential GaussYukawaCoefficient
open GaussNativeForm GaussLiveMomentum GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceScalarBalancedForce SourceMixedNativeReturn SourceInverseElectricCurrentForm SourceInverseElectricCurrentCoefficient
open SourceScalarPositiveBulkWard SourceCartanCubic

/-- All constants are norms of the actual source coframe and native representation. -/
def contactBound (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  ∑ i : Fin 3, ∑ b : Fin 3, |GaussMatterCore.coefficient i b z| *
    ‖(quantumTerm b).toContinuousLinearMap‖*‖gaugeCoordinate i v.2‖

def sourceGrowth (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) : ℝ :=
  2*contactBound v z*‖branchMap sharp‖*(‖vacuum‖+2)

private theorem contactBound_nonneg (v : Ambient) (z : SourceCoordinateSlice) : 0 ≤ contactBound v z := by
  unfold contactBound
  positivity

theorem original_contact_bound (v : Ambient) (z : SourceCoordinateSlice) :
    ‖contactFiber v z‖ ≤ contactBound v z := by
  unfold contactFiber contactBound
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_assoc]
  exact mul_le_mul_of_nonneg_left
    ((quantumTerm b).toContinuousLinearMap.le_opNorm (gaugeCoordinate i v.2)) (abs_nonneg _)

/-- The actual coefficient is at most linear in the source scalar radius, with no inverse-chart growth. -/
theorem original_current_growth (sharp : Bool) (v : Ambient) (z : SourceCoordinateSlice) :
    ‖currentKernel sharp v z‖ ≤ sourceGrowth sharp v z*radius z := by
  have hY : ‖branchMap sharp (scalarField z)‖ ≤ ‖branchMap sharp‖*((‖vacuum‖+2)*radius z) :=
    ((branchMap sharp).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (scalar_bound z) (norm_nonneg _))
  have hK : ‖currentKernel sharp v z‖ ≤ 2*‖contactFiber v z‖*‖branchMap sharp (scalarField z)‖ := by
    unfold currentKernel
    rw [norm_smul,norm_neg,Complex.norm_I,one_mul]
    apply (norm_sub_le _ _).trans
    have h := add_le_add (norm_mul_le (contactFiber v z) (branchMap sharp (scalarField z)))
      (norm_mul_le (branchMap sharp (scalarField z)) (contactFiber v z))
    nlinarith only [h]
  apply hK.trans
  calc
    _  ≤  (2*contactBound v z)*(‖branchMap sharp‖*((‖vacuum‖+2)*radius z)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (original_contact_bound v z) (by norm_num)) hY
        (norm_nonneg _) (mul_nonneg (by norm_num) (contactBound_nonneg v z))
    _ = _ := by unfold sourceGrowth;ring

/-- The same generated bound controls every actual windowed gauge-current input. -/
theorem original_window_current_growth (sharp : Bool) (m ell : ℕ) (v : Ambient) (hv : v.1=0)
    (f : QuantumTest) (z : SourceCoordinateSlice) :
    ‖windowCurrent sharp m ell v f z‖ ≤
      |SourceNativeCutoffContact.theta m ell z| *(sourceGrowth sharp v z*radius z)*‖f z‖ := by
  rw [original_window_current_apply sharp m ell v hv,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have h := ((currentKernel sharp v z).le_opNorm (f z)).trans
    (mul_le_mul_of_nonneg_right (original_current_growth sharp v z) (norm_nonneg _))
  exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (mul_assoc _ _ _).symm

end LowEnergy.SourceInverseElectricCurrentGrowth
