import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedState

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourcePreparedState
open GaussCoreHilbert GaussComposite GaussComposite.SourceGraph
open FullYSourceCutoffVolterra CanonicalGradedSpatialSource
open CanonicalPreparationCore.Completed CanonicalPreparationCreation CanonicalScalarPreparation
open PreparationChartGuard PreparationScalarCoordinates PreparationVacuumNativeClosure
open Filter
open scoped Topology InnerProductSpace BigOperators

-- Only the requested preparation accuracy changes with n; R, its domain,
-- the source coupling and the variational energy are the same fixed objects.
def preparationPrecision (n : ℕ) : ℝ := 1/((n : ℝ)+1)

theorem preparationPrecision_positive (n : ℕ) : 0<preparationPrecision n := by
  unfold preparationPrecision
  positivity

def preparationSequence (n : ℕ) : SourcePreparation (preparationPrecision n) :=
  sourcePreparation (preparationPrecision n) (preparationPrecision_positive n)

theorem preparationSequence_native_unit (n : ℕ) : ‖(preparationSequence n).point.val‖=1 :=
  (zeroLocalized_physical_norm actualNativeLocalizer (preparationSequence n).point.val).symm.trans (preparationSequence n).unit

theorem preparationSequence_residual :
    Tendsto (fun n : ℕ=>sourceOperator (preparationSequence n).point-
      (sourceEnergy : ℂ) • (preparationSequence n).point.val) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) (fun n=>(preparationSequence n).near.le)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem preparationSequence_created (n : ℕ) :
    prepared (zeroLocalizedProfile actualNativeLocalizer (preparationSequence n).point.val)=
      sourceCreated (GaussHalfDensity.halfDensityEquiv 0 (preparationSequence n).point.val.val) :=
  (preparationSequence n).created

theorem preparationSequence_yukawa_residual :
    Tendsto (fun n : ℕ=>GaussRadialDomain.closedY
      ⟨prepared (zeroLocalizedProfile actualNativeLocalizer (preparationSequence n).point.val),
        (preparationSequence n).yukawaDomain⟩-
      cutoff n (prepared (zeroLocalizedProfile actualNativeLocalizer (preparationSequence n).point.val))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) (fun n=>(preparationSequence n).yukawaCutoff n)
  have geometric : Tendsto (fun n : ℕ=>(915/916 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [pow_succ,zero_mul] using
    (((geometric.mul_const (915/916 : ℝ)).mul_const 916).mul_const GaussYukawaCoefficient.bound)

end LowEnergy.PreparationVacuumSourcePreparedState
