import H0mework.Physics.LowEnergy.FullQuantum.HistoryLaplace.Stationary

/-! Original Dirac forcing enters on the right of the same complete retarded history operator. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
open FullSpace GaugeGreen ScalarGreen GaugeHistory MatterSpace.Response
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

theorem response_norm (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) :
    ‖response gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive‖≤
      damping⁻¹+M*damping⁻¹^2 := by
  have Mpos : 0≤M := (norm_nonneg _).trans (bounded 0 le_rfl)
  exact (valueLinear gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive).mkContinuous_norm_le
    (by positivity) (value_bound gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive)

def diracResponse (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) : PerturbedGreen.SpatialOperators :=
  (response gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive).comp (inversePrincipal 0)

theorem diracResponse_integral (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    diracResponse gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive source=
      ∫ t : ℝ in Ioi 0, temporalWeight energy damping t •
        fullOperator gauge continuousGauge coupling scalar continuousScalar 0 t (inversePrincipal 0 source) := rfl

theorem diracResponse_pair_integral (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (left source : FullMatterL2) :
    inner ℂ left (diracResponse gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive source)=
      ∫ t : ℝ in Ioi 0, temporalWeight energy damping t*
        inner ℂ left (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 t (inversePrincipal 0 source)) := by
  change inner ℂ left (value gauge continuousGauge coupling scalar continuousScalar energy damping (inversePrincipal 0 source))=_
  have generated := (paired_integral gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive left
    (inversePrincipal 0 source)).symm
  simpa only [paired,integrand,inner_smul_right] using! generated

theorem diracResponse_norm (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) :
    ‖diracResponse gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive‖≤
      (damping⁻¹+M*damping⁻¹^2)*‖inversePrincipal 0‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (response_norm gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive)
      (norm_nonneg _))

theorem stationaryDirac_nonzero (field : GaugeProfile) (parameter : ℝ) (phi : ScalarProfile)
    (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) (nonzero : source≠0) :
    diracResponse (fun _ => field) continuous_const parameter (fun _ => phi) continuous_const
      ‖scalarDriftMap phi‖ (fun _ _ => le_rfl) energy damping positive source≠0 := by
  intro vanished
  have zero : stationaryValue field parameter phi energy damping 0=0 := by
    simp only [stationaryValue,value,integrand,map_zero,smul_zero,integral_zero]
  have identified : inversePrincipal 0 source=0 :=
    stationaryValue_injective field parameter phi energy damping positive (vanished.trans zero.symm)
  have restored := inversePrincipal_right 0 source
  rw [identified,map_zero] at restored
  exact nonzero restored.symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
