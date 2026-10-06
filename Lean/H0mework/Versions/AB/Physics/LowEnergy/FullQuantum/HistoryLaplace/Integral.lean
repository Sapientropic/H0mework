import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Native
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Integrability

/-! The actual complete spatial history has a strong positive-damping integral. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
open FullSpace GaugeGreen ScalarGreen GaugeHistory MatterSpace.Response
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

theorem future_growth (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (time : ℝ) (future : 0≤time) (initial : FullMatterL2) :
    ‖fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial‖≤
      (1+time*M)*‖initial‖ := by
  have integral : |∫ r in (0 : ℝ)..time, ‖scalarDriftMap (scalar r)‖|≤time*M := by
    have nonnegative : 0≤∫ r in (0 : ℝ)..time, ‖scalarDriftMap (scalar r)‖ :=
      intervalIntegral.integral_nonneg future (fun r _ => norm_nonneg _)
    rw [abs_of_nonneg nonnegative]
    have estimate := intervalIntegral.integral_mono_on future
      ((scalarDriftMap.continuous.comp continuousScalar).norm.intervalIntegrable (μ := volume) 0 time)
      (continuous_const.intervalIntegrable (μ := volume) 0 time)
      (fun r inside => bounded r inside.1)
    simpa only [Function.comp_def,intervalIntegral.integral_const,sub_zero,smul_eq_mul] using! estimate
  exact (fullOperator_bound gauge continuousGauge coupling scalar continuousScalar 0 time initial).trans
    (mul_le_mul_of_nonneg_right (add_le_add_right integral 1) (norm_nonneg initial))

def integrand (energy damping : ℝ) (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  temporalWeight energy damping time • fullOperator gauge continuousGauge coupling scalar continuousScalar 0 time initial

theorem integrand_continuous (energy damping : ℝ) (initial : FullMatterL2) :
    Continuous (integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial) :=
  (temporalWeight_continuous energy damping).smul
    (fullOperator_continuous gauge continuousGauge coupling scalar continuousScalar 0 initial)

theorem integrand_bound (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping time : ℝ) (future : 0≤time) (initial : FullMatterL2) :
    ‖integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial time‖≤
      Retarded.envelope damping M time*‖initial‖ := by
  rw [integrand,norm_smul,temporalWeight_norm]
  exact (mul_le_mul_of_nonneg_left
    (future_growth gauge continuousGauge coupling scalar continuousScalar M bounded time future initial)
    (Real.exp_pos _).le).trans_eq (by unfold Retarded.envelope; ring)

theorem integrand_integrable (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    IntegrableOn (integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial) (Ioi 0) := by
  apply ((Retarded.envelope_integrable damping M positive).mul_const ‖initial‖).mono'
    (integrand_continuous gauge continuousGauge coupling scalar continuousScalar energy damping initial).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
  exact integrand_bound gauge continuousGauge coupling scalar continuousScalar M bounded energy damping t future.le initial

def value (energy damping : ℝ) (initial : FullMatterL2) : FullMatterL2 :=
  ∫ t : ℝ in Ioi 0, integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial t

theorem value_bound (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    ‖value gauge continuousGauge coupling scalar continuousScalar energy damping initial‖≤
      (damping⁻¹+M*damping⁻¹^2)*‖initial‖ := by
  have estimate := norm_integral_le_of_norm_le
    ((Retarded.envelope_integrable damping M positive).mul_const ‖initial‖)
    (show ∀ᵐ t ∂volume.restrict (Ioi 0),
      ‖integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial t‖≤
        Retarded.envelope damping M t*‖initial‖ from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
      exact integrand_bound gauge continuousGauge coupling scalar continuousScalar M bounded energy damping t future.le initial)
  simpa only [value,integral_mul_const,Retarded.envelope_integral damping M positive] using estimate

theorem value_add (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (u v : FullMatterL2) :
    value gauge continuousGauge coupling scalar continuousScalar energy damping (u+v)=
      value gauge continuousGauge coupling scalar continuousScalar energy damping u+
      value gauge continuousGauge coupling scalar continuousScalar energy damping v := by
  simp only [value,integrand,map_add,smul_add]
  exact integral_add (integrand_integrable gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive u)
    (integrand_integrable gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive v)

theorem value_smul (energy damping : ℝ) (c : ℂ) (u : FullMatterL2) :
    value gauge continuousGauge coupling scalar continuousScalar energy damping (c • u)=
      c • value gauge continuousGauge coupling scalar continuousScalar energy damping u := by
  simp only [value,integrand,map_smul,smul_comm (temporalWeight energy damping _) c,integral_smul]

def valueLinear (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) : FullMatterL2 →ₗ[ℂ] FullMatterL2 where
  toFun := value gauge continuousGauge coupling scalar continuousScalar energy damping
  map_add' := value_add gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive
  map_smul' := value_smul gauge continuousGauge coupling scalar continuousScalar energy damping

def response (M : ℝ) (bounded : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) : PerturbedGreen.SpatialOperators :=
  (valueLinear gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive).mkContinuous
    (damping⁻¹+M*damping⁻¹^2) (value_bound gauge continuousGauge coupling scalar continuousScalar M bounded energy damping positive)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
