import H0mework.Physics.LowEnergy.FullQuantum.HistoryLaplace.Integral

/-! The actual nonautonomous force stays inside the same convergent strong time integral. -/
set_option autoImplicit false
open MeasureTheory Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
open FullSpace GaugeGreen ScalarGreen GaugeHistory MatterSpace.Response
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

include continuousGauge continuousScalar in
theorem localForce_continuous : Continuous (fun t => localForce (gauge t) coupling (scalar t)) := by
  have first : Continuous (fun t => gaugePotential (gauge t)) := gaugeOperatorMap.continuous.comp continuousGauge
  exact (first.const_smul (-Complex.I*(coupling : ℂ))).add (scalarDriftMap.continuous.comp continuousScalar)

theorem force_bound (G M time : ℝ)
    (gaugeBound : ‖gaugePotential (gauge time)‖≤G) (scalarBound : ‖scalarDriftMap (scalar time)‖≤M)
    (field : FullMatterL2) :
    ‖localForce (gauge time) coupling (scalar time) field‖≤(|coupling| * G+M)*‖field‖ := by
  have first := mul_le_mul_of_nonneg_left (((gaugePotential (gauge time)).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right gaugeBound (norm_nonneg field))) (abs_nonneg coupling)
  have second := ((scalarDriftMap (scalar time)).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right scalarBound (norm_nonneg field))
  simp only [localForce,add_apply,smul_apply]
  calc
    _ ≤ ‖(-Complex.I*(coupling : ℂ)) • gaugePotential (gauge time) field‖+‖scalarDriftMap (scalar time) field‖ := norm_add_le _ _
    _ = |coupling| * ‖gaugePotential (gauge time) field‖+‖scalarDriftMap (scalar time) field‖ := by
      rw [norm_smul,norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
    _ ≤ |coupling| * (G*‖field‖)+M*‖field‖ := add_le_add first second
    _ = _ := by ring

def forceIntegrand (energy damping : ℝ) (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  localForce (gauge time) coupling (scalar time)
    (integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial time)

theorem forceIntegrand_continuous (energy damping : ℝ) (initial : FullMatterL2) :
    Continuous (forceIntegrand gauge continuousGauge coupling scalar continuousScalar energy damping initial) :=
  (localForce_continuous gauge continuousGauge coupling scalar continuousScalar).clm_apply
    (integrand_continuous gauge continuousGauge coupling scalar continuousScalar energy damping initial)

theorem forceIntegrand_integrable (G M : ℝ)
    (gaugeBound : ∀ t, 0≤t → ‖gaugePotential (gauge t)‖≤G)
    (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    IntegrableOn (forceIntegrand gauge continuousGauge coupling scalar continuousScalar energy damping initial) (Ioi 0) := by
  have Gpos : 0≤G := (norm_nonneg _).trans (gaugeBound 0 le_rfl)
  have Mpos : 0≤M := (norm_nonneg _).trans (scalarBound 0 le_rfl)
  have size : 0≤|coupling| * G+M := by positivity
  have majorant := ((Retarded.envelope_integrable damping M positive).mul_const ‖initial‖).const_mul (|coupling| * G+M)
  apply majorant.mono'
    (forceIntegrand_continuous gauge continuousGauge coupling scalar continuousScalar energy damping initial).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t future
  exact (force_bound gauge coupling scalar G M t (gaugeBound t future.le) (scalarBound t future.le) _).trans
    (mul_le_mul_of_nonneg_left
      (integrand_bound gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping t future.le initial) size)

def forceValue (energy damping : ℝ) (initial : FullMatterL2) : FullMatterL2 :=
  ∫ t : ℝ in Ioi 0, forceIntegrand gauge continuousGauge coupling scalar continuousScalar energy damping initial t

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
