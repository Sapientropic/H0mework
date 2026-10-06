import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryLaplace.Force
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Boundary

/-! The source weak time equation generates the boundary at infinity and its true frequency equation. -/
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
open FullSpace GaugeGreen ScalarGreen GaugeHistory MatterSpace.Response
noncomputable section
attribute [local irreducible] fullOperator
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

def paired (energy damping : ℝ) (test initial : FullMatterL2) (time : ℝ) : ℂ :=
  inner ℂ test (integrand gauge continuousGauge coupling scalar continuousScalar energy damping initial time)

def pairedDerivative (energy damping : ℝ) (test : Quantum.Generator.domain freeAction)
    (initial : FullMatterL2) (time : ℝ) : ℂ :=
  (-(damping : ℂ)+Complex.I*(energy : ℂ))*paired gauge continuousGauge coupling scalar continuousScalar energy damping test initial time-
    Complex.I*paired gauge continuousGauge coupling scalar continuousScalar energy damping
      (Quantum.Generator.hamiltonian freeAction test) initial time+
    inner ℂ (test : FullMatterL2) (forceIntegrand gauge continuousGauge coupling scalar continuousScalar energy damping initial time)

theorem paired_derivative (energy damping : ℝ) (test : Quantum.Generator.domain freeAction)
    (initial : FullMatterL2) (time : ℝ) :
    HasDerivAt (paired gauge continuousGauge coupling scalar continuousScalar energy damping test initial)
      (pairedDerivative gauge continuousGauge coupling scalar continuousScalar energy damping test initial time) time := by
  have generated := (Retarded.temporalWeight_derivative energy damping time).mul
    (full_native_weak gauge continuousGauge coupling scalar continuousScalar 0 time initial test)
  have expression : paired gauge continuousGauge coupling scalar continuousScalar energy damping test initial=
      fun t => temporalWeight energy damping t*inner ℂ (test : FullMatterL2)
        (fullOperator gauge continuousGauge coupling scalar continuousScalar 0 t initial) := by
    funext t
    exact inner_smul_right _ _ _
  rw [expression]
  convert! generated using 1
  simp only [pairedDerivative,paired,forceIntegrand,integrand,map_smul,inner_smul_right]
  ring

theorem paired_integrable (M : ℝ) (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (test initial : FullMatterL2) :
    IntegrableOn (paired gauge continuousGauge coupling scalar continuousScalar energy damping test initial) (Ioi 0) :=
  (innerSL ℂ test).integrable_comp
    (integrand_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive initial)

theorem pairedDerivative_integrable (G M : ℝ)
    (gaugeBound : ∀ t, 0≤t → ‖gaugePotential (gauge t)‖≤G)
    (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (test : Quantum.Generator.domain freeAction) (initial : FullMatterL2) :
    IntegrableOn (pairedDerivative gauge continuousGauge coupling scalar continuousScalar energy damping test initial) (Ioi 0) := by
  have first := (paired_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive test initial).const_mul
    (-(damping : ℂ)+Complex.I*(energy : ℂ))
  have second := (paired_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive
    (Quantum.Generator.hamiltonian freeAction test) initial).const_mul Complex.I
  have third := (innerSL ℂ (test : FullMatterL2)).integrable_comp
    (forceIntegrand_integrable gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive initial)
  exact (first.sub second).add third

theorem paired_tendsto_zero (G M : ℝ)
    (gaugeBound : ∀ t, 0≤t → ‖gaugePotential (gauge t)‖≤G)
    (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (test : Quantum.Generator.domain freeAction) (initial : FullMatterL2) :
    Tendsto (paired gauge continuousGauge coupling scalar continuousScalar energy damping test initial) atTop (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t _ => paired_derivative gauge continuousGauge coupling scalar continuousScalar energy damping test initial t)
    (pairedDerivative_integrable gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive test initial)
    (paired_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive test initial)

theorem pairedDerivative_integral (G M : ℝ)
    (gaugeBound : ∀ t, 0≤t → ‖gaugePotential (gauge t)‖≤G)
    (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (test : Quantum.Generator.domain freeAction) (initial : FullMatterL2) :
    (∫ t : ℝ in Ioi 0, pairedDerivative gauge continuousGauge coupling scalar continuousScalar energy damping test initial t)=
      -inner ℂ (test : FullMatterL2) initial := by
  have generated := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => paired_derivative gauge continuousGauge coupling scalar continuousScalar energy damping test initial t)
    (pairedDerivative_integrable gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive test initial)
    (paired_tendsto_zero gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive test initial)
  simpa only [paired,integrand,temporalWeight,Fermion.retardedMode,sub_zero,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,one_smul,fullOperator_starts,zero_sub] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
