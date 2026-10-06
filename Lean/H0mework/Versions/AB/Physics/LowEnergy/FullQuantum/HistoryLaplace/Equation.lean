import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.HistoryLaplace.Boundary

/-! The frequency equation keeps the genuine weighted source-history force integral. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
open FullSpace GaugeGreen ScalarGreen GaugeHistory MatterSpace.Response
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)

theorem paired_integral (M : ℝ) (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (test initial : FullMatterL2) :
    (∫ t : ℝ in Ioi 0, paired gauge continuousGauge coupling scalar continuousScalar energy damping test initial t)=
      inner ℂ test (value gauge continuousGauge coupling scalar continuousScalar energy damping initial) :=
  (innerSL ℂ test).integral_comp_comm
    (integrand_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive initial)

attribute [local irreducible] fullOperator value integrand forceIntegrand paired

theorem frequency_equation (G M : ℝ)
    (gaugeBound : ∀ t, 0≤t → ‖gaugePotential (gauge t)‖≤G)
    (scalarBound : ∀ t, 0≤t → ‖scalarDriftMap (scalar t)‖≤M)
    (energy damping : ℝ) (positive : 0<damping) (test : Quantum.Generator.domain freeAction) (initial : FullMatterL2) :
    ((energy : ℂ)+Complex.I*(damping : ℂ))*
      inner ℂ (test : FullMatterL2) (value gauge continuousGauge coupling scalar continuousScalar energy damping initial)-
      inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (value gauge continuousGauge coupling scalar continuousScalar energy damping initial)-
      Complex.I*inner ℂ (test : FullMatterL2)
        (forceValue gauge continuousGauge coupling scalar continuousScalar energy damping initial)=
          Complex.I*inner ℂ (test : FullMatterL2) initial := by
  have raw := pairedDerivative_integral gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive test initial
  have first := paired_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive test initial
  have second := paired_integrable gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive
    (Quantum.Generator.hamiltonian freeAction test) initial
  have third := (innerSL ℂ (test : FullMatterL2)).integrable_comp
    (forceIntegrand_integrable gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive initial)
  have forces := (innerSL ℂ (test : FullMatterL2)).integral_comp_comm
    (forceIntegrand_integrable gauge continuousGauge coupling scalar continuousScalar G M gaugeBound scalarBound energy damping positive initial)
  change (∫ t : ℝ in Ioi 0, inner ℂ (test : FullMatterL2)
    (forceIntegrand gauge continuousGauge coupling scalar continuousScalar energy damping initial t))=
      inner ℂ (test : FullMatterL2) (forceValue gauge continuousGauge coupling scalar continuousScalar energy damping initial) at forces
  unfold pairedDerivative at raw
  erw [integral_add ((first.const_mul (-(damping : ℂ)+Complex.I*(energy : ℂ))).sub
    (second.const_mul Complex.I)) third,
    integral_sub (first.const_mul (-(damping : ℂ)+Complex.I*(energy : ℂ))) (second.const_mul Complex.I)] at raw
  have leftIntegral := paired_integral gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive
    (test : FullMatterL2) initial
  have rightIntegral := paired_integral gauge continuousGauge coupling scalar continuousScalar M scalarBound energy damping positive
    (Quantum.Generator.hamiltonian freeAction test) initial
  rw [integral_const_mul,integral_const_mul] at raw
  erw [leftIntegral] at raw
  erw [rightIntegral] at raw
  erw [forces] at raw
  have multiplied := congrArg (fun c : ℂ => (-Complex.I)*c) raw
  calc
    _ = (-Complex.I)*((-(damping : ℂ)+Complex.I*(energy : ℂ))*
      inner ℂ (test : FullMatterL2) (value gauge continuousGauge coupling scalar continuousScalar energy damping initial)-
      Complex.I*inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (value gauge continuousGauge coupling scalar continuousScalar energy damping initial)+
      inner ℂ (test : FullMatterL2) (forceValue gauge continuousGauge coupling scalar continuousScalar energy damping initial)) := by
        ring_nf
        simp [Complex.I_sq,sub_eq_add_neg]
    _ = _ := by simpa only [mul_neg,neg_mul,neg_neg] using multiplied

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryLaplace
