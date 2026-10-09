import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.FullQuantum.HistoryForcing.Source

/-! The generated forced field solves the original complete weak time equation in physical time. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
open FullSpace GaugeGreen ScalarGreen GaugeHistory PerturbedGreen
noncomputable section
variable (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge) (coupling : ℝ)
    (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (source : ℝ → FullMatterL2) (continuousSource : Continuous source)

attribute [local irreducible] gaugeUnitary scalarInteraction gaugeInteraction sourceDevelopment

include continuousScalar continuousSource in
theorem source_freeInteraction_equation (start time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => spatialFree (-t)
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial t))
      (spatialFree (-time)
        (localForce (gauge time) coupling (scalar time)
          (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)+
          inversePrincipal 0 (source time))) time := by
  let B := scalarInteraction gauge continuousGauge coupling scalar
  let u := gaugeUnitary gauge continuousGauge coupling start 0 initial
  let curve := forcedCurve B (sourceInteraction gauge continuousGauge coupling source) start u
  have curveDerivative : HasDerivAt curve
      (B time (curve time)+sourceInteraction gauge continuousGauge coupling source time) time :=
    forcedCurve_equation B (scalarInteraction_joint gauge continuousGauge coupling scalar continuousScalar)
      (scalarInteraction_twice_zero gauge continuousGauge coupling scalar scalar)
      (sourceInteraction gauge continuousGauge coupling source)
      (sourceInteraction_continuous gauge continuousGauge coupling source continuousSource) start time u
  have fixed : HasDerivAt (fun t => gaugeInteraction gauge continuousGauge coupling t (curve time))
      ((-Complex.I*(coupling : ℂ)) • spatialFree (-time)
        (gaugePotential (gauge time) (gaugeUnitary gauge continuousGauge coupling 0 time (curve time)))) time := by
    simpa only [gaugeInteraction_apply] using
      gaugeUnitary_equation gauge continuousGauge coupling 0 time (curve time)
  have generated := strong_isometry_product (gaugeInteraction gauge continuousGauge coupling)
    (gaugeInteraction_continuous gauge continuousGauge coupling) curve _ _ time fixed curveDerivative
  simp only [gaugeInteraction_apply] at generated
  dsimp only [B] at generated
  rw [map_add,scalarInteraction_apply,sourceInteraction,gaugeUnitary_inverse,gaugeUnitary_inverse] at generated
  simp only [map_add] at generated
  have physical (t : ℝ) : sourceDevelopment gauge continuousGauge coupling scalar source start initial t=
      gaugeUnitary gauge continuousGauge coupling 0 t (curve t) := by unfold sourceDevelopment; rfl
  simp only [physical,localForce,add_apply,smul_apply,map_add,map_smul]
  convert! generated using 1
  module

include continuousScalar continuousSource in
theorem source_native_weak (start time : ℝ) (initial : FullMatterL2) (test : Quantum.Generator.domain freeAction) :
    HasDerivAt (fun t => inner ℂ (test : FullMatterL2)
      (sourceDevelopment gauge continuousGauge coupling scalar source start initial t))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)+
        inner ℂ (test : FullMatterL2)
          (localForce (gauge time) coupling (scalar time)
            (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)+
            inversePrincipal 0 (source time))) time := by
  have left := (free_domain_derivative test (-time)).scomp time (hasDerivAt_neg time)
  have right := source_freeInteraction_equation gauge continuousGauge coupling scalar continuousScalar
    source continuousSource start time initial
  have paired := left.inner ℂ right
  have unitary (t : ℝ) (u v : FullMatterL2) : inner ℂ (spatialFree t u) (spatialFree t v)=inner ℂ u v :=
    (freeUnitary t).inner_map_map _ _
  simp only [Function.comp_apply,neg_smul,one_smul,inner_neg_left,unitary] at paired
  convert! paired using 1
  change (-Complex.I)*inner ℂ (Complex.I • Quantum.Generator.generator freeAction test)
    (sourceDevelopment gauge continuousGauge coupling scalar source start initial time)+_=_
  rw [inner_smul_left]
  simp only [Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

theorem source_native_principal_force (start time : ℝ) (initial : FullMatterL2) :
    let field := sourceDevelopment gauge continuousGauge coupling scalar source start initial time
    principal 0 (localForce (gauge time) coupling (scalar time) field+inversePrincipal 0 (source time))=
      -(coupling : ℂ) • rawGauge 0 (gauge time) field-potential (scalar time) field+source time := by
  dsimp only
  rw [map_add,localForce_original,inversePrincipal_right]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryForcing
