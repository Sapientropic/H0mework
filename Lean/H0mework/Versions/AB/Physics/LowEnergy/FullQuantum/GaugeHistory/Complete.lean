import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Full
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Weak
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.StrongProduct

/-! Both original time-dependent fields enter one actual full-space weak Dirac development. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen PerturbedGreen
noncomputable section

def gaugeInteraction (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon time : ℝ) : FullMatterL2 ≃ₗᵢ[ℂ] FullMatterL2 :=
  (gaugeUnitary gauge continuousGauge epsilon 0 time).trans (freeUnitary (-time))

theorem gaugeInteraction_apply (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon time : ℝ) (field : FullMatterL2) :
    gaugeInteraction gauge continuousGauge epsilon time field=
      spatialFree (-time) (gaugeUnitary gauge continuousGauge epsilon 0 time field) := rfl

theorem gaugeInteraction_continuous (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (field : FullMatterL2) :
    Continuous (fun t => gaugeInteraction gauge continuousGauge epsilon t field) := by
  have composed := spatialFree_joint.comp
    (continuous_id.neg.prodMk (gaugeUnitary_continuous gauge continuousGauge epsilon 0 field))
  simpa only [gaugeInteraction_apply,Function.comp_def,id_eq] using! composed

attribute [local irreducible] nativeDevelopment gaugeUnitary fullOperator scalarInteraction gaugeInteraction

theorem full_freeInteraction_equation (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => spatialFree (-t)
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial))
      (spatialFree (-time) ((-Complex.I*(epsilon : ℂ)) • gaugePotential (gauge time)
        (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)+
        scalarDriftMap (scalar time)
          (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial))) time := by
  let B : ℝ → SpatialOperators := scalarInteraction gauge continuousGauge epsilon scalar
  let u : FullMatterL2 := gaugeUnitary gauge continuousGauge epsilon start 0 initial
  let curve : ℝ → FullMatterL2 := triangularCurve B start u
  have curveDerivative : HasDerivAt curve (B time (curve time)) time := triangularCurve_equation B
    (scalarInteraction_continuous gauge continuousGauge epsilon scalar continuousScalar)
    (scalarInteraction_twice_zero gauge continuousGauge epsilon scalar scalar) start time u
  have fixed : HasDerivAt (fun t => gaugeInteraction gauge continuousGauge epsilon t (curve time))
      ((-Complex.I*(epsilon : ℂ)) • spatialFree (-time)
        (gaugePotential (gauge time) (gaugeUnitary gauge continuousGauge epsilon 0 time (curve time)))) time :=
    by simpa only [gaugeInteraction_apply] using
      gaugeUnitary_equation gauge continuousGauge epsilon 0 time (curve time)
  have generated := strong_isometry_product (gaugeInteraction gauge continuousGauge epsilon)
    (gaugeInteraction_continuous gauge continuousGauge epsilon) curve _ _ time fixed curveDerivative
  simp only [gaugeInteraction_apply] at generated
  dsimp only [B] at generated
  rw [scalarInteraction_apply,gaugeUnitary_inverse] at generated
  have physical (t : ℝ) : fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial=
      gaugeUnitary gauge continuousGauge epsilon 0 t (curve t) :=
    fullOperator_apply gauge continuousGauge epsilon scalar continuousScalar start t initial
  simp only [physical,map_add,map_smul]
  convert! generated using 1
  exact add_comm _ _

theorem full_weak_equation (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) (test : Quantum.Generator.domain freeAction) :
    HasDerivAt (fun t => inner ℂ (test : FullMatterL2)
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)+
        inner ℂ (test : FullMatterL2)
          ((-Complex.I*(epsilon : ℂ)) • gaugePotential (gauge time)
            (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)+
            scalarDriftMap (scalar time)
              (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial))) time := by
  have left := (free_domain_derivative test (-time)).scomp time (hasDerivAt_neg time)
  have right := full_freeInteraction_equation gauge continuousGauge epsilon scalar continuousScalar start time initial
  have paired := left.inner ℂ right
  have unitary (t : ℝ) (u v : FullMatterL2) : inner ℂ (spatialFree t u) (spatialFree t v)=inner ℂ u v :=
    (freeUnitary t).inner_map_map _ _
  simp only [Function.comp_apply,neg_smul,one_smul,inner_neg_left,unitary] at paired
  convert! paired using 1
  change (-Complex.I)*inner ℂ (Complex.I • Quantum.Generator.generator freeAction test)
    (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)+_=_
  rw [inner_smul_left]
  simp only [Complex.conj_I]
  ring_nf
  simp [Complex.I_sq]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
