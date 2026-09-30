import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Complete
import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Primitive
import H0mework.Physics.LowEnergy.FullQuantum.GaugeHistory.Uniqueness

/-! A complete native field history has a unique source development and keeps the independent dual. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen ScalarGreen PerturbedGreen
noncomputable section

theorem fullOperator_continuous (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start : ℝ) (initial : FullMatterL2) :
    Continuous (fun t => fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial) := by
  have interaction : Continuous (fun t => spatialFree (-t)
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial)) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (full_freeInteraction_equation gauge continuousGauge epsilon scalar continuousScalar start t initial).continuousAt)
  have composed := spatialFree_joint.comp (continuous_id.prodMk interaction)
  simpa only [Function.comp_def,id_eq,← spatialFree_add,add_neg_cancel,spatialFree_zero] using composed

theorem fullOperator_nonzero (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) (nonzero : initial≠0) :
    fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial≠0 := by
  intro vanished
  have recovered := fullOperator_inverse gauge continuousGauge epsilon scalar continuousScalar start time initial
  rw [vanished,map_zero] at recovered
  exact nonzero recovered.symm

theorem full_native_weak (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) (test : Quantum.Generator.domain freeAction) :
    HasDerivAt (fun t => inner ℂ (test : FullMatterL2)
      (fullOperator gauge continuousGauge epsilon scalar continuousScalar start t initial))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian freeAction test)
        (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial)+
        inner ℂ (test : FullMatterL2) (localForce (gauge time) epsilon (scalar time)
          (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial))) time := by
  simpa only [localForce,add_apply,smul_apply] using
    full_weak_equation gauge continuousGauge epsilon scalar continuousScalar start time initial test

theorem full_native_principal_force (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (initial : FullMatterL2) :
    let field := fullOperator gauge continuousGauge epsilon scalar continuousScalar start time initial
    principal 0 (localForce (gauge time) epsilon (scalar time) field)=
      -(epsilon : ℂ) • rawGauge 0 (gauge time) field-potential (scalar time) field :=
  localForce_original (gauge time) epsilon (scalar time) _

theorem full_original_dual_integral (gauge : ℝ → GaugeProfile) (continuousGauge : Continuous gauge)
    (epsilon : ℝ) (scalar : ℝ → ScalarProfile) (continuousScalar : Continuous scalar)
    (start time : ℝ) (dual field : FullMatterL2) :
    (∫ x, inner ℂ (originalDualOperator gauge continuousGauge epsilon scalar continuousScalar start time dual x)
      (principal 0 (fullOperator gauge continuousGauge epsilon scalar continuousScalar start time field) x))=
      ∫ x, inner ℂ (dual x) (principal 0 field x) := by
  rw [← L2.inner_def,← L2.inner_def]
  exact original_pair_preserved gauge continuousGauge epsilon scalar continuousScalar start time dual field

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
