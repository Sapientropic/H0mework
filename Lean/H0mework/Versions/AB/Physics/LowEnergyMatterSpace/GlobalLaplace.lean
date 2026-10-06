import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GlobalResponse
import H0mework.Physics.LowEnergyFockDynamics.Retarded

/-! Genuine all-time unitary developments generate bounded damped retarded operators on all of L². -/
set_option autoImplicit false
open Set MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

def temporalWeight (energy damping time : ℝ) : ℂ := Fermion.retardedMode energy damping 0 time

theorem temporalWeight_norm (energy damping time : ℝ) :
    ‖temporalWeight energy damping time‖=Real.exp (-damping*time) := by
  simp [temporalWeight,Fermion.retardedMode,Complex.norm_exp]

theorem temporalWeight_continuous (energy damping : ℝ) : Continuous (temporalWeight energy damping) := by
  unfold temporalWeight Fermion.retardedMode
  fun_prop

theorem temporalWeight_norm_integral (energy damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, ‖temporalWeight energy damping t‖)=damping⁻¹ := by
  simp_rw [temporalWeight_norm]
  rw [integral_exp_mul_Ioi (neg_neg_of_pos positive) 0]
  simp

namespace GlobalPerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : GlobalPerturbedDevelopment perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t))

theorem physicalCurve_continuous (epsilon start : ℝ) (initial : MatterL2) :
    Continuous (fun t => development.physicalCurve epsilon start t initial) := by
  have curve : Continuous (development.curve epsilon start (spatialUnitary (-start) initial)) :=
    continuous_iff_continuousAt.mpr fun t => (development.evolves epsilon start _ t).continuousAt
  convert! spatialUnitary_joint.comp (continuous_id.prodMk curve) using 1

include symmetric in
theorem physical_norm (epsilon start time : ℝ) (initial : MatterL2) :
    ‖development.physicalCurve epsilon start time initial‖=‖initial‖ := by
  simpa only [physicalUnitary_apply] using (development.physicalUnitary symmetric epsilon start time).norm_map initial

def retardedIntegrand (epsilon energy damping : ℝ) (initial : MatterL2) (time : ℝ) : MatterL2 :=
  temporalWeight energy damping time • development.physicalCurve epsilon 0 time initial

theorem retardedIntegrand_continuous (epsilon energy damping : ℝ) (initial : MatterL2) :
    Continuous (development.retardedIntegrand epsilon energy damping initial) :=
  (temporalWeight_continuous energy damping).smul (development.physicalCurve_continuous epsilon 0 initial)

include symmetric in
theorem retardedIntegrand_integrable (epsilon energy damping : ℝ) (positive : 0<damping) (initial : MatterL2) :
    IntegrableOn (development.retardedIntegrand epsilon energy damping initial) (Ioi 0) := by
  have majorant := (Fermion.retardedMode_integrable energy damping 0 positive).norm.mul_const ‖initial‖
  apply majorant.mono' (development.retardedIntegrand_continuous epsilon energy damping initial).aestronglyMeasurable
  exact ae_of_all _ fun t => by
    change ‖temporalWeight energy damping t • development.physicalCurve epsilon 0 t initial‖≤
      ‖temporalWeight energy damping t‖*‖initial‖
    rw [norm_smul,development.physical_norm symmetric]

def retardedValue (epsilon energy damping : ℝ) (initial : MatterL2) : MatterL2 :=
  ∫ t : ℝ in Ioi 0, development.retardedIntegrand epsilon energy damping initial t

include symmetric in
theorem retardedValue_bound (epsilon energy damping : ℝ) (positive : 0<damping) (initial : MatterL2) :
    ‖development.retardedValue epsilon energy damping initial‖≤damping⁻¹*‖initial‖ := by
  apply (norm_integral_le_integral_norm _).trans_eq
  have point (t : ℝ) : ‖development.retardedIntegrand epsilon energy damping initial t‖=
      ‖temporalWeight energy damping t‖*‖initial‖ := by
    rw [retardedIntegrand,norm_smul,development.physical_norm symmetric]
  simp_rw [point]
  rw [integral_mul_const,temporalWeight_norm_integral energy damping positive]

include symmetric in
theorem retardedValue_add (epsilon energy damping : ℝ) (positive : 0<damping) (u v : MatterL2) :
    development.retardedValue epsilon energy damping (u+v)=
      development.retardedValue epsilon energy damping u+development.retardedValue epsilon energy damping v := by
  have point (t : ℝ) : development.retardedIntegrand epsilon energy damping (u+v) t=
      development.retardedIntegrand epsilon energy damping u t+development.retardedIntegrand epsilon energy damping v t := by
    change temporalWeight energy damping t •
      (development.physicalUnitary symmetric epsilon 0 t) (u+v)=_
    rw [map_add,smul_add]
    rfl
  unfold retardedValue
  simp_rw [point]
  exact integral_add (development.retardedIntegrand_integrable symmetric epsilon energy damping positive u)
    (development.retardedIntegrand_integrable symmetric epsilon energy damping positive v)

include symmetric in
theorem retardedValue_smul (epsilon energy damping : ℝ) (c : ℂ) (u : MatterL2) :
    development.retardedValue epsilon energy damping (c • u)=c • development.retardedValue epsilon energy damping u := by
  have point (t : ℝ) : development.retardedIntegrand epsilon energy damping (c • u) t=
      c • development.retardedIntegrand epsilon energy damping u t := by
    change temporalWeight energy damping t • (development.physicalUnitary symmetric epsilon 0 t) (c • u)=_
    rw [map_smul]
    exact smul_comm _ _ _
  unfold retardedValue
  simp_rw [point]
  exact integral_smul c _

def retardedLinear (epsilon energy damping : ℝ) (positive : 0<damping) : MatterL2 →ₗ[ℂ] MatterL2 where
  toFun := development.retardedValue epsilon energy damping
  map_add' := development.retardedValue_add symmetric epsilon energy damping positive
  map_smul' := development.retardedValue_smul symmetric epsilon energy damping

def retardedOperator (epsilon energy damping : ℝ) (positive : 0<damping) : MatterL2 →L[ℂ] MatterL2 :=
  (development.retardedLinear symmetric epsilon energy damping positive).mkContinuous damping⁻¹
    (development.retardedValue_bound symmetric epsilon energy damping positive)

theorem retardedOperator_norm (epsilon energy damping : ℝ) (positive : 0<damping) :
    ‖development.retardedOperator symmetric epsilon energy damping positive‖≤damping⁻¹ :=
  (development.retardedLinear symmetric epsilon energy damping positive).mkContinuous_norm_le
    (inv_nonneg.mpr positive.le) (development.retardedValue_bound symmetric epsilon energy damping positive)

end GlobalPerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
