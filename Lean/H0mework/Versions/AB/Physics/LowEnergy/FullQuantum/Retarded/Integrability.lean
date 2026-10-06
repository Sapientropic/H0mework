import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Free
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Growth
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.LaplaceMoments

/-! Every positive damping controls the full source evolution, including its
single-insertion polynomial growth. -/
set_option autoImplicit false
open Set MeasureTheory Filter
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair YangMills.FullPairing
open Triangular FullSpace MatterSpace.Response
noncomputable section
local instance : NormedAlgebra ℚ Operators := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Operators := NormedAlgebra.restrictScalars ℝ ℂ _

def couplingNorm (point : BasePoint) : ℝ := ‖operator (interaction actual point)‖

def integrand (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping time : ℝ) : Operators :=
  temporalWeight energy damping time • evolution actual point momentum time

def envelope (damping coefficient time : ℝ) : ℝ :=
  Real.exp (-damping*time)*(1+time*coefficient)

theorem envelope_integrable (damping coefficient : ℝ) (positive : 0<damping) :
    IntegrableOn (envelope damping coefficient) (Ioi 0) := by
  have zeroth := damping_moment_integrable 0 damping positive
  have first := (damping_moment_integrable 1 damping positive).mul_const coefficient
  have same : envelope damping coefficient =
      (fun t => Real.exp (-damping*t)*t^0+(Real.exp (-damping*t)*t^1)*coefficient) := by
    funext t
    simp [envelope]
    ring
  rw [same]
  exact zeroth.add first

theorem envelope_integral (damping coefficient : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, envelope damping coefficient t)=
      damping⁻¹+coefficient*damping⁻¹^2 := by
  have zeroth := damping_moment_integrable 0 damping positive
  have first := damping_moment_integrable 1 damping positive
  have same (t : ℝ) : envelope damping coefficient t =
      Real.exp (-damping*t)*t^0+(Real.exp (-damping*t)*t^1)*coefficient := by
    simp [envelope]
    ring
  simp only [same]
  rw [integral_add zeroth (first.mul_const coefficient),integral_mul_const,
    damping_moment_integral 0 damping positive,damping_moment_integral 1 damping positive]
  norm_num
  ring

theorem integrand_continuous (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) :
    Continuous (integrand point momentum energy damping) := by
  apply (temporalWeight_continuous energy damping).smul
  exact continuous_iff_continuousAt.mpr fun t => (evolution_derivative actual point momentum t).continuousAt

theorem integrand_bound (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping time : ℝ) (future : 0≤time) :
    ‖integrand point momentum energy damping time‖≤envelope damping (couplingNorm point) time := by
  have bound := complete_evolution_bound actual point momentum
    (original_freeHamiltonian_selfAdjoint point momentum) time
  rw [abs_of_nonneg future] at bound
  unfold integrand envelope couplingNorm
  rw [norm_smul,temporalWeight_norm]
  exact mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le

theorem integrand_integrable (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    IntegrableOn (integrand point momentum energy damping) (Ioi 0) := by
  apply (envelope_integrable damping (couplingNorm point) positive).mono'
    (integrand_continuous point momentum energy damping).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integrand_bound point momentum energy damping t ht.le

def value (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : Operators :=
  ∫ t : ℝ in Ioi 0, integrand point momentum energy damping t

theorem value_bound (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    ‖value point momentum energy damping‖≤damping⁻¹+couplingNorm point*damping⁻¹^2 := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← envelope_integral damping (couplingNorm point) positive]
  apply integral_mono_ae (integrand_integrable point momentum energy damping positive).norm
    (envelope_integrable damping (couplingNorm point) positive)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact integrand_bound point momentum energy damping t ht.le

theorem integrand_zero (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) :
    integrand point momentum energy damping 0=1 := by
  simp [integrand,temporalWeight,Fermion.retardedMode,evolution_zero]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
