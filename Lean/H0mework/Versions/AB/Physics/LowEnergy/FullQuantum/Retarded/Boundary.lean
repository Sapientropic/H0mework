import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Integrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The true damped flow and its integrable derivative generate the causal
boundary at infinity, then both inverse identities by improper FTC. -/
set_option autoImplicit false
open Set MeasureTheory Filter
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair YangMills.FullPairing
open Triangular FullSpace MatterSpace.Response
noncomputable section
local instance : NormedAlgebra ℚ Operators := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ Operators := NormedAlgebra.restrictScalars ℝ ℂ _

def weightedGenerator (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : Operators :=
  (-(damping : ℂ)+Complex.I*(energy : ℂ)) • (1 : Operators)+operator (drift actual point momentum)

theorem temporalWeight_derivative (energy damping time : ℝ) :
    HasDerivAt (temporalWeight energy damping)
      (temporalWeight energy damping time * (-(damping : ℂ)+Complex.I*(energy : ℂ))) time := by
  have generated := (Complex.ofRealCLM.hasDerivAt.const_mul
    (-(damping : ℂ)+Complex.I*(energy : ℂ))).cexp (x := time)
  unfold temporalWeight Fermion.retardedMode
  simpa only [sub_zero,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one] using generated

theorem integrand_derivative (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping time : ℝ) :
    HasDerivAt (integrand point momentum energy damping)
      (integrand point momentum energy damping time*weightedGenerator point momentum energy damping) time := by
  have generated := (temporalWeight_derivative energy damping time).smul
    (evolution_derivative actual point momentum time)
  convert! generated using 1
  simp only [integrand,weightedGenerator,mul_add,mul_smul_comm,mul_one,smul_mul_assoc,smul_smul]
  module

theorem integrand_commutes (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping time : ℝ) :
    Commute (integrand point momentum energy damping time) (weightedGenerator point momentum energy damping) := by
  change integrand point momentum energy damping time*weightedGenerator point momentum energy damping=
    weightedGenerator point momentum energy damping*integrand point momentum energy damping time
  simp only [integrand,weightedGenerator,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,smul_smul]
  rw [evolution_commutes]
  module

theorem derivative_integrable (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    IntegrableOn (fun t => integrand point momentum energy damping t*
      weightedGenerator point momentum energy damping) (Ioi 0) := by
  let multiply := (ContinuousLinearMap.mul ℂ Operators).flip
    (weightedGenerator point momentum energy damping)
  exact multiply.integrable_comp (integrand_integrable point momentum energy damping positive)

theorem integrand_tendsto_zero (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    Tendsto (integrand point momentum energy damping) atTop (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t _ => integrand_derivative point momentum energy damping t)
    (derivative_integrable point momentum energy damping positive)
    (integrand_integrable point momentum energy damping positive)

theorem derivative_integral (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, integrand point momentum energy damping t*
      weightedGenerator point momentum energy damping)=-(1 : Operators) := by
  have generated := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => integrand_derivative point momentum energy damping t)
    (derivative_integrable point momentum energy damping positive)
    (integrand_tendsto_zero point momentum energy damping positive)
  simpa only [integrand_zero,zero_sub] using generated

theorem value_generator_right (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    value point momentum energy damping*weightedGenerator point momentum energy damping=-(1 : Operators) := by
  have pull := ((ContinuousLinearMap.mul ℂ Operators).flip
    (weightedGenerator point momentum energy damping)).integral_comp_comm
      (integrand_integrable point momentum energy damping positive)
  exact pull.symm.trans (derivative_integral point momentum energy damping positive)

theorem value_generator_left (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    weightedGenerator point momentum energy damping*value point momentum energy damping=-(1 : Operators) := by
  have pull := ((ContinuousLinearMap.mul ℂ Operators)
    (weightedGenerator point momentum energy damping)).integral_comp_comm
      (integrand_integrable point momentum energy damping positive)
  calc
    _ = ∫ t : ℝ in Ioi 0, weightedGenerator point momentum energy damping*
        integrand point momentum energy damping t := pull.symm
    _ = ∫ t : ℝ in Ioi 0, integrand point momentum energy damping t*
        weightedGenerator point momentum energy damping := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => (integrand_commutes point momentum energy damping t).eq.symm
    _ = _ := derivative_integral point momentum energy damping positive

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
