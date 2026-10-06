import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Native
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Boundary

/-! The same source free time integral is its original complete Fourier resolvent. -/
set_option autoImplicit false
open MeasureTheory Set Filter
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen Triangular YangMills.FullPairing MatterSpace.Response
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair
noncomputable section
local instance freeIntegralReal : NormedAlgebra ℝ FiberOperators := NormedAlgebra.restrictScalars ℝ ℂ _
local instance freeIntegralRational : NormedAlgebra ℚ FiberOperators := NormedAlgebra.restrictScalars ℚ ℂ _

def freeIntegrand (k : Fin 3 → ℝ) (energy damping time : ℝ) : FiberOperators :=
  temporalWeight energy damping time • freeEvolution actual 0 k time

theorem freeIntegrand_continuous (k : Fin 3 → ℝ) (energy damping : ℝ) :
    Continuous (freeIntegrand k energy damping) :=
  (temporalWeight_continuous energy damping).smul (flow_continuous _)

theorem freeIntegrand_norm (k : Fin 3 → ℝ) (energy damping time : ℝ) :
    ‖freeIntegrand k energy damping time‖≤Real.exp (-damping*time) := by
  rw [freeIntegrand,norm_smul,temporalWeight_norm]
  exact mul_le_of_le_one_right (Real.exp_pos _).le
    (freeEvolution_norm_le_one actual 0 k (original_freeHamiltonian_selfAdjoint 0 k) time)

theorem freeIntegrand_integrable (k : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0<damping) :
    IntegrableOn (freeIntegrand k energy damping) (Ioi 0) := by
  have bound := Retarded.envelope_integrable damping 0 positive
  have same : Retarded.envelope damping 0=(fun t : ℝ => Real.exp (-damping*t)) := by
    funext t
    simp only [Retarded.envelope,mul_zero,add_zero,mul_one]
  have exponential : IntegrableOn (fun t : ℝ => Real.exp (-damping*t)) (Ioi 0) := by
    rw [← same]
    exact bound
  apply exponential.mono' (freeIntegrand_continuous k energy damping).aestronglyMeasurable
  exact ae_of_all _ (freeIntegrand_norm k energy damping)

def freeWeightedGenerator (k : Fin 3 → ℝ) (energy damping : ℝ) : FiberOperators :=
  (-(damping : ℂ)+Complex.I*(energy : ℂ)) • (1 : FiberOperators)+operator (freeDrift actual 0 k)

theorem freeIntegrand_derivative (k : Fin 3 → ℝ) (energy damping time : ℝ) :
    HasDerivAt (freeIntegrand k energy damping)
      (freeIntegrand k energy damping time*freeWeightedGenerator k energy damping) time := by
  have generated := (Retarded.temporalWeight_derivative energy damping time).smul
    (flow_derivative (operator (freeDrift actual 0 k)) time)
  convert! generated using 1
  simp only [freeIntegrand,freeWeightedGenerator,freeEvolution,mul_add,mul_smul_comm,mul_one,
    smul_mul_assoc,smul_smul]
  module

theorem freeDerivative_integrable (k : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0<damping) :
    IntegrableOn (fun t => freeIntegrand k energy damping t*freeWeightedGenerator k energy damping) (Ioi 0) :=
  ((ContinuousLinearMap.mul ℂ FiberOperators).flip (freeWeightedGenerator k energy damping)).integrable_comp
    (freeIntegrand_integrable k energy damping positive)

theorem freeIntegrand_tendsto_zero (k : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0<damping) :
    Tendsto (freeIntegrand k energy damping) atTop (nhds 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi
    (fun t _ => freeIntegrand_derivative k energy damping t)
    (freeDerivative_integrable k energy damping positive) (freeIntegrand_integrable k energy damping positive)

theorem freeIntegral_generator (k : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, freeIntegrand k energy damping t)*freeWeightedGenerator k energy damping= -1 := by
  have boundary := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t _ => freeIntegrand_derivative k energy damping t)
    (freeDerivative_integrable k energy damping positive) (freeIntegrand_tendsto_zero k energy damping positive)
  have pull := ((ContinuousLinearMap.mul ℂ FiberOperators).flip (freeWeightedGenerator k energy damping)).integral_comp_comm
    (freeIntegrand_integrable k energy damping positive)
  change (∫ t : ℝ in Ioi 0, freeIntegrand k energy damping t*freeWeightedGenerator k energy damping)=
    (∫ t : ℝ in Ioi 0, freeIntegrand k energy damping t)*freeWeightedGenerator k energy damping at pull
  rw [← pull]
  simpa only [freeIntegrand,temporalWeight,Fermion.retardedMode,sub_zero,Complex.ofReal_zero,
    mul_zero,Complex.exp_zero,one_smul,freeEvolution,flow_zero,zero_sub] using boundary

theorem freeWeightedGenerator_kernel (k : Fin 3 → ℝ) (energy damping : ℝ) :
    freeWeightedGenerator k energy damping=Complex.I • freeKernelOperator 0 k energy damping := by
  have one : operator (1 : Mother)=(1 : FiberOperators) := by ext v; simp [operator]
  have sub (A B : Mother) : operator (A-B)=operator A-operator B := by ext v; simp [operator]
  simp only [freeWeightedGenerator,freeKernelOperator,freeKernel,sub,operator_smul,one,
    Retarded.spectralParameter,smul_sub,smul_smul,← free_hamiltonian_drift,operator_smul]
  have coefficient : Complex.I*((energy : ℂ)+Complex.I*(damping : ℂ))=
      -(damping : ℂ)+Complex.I*(energy : ℂ) := by
    ring_nf
    simp [Complex.I_sq,sub_eq_add_neg]
  rw [coefficient]
  module

theorem freeIntegral_original_resolvent (k : Fin 3 → ℝ) (energy damping : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi 0, freeIntegrand k energy damping t)=Complex.I • freeValue 0 k energy damping := by
  have generated := freeIntegral_generator k energy damping positive
  rw [freeWeightedGenerator_kernel,mul_smul_comm] at generated
  have inverse := (freeValue_two_sided 0 k energy damping positive).1
  have multiplied := congrArg (fun A : FiberOperators => A*((-Complex.I) • freeValue 0 k energy damping)) generated
  have negative (A : FiberOperators) : (-(1 : FiberOperators))*A= -A := by
    ext v i
    simp
  have double (A : FiberOperators) : -((-Complex.I) • A)=Complex.I • A := by
    ext v i
    simp
  simpa only [smul_mul_assoc,mul_smul_comm,mul_assoc,inverse,smul_smul,
    mul_one,mul_neg,neg_mul,Complex.I_mul_I,neg_neg,one_smul,negative,smul_neg,neg_smul,double] using! multiplied

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
