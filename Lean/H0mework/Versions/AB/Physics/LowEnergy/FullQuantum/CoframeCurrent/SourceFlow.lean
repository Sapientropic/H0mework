import H0mework.Physics.LowEnergy.FullQuantum.CoframeCurrent.Flow
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.CoframeResponse.Source
import Mathlib.Analysis.Calculus.MeanValue

/-! The source's full original primal flow is exactly the matrix exponential;
its coframe derivative therefore has a true two-sided Duhamel producer. -/
set_option autoImplicit false
open scoped Matrix Matrix.Norms.L2Operator
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
open ProofFreeRicherAnholonomicSource StageNineHolonomicField Stage9C.Material.SpinPair
open DiracExteriorMatterAction StateGreen CoframeResponse
noncomputable section
local instance sourceFlowIndex : DecidableEq Quantum.Index := Classical.decEq _
local instance sourceFlowReal : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _
local instance sourceFlowRational : NormedAlgebra ℚ SourceMatrix := NormedAlgebra.restrictScalars ℚ ℂ _

def sourceGenerator (C : StageNineHolonomicConfiguration) (point : BasePoint) (k : Fin 3 → ℝ) : SourceMatrix :=
  (-Complex.I) • Quantum.operatorMatrix (hamiltonian C point k)

theorem sourceMatrix_entry (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) (i j : Quantum.Index) :
    primalMatrix C point k t i j=Quantum.coordinates (primal C point k t (Quantum.wholeBasis j)) i := by
  rw [primalMatrix,Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply]
  rfl

theorem sourceMatrix_zero (C : StageNineHolonomicConfiguration) (point : BasePoint) (k : Fin 3 → ℝ) :
    primalMatrix C point k 0=1 := by
  ext i j
  rw [sourceMatrix_entry,primal_zero]
  by_cases same : i=j
  · subst j
    simp [Quantum.coordinates]
  · simp [Quantum.coordinates,same,Ne.symm same]

theorem sourceMatrix_derivative (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (primalMatrix C point k) (sourceGenerator C point k*primalMatrix C point k t) t := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have component := hasDerivAt_pi.mp (original_wave_derivative C point k t (Quantum.wholeBasis j)) i
  simpa only [sourceGenerator,Matrix.smul_mul,Matrix.smul_apply,Pi.smul_apply,Matrix.mul_apply,
    sourceMatrix_entry,Matrix.mulVec,dotProduct,smul_eq_mul,Finset.mul_sum,mul_assoc] using component

theorem sourceMatrix_flow (C : StageNineHolonomicConfiguration) (point : BasePoint)
    (k : Fin 3 → ℝ) (t : ℝ) : primalMatrix C point k t=flow (sourceGenerator C point k) t := by
  let A := sourceGenerator C point k
  have derivative (s : ℝ) : HasDerivAt (fun r => flow A (-r)*primalMatrix C point k r) 0 s := by
    have inverse := (flow_derivative A (-s)).scomp s (hasDerivAt_neg s)
    have generated := inverse.mul (sourceMatrix_derivative C point k s)
    convert! generated using 1
    simp only [Function.comp_apply,neg_one_smul,neg_mul,mul_assoc]
    change 0=-(flow A (-s)*(A*primalMatrix C point k s))+flow A (-s)*(A*primalMatrix C point k s)
    exact (neg_add_cancel _).symm
  have same := is_const_of_deriv_eq_zero (fun s => (derivative s).differentiableAt)
    (fun s => (derivative s).deriv) t 0
  simp only [neg_zero,sourceMatrix_zero,flow_zero,mul_one] at same
  have multiplied := congrArg (fun M : SourceMatrix => flow A t*M) same
  have inverse : flow A t*flow A (-t)=1 := by
    rw [← flow_add,add_neg_cancel,flow_zero]
  rw [← mul_assoc,inverse,one_mul,mul_one] at multiplied
  exact multiplied

theorem sourceGenerator_parameter (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe) :
    HasDerivAt (fun epsilon => sourceGenerator
      (coframeConfiguration (coframePath point direction epsilon)) point k)
      ((-Complex.I) • hamiltonianDirection point k direction) 0 := by
  exact (original_hamiltonian_parameter point k direction).const_smul (-Complex.I)

def sourceFlowVariation (point : BasePoint) (k : Fin 3 → ℝ) (direction : LorentzianCoframe)
    (t : ℝ) : SourceMatrix :=
  duhamel (sourceGenerator actual point k) ((-Complex.I) • hamiltonianDirection point k direction) t

theorem original_flow_parameter (point : BasePoint) (k : Fin 3 → ℝ)
    (direction : LorentzianCoframe) (t : ℝ) :
    HasDerivAt (fun epsilon => primalMatrix
      (coframeConfiguration (coframePath point direction epsilon)) point k t)
      (sourceFlowVariation point k direction t) 0 := by
  simp only [sourceMatrix_flow]
  have generated := flow_parameter
    (fun epsilon => sourceGenerator (coframeConfiguration (coframePath point direction epsilon)) point k)
    ((-Complex.I) • hamiltonianDirection point k direction) (sourceGenerator_parameter point k direction) t
  simpa only [coframePath_zero,coframeConfiguration_actual,sourceFlowVariation] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.CoframeCurrent
