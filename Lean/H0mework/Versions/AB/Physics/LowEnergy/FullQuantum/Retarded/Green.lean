import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Boundary
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.TriangularDirac
import Mathlib.Analysis.Normed.Ring.Units

/-! The positive-damped causal integral generates the complete upper-half-plane
inverse, without assuming regularity or self-adjointness of the full Hamiltonian. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair YangMills.FullPairing
open Triangular FullSpace
noncomputable section

def spectralParameter (energy damping : ℝ) : ℂ := (energy : ℂ)+Complex.I*(damping : ℂ)

def kernel (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : Operators :=
  operator (fullKernel actual point momentum (spectralParameter energy damping))

private theorem operator_one : operator (1 : Mother)=(1 : Operators) := by
  ext v
  simp [operator]

private theorem operator_sub (A B : Mother) : operator (A-B)=operator A-operator B := by
  ext v
  simp [operator]

theorem kernel_original (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) :
    kernel point momentum energy damping = spectralParameter energy damping • (1 : Operators)-
      operator (hamiltonian actual point momentum) := by
  rw [kernel,fullKernel,operator_sub,operator_smul,operator_one]

theorem weightedGenerator_original (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) :
    weightedGenerator point momentum energy damping=Complex.I • kernel point momentum energy damping := by
  rw [weightedGenerator,kernel_original,← hamiltonian_drift actual point momentum,operator_smul]
  have scalar : Complex.I*spectralParameter energy damping = -(damping : ℂ)+Complex.I*(energy : ℂ) := by
    simp only [spectralParameter,mul_add,← mul_assoc,Complex.I_mul_I,neg_one_mul]
    ring
  rw [smul_sub,smul_smul,scalar]
  module

theorem value_kernel_right (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    value point momentum energy damping*kernel point momentum energy damping=Complex.I • (1 : Operators) := by
  have generated := value_generator_right point momentum energy damping positive
  rw [weightedGenerator_original] at generated
  calc
    _ = (-Complex.I) • (value point momentum energy damping*(Complex.I • kernel point momentum energy damping)) := by
      rw [mul_smul_comm,smul_smul]
      simp
    _ = (-Complex.I) • (-(1 : Operators)) := congrArg (fun A : Operators => (-Complex.I) • A) generated
    _ = _ := by simp

theorem value_kernel_left (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    kernel point momentum energy damping*value point momentum energy damping=Complex.I • (1 : Operators) := by
  have generated := value_generator_left point momentum energy damping positive
  rw [weightedGenerator_original] at generated
  calc
    _ = (-Complex.I) • ((Complex.I • kernel point momentum energy damping)*value point momentum energy damping) := by
      rw [smul_mul_assoc,smul_smul]
      simp
    _ = (-Complex.I) • (-(1 : Operators)) := congrArg (fun A : Operators => (-Complex.I) • A) generated
    _ = _ := by simp

def resolvent (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : Operators :=
  (-Complex.I) • value point momentum energy damping

theorem resolvent_two_sided (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    kernel point momentum energy damping*resolvent point momentum energy damping=1 ∧
      resolvent point momentum energy damping*kernel point momentum energy damping=1 := by
  constructor
  · rw [resolvent,mul_smul_comm,value_kernel_left point momentum energy damping positive,smul_smul]
    simp
  · rw [resolvent,smul_mul_assoc,value_kernel_right point momentum energy damping positive,smul_smul]
    simp

theorem kernel_isUnit (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) : IsUnit (kernel point momentum energy damping) :=
  ⟨⟨kernel point momentum energy damping,resolvent point momentum energy damping,
    (resolvent_two_sided point momentum energy damping positive).1,
    (resolvent_two_sided point momentum energy damping positive).2⟩,rfl⟩

theorem resolvent_ring_inverse (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    resolvent point momentum energy damping=Ring.inverse (kernel point momentum energy damping) := by
  have inverse := resolvent_two_sided point momentum energy damping positive
  have unit := kernel_isUnit point momentum energy damping positive
  calc
    _ = resolvent point momentum energy damping*(kernel point momentum energy damping*
        Ring.inverse (kernel point momentum energy damping)) := by rw [Ring.mul_inverse_cancel _ unit,mul_one]
    _ = (resolvent point momentum energy damping*kernel point momentum energy damping)*
        Ring.inverse (kernel point momentum energy damping) := (mul_assoc _ _ _).symm
    _ = _ := by rw [inverse.2,one_mul]

theorem value_eq_inverse (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    value point momentum energy damping=Complex.I • Ring.inverse (kernel point momentum energy damping) := by
  rw [← resolvent_ring_inverse point momentum energy damping positive,resolvent,smul_smul]
  simp

theorem resolvent_bound (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    ‖resolvent point momentum energy damping‖≤damping⁻¹+couplingNorm point*damping⁻¹^2 := by
  simpa only [resolvent,norm_smul,norm_neg,Complex.norm_I,one_mul] using
    value_bound point momentum energy damping positive

theorem kernel_continuous (point : BasePoint) (energy damping : ℝ) :
    Continuous (fun momentum : Fin 3 → ℝ => kernel point momentum energy damping) := by
  simp only [kernel_original,hamiltonian_split,operator_add]
  exact continuous_const.sub ((original_freeHamiltonian_continuous point).add continuous_const)

theorem value_continuous (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    Continuous (fun momentum : Fin 3 → ℝ => value point momentum energy damping) := by
  apply continuous_iff_continuousAt.mpr
  intro momentum
  have unit := kernel_isUnit point momentum energy damping positive
  have inverseAt : ContinuousAt Ring.inverse (kernel point momentum energy damping) := by
    simpa only [IsUnit.unit_spec] using NormedRing.inverse_continuousAt unit.unit
  have inverse : ContinuousAt (fun k : Fin 3 → ℝ => Ring.inverse (kernel point k energy damping)) momentum :=
    inverseAt.comp (f := fun k : Fin 3 → ℝ => kernel point k energy damping)
      (x := momentum) (kernel_continuous point energy damping).continuousAt
  have result := inverse.const_smul Complex.I
  change ContinuousAt (fun k : Fin 3 → ℝ => Complex.I • Ring.inverse (kernel point k energy damping)) momentum at result
  simpa only [← value_eq_inverse point _ energy damping positive] using result

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
