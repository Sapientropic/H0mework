import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialGreen.Integral
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! Positive imaginary frequency gives a coercive source estimate before any gauge continuation. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace Retarded YangMills.FullPairing ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Triangular
noncomputable section

theorem source_imaginary_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (energy damping : ℝ) (field hamiltonianValue : E)
    (real : (inner ℂ field hamiltonianValue).im=0) :
    (inner ℂ field (spectralParameter energy damping • field-hamiltonianValue)).im=damping*‖field‖^2 := by
  rw [inner_sub_right,inner_smul_right,Complex.sub_im,real,sub_zero,Complex.mul_im]
  simp [spectralParameter,← Complex.ofReal_pow]

theorem norm_of_imaginary_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (damping : ℝ) (field source : E)
    (identity : (inner ℂ field source).im=damping*‖field‖^2) :
    damping*‖field‖≤‖source‖ := by
  by_cases zero : field=0
  · simp [zero]
  have positive : 0<‖field‖ := norm_pos_iff.mpr zero
  have bound := (Complex.im_le_norm (inner ℂ field source)).trans (norm_inner_le_norm field source)
  rw [identity] at bound
  apply (mul_le_mul_iff_right₀ positive).mp
  nlinarith

theorem free_hamiltonian_real (point : BasePoint) (momentum : Fin 3 → ℝ) (field : Hilbert) :
    (inner ℂ field (operator (freeHamiltonian actual point momentum) field)).im=0 := by
  have source := original_freeHamiltonian_selfAdjoint point momentum
  have symmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp source
  exact symmetric.im_inner_self_apply field

def freeValue (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : FiberOperators :=
  operator (freeResolvent actual point momentum (spectralParameter energy damping))

theorem freeValue_equation (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) (source : Hilbert) :
    spectralParameter energy damping • freeValue point momentum energy damping source-
      operator (freeHamiltonian actual point momentum) (freeValue point momentum energy damping source)=source := by
  obtain ⟨field,rfl⟩ := naturalCoordinates.surjective source
  have inverse := LinearMap.congr_fun
    (Ring.mul_inverse_cancel (freeKernel actual point momentum (spectralParameter energy damping))
      (sourceFree_regular point momentum energy damping positive)) field
  have read := congrArg naturalCoordinates inverse
  simpa only [freeValue,operator_coordinates,freeKernel,freeResolvent,Module.End.mul_apply,
    LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,map_sub,map_smul] using read

theorem freeValue_imaginary_pair (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) (source : Hilbert) :
    (inner ℂ (freeValue point momentum energy damping source) source).im=
      damping*‖freeValue point momentum energy damping source‖^2 := by
  have result := source_imaginary_pair energy damping (freeValue point momentum energy damping source)
    (operator (freeHamiltonian actual point momentum) (freeValue point momentum energy damping source))
    (free_hamiltonian_real point momentum _)
  rw [freeValue_equation point momentum energy damping positive source] at result
  exact result

theorem freeValue_bound (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    ‖freeValue point momentum energy damping‖≤damping⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr positive.le)
  intro source
  have bound := norm_of_imaginary_pair damping (freeValue point momentum energy damping source) source
    (freeValue_imaginary_pair point momentum energy damping positive source)
  exact (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using bound) |>.trans_eq (by ring)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
