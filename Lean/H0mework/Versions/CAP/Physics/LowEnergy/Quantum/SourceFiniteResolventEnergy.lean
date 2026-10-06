import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceResolventLorentzian
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceResolventGraphSplice
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! A finite self-adjoint action generates its full-frequency resolvent energy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceFiniteResolventEnergy
open MeasureTheory FullYSourceResolventGraphSplice SourceResolventLorentzian
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [FiniteDimensional ℂ E]

def basis (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) :
    OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E :=
  (show C.toLinearMap.IsSymmetric from hC.isSymmetric).eigenvectorBasis rfl

def eigenvalue (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) : Fin (Module.finrank ℂ E) → ℝ :=
  (show C.toLinearMap.IsSymmetric from hC.isSymmetric).eigenvalues rfl

theorem coordinate_action (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (x : E) (i : Fin (Module.finrank ℂ E)) :
    (basis C hC).repr (C x) i=(eigenvalue C hC i : ℂ)*(basis C hC).repr x i :=
  (show C.toLinearMap.IsSymmetric from hC.isSymmetric).eigenvectorBasis_apply_self_apply rfl x i

theorem coordinate_resolvent (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (z : ℂ) (hz : z.im≠0) (x : E) (i : Fin (Module.finrank ℂ E)) :
    (basis C hC).repr (FullYSourceResolventGraphSplice.resolvent C z x) i=
      ((eigenvalue C hC i : ℂ)-z)⁻¹*(basis C hC).repr x i := by
  have he := congrArg (fun T : E →L[ℂ] E => T x) (resolvent_right C hC z hz)
  change C (FullYSourceResolventGraphSplice.resolvent C z x)-z • FullYSourceResolventGraphSplice.resolvent C z x=x at he
  have h := congrArg (fun y : E => (basis C hC).repr y i) he
  simp only [map_sub,map_smul,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at h
  rw [coordinate_action] at h
  have hn : (eigenvalue C hC i : ℂ)-z≠0 := by
    intro hzero
    have hi := congrArg Complex.im hzero
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hz hi
  apply mul_left_cancel₀ hn
  rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
  linear_combination h

theorem norm_square (C : E →L[ℂ] E) (hC : IsSelfAdjoint C) (x : E) :
    ‖x‖^2=∑ i, ‖(basis C hC).repr x i‖^2 := by
  rw [←(basis C hC).repr.norm_map x,PiLp.norm_sq_eq_of_L2]

theorem resolvent_norm_square (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ t : ℝ) (hμ : 0<μ) (x : E) :
    ‖FullYSourceResolventGraphSplice.resolvent C ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2=
      ∑ i, kernel μ (eigenvalue C hC i) t*‖(basis C hC).repr x i‖^2 := by
  rw [norm_square C hC]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinate_resolvent C hC ((t : ℂ)+Complex.I*(μ : ℂ)) (by simpa using hμ.ne'),norm_mul,mul_pow,inverse_norm_square]

theorem resolvent_square_integrable (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (x : E) :
    Integrable (fun t : ℝ => ‖FullYSourceResolventGraphSplice.resolvent C ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2) := by
  simp_rw [resolvent_norm_square C hC μ _ hμ x]
  exact integrable_finsetSum _ (fun i _ => (kernel_integrable μ (eigenvalue C hC i) hμ).mul_const _)

theorem resolvent_square_integral (C : E →L[ℂ] E) (hC : IsSelfAdjoint C)
    (μ : ℝ) (hμ : 0<μ) (x : E) :
    (∫ t : ℝ, ‖FullYSourceResolventGraphSplice.resolvent C ((t : ℂ)+Complex.I*(μ : ℂ)) x‖^2)=Real.pi/μ*‖x‖^2 := by
  simp_rw [resolvent_norm_square C hC μ _ hμ x]
  rw [integral_finsetSum _ (fun i _ => (kernel_integrable μ (eigenvalue C hC i) hμ).mul_const _)]
  simp_rw [integral_mul_const,kernel_integral μ _ hμ]
  rw [←Finset.mul_sum,←norm_square C hC x]

end LowEnergy.SourceFiniteResolventEnergy
