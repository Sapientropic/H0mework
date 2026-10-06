import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.Normed.Operator.Extend

/-! A faithful dense reflection map determines a unitary onto its source
Hilbert space. The positive square root preserves exactly the reflection
norm, so the identification is generated without a supplied inverse. -/

set_option autoImplicit false

open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Transfer.Polar

noncomputable section

variable {F H : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjoint_denseRange (A : F →L[ℂ] F) (symmetric : IsSelfAdjoint A)
    (injective : Function.Injective A) : DenseRange A := by
  change Dense (A.range : Set F)
  rw [Submodule.dense_iff_topologicalClosure_eq_top, ← symmetric.adjoint_eq,
    ← A.orthogonal_ker, LinearMap.ker_eq_bot.mpr injective]
  simp

variable (R : F →L[ℂ] H)

def covariance : F →L[ℂ] F := R.adjoint.comp R

def squareRoot : F →L[ℂ] F := CFC.sqrt (covariance R)

theorem covariance_nonnegative : 0 ≤ covariance R :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
    (ContinuousLinearMap.isPositive_adjoint_comp_self R)

theorem squareRoot_selfAdjoint : IsSelfAdjoint (squareRoot R) :=
  (CFC.sqrt_nonneg (covariance R)).isSelfAdjoint

theorem squareRoot_square : (squareRoot R).comp (squareRoot R) = covariance R :=
  CFC.sqrt_mul_sqrt_self (covariance R) (covariance_nonnegative R)

theorem squareRoot_norm (x : F) : ‖squareRoot R x‖ = ‖R x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left,
    (squareRoot_selfAdjoint R).adjoint_eq,
    squareRoot_square]
  exact (R.apply_norm_sq_eq_inner_adjoint_left x).symm

theorem squareRoot_commutes : (squareRoot R).comp (covariance R) =
    (covariance R).comp (squareRoot R) := by
  conv_lhs => rw [← squareRoot_square R]
  rw [← ContinuousLinearMap.comp_assoc, squareRoot_square]

theorem squareRoot_injective (injective : Function.Injective R) :
    Function.Injective (squareRoot R) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x zero
  change squareRoot R x = 0 at zero
  apply injective
  rw [map_zero]
  apply norm_eq_zero.mp
  rw [← squareRoot_norm R x, zero, norm_zero]

theorem squareRoot_denseRange (injective : Function.Injective R) : DenseRange (squareRoot R) :=
  selfAdjoint_denseRange (squareRoot R) (squareRoot_selfAdjoint R) (squareRoot_injective R injective)

def identification (injective : Function.Injective R) (dense : DenseRange R) : H ≃ₗᵢ[ℂ] F :=
  (LinearEquiv.refl ℂ F).extendOfIsometry R.toLinearMap (squareRoot R).toLinearMap
    dense (squareRoot_denseRange R injective) (squareRoot_norm R)

theorem identification_reflection (injective : Function.Injective R) (dense : DenseRange R) (f : F) :
    identification R injective dense (R f) = squareRoot R f :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

theorem identification_intertwines (injective : Function.Injective R) (dense : DenseRange R) (h : H) :
    identification R injective dense ((R.comp R.adjoint) h) =
      covariance R (identification R injective dense h) := by
  refine dense.induction ?_ (isClosed_eq
    ((identification R injective dense).continuous.comp (R.comp R.adjoint).continuous)
    ((covariance R).continuous.comp (identification R injective dense).continuous)) h
  rintro _ ⟨f, rfl⟩
  change identification R injective dense (R (covariance R f)) =
    covariance R (identification R injective dense (R f))
  rw [identification_reflection, identification_reflection]
  exact congrArg (fun A : F →L[ℂ] F => A f) (squareRoot_commutes R)



end
end SaturationMonoid.Quantum.Transfer.Polar
