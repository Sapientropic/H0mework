import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Generator read directly from an isometric flow

The construction uses only the complex normed-space structure, so it also
accepts isometric actions on observable Banach algebras. The differentiable
vectors form a complex submodule. The generator is the
actual orbit derivative on that domain, and its translates give the orbit
derivative at every real time. Domain density is proved from strong continuity
in the time-average construction.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace SaturationMonoid.Quantum.Generator

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (U : Multiplicative ℝ →* (E ≃ₗᵢ[ℂ] E))

/-- The flow sends each vector to its complete real-time orbit. -/
def orbit : E →ₗ[ℂ] (ℝ → E) where
  toFun x t := U (Multiplicative.ofAdd t) x
  map_add' x y := funext (fun t => map_add (U (Multiplicative.ofAdd t)) x y)
  map_smul' c x := funext (fun t => map_smul (U (Multiplicative.ofAdd t)) c x)

@[simp] theorem orbit_zero (x : E) : orbit U x 0 = x := by simp [orbit]

theorem orbit_add (x : E) (s t : ℝ) :
    orbit U x (s + t) = orbit U (orbit U x t) s := by
  change (U (Multiplicative.ofAdd s * Multiplicative.ofAdd t)) x = _
  rw [map_mul]
  rfl

/-- The actual differentiability domain; no domain is supplied by the caller. -/
def domain : Submodule ℂ E where
  carrier := {x | DifferentiableAt ℝ (orbit U x) 0}
  zero_mem' := by
    change DifferentiableAt ℝ (orbit U 0) 0
    rw [map_zero]
    exact differentiableAt_const 0
  add_mem' := by
    intro x y hx hy
    change DifferentiableAt ℝ (orbit U (x + y)) 0
    simpa only [map_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    change DifferentiableAt ℝ (orbit U (c • x)) 0
    simpa only [map_smul] using hx.const_smul c

/-- The infinitesimal generator is the derivative of this same flow. -/
def generator : domain U →ₗ[ℂ] E where
  toFun x := deriv (orbit U x) 0
  map_add' x y := by
    have h := deriv_add x.property y.property
    simpa only [Submodule.coe_add, map_add] using h
  map_smul' c x := by
    have h := deriv_const_smul c x.property
    simpa only [Submodule.coe_smul, map_smul, RingHom.id_apply] using h

/-- The convention `U(t) = exp(-itH)` fixes `H = i dU/dt`. -/
def hamiltonian : domain U →ₗ[ℂ] E := Complex.I • generator U

theorem hasDerivAt_zero (x : domain U) :
    HasDerivAt (orbit U x) (generator U x) 0 := x.property.hasDerivAt

/-- Differentiability at zero generates the derivative at every physical time. -/
theorem orbit_hasDerivAt (x : domain U) (t : ℝ) :
    HasDerivAt (orbit U x) (orbit U (generator U x) t) t := by
  have shifted := (hasDerivAt_zero U x).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (sub_self t).symm
  have acted := ((U (Multiplicative.ofAdd t)).toContinuousLinearEquiv.toContinuousLinearMap
    |>.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t shifted
  convert acted using 1
  · funext s
    change orbit U x s = orbit U (orbit U x (s - t)) t
    rw [← orbit_add, add_sub_cancel]
  · simp [orbit]

end
end SaturationMonoid.Quantum.Generator
