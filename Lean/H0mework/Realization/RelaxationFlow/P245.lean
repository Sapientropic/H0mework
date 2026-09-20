import H0mework.Realization.Relaxation.P244
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Proposition 245: real continuous-time relaxation flow

P243/P244 prove the finite-iterate laws for fixed target/rate relaxation.  This
file records the continuous-time real-rate envelope that those laws approximate
when the residual factor is written as an exponential:

`sigma(t) = 1 - exp(-lambda * t)`.

For a fixed target and fixed real `lambda`, this produces a same-target flow
whose residual is `exp(-lambda * t)`, whose time composition is additive, and
whose derivative satisfies the linear relaxation equation

`dX/dt = lambda • (target - X(t))`.

Boundary: this is the exact flow of a fixed-target real affine relaxation.  It
does not choose the physical time parameter, fit an empirical rate, identify a
Hamiltonian generator, prove Schrödinger evolution, tensor geometry, gauge
transport, or a Standard Model projection.
-/

namespace SaturationMonoid
namespace AffineRelaxation

noncomputable section

/-! ## Exponential residual and induced rate -/

/-- Continuous-time residual factor `exp(-lambda * t)`. -/
def realDecayResidual (lambda t : ℝ) : ℝ :=
  Real.exp ((-lambda) * t)

/-- The relaxation rate whose residual is `exp(-lambda * t)`. -/
def realDecayRate (lambda t : ℝ) : ℝ :=
  1 - realDecayResidual lambda t

/-- The fixed-target real continuous-time affine relaxation flow. -/
def realDecayRelaxFlow
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda t : ℝ) (x : E) : E :=
  relaxModule target (realDecayRate lambda t) x

/-- The residual factor maps time addition to multiplication. -/
theorem realDecayResidual_add (lambda t s : ℝ) :
    realDecayResidual lambda (t + s) =
      realDecayResidual lambda t * realDecayResidual lambda s := by
  unfold realDecayResidual
  calc
    Real.exp ((-lambda) * (t + s)) =
        Real.exp ((-lambda) * t + (-lambda) * s) := by
          congr 1
          ring
    _ = Real.exp ((-lambda) * t) * Real.exp ((-lambda) * s) := by
          rw [Real.exp_add]

/-- At time zero the residual is one. -/
theorem realDecayResidual_zero (lambda : ℝ) :
    realDecayResidual lambda 0 = 1 := by
  simp [realDecayResidual]

/-- At time zero the induced rate is zero. -/
theorem realDecayRate_zero (lambda : ℝ) :
    realDecayRate lambda 0 = 0 := by
  simp [realDecayRate, realDecayResidual_zero]

/-- The exponential-rate law composes by the same noisy-OR law as discrete
same-target relaxation. -/
theorem satOrField_realDecayRate (lambda t s : ℝ) :
    satOrField (realDecayRate lambda t) (realDecayRate lambda s) =
      realDecayRate lambda (t + s) := by
  unfold satOrField realDecayRate
  rw [realDecayResidual_add]
  ring

/-! ## Flow laws -/

/-- Closed residual form of the real continuous-time relaxation flow. -/
theorem realDecayRelaxFlow_eq_closed
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda t : ℝ) (x : E) :
    realDecayRelaxFlow target lambda t x =
      target - realDecayResidual lambda t • (target - x) := by
  unfold realDecayRelaxFlow realDecayRate realDecayResidual relaxModule
  module

/-- Time zero is the identity map. -/
theorem realDecayRelaxFlow_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda : ℝ) (x : E) :
    realDecayRelaxFlow target lambda 0 x = x := by
  unfold realDecayRelaxFlow
  rw [realDecayRate_zero, relaxModule_zero]

/-- The fixed-target exponential-rate relaxation flow composes by time
addition.  Applying time `t` and then time `s` is the same as applying
time `t+s`. -/
theorem realDecayRelaxFlow_add
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (target : E) (lambda t s : ℝ) (x : E) :
    realDecayRelaxFlow target lambda s
        (realDecayRelaxFlow target lambda t x) =
      realDecayRelaxFlow target lambda (t + s) x := by
  unfold realDecayRelaxFlow
  rw [relaxModule_compose]
  rw [satOrField_realDecayRate]

/-- The distance between two trajectories at the same time is scaled by the
exponential residual factor. -/
theorem dist_realDecayRelaxFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda t : ℝ) (x y : E) :
    dist (realDecayRelaxFlow target lambda t x)
        (realDecayRelaxFlow target lambda t y) =
      realDecayResidual lambda t * dist x y := by
  unfold realDecayRelaxFlow realDecayRate
  rw [dist_relaxModule_real]
  have h :
      |(1 : ℝ) - (1 - realDecayResidual lambda t)| =
        realDecayResidual lambda t := by
    have hpos : 0 <= realDecayResidual lambda t := by
      exact Real.exp_nonneg _
    rw [sub_sub_cancel, abs_of_nonneg hpos]
  rw [h]

/-- Distance to the target under the same flow is scaled by the exponential
residual factor. -/
theorem dist_realDecayRelaxFlow_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda t : ℝ) (x : E) :
    dist (realDecayRelaxFlow target lambda t x) target =
      realDecayResidual lambda t * dist x target := by
  unfold realDecayRelaxFlow realDecayRate
  rw [dist_relaxModule_target_real]
  have h :
      |(1 : ℝ) - (1 - realDecayResidual lambda t)| =
        realDecayResidual lambda t := by
    have hpos : 0 <= realDecayResidual lambda t := by
      exact Real.exp_nonneg _
    rw [sub_sub_cancel, abs_of_nonneg hpos]
  rw [h]

/-! ## Differential equation -/

/-- Derivative of the exponential residual factor. -/
theorem hasDerivAt_realDecayResidual (lambda t : ℝ) :
    HasDerivAt (fun τ : ℝ => realDecayResidual lambda τ)
      ((-lambda) * realDecayResidual lambda t) t := by
  unfold realDecayResidual
  have hlinear : HasDerivAt (fun τ : ℝ => (-lambda) * τ) (-lambda) t := by
    simpa using (hasDerivAt_id' t).const_mul (-lambda)
  convert hlinear.exp using 1
  ring

/-- Derivative of the induced rate `1 - exp(-lambda*t)`. -/
theorem hasDerivAt_realDecayRate (lambda t : ℝ) :
    HasDerivAt (fun τ : ℝ => realDecayRate lambda τ)
      (lambda * realDecayResidual lambda t) t := by
  have hres := hasDerivAt_realDecayResidual lambda t
  have hsub :
      HasDerivAt (fun τ : ℝ => (1 : ℝ) - realDecayResidual lambda τ)
        (0 - ((-lambda) * realDecayResidual lambda t)) t :=
    (hasDerivAt_const (x := t) (c := (1 : ℝ))).sub hres
  have hderiv :
      0 - ((-lambda) * realDecayResidual lambda t) =
        lambda * realDecayResidual lambda t := by
    ring
  simpa [realDecayRate, hderiv] using hsub

/-- The continuous-time relaxation flow is the exact solution of the fixed
target linear relaxation equation `dX/dt = lambda • (target - X(t))`. -/
theorem hasDerivAt_realDecayRelaxFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (target : E) (lambda t : ℝ) (x : E) :
    HasDerivAt (fun τ : ℝ => realDecayRelaxFlow target lambda τ x)
      (lambda • (target - realDecayRelaxFlow target lambda t x)) t := by
  have hres := hasDerivAt_realDecayResidual lambda t
  have hvec :
      HasDerivAt
        (fun τ : ℝ => realDecayResidual lambda τ • (target - x))
        (((-lambda) * realDecayResidual lambda t) • (target - x)) t :=
    hres.smul_const (target - x)
  have hclosed :
      HasDerivAt
        (fun τ : ℝ => target - realDecayResidual lambda τ • (target - x))
        (0 - (((-lambda) * realDecayResidual lambda t) • (target - x))) t :=
    (hasDerivAt_const (x := t) (c := target)).sub hvec
  have hderiv_eq :
      0 - (((-lambda) * realDecayResidual lambda t) • (target - x)) =
        lambda • (target - realDecayRelaxFlow target lambda t x) := by
    rw [realDecayRelaxFlow_eq_closed]
    module
  convert hclosed using 1
  · ext τ
    rw [realDecayRelaxFlow_eq_closed]
  · exact hderiv_eq.symm

/-- A bundled certificate for the real continuous-time relaxation envelope. -/
structure RealContinuousRelaxationFlowCertificate
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  residual_add :
    ∀ lambda t s : ℝ,
      realDecayResidual lambda (t + s) =
        realDecayResidual lambda t * realDecayResidual lambda s
  flow_zero :
    ∀ target : E, ∀ lambda : ℝ, ∀ x : E,
      realDecayRelaxFlow target lambda 0 x = x
  flow_add :
    ∀ target : E, ∀ lambda t s : ℝ, ∀ x : E,
      realDecayRelaxFlow target lambda s
          (realDecayRelaxFlow target lambda t x) =
        realDecayRelaxFlow target lambda (t + s) x
  distance :
    ∀ target : E, ∀ lambda t : ℝ, ∀ x y : E,
      dist (realDecayRelaxFlow target lambda t x)
          (realDecayRelaxFlow target lambda t y) =
        realDecayResidual lambda t * dist x y
  ode :
    ∀ target : E, ∀ lambda t : ℝ, ∀ x : E,
      HasDerivAt (fun τ : ℝ => realDecayRelaxFlow target lambda τ x)
        (lambda • (target - realDecayRelaxFlow target lambda t x)) t

/-- Real normed-vector carriers supply the continuous-time relaxation-flow
certificate. -/
theorem realContinuousRelaxationFlowCertificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    RealContinuousRelaxationFlowCertificate E where
  residual_add := realDecayResidual_add
  flow_zero := realDecayRelaxFlow_zero
  flow_add := realDecayRelaxFlow_add
  distance := dist_realDecayRelaxFlow
  ode := hasDerivAt_realDecayRelaxFlow


end

end AffineRelaxation
end SaturationMonoid
