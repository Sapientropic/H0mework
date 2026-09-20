import H0mework.Realization.Observation.Saturation

/-!
# Residual transport primitive kernel

This file is the direct Mathlib linear-algebra mouth used by modern effective
processes.  It contains no Proposition-series import: historical proposition
modules may prove richer readings, but the actual update, forced trace, and
active/fixed laws do not depend on that presentation chain.

The axiom-free source/event/path kernel remains
`ConstructiveNativeResidualGenerationKernel`; this module is its linear
carrier adapter and may inherit Mathlib's standard logical dependencies.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

universe u v

/-! ## Actual update and forced trace -/

/-- Relax a module-valued state toward `target` by scalar rate `sigma`. -/
def relaxModule
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (state : E) : E :=
  state + sigma • (target - state)

/-- State update induced by an arbitrary keep operator on target residuals. -/
def residualTransportUpdate
    {E : Type*} [AddCommGroup E]
    (keep : E → E) (target state : E) : E :=
  target - keep (target - state)

/-- The trace is the complementary residual forced by a linear keep map. -/
def linearResidualTrace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (residual : E) : E :=
  residual - keep residual

/-- Kept residual and forced trace reconstruct the source residual. -/
theorem linearResidualSplit_conserved
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (residual : E) :
    keep residual + linearResidualTrace keep residual = residual := by
  dsimp [linearResidualTrace]
  abel

/-- The same conservation law in source-oriented order. -/
theorem residual_eq_linearKeep_add_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (residual : E) :
    residual = keep residual + linearResidualTrace keep residual :=
  (linearResidualSplit_conserved keep residual).symm

/-- Two actual keeps spend exactly the trace of their composite. -/
theorem linearResidualTrace_twoStep_eq_composite_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep₂ keep₁ : E →ₗ[K] E) (residual : E) :
    linearResidualTrace keep₁ residual +
        linearResidualTrace keep₂ (keep₁ residual) =
      linearResidualTrace (keep₂.comp keep₁) residual := by
  dsimp [linearResidualTrace]
  abel

/-! ## Active transport -/

/-- A keep map is active when it has no nonzero fixed residual. -/
def ResidualTransportActive
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) : Prop :=
  ∀ residual : E, keep residual = residual → residual = 0

/-- Active transport is exactly `ker (id - keep) = ⊥`. -/
theorem residualTransportActive_iff_ker_id_sub_eq_bot
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) :
    ResidualTransportActive keep ↔
      LinearMap.ker ((LinearMap.id : E →ₗ[K] E) - keep) = ⊥ := by
  constructor
  · intro active
    apply le_antisymm
    · intro residual inKernel
      rw [Submodule.mem_bot]
      apply active residual
      have traceZero : residual - keep residual = 0 := by
        simpa using inKernel
      calc
        keep residual = residual - (residual - keep residual) := by abel
        _ = residual - 0 := by rw [traceZero]
        _ = residual := by simp
    · exact bot_le
  · intro kernel residual fixed
    have inKernel :
        residual ∈ LinearMap.ker ((LinearMap.id : E →ₗ[K] E) - keep) := by
      simp [fixed]
    have inBottom : residual ∈ (⊥ : Submodule K E) := by
      simpa [kernel] using inKernel
    simpa using inBottom

/-- Fixedness under a residual keep map. -/
def ResidualTransportFixed
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (residual : E) : Prop :=
  keep residual = residual

/-- Active transport is fixed exactly at zero residual. -/
theorem residualTransport_fixed_iff_zero_residual
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (active : ResidualTransportActive keep)
    (residual : E) :
    ResidualTransportFixed keep residual ↔ residual = 0 := by
  constructor
  · exact active residual
  · intro zero
    rw [zero]
    simp [ResidualTransportFixed]

/-- Active transport is fixed exactly when its forced trace vanishes. -/
theorem residualTransport_fixed_iff_zero_trace
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (active : ResidualTransportActive keep)
    (residual : E) :
    ResidualTransportFixed keep residual ↔
      linearResidualTrace keep residual = 0 := by
  constructor
  · intro fixed
    dsimp [ResidualTransportFixed] at fixed
    dsimp [linearResidualTrace]
    rw [fixed]
    simp
  · intro traceZero
    apply (residualTransport_fixed_iff_zero_residual keep active residual).2
    apply active residual
    dsimp [linearResidualTrace] at traceZero
    calc
      keep residual = residual - (residual - keep residual) := by abel
      _ = residual - 0 := by rw [traceZero]
      _ = residual := by simp

/-- A positive-definite energy reads active fixedness exactly as zero energy. -/
theorem residualTransport_fixed_iff_zero_energy
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E → ℝ)
    (active : ResidualTransportActive keep)
    (energyZero : ∀ residual : E, energy residual = 0 ↔ residual = 0)
    (residual : E) :
    ResidualTransportFixed keep residual ↔ energy residual = 0 :=
  (residualTransport_fixed_iff_zero_residual keep active residual).trans
    (energyZero residual).symm

/-- Zero forced trace and zero positive-definite energy are the same reading. -/
theorem residualTransport_zero_trace_iff_zero_energy
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (keep : E →ₗ[K] E) (energy : E → ℝ)
    (active : ResidualTransportActive keep)
    (energyZero : ∀ residual : E, energy residual = 0 ↔ residual = 0)
    (residual : E) :
    linearResidualTrace keep residual = 0 ↔ energy residual = 0 :=
  (residualTransport_fixed_iff_zero_trace keep active residual).symm.trans
    (residualTransport_fixed_iff_zero_energy
      keep energy active energyZero residual)

/-! ## Scalar chart -/

/-- Scalar keep map `residual ↦ (1 - sigma) • residual`. -/
def scalarKeepLinearMap
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (sigma : K) : E →ₗ[K] E :=
  (1 - sigma) • LinearMap.id

/-- Scalar residual transport is the affine relaxation update. -/
theorem scalar_linearResidualTransportUpdate_eq_relaxModule
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (target : E) (sigma : K) (state : E) :
    residualTransportUpdate
        (fun residual : E =>
          scalarKeepLinearMap (K := K) (E := E) sigma residual)
        target state =
      relaxModule target sigma state := by
  dsimp [residualTransportUpdate, scalarKeepLinearMap, relaxModule]
  module

/-- A nonzero scalar rate has no nonzero fixed residual. -/
theorem scalarKeepLinearMap_active_of_ne_zero
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [NoZeroSMulDivisors K E]
    (sigma : K) (sigma_ne_zero : sigma ≠ 0) :
    ResidualTransportActive
      (scalarKeepLinearMap (K := K) (E := E) sigma) := by
  intro residual fixed
  have spent : sigma • residual = 0 := by
    have complement : residual - (1 - sigma) • residual = 0 := by
      calc
        residual - (1 - sigma) • residual =
            residual - scalarKeepLinearMap (K := K) (E := E) sigma residual := by
              rfl
        _ = residual - residual := by rw [fixed]
        _ = 0 := by simp
    calc
      sigma • residual = residual - (1 - sigma) • residual := by
        rw [sub_smul]
        simp
      _ = 0 := complement
  exact (smul_eq_zero.mp spent).resolve_left sigma_ne_zero

end AffineRelaxation
end SaturationMonoid
