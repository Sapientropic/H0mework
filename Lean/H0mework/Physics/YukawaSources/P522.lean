import Mathlib.Tactic
import H0mework.Physics.RunningSources.P521

/-!
# Proposition 522: Yukawa leave-one-out sigma lock

The physics roadmap asks for a leave-one-out check on the frozen GUT-scale
Yukawa table: use eight Yukawa slots to lock the common running/consolidation
sigma, then predict the ninth.

This file formalizes the exact mathematical contract for that check.

Given a frozen table

`observed y = amplitude y * (1 - sigma) ^ exponent y`,

eight non-target slots lock sigma if any two sigma candidates matching those
eight slots must be equal.  Under that lock, the target-slot prediction is
unique.  Therefore a concrete GUT-scale Yukawa producer can no longer merely
"fit nine numbers"; it must provide, for each held-out slot, a sigma-lock
certificate from the other eight slots.

Boundary: this file does not supply the physical frozen Yukawa table, the
integer depths, or the RG extraction of GUT-scale Yukawas.  It turns the
leave-one-out demand into a small Lean-checkable certificate.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Residual-power Yukawa table -/

/-- The residual-power prediction for a Yukawa slot at a shared sigma. -/
def yukawaResidualPowerPrediction
    (amplitude : YukawaParameter -> ℝ)
    (exponent : YukawaParameter -> Nat)
    (sigma : ℝ)
    (y : YukawaParameter) : ℝ :=
  amplitude y * (((1 : ℝ) - sigma) ^ exponent y)

/-- A frozen GUT-scale Yukawa table in the residual-power coordinate. -/
structure FrozenGUTScaleYukawaTable where
  observed : YukawaParameter -> ℝ
  amplitude : YukawaParameter -> ℝ
  exponent : YukawaParameter -> Nat
  sigma : ℝ
  observed_eq_prediction :
    ∀ y : YukawaParameter,
      observed y =
        yukawaResidualPowerPrediction amplitude exponent sigma y

namespace FrozenGUTScaleYukawaTable

/-- The prediction function carried by a frozen table. -/
def predictionAt
    (T : FrozenGUTScaleYukawaTable)
    (sigma : ℝ)
    (y : YukawaParameter) : ℝ :=
  yukawaResidualPowerPrediction T.amplitude T.exponent sigma y

/-- THEOREM 1: the table's own sigma predicts every observed slot. -/
theorem observed_eq_predictionAt
    (T : FrozenGUTScaleYukawaTable)
    (y : YukawaParameter) :
    T.observed y = T.predictionAt T.sigma y :=
  T.observed_eq_prediction y

end FrozenGUTScaleYukawaTable

/-! ## Eight-slot sigma lock -/

/-- Eight non-target slots identify sigma when any two sigma candidates that
match those eight observations must be the same sigma. -/
def EightSlotSigmaLock
    (target : YukawaParameter)
    (observed amplitude : YukawaParameter -> ℝ)
    (exponent : YukawaParameter -> Nat) : Prop :=
  ∀ sigma₁ sigma₂ : ℝ,
    (∀ y : YukawaParameter, y ≠ target ->
      observed y =
        yukawaResidualPowerPrediction amplitude exponent sigma₁ y) ->
    (∀ y : YukawaParameter, y ≠ target ->
      observed y =
        yukawaResidualPowerPrediction amplitude exponent sigma₂ y) ->
    sigma₁ = sigma₂

/-- A candidate sigma for a leave-one-out table: it is judged only by the
eight non-target slots. -/
structure YukawaLeaveOneOutCandidate
    (T : FrozenGUTScaleYukawaTable)
    (target : YukawaParameter) where
  sigma : ℝ
  matches_eight :
    ∀ y : YukawaParameter, y ≠ target ->
      T.observed y = T.predictionAt sigma y

namespace YukawaLeaveOneOutCandidate

/-- THEOREM 2: under an eight-slot lock, any leave-one-out sigma candidate is
the frozen table's sigma. -/
theorem sigma_eq_table_sigma
    {T : FrozenGUTScaleYukawaTable}
    {target : YukawaParameter}
    (lock :
      EightSlotSigmaLock target T.observed T.amplitude T.exponent)
    (C : YukawaLeaveOneOutCandidate T target) :
    C.sigma = T.sigma := by
  symm
  exact
    lock T.sigma C.sigma
      (fun y _hy => T.observed_eq_predictionAt y)
      (fun y hy => C.matches_eight y hy)

/-- THEOREM 3: under an eight-slot lock, a leave-one-out sigma candidate
predicts the held-out target exactly. -/
theorem predicts_target
    {T : FrozenGUTScaleYukawaTable}
    {target : YukawaParameter}
    (lock :
      EightSlotSigmaLock target T.observed T.amplitude T.exponent)
    (C : YukawaLeaveOneOutCandidate T target) :
    T.observed target = T.predictionAt C.sigma target := by
  rw [T.observed_eq_predictionAt target, C.sigma_eq_table_sigma lock]

/-- THEOREM 4: under an eight-slot lock, any two candidate sigmas give the
same held-out target prediction. -/
theorem target_prediction_unique
    {T : FrozenGUTScaleYukawaTable}
    {target : YukawaParameter}
    (lock :
      EightSlotSigmaLock target T.observed T.amplitude T.exponent)
    (C₁ C₂ : YukawaLeaveOneOutCandidate T target) :
    T.predictionAt C₁.sigma target = T.predictionAt C₂.sigma target := by
  rw [C₁.sigma_eq_table_sigma lock, C₂.sigma_eq_table_sigma lock]

end YukawaLeaveOneOutCandidate

/-! ## A concrete sufficient lock: one linear anchor among the eight slots -/

/-- THEOREM 5: if one non-target Yukawa slot is linear in `(1-sigma)` and has
nonzero amplitude, that single anchor already identifies sigma, hence the
eight-slot lock holds.  This is not claimed to be the only possible lock; it is
a reusable sufficient certificate shape. -/
theorem eightSlotSigmaLock_of_linear_anchor
    {target anchor : YukawaParameter}
    {observed amplitude : YukawaParameter -> ℝ}
    {exponent : YukawaParameter -> Nat}
    (hanchor : anchor ≠ target)
    (hexp : exponent anchor = 1)
    (hamp : amplitude anchor ≠ 0) :
    EightSlotSigmaLock target observed amplitude exponent := by
  intro sigma₁ sigma₂ h₁ h₂
  have hpred :
      amplitude anchor * ((1 : ℝ) - sigma₁) =
        amplitude anchor * ((1 : ℝ) - sigma₂) := by
    have h₁a := h₁ anchor hanchor
    have h₂a := h₂ anchor hanchor
    rw [yukawaResidualPowerPrediction, hexp, pow_one] at h₁a h₂a
    rw [← h₁a, ← h₂a]
  have htail : (1 : ℝ) - sigma₁ = (1 : ℝ) - sigma₂ :=
    mul_left_cancel₀ hamp hpred
  linarith

/-- THEOREM 6: the linear-anchor sufficient lock gives exact leave-one-out
prediction of the held-out Yukawa slot. -/
theorem leaveOneOut_predicts_target_of_linear_anchor
    {T : FrozenGUTScaleYukawaTable}
    {target anchor : YukawaParameter}
    (hanchor : anchor ≠ target)
    (hexp : T.exponent anchor = 1)
    (hamp : T.amplitude anchor ≠ 0)
    (C : YukawaLeaveOneOutCandidate T target) :
    T.observed target = T.predictionAt C.sigma target := by
  exact
    C.predicts_target
      (eightSlotSigmaLock_of_linear_anchor
        (observed := T.observed)
        (amplitude := T.amplitude)
        (exponent := T.exponent)
        hanchor hexp hamp)

end StandardModelConstraint
end SaturationMonoid
