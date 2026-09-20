import H0mework.Physics.EmpiricalContact.Statistic

/-! Exact-source version of the frozen Methods nominal controls. The empirical
input tests the joint ideal preparation/phase/readout hypothesis. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical

open Bell Matrix StageNineEnrichedProofFreeSource ProofFreeRicherAnholonomicSource

noncomputable section

def axisScale : ℝ := Real.sqrt 2 / 2

theorem axisScale_sq : axisScale ^ 2 = 1 / 2 := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [axisScale]
  nlinarith

theorem axisScale_bounds : (2 / 3 : ℝ) < axisScale ∧ axisScale < 1 := by
  have nonnegative : 0 ≤ axisScale := by unfold axisScale; positivity
  have square := axisScale_sq
  constructor <;> nlinarith

def nominalAlice (setting : Bool) : Axis where
  x := if setting then -1 else 0
  z := if setting then 0 else 1
  unit := by cases setting <;> norm_num

def nominalBob (setting : Bool) : Axis where
  x := if setting then -axisScale else axisScale
  z := axisScale
  unit := by cases setting <;> simp only [Bool.false_eq_true, ↓reduceIte, neg_sq] <;>
      nlinarith [axisScale_sq]

def nominalHigh : ℝ := (1 + axisScale) / 4
def nominalLow : ℝ := (1 - axisScale) / 4

def nominalPrediction (a b x y : Bool) : ℝ :=
  probability (nominalAlice a) (heraldAxis true (colorXFrame (nominalBob b))) x y

theorem nominalPrediction_value (a b x y : Bool) :
    nominalPrediction a b x y =
      if (a && !b) = (x != y) then nominalHigh else nominalLow := by
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [nominalPrediction, probability, nominalAlice, nominalBob, heraldAxis,
      Axis.reflected, sign, colorXFrame, nominalHigh, nominalLow]

theorem exact_source_bounds :
    0 < nominalHigh ∧ nominalHigh ≤ 1 / 2 ∧
    0 < nominalLow ∧ nominalLow ≤ 1 / 12 := by
  obtain ⟨lower, upper⟩ := axisScale_bounds
  dsimp [nominalHigh, nominalLow]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exact_source_uniform_residual_positive :
    0 < uniformMixtureResidual nominalHigh nominalLow := by
  obtain ⟨hp, hu, lp, lu⟩ := exact_source_bounds
  have crossing := uniformComponent_gt_threshold nominalHigh nominalLow hp hu lp lu
  unfold uniformMixtureResidual
  linarith

theorem nominal_from_original_runtime (point : BasePoint) (a b x y : Bool) :
    (Stage9DEF.State.vectorEvaluation
      (right 1 0 *ᵥ (right 0 1 *ᵥ Runtime.tick.answer point))
      (outcomeEffect (nominalAlice a) (nominalBob b) x y).matrix).re =
      nominalPrediction a b x y :=
  phi_from_original_runtime point (nominalAlice a) (nominalBob b) x y

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical
