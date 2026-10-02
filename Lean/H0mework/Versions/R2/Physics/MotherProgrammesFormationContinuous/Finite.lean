import H0mework.Versions.R2.Physics.MotherProgrammesFormationRational.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCollision.Consumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContinuousSourceFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open AffineRelaxation Stage9C.Revision StageNineEnrichedProofFreeSource
open MotherFamilyOccurrence StageEightDiscreteFormation

noncomputable section

abbrev Coordinates := Fin 65 → ℝ

def coordinates (source : SmoothUnifiedSource) : Coordinates :=
  Fin.cons source.continuousContactResidual (fun slot =>
    source.stageEight.coframeLinearCoefficient
      (RationalSourceFormation.coframeIndex.symm slot).1
      (RationalSourceFormation.coframeIndex.symm slot).2.1
      (RationalSourceFormation.coframeIndex.symm slot).2.2)

def response (value : ℝ) : ℝ := value^2 / (1+value^2)

theorem response_nonnegative (value : ℝ) : 0 ≤ response value := by unfold response; positivity

theorem response_lt_one (value : ℝ) : response value < 1 := by
  unfold response
  exact (div_lt_one (by positivity)).2 (by linarith)

def responseAt (visit : MotherVisit) : Coordinates :=
  fun slot => response (coordinates (RationalSourceFormation.assembledSource visit) slot)

def retained (step : ℕ) : ℝ := (Runtime.source.continuousKeep : ℝ → ℝ)^[step] 1

def weight (step : ℕ) : ℝ := linearResidualTrace Runtime.source.continuousKeep (retained step)

theorem original_sigma : Runtime.source.legacy.sigma = 1/2 :=
  Stage9C.Material.SpinPair.sourceCoupling_eq

theorem retained_eq (step : ℕ) : retained step = (1/2:ℝ)^step := by
  induction step with
  | zero => rfl
  | succ step induction =>
      rw [retained, Function.iterate_succ_apply']
      change Runtime.source.continuousKeep (retained step) = _
      change (1-Runtime.source.legacy.sigma)*retained step = _
      rw [original_sigma, induction, pow_succ]
      ring

theorem weight_native (step : ℕ) :
    weight step = Runtime.source.legacy.sigma * (1-Runtime.source.legacy.sigma)^step := by
  have trace := residualTransportCore_scalar_trace Runtime.source.legacy.sigma (retained step)
  change weight step = Runtime.source.legacy.sigma * retained step at trace
  rw [trace, original_sigma, retained_eq]
  norm_num

theorem weight_eq (step : ℕ) : weight step = (1/2:ℝ)^(step+1) := by
  rw [weight_native, original_sigma, pow_succ]
  norm_num
  ring

theorem weight_positive (step : ℕ) : 0 < weight step := by rw [weight_eq]; positivity

def contribution (step : ℕ) : Coordinates := weight step • responseAt (SpinPair.visit (10+step))

theorem contribution_bounds (step : ℕ) (slot : Fin 65) :
    0 ≤ contribution step slot ∧ contribution step slot ≤ weight step := by
  change 0 ≤ weight step * response _ ∧ weight step * response _ ≤ weight step
  exact ⟨mul_nonneg (le_of_lt (weight_positive step)) (response_nonnegative _),
    mul_le_of_le_one_right (le_of_lt (weight_positive step)) (le_of_lt (response_lt_one _))⟩

/-- The accumulator only reads the predecessor visit stored in each actual
history edge. Rational sampling itself is confined to that predecessor's prefix. -/
def accumulateHistory {current : SpinPair.V.Current} :
    MotherRoot.toRoot.ReachableAt current → Coordinates
  | .initial => 0
  | @RootClosure.ReachableAt.step _ _ _ current _ prior _ =>
      if ProductiveFiniteRootHistoryAt.causalDepth prior < originDepth then accumulateHistory prior
      else accumulateHistory prior +
        weight (ProductiveFiniteRootHistoryAt.causalDepth prior-originDepth) •
          responseAt (.finite ⟨current, prior⟩)

def accumulator (visit : MotherVisit) : Coordinates := accumulateHistory (finiteVisit visit).history

theorem accumulator_next (visit : MotherVisit) (afterOrigin : originDepth ≤ temporalDepth visit.history) :
    accumulator (targetVisit visit) = accumulator visit + weight (codeOf visit) • responseAt visit := by
  rw [target_native]
  unfold accumulator
  rw [finite_next]
  change (if ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit visit).history < originDepth then _
    else accumulateHistory (finiteVisit visit).history +
      weight (ProductiveFiniteRootHistoryAt.causalDepth (finiteVisit visit).history-originDepth) •
        responseAt (.finite (finiteVisit visit))) = _
  rw [finite_depth, if_neg (not_lt_of_ge afterOrigin), finite_readback]
  rfl

def finite (step : ℕ) : Coordinates := accumulator (SpinPair.visit (10+step))

theorem finite_zero : finite 0 = 0 := rfl

theorem finite_next (step : ℕ) : finite (step+1) = finite step + contribution step := by
  have next := accumulator_next (SpinPair.visit (10+step)) (by rw [origin_depth, visit_depth]; omega)
  unfold finite contribution
  rw [← (MotherFamilyOccurrence.generated_family_next step).1]
  simpa only [code_at] using next

theorem finite_prefix (step : ℕ) : finite step = ∑ prior ∈ Finset.range step, contribution prior := by
  induction step with
  | zero => simp [finite_zero]
  | succ step induction => rw [finite_next, induction, Finset.sum_range_succ]

theorem input_in_original_prefix (step : ℕ) (slot : Fin 66) :
    temporalDepth (RationalSourceFormation.sampleVisit (SpinPair.visit (10+step)) slot).history ≤
      temporalDepth (SpinPair.visit (10+step)).history :=
  RationalSourceFormation.sample_depth_le _ _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContinuousSourceFormation
