import H0mework.Physics.MotherProgrammesFormation.Source
import H0mework.Physics.MotherProgrammesFormationCollision.History

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointContactSource

open StageNineEnrichedProofFreeSource AffineRelaxation
open ContactCollision CollisionHistory

noncomputable section

/-- The source chart is read from the actual channel weight. -/
def transportFraction : ℝ := Complex.normSq b

def generatedSeed : ℕ := Nat.floor transportFraction⁻¹ - 2

def generatedResidual : ℝ := 2 * Complex.arg (primitive : ℂ)

theorem fraction_half : transportFraction = (1 / 2 : ℝ) := normSq_b

theorem generatedSeed_zero : generatedSeed = 0 := by
  norm_num [generatedSeed, fraction_half]

theorem residual_normalForm : generatedResidual = 2 * Real.pi := by
  simp [generatedResidual, primitive_eq]

/-- Five material coordinates remain inputs. The scalar chart and contact
residual are outputs of the same two-channel operation; the old seed is unused. -/
def formedSource (material : StageEightProofFreeSource.Source) : SmoothUnifiedSource where
  stageEight := { material with sigmaSeed := generatedSeed }
  continuousContactResidual := generatedResidual

theorem old_seed_irrelevant (material : StageEightProofFreeSource.Source) (seed : ℕ) :
    formedSource {material with sigmaSeed := seed} = formedSource material := rfl

theorem source_fraction (material : StageEightProofFreeSource.Source) :
    (formedSource material).legacy.sigma = transportFraction := by
  norm_num [formedSource, SmoothUnifiedSource.legacy, SmoothUnifiedSource.forget,
    StageEightProofFreeSource.Source.toPhysicalSource,
    ProofFreeRicherAnholonomicSource.Source.sigma, generatedSeed_zero, fraction_half]

theorem source_rate (material : StageEightProofFreeSource.Source) :
    (formedSource material).continuousContactRate = Real.pi := by
  rw [SmoothUnifiedSource.continuousContactRate_eq_scalar, source_fraction, fraction_half]
  change (1 / 2 : ℝ) * generatedResidual = Real.pi
  rw [residual_normalForm]
  ring

theorem source_flow (material : StageEightProofFreeSource.Source) :
    generatedUnitaryFlow (formedSource material) = ContactFlow.generatedFlow := by
  apply ContactFlow.flow_ext
  funext time
  change Circle.exp ((formedSource material).continuousContactRate * time) = _
  rw [source_rate]
  simp [ContactFlow.generatedFlow]

theorem source_primitive (material : StageEightProofFreeSource.Source) :
    ContactFlow.Primitive (ContactSource.normalizedFlow (formedSource material)) := by
  have same : ContactSource.normalizedFlow (formedSource material) =
      generatedUnitaryFlow (formedSource material) := by
    apply ContactFlow.flow_ext
    funext time
    change (generatedUnitaryFlow (formedSource material)).evolve
      (time / (2 * (formedSource material).legacy.sigma)) = _
    rw [source_fraction, fraction_half]
    norm_num
  rw [same, source_flow]
  exact ContactFlow.generatedFlow_primitive

theorem keep_generated (material : StageEightProofFreeSource.Source) (r : ℝ) :
    (formedSource material).continuousKeep r = Complex.normSq a * r := by
  change (1 - (formedSource material).legacy.sigma) * r = Complex.normSq a * r
  rw [source_fraction, fraction_half, normSq_a]
  ring

theorem trace_generated (material : StageEightProofFreeSource.Source) (r : ℝ) :
    linearResidualTrace (formedSource material).continuousKeep r = Complex.normSq b * r := by
  change linearResidualTrace (scalarKeepLinearMap (formedSource material).legacy.sigma) r = _
  rw [residualTransportCore_scalar_trace, source_fraction]
  rfl

theorem retained_step (material : StageEightProofFreeSource.Source) (r : ℝ)
    {depth : ℕ} (v : H depth) :
    r * Complex.normSq (CollisionHistory.step a b v 0) =
      (formedSource material).continuousKeep (r * Complex.normSq (v 0)) := by
  rw [step_retained, Complex.normSq_mul, keep_generated]
  ring

theorem emitted_step (material : StageEightProofFreeSource.Source) (r : ℝ)
    {depth : ℕ} (v : H depth) :
    r * Complex.normSq (CollisionHistory.step a b v (Fin.last (depth + 1))) =
      linearResidualTrace (formedSource material).continuousKeep (r * Complex.normSq (v 0)) := by
  rw [step_fresh_emitted, Complex.normSq_mul, trace_generated]
  ring

theorem generated_recurrence (material : StageEightProofFreeSource.Source) (r : ℝ) (depth : ℕ) :
    r * Complex.normSq (formed depth 0) =
      ((formedSource material).continuousKeep : ℝ → ℝ)^[depth] r := by
  induction depth with
  | zero => simp [formed_retained_weight]
  | succ depth previous =>
    rw [formed_next, retained_step, previous, Function.iterate_succ_apply']

theorem original_formed : formedSource StageEightProofFreeSource.canonicalSource =
    positiveSmoothUnifiedSource := by
  simp only [formedSource, generatedSeed_zero, residual_normalForm, positiveSmoothUnifiedSource,
    StageEightProofFreeSource.canonicalSource]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointContactSource
