import H0mework.Physics.MotherSource.Contact
import H0mework.Physics.MotherProgrammesFormation.Flow

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContactSource

open StageNineEnrichedProofFreeSource StageNineSourceBridgeNoGo
open ContactFlow

noncomputable section

/-- The clock conversion uses the source's existing transport coefficient. -/
def normalizedFlow (source : StageNineEnrichedProofFreeSource.SmoothUnifiedSource) :
    ComplexUnitaryOneParameterFlow where
  evolve := fun time => (generatedUnitaryFlow source).evolve (time / (2 * source.legacy.sigma))
  evolve_zero := by simp [generatedUnitaryFlow]
  evolve_add := by
    intro a b
    rw [add_div]
    exact (generatedUnitaryFlow source).evolve_add _ _
  continuous_evolve := (generatedUnitaryFlow source).continuous_evolve.comp
    (continuous_id.div_const _)

/-- The contact datum is now an output of the primitive complement. The parent
material remains a separate formation responsibility. -/
def formedSource (parent : StageEightProofFreeSource.Source) :
    StageNineEnrichedProofFreeSource.SmoothUnifiedSource where
  stageEight := parent
  continuousContactResidual := 2 * Complex.arg (-1 : ℂ)

theorem normalized_formed (parent : StageEightProofFreeSource.Source) :
    normalizedFlow (formedSource parent) = generatedFlow := by
  apply flow_ext
  funext time
  change Circle.exp ((formedSource parent).continuousContactRate *
      (time / (2 * parent.toPhysicalSource.sigma))) =
    Circle.exp (Complex.arg (-1 : ℂ) * time)
  rw [SmoothUnifiedSource.continuousContactRate_eq_scalar]
  apply congrArg Circle.exp
  change parent.toPhysicalSource.sigma * (2 * Complex.arg (-1 : ℂ)) *
    (time / (2 * parent.toPhysicalSource.sigma)) = _
  field_simp [ne_of_gt parent.toPhysicalSource.sigma_pos]

theorem formed_primitive (parent : StageEightProofFreeSource.Source) :
    Primitive (normalizedFlow (formedSource parent)) := by
  rw [normalized_formed]
  exact generatedFlow_primitive

theorem physicalTime_restored (source : StageNineEnrichedProofFreeSource.SmoothUnifiedSource)
    (time : ℝ) :
    (normalizedFlow source).evolve ((2 * source.legacy.sigma) * time) =
      (generatedUnitaryFlow source).evolve time := by
  change (generatedUnitaryFlow source).evolve
    (((2 * source.legacy.sigma) * time) / (2 * source.legacy.sigma)) = _
  rw [mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) (ne_of_gt source.legacy.sigma_pos))]

theorem source_formed (source : StageNineEnrichedProofFreeSource.SmoothUnifiedSource)
    (law : Primitive (normalizedFlow source)) : source = formedSource source.stageEight := by
  apply source_eq_of_actual_flow source (formedSource source.stageEight) rfl
  funext time
  have normalized : normalizedFlow source = normalizedFlow (formedSource source.stageEight) :=
    (primitive_flow _ law).trans (normalized_formed source.stageEight).symm
  have read := congrArg
    (fun flow : ComplexUnitaryOneParameterFlow => flow.evolve ((2 * source.legacy.sigma) * time)) normalized
  rw [physicalTime_restored] at read
  exact read.trans (physicalTime_restored (formedSource source.stageEight) time)

theorem contact_formed (parent : StageEightProofFreeSource.Source) :
    ∃! source : StageNineEnrichedProofFreeSource.SmoothUnifiedSource,
      source.stageEight = parent ∧ Primitive (normalizedFlow source) := by
  refine ⟨formedSource parent, ⟨rfl, formed_primitive parent⟩, ?_⟩
  intro source valid
  rw [source_formed source valid.2, valid.1]

theorem original_formed : formedSource StageEightProofFreeSource.canonicalSource =
    positiveSmoothUnifiedSource := by
  simp [formedSource, positiveSmoothUnifiedSource]

theorem original_primitive : Primitive (normalizedFlow positiveSmoothUnifiedSource) := by
  rw [← original_formed]
  exact formed_primitive _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ContactSource
