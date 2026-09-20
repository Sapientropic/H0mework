import H0mework.Physics.Source.EnrichedProofFreeSource

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness

open StageEightProofFreeSource StageNineEnrichedProofFreeSource
open ProofFreeRicherAnholonomicSource SU7MotherLieAlgebra
open StandardModelConstraint

noncomputable section

/-- The contact datum is recovered from the original generated curvature,
using the positive source transport coefficient already paid by Stage 8. -/
def curvatureRate (curvature : SU7MotherLieMatrix) : ℝ :=
  (curvature : Matrix SU7MotherIndex SU7MotherIndex ℂ) hyperPlusIndex hyperPlusIndex |>.im

theorem curvatureRate_generated (source : SmoothUnifiedSource) :
    curvatureRate (generatedMotherCurvature source 0 1) = source.continuousContactRate := by
  rw [generatedMotherCurvature_zero_one]
  simp [curvatureRate, motherHyperchargeDirection_hyperPlus_entry]

theorem contact_from_curvature (source : SmoothUnifiedSource) :
    curvatureRate (generatedMotherCurvature source 0 1) / source.legacy.sigma = source.continuousContactResidual := by
  rw [curvatureRate_generated, SmoothUnifiedSource.continuousContactRate_eq_scalar]
  exact mul_div_cancel_left₀ _ (ne_of_gt source.legacy.sigma_pos)

def reconstruct (parent : StageEightProofFreeSource.Source) (curvature : SU7MotherLieMatrix) : SmoothUnifiedSource where
  stageEight := parent
  continuousContactResidual := curvatureRate curvature / parent.toPhysicalSource.sigma

theorem reconstruct_generated (source : SmoothUnifiedSource) :
    reconstruct source.stageEight (generatedMotherCurvature source 0 1) = source := by
  have restored := contact_from_curvature source
  cases source with
  | mk parent contact =>
    exact congrArg (SmoothUnifiedSource.mk parent) restored

theorem source_eq_of_generated_curvature (first last : SmoothUnifiedSource)
    (parent : first.stageEight = last.stageEight)
    (curvature : generatedMotherCurvature first 0 1 = generatedMotherCurvature last 0 1) : first = last := by
  calc
    first = reconstruct first.stageEight (generatedMotherCurvature first 0 1) := (reconstruct_generated first).symm
    _ = reconstruct last.stageEight (generatedMotherCurvature last 0 1) := by rw [parent, curvature]
    _ = last := reconstruct_generated last

theorem source_eq_iff_parent_curvature (first last : SmoothUnifiedSource) :
    first = last ↔ first.stageEight = last.stageEight ∧
      generatedMotherCurvature first 0 1 = generatedMotherCurvature last 0 1 := by
  constructor
  · intro same; cases same; exact ⟨rfl,rfl⟩
  · rintro ⟨parent, curvature⟩; exact source_eq_of_generated_curvature first last parent curvature

def separatingTime (first last : SmoothUnifiedSource) : ℝ :=
  Real.pi / (first.continuousContactRate-last.continuousContactRate)

theorem different_rate_separates_actual_flow (first last : SmoothUnifiedSource)
    (different : first.continuousContactRate ≠ last.continuousContactRate) :
    (generatedUnitaryFlow first).evolve (separatingTime first last) ≠
      (generatedUnitaryFlow last).evolve (separatingTime first last) := by
  intro same
  have normalized : (first.continuousContactRate-last.continuousContactRate)*separatingTime first last = Real.pi := by
    unfold separatingTime
    field_simp [sub_ne_zero.mpr different]
  have ratio : Circle.exp ((first.continuousContactRate-last.continuousContactRate)*separatingTime first last) = 1 := by
    rw [sub_mul, Circle.exp_sub]
    change (generatedUnitaryFlow first).evolve (separatingTime first last) /
      (generatedUnitaryFlow last).evolve (separatingTime first last) = 1
    rw [same, div_self']
  exact Circle.exp_pi_ne_one (normalized ▸ ratio)

theorem flow_eq_iff_rate (first last : SmoothUnifiedSource) :
    (generatedUnitaryFlow first).evolve = (generatedUnitaryFlow last).evolve ↔
      first.continuousContactRate = last.continuousContactRate := by
  constructor
  · intro same
    by_contra different
    exact different_rate_separates_actual_flow first last different (congrFun same _)
  · intro same; funext time; change Circle.exp (_*time)=Circle.exp (_*time); rw [same]

theorem source_eq_of_actual_flow (first last : SmoothUnifiedSource)
    (parent : first.stageEight = last.stageEight)
    (flow : (generatedUnitaryFlow first).evolve = (generatedUnitaryFlow last).evolve) : first = last := by
  apply source_eq_of_generated_curvature first last parent
  rw [generatedMotherCurvature_zero_one, generatedMotherCurvature_zero_one, (flow_eq_iff_rate first last).mp flow]

def curvatureResidual (parent : StageEightProofFreeSource.Source) (curvature : SU7MotherLieMatrix) : SU7MotherLieMatrix :=
  curvature-generatedMotherCurvature (reconstruct parent curvature) 0 1

theorem curvature_realization_iff (parent : StageEightProofFreeSource.Source) (curvature : SU7MotherLieMatrix) :
    curvatureResidual parent curvature = 0 ↔
      ∃! source : SmoothUnifiedSource, source.stageEight = parent ∧ generatedMotherCurvature source 0 1 = curvature := by
  constructor
  · intro closed
    have generated : generatedMotherCurvature (reconstruct parent curvature) 0 1 = curvature :=
      (sub_eq_zero.mp closed).symm
    refine ⟨reconstruct parent curvature, ⟨rfl,generated⟩, ?_⟩
    intro source compatible
    exact source_eq_of_generated_curvature source (reconstruct parent curvature)
      compatible.1 (compatible.2.trans generated.symm)
  · rintro ⟨source, compatible, _⟩
    have reconstructed : reconstruct parent curvature = source := by
      rw [← compatible.1, ← compatible.2, reconstruct_generated]
    change curvature-generatedMotherCurvature (reconstruct parent curvature) 0 1 = 0
    rw [reconstructed, compatible.2, sub_self]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness
