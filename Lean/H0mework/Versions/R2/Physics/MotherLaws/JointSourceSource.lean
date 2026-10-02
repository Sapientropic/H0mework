import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.WholeConsumer
import H0mework.Versions.R2.Physics.MotherLaws.CurrentConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointSourceLaws

open StageNineEnrichedProofFreeSource Stage9C.Revision
open MotherCoordinateCompletion MotherStreamLaws

noncomputable section

def sourceCode (source : SmoothUnifiedSource) : ℕ :=
  (PotentialSourceFormation.every_source_generated source 0).choose

def sourcePoints (source : SmoothUnifiedSource) : PotentialSourceFormation.Points :=
  (PotentialSourceFormation.every_source_generated source 0).choose_spec.choose

def sourceOperand (source : SmoothUnifiedSource) : WholePointFormation.Carrier :=
  WholePointFormation.pointEquiv.symm (sourcePoints source)

theorem source_generated (source : SmoothUnifiedSource) :
    WholePointFormation.source (SpinPair.visit (10 + sourceCode source)) (sourceOperand source) = source := by
  unfold WholePointFormation.source sourceOperand
  change PotentialSourceFormation.sourceOf (SpinPair.visit (10 + sourceCode source))
    (WholePointFormation.pointEquiv (WholePointFormation.pointEquiv.symm (sourcePoints source))) = source
  rw [WholePointFormation.pointEquiv.apply_symm_apply]
  exact (PotentialSourceFormation.every_source_generated source 0).choose_spec.choose_spec.1

/-- Code and all 260 original point coordinates retain the source's own formation witness. -/
def sourceSamples (source : SmoothUnifiedSource) : Stream
  | 0 => sourceCode source
  | index + 1 => if bound : index < 65 * 4 then
      coordinates (65 * 4) (sourceOperand source) ⟨index, bound⟩ else 0

def readSource (data : Stream) : SmoothUnifiedSource :=
  WholePointFormation.source (SpinPair.visit (10 + Nat.floor (data 0)))
    ((realEquiv (65 * 4)).symm (fun index => data (index.val + 1)))

theorem source_recovered (source : SmoothUnifiedSource) : readSource (sourceSamples source) = source := by
  unfold readSource
  have values : (fun index : Fin (65 * 4) => sourceSamples source (index.val + 1)) =
      coordinates (65 * 4) (sourceOperand source) := by
    funext index
    simp only [sourceSamples, index.isLt, ↓reduceDIte]
  rw [values]
  change WholePointFormation.source
    (SpinPair.visit (10 + Nat.floor (sourceCode source : ℝ)))
    ((realEquiv (65 * 4)).symm ((realEquiv (65 * 4)) (sourceOperand source))) = source
  rw [Nat.floor_natCast, (realEquiv (65 * 4)).symm_apply_apply]
  exact source_generated source

theorem sourceSamples_injective : Function.Injective sourceSamples := by
  intro first second same
  exact (source_recovered first).symm.trans ((congrArg readSource same).trans (source_recovered second))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.JointSourceLaws
