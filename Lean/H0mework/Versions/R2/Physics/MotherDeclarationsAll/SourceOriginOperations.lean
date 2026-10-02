import H0mework.Versions.R2.Physics.MotherLaws.JointSourceConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open StageNineEnrichedProofFreeSource StageNineHolonomicField ProofFreeRicherAnholonomicSource
open MotherClosedRestrictions Stage9C.Reduction

noncomputable section

abbrev Law := MotherPointwiseLaws.Law
abbrev Material := MotherStreamFormation.Carrier

def input (material : Material) : JointSourceLaws.Input := JointSourceLaws.recover material

def output (law : Law) (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source)
    (center : BasePoint) : JointSourceLaws.Input :=
  JointSourceLaws.recoverSamples (lastStream (MotherPointwiseLaws.eval law
    (MotherStreamFormation.read (JointSourceLaws.encode ⟨source, state, center⟩))))

/-- The source fibre is checked internally after actual mother-law evaluation. -/
def next (law : Law) (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source)
    (center : BasePoint) : GeneralSourceEvolution.State source := by
  classical
  let after := output law source state center
  exact if same : after.1 = source then same ▸ after.2.1 else state

def vocabulary (law : Law) (source : SmoothUnifiedSource) : ConstructiveRoot.Vocabulary where
  Current := GeneralSourceEvolution.State source
  Anchor := SmoothUnifiedSource
  Incidence := GeneralSourceEvolution.State source
  Lineage := SmoothUnifiedSource
  anchorAt := fun _ => source
  incidenceAt := id
  lineageAt := fun _ => source
  NativeWriteAt := fun _ => BasePoint
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := fun {state} center => next law source state center
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

theorem next_of_output (law : Law) (source : SmoothUnifiedSource) (state : GeneralSourceEvolution.State source)
    (center : BasePoint) (after : GeneralSourceEvolution.State source)
    (generated : output law source state center = ⟨source, after, center⟩) :
    next law source state center = after := by
  classical
  unfold next
  rw [generated]
  exact dif_pos rfl

theorem all_native_targets : ∃ law : Law, ∀ (source : SmoothUnifiedSource)
    (state : GeneralSourceEvolution.State source) (center : BasePoint),
    (vocabulary law source).nativeTarget (current := state) center = p286CartanStateNext center state := by
  obtain ⟨law, formed, _⟩ := JointSourceLaws.all_sources_writer
  refine ⟨law, fun source state center => ?_⟩
  exact next_of_output law source state center (p286CartanStateNext center state)
    (formed source state center).2.2.1

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin
