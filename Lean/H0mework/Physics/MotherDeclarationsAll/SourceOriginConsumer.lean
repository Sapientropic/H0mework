import H0mework.Physics.MotherDeclarationsAll.SourceOriginAuthority

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open StageNineEnrichedProofFreeSource StageNineHolonomicField ProofFreeRicherAnholonomicSource
open MotherClosedRestrictions
open Stage9C.Reduction

noncomputable section

def materialOf (source : SmoothUnifiedSource)
    (state : GeneralSourceEvolution.State source) (center : BasePoint) : Material :=
  JointSourceLaws.encode ⟨source, state, center⟩

theorem materialOf_input (source : SmoothUnifiedSource)
    (state : GeneralSourceEvolution.State source) (center : BasePoint) :
    input (materialOf source state center) = ⟨source, state, center⟩ := by
  exact JointSourceLaws.recover_encode ⟨source, state, center⟩

theorem all_source_writer_consumed :
    ∃ law : Law, ∀ (source : SmoothUnifiedSource)
      (state : GeneralSourceEvolution.State source) (center : BasePoint),
      let input0 : JointSourceLaws.Input := ⟨source, state, center⟩
      let after : JointSourceLaws.Input :=
        ⟨source, p286CartanStateNext center state, center⟩
      let value := MotherPointwiseLaws.eval law
        (MotherStreamFormation.read (JointSourceLaws.encode input0))
      value = pairStream (JointSourceLaws.samples input0) (JointSourceLaws.samples after) ∧
      JointSourceLaws.recoverSamples (firstStream value) = input0 ∧
      output law source state center = after ∧
      JointSourceLaws.readSource (firstStream (firstStream value)) = source ∧
      (JointSourceLaws.recoverSamples (lastStream value)).2.1.current =
        p286CartanNext source state.current state.smooth state.nondegenerate center ∧
      actualRelativeAction
          (JointSourceLaws.readSource (firstStream (firstStream value)))
          (JointSourceLaws.recoverSamples (firstStream value)).2.1.current
          (JointSourceLaws.recoverSamples (lastStream value)).2.1.current =
        actualRelativeAction source state.current
          (p286CartanStateNext center state).current := by
  obtain ⟨law, formed, _⟩ := JointSourceLaws.all_sources_writer
  refine ⟨law, ?_⟩
  intro source state center
  dsimp only
  rcases formed source state center with
    ⟨valueEq, beforeEq, afterEq, sourceEq, targetEq, actionEq⟩
  refine ⟨valueEq, beforeEq, ?_, sourceEq, ?_, ?_⟩
  · simpa only [output] using afterEq
  · exact targetEq
  · simpa only [sourceEq, beforeEq, afterEq] using actionEq

theorem all_source_native_compiled :
    ∃ law : Law, ∀ (material : Material)
      {current : GeneralSourceEvolution.State (input material).1}
      (occurrence : (sourceAt law material).toRootSource.actual.OccurrenceAt current),
      (sourceAt law material).toRootSource.actual.compile occurrence =
        .nativeWrite occurrence.2.center ∧
      ((sourceAt law material).toRootSource.actual.compile occurrence).nextCurrent? =
        some (p286CartanStateNext occurrence.2.center current) := by
  obtain ⟨law, targets⟩ := all_native_targets
  refine ⟨law, ?_⟩
  intro material current occurrence
  refine ⟨rfl, ?_⟩
  change some (next law (input material).1 current occurrence.2.center) = _
  rw [show next law (input material).1 current occurrence.2.center =
      p286CartanStateNext occurrence.2.center current by
    exact targets (input material).1 current occurrence.2.center]

theorem all_source_target_is_writer :
    ∃ law : Law, ∀ (material : Material)
      {current : GeneralSourceEvolution.State (input material).1}
      (occurrence : (sourceAt law material).toRootSource.actual.OccurrenceAt current),
      target law material occurrence =
        p286CartanStateNext occurrence.2.center current := by
  obtain ⟨law, targets⟩ := all_native_targets
  refine ⟨law, ?_⟩
  intro material current occurrence
  change next law (input material).1 current occurrence.2.center = _
  exact targets (input material).1 current occurrence.2.center

theorem all_source_evolution_is_native
    (law : Law) (material : Material)
    {current : GeneralSourceEvolution.State (input material).1}
    (occurrence : (sourceAt law material).toRootSource.actual.OccurrenceAt current) :
    ∃ successor : SourceNativeLedgerGeneratedSuccessorAt
        occurrence (evolution law material occurrence),
      SourceNativeLedgerGeneratedSuccessorAt.targetCurrent successor =
        target law material occurrence := by
  let successor := (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (evolution law material occurrence)).get (by rfl)
  exact ⟨successor, rfl⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAllSourceOrigin
