import H0mework.Physics.MotherProgrammesFormation.Declarations.PhysicalSource.Factory

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open RootedAccountedUnfolding MotherClosedRestrictions MotherEvaluatorTrees MotherDurationExposure

noncomputable section

abbrev ExposureFamily := {current : Current} → OccurrenceAt current →
  RootedAccountedUnfolding (OccurrenceAt current)
abbrev RootExact (roots : ExposureFamily) :=
  ∀ {current : Current} (occurrence : OccurrenceAt current), (roots occurrence).root = occurrence
abbrev SeedFamily := {current : Current} → OccurrenceAt current → RootedAccountedUnfolding Event
abbrev ContinuationFamily := {current : Current} → OccurrenceAt current →
  RootedAccountedUnfolding (Event → RootedAccountedUnfolding Event)
abbrev EvaluatorFamily := {current : Current} → OccurrenceAt current → RootedAccountedUnfolding (Generator → Carrier)

theorem every_fields (roots : ExposureFamily) (rootExact : RootExact roots) (seeds : SeedFamily)
    (continuations : ContinuationFamily) (evaluators : EvaluatorFamily) :
    ∃ law : MotherPhysicalLaws.Law,
      @rootExposureAt law = @roots ∧ @seedAt law = @seeds ∧
      @continuationAt law = @continuations ∧ @evaluatorAt law = @evaluators ∧
      ∀ input : Input, firstStream (MotherPhysicalLaws.eval law (inputAt input)) = sideSamples input.2 := by
  let rootValues (current : Current) (duration : Duration) : ℕ → OccurrenceAt current :=
    (positions_recover (roots (occurrenceOf current duration))).choose
  let continuationValues (current : Current) (duration : Duration) : ℕ → Event → RootedAccountedUnfolding Event :=
    (positions_recover (continuations (occurrenceOf current duration))).choose
  let evaluatorValues (current : Current) (duration : Duration) : ℕ → Generator → Carrier :=
    (positions_recover (evaluators (occurrenceOf current duration))).choose
  let output (input : Input) : MotherStreamLaws.Stream := match input.2.2 with
    | .inl node => fun _ => (durationOf (rootValues input.1 input.2.1 node)).val
    | .inr (.inl kind) => fun _ => ((if kind = 0 then
          MotherUnitSource.shapeCode (positions (roots (occurrenceOf input.1 input.2.1)))
        else if kind = 1 then MotherHistoryFormation.treeCode (seeds (occurrenceOf input.1 input.2.1))
        else if kind = 2 then MotherUnitSource.shapeCode (positions (continuations (occurrenceOf input.1 input.2.1)))
        else MotherUnitSource.shapeCode (positions (evaluators (occurrenceOf input.1 input.2.1)))) : ℝ)
    | .inr (.inr (.inl (node, event))) => fun _ =>
        (MotherHistoryFormation.treeCode (continuationValues input.1 input.2.1 node event) : ℝ)
    | .inr (.inr (.inr (node, generator, test, scale))) =>
        MotherEvaluatorTreeFunctions.complexSamples (evaluatorValues input.1 input.2.1 node generator test scale)
  let target (input : Input) := pairStream (sideSamples input.2) (output input)
  obtain ⟨law, formed, _⟩ := MotherPhysicalLaws.every_law (Function.extend inputAt target (fun _ => 0))
  have lawValues (input : Input) : MotherPhysicalLaws.eval law (inputAt input) = target input :=
    (formed _).trans (inputAt_injective.extend_apply _ _ input)
  have read (current : Current) (duration : Duration) (body : Body) :
      readValue law current duration body = output (current, duration, body) := by
    dsimp only [readValue]
    rw [lawValues]
    exact last_pair _ _
  have durationBack (current : Current) (duration : Duration) :
      durationOf (occurrenceOf current duration) = duration := rfl
  have rootsAt (current : Current) (duration : Duration) :
      rootExposureAt law (occurrenceOf current duration) = roots (occurrenceOf current duration) := by
    simp only [rootExposureAt, durationBack]
    have shape : shapeAt law current duration 0 = positions (roots (occurrenceOf current duration)) := by
      simp [shapeAt, read, output, MotherUnitSource.shape_recovered]
    have nodes : branchOccurrence law current duration = rootValues current duration := by
      funext node
      dsimp only [branchOccurrence]
      rw [read]
      simp only [output, duration_recovered]
      exact occurrence_recovered _
    rw [shape, nodes, (positions_recover (roots (occurrenceOf current duration))).choose_spec]
    have eta : .occur (roots (occurrenceOf current duration)).root
        (roots (occurrenceOf current duration)).branches = roots (occurrenceOf current duration) := by
      cases roots (occurrenceOf current duration)
      rfl
    exact (congrArg (fun value => RootedAccountedUnfolding.occur value
      (roots (occurrenceOf current duration)).branches) (rootExact (occurrenceOf current duration))).symm.trans eta
  have seedsAt (current : Current) (duration : Duration) :
      seedAt law (occurrenceOf current duration) = seeds (occurrenceOf current duration) := by
    simp only [seedAt, durationBack]
    rw [read]
    simp [output, MotherHistoryFormation.tree_recovered]
  have continuationsAt (current : Current) (duration : Duration) :
      continuationAt law (occurrenceOf current duration) = continuations (occurrenceOf current duration) := by
    simp only [continuationAt, durationBack]
    have shape : shapeAt law current duration 2 = positions (continuations (occurrenceOf current duration)) := by
      simp [shapeAt, read, output, MotherUnitSource.shape_recovered]
    have values : (fun node event => MotherHistoryFormation.treeAtCode
        (Nat.floor (readValue law current duration (.inr (.inr (.inl (node, event)))) 0))) =
        continuationValues current duration := by
      funext node event
      rw [read]
      simp [output, MotherHistoryFormation.tree_recovered]
    rw [shape, values]
    exact (positions_recover (continuations (occurrenceOf current duration))).choose_spec
  have evaluatorsAt (current : Current) (duration : Duration) :
      evaluatorAt law (occurrenceOf current duration) = evaluators (occurrenceOf current duration) := by
    simp only [evaluatorAt, durationBack]
    have shape : shapeAt law current duration 3 = positions (evaluators (occurrenceOf current duration)) := by
      simp [shapeAt, read, output, MotherUnitSource.shape_recovered]
    have values : (fun node generator test scale => MotherEvaluatorTreeFunctions.complexRead
        (readValue law current duration (.inr (.inr (.inr (node, generator, test, scale)))))) =
        evaluatorValues current duration := by
      funext node generator test scale
      rw [read]
      simp only [output, MotherEvaluatorTreeFunctions.complex_recovered]
    rw [shape, values]
    exact (positions_recover (evaluators (occurrenceOf current duration))).choose_spec
  refine ⟨law, ?_, ?_, ?_, ?_, ?_⟩
  · funext current occurrence
    simpa only [occurrence_recovered] using rootsAt current (durationOf occurrence)
  · funext current occurrence
    simpa only [occurrence_recovered] using seedsAt current (durationOf occurrence)
  · funext current occurrence
    simpa only [occurrence_recovered] using continuationsAt current (durationOf occurrence)
  · funext current occurrence
    simpa only [occurrence_recovered] using evaluatorsAt current (durationOf occurrence)
  · intro input
    rw [lawValues]
    exact first_pair _ _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource
