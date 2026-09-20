import H0mework.Physics.MotherDeclarationsEvaluator.TreesPosition
import H0mework.Physics.MotherProgrammesFormationCauchy.Source
import H0mework.Physics.MotherLaws.PointwiseCompletion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherDurationExposure

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherFamilyOccurrence Stage9C.Revision RootedAccountedUnfolding

noncomputable section

abbrev dynamics := PhysicalCoverage.dynamics PhysicalCoverage.originalInitial
abbrev ledgerSource := (RawGeneratedRoot.root dynamics).toAuthoritativeRoot.toLedgerRoot.source
abbrev OccurrenceAt (current : PhysicalCoverage.Current) :=
  ledgerSource.source.toRootSource.actual.OccurrenceAt current

def occurrenceOf (current : PhysicalCoverage.Current) (duration : PhysicalCoverage.Duration) :
    OccurrenceAt current := (RawGeneratedRoot.eventPresentation dynamics current).forward duration

def durationOf {current : PhysicalCoverage.Current} (occurrence : OccurrenceAt current) :
    PhysicalCoverage.Duration := (RawGeneratedRoot.eventPresentation dynamics current).backward occurrence

theorem occurrence_recovered {current : PhysicalCoverage.Current} (occurrence : OccurrenceAt current) :
    occurrenceOf current (durationOf occurrence) = occurrence :=
  (RawGeneratedRoot.eventPresentation dynamics current).forward_backward occurrence

def durationRead (value : ℝ) : PhysicalCoverage.Duration :=
  if positive : 0 < value then ⟨value, positive⟩ else ⟨1, by norm_num⟩

theorem duration_recovered (duration : PhysicalCoverage.Duration) : durationRead duration.val = duration := by
  simp only [durationRead, dif_pos duration.property]

def nodeInput (node : ℕ) : MotherStreamLaws.Stream := fun _ => (node : ℝ)

def nodeDuration (law : MotherPointwiseLaws.Law) (node : ℕ) : PhysicalCoverage.Duration :=
  durationRead (MotherPointwiseLaws.eval law (nodeInput node) 0)

def nodeOccurrence (law : MotherPointwiseLaws.Law) (current : PhysicalCoverage.Current)
    (node : ℕ) : OccurrenceAt current := occurrenceOf current (nodeDuration law node)

/-- The root is the given actual occurrence; every other node is separately generated. -/
def exposure {current : PhysicalCoverage.Current} (root : OccurrenceAt current)
    (parent : MotherVisit) (law : MotherPointwiseLaws.Law) : RootedAccountedUnfolding (OccurrenceAt current) :=
  .occur root (((MotherEvaluatorTrees.shapeAt parent).map (nodeOccurrence law current)).branches)

theorem every_exposure {current : PhysicalCoverage.Current} (root : OccurrenceAt current)
    (target : RootedAccountedUnfolding (OccurrenceAt current)) (exactRoot : target.root = root) :
    ∃ code : ℕ, ∃ law : MotherPointwiseLaws.Law,
      exposure root (SpinPair.visit (10 + code)) law = target := by
  obtain ⟨values, recovered⟩ := MotherEvaluatorTrees.positions_recover target
  obtain ⟨code, formedShape⟩ := MotherEvaluatorTrees.every_shape (MotherEvaluatorTrees.positions target)
  obtain ⟨law, formed, _⟩ := MotherPointwiseLaws.every_law
    (fun input => fun _ => (durationOf (values (Nat.floor (input 0)))).val)
  have nodes : nodeOccurrence law current = values := by
    funext node
    dsimp only [nodeOccurrence, nodeDuration]
    rw [formed]
    simp only [nodeInput, Nat.floor_natCast, duration_recovered]
    exact occurrence_recovered (values node)
  refine ⟨code, law, ?_⟩
  unfold exposure
  rw [formedShape, nodes, recovered]
  cases target with
  | occur value branches =>
    change value = root at exactRoot
    cases exactRoot
    rfl

theorem node_consumed (law : MotherPointwiseLaws.Law) (current : PhysicalCoverage.Current) (node : ℕ) :
    ledgerSource.source.toRootSource.actual.compile (nodeOccurrence law current node) =
      .nativeWrite (nodeDuration law node) ∧
      type_of% (PhysicalCoverage.event_consumed PhysicalCoverage.originalInitial current (nodeDuration law node)) :=
  ⟨rfl, PhysicalCoverage.event_consumed PhysicalCoverage.originalInitial current (nodeDuration law node)⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherDurationExposure
