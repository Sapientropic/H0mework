import H0mework.Physics.MotherProgrammesFormation.Declarations.History.Source
import H0mework.Physics.MotherDeclarationsEvaluator.TreesPosition
import H0mework.Physics.MotherLaws.PointwiseRestriction

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHistoryFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherClosedRestrictions MotherStreamLaws MotherFamilyOccurrence Stage9C.Revision

noncomputable section

abbrev Input := ℕ × Event

def inputSamples (input : Input) : Stream :=
  pairStream (fun _ => (input.1 : ℝ)) (fun _ => (eventCode input.2 : ℝ))

def inputRead (raw : Stream) : Input :=
  (Nat.floor (firstStream raw 0), eventAtCode (Nat.floor (lastStream raw 0)))

theorem input_recovered (input : Input) : inputRead (inputSamples input) = input := by
  simp only [inputRead, inputSamples, first_pair, last_pair, Nat.floor_natCast, event_recovered]

theorem inputSamples_injective : Function.Injective inputSamples :=
  Function.LeftInverse.injective input_recovered

def evaluated (law : MotherPointwiseLaws.Law) (input : Input) : Stream :=
  MotherPointwiseLaws.eval law (inputSamples input)

def evaluate (law : MotherPointwiseLaws.Law) (node : ℕ) (event : Event) :
    RootedAccountedUnfolding Event :=
  treeAtCode (Nat.floor (lastStream (evaluated law (node, event)) 0))

theorem every_family (target : ℕ → Event → RootedAccountedUnfolding Event) :
    ∃ law : MotherPointwiseLaws.Law, evaluate law = target ∧
      ∀ input : Input, firstStream (evaluated law input) = inputSamples input := by
  obtain ⟨law, formed⟩ := MotherPointwiseLaws.every_restriction inputSamples inputSamples_injective
    (fun input => pairStream (inputSamples input)
      (fun _ => (treeCode (target input.1 input.2) : ℝ)))
  refine ⟨law, ?_, ?_⟩
  · funext node event
    dsimp only [evaluate, evaluated]
    rw [formed, last_pair, Nat.floor_natCast, tree_recovered]
  · intro input
    dsimp only [evaluated]
    rw [formed, first_pair]

def continuationAt (parent : MotherVisit) (law : MotherPointwiseLaws.Law) :
    RootedAccountedUnfolding (Event → RootedAccountedUnfolding Event) :=
  (MotherEvaluatorTrees.shapeAt parent).map (evaluate law)

theorem every_continuation
    (target : RootedAccountedUnfolding (Event → RootedAccountedUnfolding Event)) :
    ∃ code : ℕ, ∃ law : MotherPointwiseLaws.Law,
      continuationAt (SpinPair.visit (10 + code)) law = target ∧
        ∀ input : Input, firstStream (evaluated law input) = inputSamples input := by
  obtain ⟨values, recovered⟩ := MotherEvaluatorTrees.positions_recover target
  obtain ⟨code, formedShape⟩ := MotherEvaluatorTrees.every_shape (MotherEvaluatorTrees.positions target)
  obtain ⟨law, formedValues, keyed⟩ := every_family values
  refine ⟨code, law, ?_, keyed⟩
  unfold continuationAt
  rw [formedShape, formedValues]
  exact recovered

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHistoryFormation
