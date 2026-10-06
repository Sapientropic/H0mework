import H0mework.Physics.MotherDeclarationsEvaluator.TreesShape
import H0mework.Physics.MotherProgrammesFormation.Declarations.Conductor.Evaluator
import Mathlib.Data.Finsupp.Encodable

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHistoryFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open CofinalHistorySettlement RootedAccountedUnfolding
open NoIslandNoMagic.CanonicalRiemann.AllPlace.WeilQuadratic.Runtime.MuntzGraph.Conductor.History
open MotherFamilyOccurrence Stage9C.Revision

private def roleToBool : ConductorHistoryRole → Bool
  | .prefix => false
  | .increment => true

private def roleFromBool : Bool → ConductorHistoryRole
  | false => .prefix
  | true => .increment

@[instance_reducible] def roleCodec : Encodable ConductorHistoryRole :=
  Encodable.ofLeftInverse roleToBool roleFromBool (by intro role; cases role <;> rfl)

local instance instEncodableConductorHistoryRole_scratch : Encodable ConductorHistoryRole := roleCodec

abbrev Event := PresentedRelationEventAt ConductorHistoryGenerator

private def eventToSum : Event → ConductorHistoryGenerator ⊕ (ConductorHistoryGenerator →₀ ℤ)
  | .generator generator => .inl generator
  | .relation relation => .inr relation

private def eventFromSum : ConductorHistoryGenerator ⊕ (ConductorHistoryGenerator →₀ ℤ) → Event
  | .inl generator => .generator generator
  | .inr relation => .relation relation

@[instance_reducible] def eventCodec : Encodable Event :=
  Encodable.ofLeftInverse eventToSum eventFromSum (by intro event; cases event <;> rfl)

local instance instEncodableEvent : Encodable Event := eventCodec
local instance instEncodableRootedAccountedUnfoldingNat_scratch : Encodable (RootedAccountedUnfolding ℕ) := MotherEvaluatorTrees.shapeCodec

noncomputable section

def eventCode (event : Event) : ℕ := Encodable.encode event

def eventAtCode (code : ℕ) : Event :=
  (Encodable.decode code).getD (.generator (0, .prefix))

theorem event_recovered (event : Event) : eventAtCode (eventCode event) = event := by
  simp only [eventAtCode, eventCode, Encodable.encodek, Option.getD_some]

def treeCode (tree : RootedAccountedUnfolding Event) : ℕ :=
  Encodable.encode (tree.map eventCode)

def treeAtCode (code : ℕ) : RootedAccountedUnfolding Event :=
  ((Encodable.decode code).getD (.zero 0) : RootedAccountedUnfolding ℕ).map eventAtCode

theorem tree_recovered (tree : RootedAccountedUnfolding Event) :
    treeAtCode (treeCode tree) = tree := by
  simp only [treeAtCode, treeCode, Encodable.encodek, Option.getD_some, map_map]
  have inverse : eventAtCode ∘ eventCode = id := funext event_recovered
  rw [inverse, map_id]

def seedAt (parent : MotherVisit) : RootedAccountedUnfolding Event :=
  treeAtCode (StageEightDiscreteFormation.codeOf parent)

theorem every_seed (target : RootedAccountedUnfolding Event) :
    ∃ code : ℕ, seedAt (SpinPair.visit (10 + code)) = target := by
  refine ⟨treeCode target, ?_⟩
  rw [seedAt, StageEightDiscreteFormation.code_at, tree_recovered]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherHistoryFormation
