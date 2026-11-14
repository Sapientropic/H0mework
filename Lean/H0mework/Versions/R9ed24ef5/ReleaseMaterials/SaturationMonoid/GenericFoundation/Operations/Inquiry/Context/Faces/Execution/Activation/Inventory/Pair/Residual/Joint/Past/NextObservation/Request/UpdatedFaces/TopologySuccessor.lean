import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Successor
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Inventory.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.InverseRead

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces

open SourceOperationEffects SourceOperationScalarInventoryLift CofinalHistorySettlement CofinalAllPrimeTopology

variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar sort)))
variable (initial : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

local notation "Words" => Context.History.Words
  (PhysicalValue := PairValue PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
local notation "sourceAt" => Context.Faces.Cofinal.sourceMap (inventoryRuntime seed initial) (rawSource seed initial)
local notation "stepAt" => successor seed initial

/-- The actual cofinal action advances the same word through every topological face. -/
theorem actual_topology_successor (count : Nat) (word : Words) :
    @UniformContinuous (field seed initial count) (field seed initial (count+1))
      (topology seed initial count) (topology seed initial (count+1)) (stepAt count) ∧
    allStageSuccessor (stepAt count) (allStageMap (sourceAt count word)) =
      allStageMap (sourceAt (count+1) word) ∧
    allPrimeSuccessor (stepAt count) (allPrime seed initial count (sourceAt count word)) =
      allPrime seed initial (count+1) (sourceAt (count+1) word) ∧
    allPrimeCoimageSuccessor (stepAt count) ((AllPrimeKernel (L := field seed initial count)).mkQ
      (sourceAt count word)) =
      (AllPrimeKernel (L := field seed initial (count+1))).mkQ (sourceAt (count+1) word) ∧
    type_of% (actual_tick seed initial count) := by
  have source := Context.Faces.Cofinal.next_source (inventoryRuntime seed initial) (rawSource seed initial) count word
  exact ⟨allStage_source_successor_uniformContinuous (stepAt count),
    (allStage_successor_source (stepAt count) _).trans (congrArg (allStageMap (L := field seed initial (count+1))) source),
    (allPrime_successor_source (stepAt count) _).trans (congrArg (allPrime seed initial (count+1)) source),
    (allPrime_coimage_successor_source (stepAt count) _).trans
      (congrArg ((AllPrimeKernel (L := field seed initial (count+1))).mkQ) source),
    actual_tick seed initial count⟩

theorem actual_topology_successor_fibre (count : Nat) (left right : Words) :
    allStageSuccessor (stepAt count) (allStageMap (sourceAt count left)) =
      allStageSuccessor (stepAt count) (allStageMap (sourceAt count right)) ↔
        ∀ p : Nat.Primes, ∀ j : Nat, ∃ divided : field seed initial (count+1),
          (p.1 : ℤ)^(j+1) • divided = sourceAt (count+1) (left-right) := by
  have image : stepAt count (sourceAt count left-sourceAt count right) =
      sourceAt (count+1) (left-right) := by
    rw [← map_sub]
    exact Context.Faces.Cofinal.next_source (inventoryRuntime seed initial)
      (rawSource seed initial) count (left-right)
  rw [allStage_successor_fibre, image]

/-- The installed inverse programme supplies the word before the topological action reads it. -/
theorem actual_inverse_relation_topology (count : Nat) :
    type_of% (actual_topology_successor seed initial count (InverseRead.sourceWord seed initial count)) ∧
    type_of% (InverseRead.execution_original seed initial count) ∧
    type_of% (InverseRead.execution_whole seed initial count) ∧
    type_of% (InverseRead.execution_next seed initial count) :=
  ⟨actual_topology_successor seed initial count (InverseRead.sourceWord seed initial count),
    InverseRead.execution_original seed initial count,
    InverseRead.execution_whole seed initial count,
    InverseRead.execution_next seed initial count⟩

end SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
