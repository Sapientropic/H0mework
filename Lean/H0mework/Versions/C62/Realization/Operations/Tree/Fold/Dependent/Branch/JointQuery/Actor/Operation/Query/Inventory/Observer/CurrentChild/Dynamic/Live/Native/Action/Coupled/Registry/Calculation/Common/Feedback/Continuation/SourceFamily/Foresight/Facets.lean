import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Operator
import H0mework.Realization.Logic.SourceScope
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Kernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] sourceGroups
variable (binding : ∀ t,X t → Expr W X t) (state : L.State (W:=W) (X:=X) (s:=s))
section Logic
local instance modelModule (t : S) (k : Nat) : Module ℤ (Model binding state t k) :=
 (C.Carrier ℤ (completion binding state t k)).module
def logical (t : S) (k : Nat) := SourceOperationLogic.fibreDecomposition (sourceMap binding state t k)
theorem complete_word (t : S) (k : Nat) (word : Word binding state t k) :
 (logical binding state t k).symm ⟨SourceOperationLogic.q (sourceMap binding state t k) word,
 SourceOperationLogic.sourceWitness (sourceMap binding state t k) word⟩=word := rfl
end Logic
section Topology
local instance topologyModule (t : S) (k : Nat) : Module ℤ (Model binding state t k) := AddCommGroup.toIntModule _
def fullPrime (t : S) (k : Nat) := CofinalAllPrimeTopology.allPrimeMap (L:=Model binding state t k)
theorem fullPrime_kernel (t : S) (k : Nat) (point : Model binding state t k) :
 point ∈ LinearMap.ker (fullPrime binding state t k) ↔
 ∀ prime : Nat.Primes,∀ bound : Nat,∃ divided : Model binding state t k,
 (prime.1 : ℤ)^(bound+1) • divided=point := CofinalAllPrimeTopology.allPrimeKernel_iff point
end Topology

def wordDual (t : S) (k : Nat) : Word binding state t k →ₗ[ℤ] Module.Dual ℤ (Word binding state t k) := SourceGeneratedCompleteWordDual.pairing
theorem wordDual_recovery (t : S) (k : Nat) (word : Word binding state t k) :
 SourceGeneratedCompleteWordDual.coimageRecovery (SourceGeneratedPerfectification.canonicalMap (wordDual binding state t k) word)=word :=
 SourceGeneratedCompleteWordDual.recovery_source word
end Lower.SourceFamily.Foresight
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
