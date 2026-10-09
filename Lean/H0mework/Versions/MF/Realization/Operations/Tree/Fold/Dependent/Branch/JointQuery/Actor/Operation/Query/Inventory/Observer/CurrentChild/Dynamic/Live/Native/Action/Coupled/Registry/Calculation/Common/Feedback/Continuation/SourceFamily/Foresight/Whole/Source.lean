import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Elimination
import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Effect
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Whole
namespace F
export Lower.SourceFamily.Foresight.Contextual (factory)
export Lower.SourceFamily.Foresight (Word Model sourceMap readPrefix action logical fullPrime wordDual wordDual_recovery source_prefix)
end F
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState)
end I
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
local instance groups (n : Nat) (t : S) : AddCommGroup (Lower.Value W n t) := Lower.groups W n t
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev currentState := I.nativeState n data.2 data.1
def actualNext := Lower.SourceFamily.step (F.factory (s:=s) binding) n data
abbrev nextState := I.nativeState (n+1) (actualNext binding n data).2 (actualNext binding n data).1
abbrev Word (t : S) := F.Word binding (currentState n data) t 0
abbrev NextWord (t : S) := F.Word binding (nextState binding n data) t 0
local instance currentModule (t : S) : Module ℤ (F.Model binding (currentState n data) t 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (currentState n data) t 0)).module
local instance nextModule (t : S) : Module ℤ (F.Model binding (nextState binding n data) t 0) :=
 (SourceGeneratedScalarCharacterExact.Carrier ℤ (Lower.SourceFamily.Foresight.completion binding (nextState binding n data) t 0)).module

def currentMap (t : S) := F.sourceMap binding (currentState n data) t 0
def nextMap (t : S) := F.sourceMap binding (nextState binding n data) t 0
def action (t : S) : Word binding n data t →ₗ[ℤ] NextWord binding n data t := liftMap
def dual (t : S) := F.wordDual binding (currentState n data) t 0
abbrev Full (t : S) := SourceGeneratedPerfectification.PerfectificationCarrier (dual binding n data t)
def fullMap (t : S) := SourceGeneratedPerfectification.canonicalMap (dual binding n data t)
def recover (t : S) : Full binding n data t →ₗ[ℤ] Word binding n data t := SourceGeneratedCompleteWordDual.coimageRecovery

theorem recovery_source (t : S) (word : Word binding n data t) :
 recover binding n data t (fullMap binding n data t word)=word := F.wordDual_recovery binding (currentState n data) t 0 word

def currentRestriction (t : S) := (currentMap binding n data t).comp (recover binding n data t)
def nextRestriction (t : S) := (nextMap binding n data t).comp ((action binding n data t).comp (recover binding n data t))
theorem current_square (t : S) (word : Word binding n data t) :
 currentRestriction binding n data t (fullMap binding n data t word)=currentMap binding n data t word :=
 congrArg (currentMap binding n data t) (recovery_source binding n data t word)
theorem next_square (t : S) (word : Word binding n data t) :
 nextRestriction binding n data t (fullMap binding n data t word)=nextMap binding n data t (action binding n data t word) :=
 congrArg (fun source => nextMap binding n data t (action binding n data t source)) (recovery_source binding n data t word)

def nextPrefix (t : S) (bound : Nat) :=
 (F.readPrefix binding (nextState binding n data) t 0 bound).comp (nextRestriction binding n data t)
theorem next_prefix (t : S) (bound : Nat) (word : Word binding n data t) :
 nextPrefix binding n data t bound (fullMap binding n data t word)=
 AlgebraicDependent.evaluator (Lower.SourceFamily.Foresight.action binding (nextState binding n data) t)
 (Lower.SourceFamily.Foresight.read binding (nextState binding n data) t) 0 bound (action binding n data t word) :=
 (congrArg (F.readPrefix binding (nextState binding n data) t 0 bound) (next_square binding n data t word)).trans
 (F.source_prefix binding (nextState binding n data) t 0 bound (action binding n data t word))

def nextMorphism (t : S) : Morphism (fullMap binding n data t) (nextMap binding n data t) where
 sourceMap:=action binding n data t
 targetMap:=nextRestriction binding n data t
 commutes:=by
  apply LinearMap.ext
  intro word
  exact (next_square binding n data t word).symm

theorem next_residual (t : S) (word : Word binding n data t) :
 inducedResidualMap (nextMorphism binding n data t) (canonicalResidual (fullMap binding n data t) word)=
 canonicalResidual (nextMap binding n data t) (action binding n data t word) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (nextMorphism binding n data t)) word

def nextLogic (t : S) (point : Full binding n data t) :=
 (SourceOperationLogic.fibreDecomposition (nextMap binding n data t)) (action binding n data t (recover binding n data t point))
theorem next_logic_source (t : S) (word : Word binding n data t) :
 (nextLogic binding n data t (fullMap binding n data t word)).2.val=action binding n data t word :=
 congrArg (action binding n data t) (recovery_source binding n data t word)

def coordinate (t : S) (name : X t) : Word binding n data t := Finsupp.single (Expr.var name) 1
def coordinateSource (t : S) (name : X t) := fullMap binding n data t (coordinate binding n data t name)
theorem next_coordinate (t : S) (name : X t) : type_of%
 (next_square binding n data t (coordinate binding n data t name)) := next_square _ _ _ _ _

end Lower.SourceFamily.Foresight.Whole
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
