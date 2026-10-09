import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Equation
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
namespace Lower.SourceFamily.Foresight.Whole
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] groups
variable (binding : ∀ t,X t → Expr W X t) (n : Nat)
variable (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)

def physicalCochain (t : S) := SourceOperationScalarCochain.cochain (R:=ℤ) (s:=t)
 (Lower.SourceFamily.Foresight.Update.decoder binding n data.2 data.1
  (Lower.SourceFamily.scalar (F.factory (s:=s) binding) n data)
  (Lower.SourceFamily.pair (F.factory (s:=s) binding) n data))
 (Lower.SourceFamily.Foresight.Update.increment binding n data.2 data.1
  (Lower.SourceFamily.scalar (F.factory (s:=s) binding) n data)
  (Lower.SourceFamily.pair (F.factory (s:=s) binding) n data))
theorem cochain_zero (t : S) : type_of% ((physicalCochain binding n data t).d_comp_d 0 1 2) :=
 (physicalCochain binding n data t).d_comp_d 0 1 2

def primeRead (t : S) (point : Full binding n data t) :=
 F.fullPrime binding (nextState binding n data) t 0 (nextRestriction binding n data t point)
abbrev AlgebraFace (t : S) := Full binding n data t ×
 F.Model binding (currentState n data) t 0 × F.Model binding (nextState binding n data) t 0
abbrev CombinatorialFace (t : S) := Full binding n data t × Word binding n data t × NextWord binding n data t
abbrev TopologicalFace (t : S) := Σ point : Full binding n data t, type_of% (primeRead binding n data t point)
abbrev LogicalFace (t : S) := Σ point : Full binding n data t, type_of% (nextLogic binding n data t point)
abbrev RelationFace (t : S) := Full binding n data t × type_of% (nextMorphism binding n data t)
abbrev CochainFace (t : S) := Full binding n data t × type_of% (physicalCochain binding n data t)
def faceInput (t : S) (point : Full binding n data t) := ({
 occurrence:=RootedAccountedUnfolding.zero point
 algebraAt:=fun source => (source,currentRestriction binding n data t source,nextRestriction binding n data t source)
 combinatorialAt:=fun source => (source,recover binding n data t source,action binding n data t (recover binding n data t source))
 topologicalAt:=fun source => ⟨source,primeRead binding n data t source⟩
 logicalAt:=fun source => ⟨source,nextLogic binding n data t source⟩
 relationAt:=fun source => (source,nextMorphism binding n data t)
 cochainAt:=fun source => (source,physicalCochain binding n data t)
 dualEvaluationAt:=fun _ => dual binding n data t
 faithfulAt:=fun _ => LinearMap.id } : UnifiedFourFace.Input (Full binding n data t)
 (AlgebraFace binding n data t) (CombinatorialFace binding n data t) (TopologicalFace binding n data t)
 (LogicalFace binding n data t) (RelationFace binding n data t) (CochainFace binding n data t)
 (Word binding n data t) (Word binding n data t))
def fourFaces (t : S) (point : Full binding n data t) := UnifiedFourFace.generate (faceInput binding n data t point)
theorem dual_readback (t : S) (point : Full binding n data t) :
 type_of% (UnifiedFourFace.generated_dual_readback (faceInput binding n data t point)) := UnifiedFourFace.generated_dual_readback _
def actual_raw_faces := fourFaces binding n data s (rawSource binding n data)
theorem actual_raw_next (bound : Nat) :
 type_of% (next_square binding n data s (rawWord binding n data)) ∧
 type_of% (actual_raw_prefix binding n data bound) ∧ type_of% (actual_raw_residual binding n data) ∧
 type_of% (dual_readback binding n data s (rawSource binding n data)) ∧ type_of% (actual_whole_root binding n data) :=
 ⟨next_square _ _ _ _ _,actual_raw_prefix _ _ _ _,actual_raw_residual _ _ _,dual_readback _ _ _ _ _,actual_whole_root _ _ _⟩

end Lower.SourceFamily.Foresight.Whole
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
