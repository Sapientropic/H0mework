import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.CompletedPaEulerTateConsumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornWholeStockRAction
open Complex MeasureTheory Set
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace C
export CountedPaInitial.CompletedSourceRCalculation
 (Value Var Slot sourceConfiguration settledSourceFrame registeredMaterial value actual_source_value environment)
end C
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (nextBorn root visit actualOccurrence)
end S
namespace IS
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source (request_environment environment_source)
end IS
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_value)
end I
end OF
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "frame" => C.settledSourceFrame observation nontrivial half depth ordinal
abbrev born := S.nextBorn frame C.sourceConfiguration
local notation "slot" => CountedPaInitial.CompletedSourceRCalculation.Slot.branches
abbrev branches := C.Value slot

def bornRaw : OF.Raw (Value:=C.Value) (Var:=C.Var) (sort:=CountedPaInitial.CompletedSourceRCalculation.Slot.branches) :=
 ⟨(born observation nontrivial half depth ordinal).registered.input.environment,
  (born observation nontrivial half depth ordinal).registered.input.expression⟩

/-- The inner paid leg is retained by the actual born's two residual registrations. -/
def retainedStock? : Option (C.Value slot) :=
 match (bornRaw observation nontrivial half depth ordinal).expression with
 | .add (.add _ paid) _ => some (-paid.eval (bornRaw observation nontrivial half depth ordinal).environment)
 | _ => none

theorem retained_present : (retainedStock? observation nontrivial half depth ordinal).isSome=true := by
 rfl

def bornStock : C.Value slot :=
 (retainedStock? observation nontrivial half depth ordinal).get
  (retained_present observation nontrivial half depth ordinal)

theorem born_environment : (bornRaw observation nontrivial half depth ordinal).environment=
 C.environment observation nontrivial half depth := by
 exact (IS.request_environment (frame).old (frame).registered (frame).packetAt (frame).environment (frame).depth).trans (by rfl)

/-- One complete source R node acts before any physical projection. -/
def code : Expr C.Value C.Var CountedPaInitial.CompletedSourceRCalculation.Slot.branches :=
 .linear (s:=CountedPaInitial.CompletedSourceRCalculation.Slot.branches)
  (t:=CountedPaInitial.CompletedSourceRCalculation.Slot.branches) (OriginalKFullSourceRAction.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom
  (.const (bornStock observation nontrivial half depth ordinal))
abbrev actionRoot := S.root (born observation nontrivial half depth ordinal) C.sourceConfiguration
def actionVisit : SourceNativeTemporalVisitAt
 (actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot :=
 S.visit (born observation nontrivial half depth ordinal) C.sourceConfiguration
def actionPoint : (actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
 (actionVisit observation nontrivial half depth ordinal).current :=
 (actionRoot observation nontrivial half depth ordinal).emitted
  (actionVisit observation nontrivial half depth ordinal).current
def reader := fun {now} (_:(actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
 now) =>
 (⟨(bornRaw observation nontrivial half depth ordinal).environment,code observation nontrivial half depth ordinal⟩ :
  OF.Raw (Value:=C.Value) (Var:=C.Var) (sort:=slot))
def result : OF.I.ResultAt (Value:=C.Value) (Var:=C.Var) (sort:=slot)
 (actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
 (reader observation nontrivial half depth ordinal)
 (current:=(actionVisit observation nontrivial half depth ordinal).current)
 (actionPoint observation nontrivial half depth ordinal) :=
 OF.I.resultAt (Value:=C.Value) (Var:=C.Var) (sort:=slot)
 (actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
 (reader observation nontrivial half depth ordinal)
 (current:=(actionVisit observation nontrivial half depth ordinal).current)
 (actionPoint observation nontrivial half depth ordinal)
def bornActed : C.Value slot := (result observation nontrivial half depth ordinal).2.2.1

theorem actual_whole_R : bornActed observation nontrivial half depth ordinal=
 OriginalKFullSourceRAction.variableAction observation nontrivial half
  (bornStock observation nontrivial half depth ordinal) := by
 exact OF.I.source_value (actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
  (reader observation nontrivial half depth ordinal)
  (current:=(actionVisit observation nontrivial half depth ordinal).current)
  (actionPoint observation nontrivial half depth ordinal)
end CountedPaInitial.BornWholeStockRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
