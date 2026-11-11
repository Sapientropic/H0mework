import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornWholeStockRConsumer
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Inventory.ActualQuery.Consumer
import H0mework.Versions.Rdf421ff6.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRSourceMethodHistory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
namespace C
export CompletedSourceRCalculation (Value Var Slot sourceConfiguration)
end C
namespace F
export BornWholeStockRConsumer (settledActionFrame registeredValue actual_registered_next)
end F
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn runtime)
end S
namespace Q
export SourceGeneratedInquiryReceiptAction.Inventory.ActualQuery (programme)
end Q
namespace Configured
export SourceGeneratedInquiryReceiptAction.Configured (lowInitial lowProgramme)
end Configured
namespace Intake
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Intake.Lower
 (generatedAction compiles successor_valid)
end Intake
namespace IS
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source (request_environment)
end IS
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "slot" => CountedPaInitial.CompletedSourceRCalculation.Slot.branches
abbrev born := S.nextBorn (F.settledActionFrame observation nontrivial half depth ordinal) C.sourceConfiguration
local notation "b" => born observation nontrivial half depth ordinal
/-- The complete stock syntax is read from the actual birth's retained paid leg. -/
def retainedCode? : Option (Expr C.Value C.Var slot) :=
 match (b).registered.input.expression with
 | .add (.add _ paid) _ => some (.linear (-AddMonoidHom.id (C.Value slot)) paid)
 | _ => none

theorem retained_present : (retainedCode? observation nontrivial half depth ordinal).isSome = true := rfl

def retainedCode : Expr C.Value C.Var slot :=
 (retainedCode? observation nontrivial half depth ordinal).get
 (retained_present observation nontrivial half depth ordinal)

/-- The fixed full R acts on every whole branch of the source's paired carrier. -/
def action : PairValue (PairValue C.Value) slot →+ PairValue (PairValue C.Value) slot :=
 let r := (OriginalKFullSourceRAction.variableAction observation nontrivial half).toLinearMap.toAddMonoidHom
 (r.prodMap r).prodMap (r.prodMap r)
local notation "a" => action observation nontrivial half

def raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (PairValue C.Value)) (Var:=C.Var) (sort:=slot) :=
 ⟨pairEnvironment (pairEnvironment (b).registered.input.environment 0) 0,
  .linear a (liftExpr (liftExpr (retainedCode observation nontrivial half depth ordinal)))⟩

abbrev receiver := Configured.lowInitial b C.sourceConfiguration

def lowProgramme := { Configured.lowProgramme b C.sourceConfiguration with
 datum := fun current => { (Configured.lowProgramme b C.sourceConfiguration).datum current with
  calculationReader := some (fun {_current} _supplied => raw observation nontrivial half depth ordinal) } }

def methodProgramme := Q.programme (lowProgramme observation nontrivial half depth ordinal)
local notation "pR" => methodProgramme observation nontrivial half depth ordinal
abbrev admitted := Intake.generatedAction b C.sourceConfiguration pR

theorem reader_actual_source :
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.query
  (receiver observation nontrivial half depth ordinal) pR).raw =
 raw observation nontrivial half depth ordinal := rfl

theorem compiled : type_of% (Intake.compiles b C.sourceConfiguration pR) :=
 Intake.compiles b C.sourceConfiguration pR

theorem actualSuccessor : type_of% (Intake.successor_valid b C.sourceConfiguration pR) :=
 Intake.successor_valid b C.sourceConfiguration pR

def first_typed_splice :=
 PProd.mk (reader_actual_source observation nontrivial half depth ordinal) <|
 PProd.mk (compiled observation nontrivial half depth ordinal)
 (actualSuccessor observation nontrivial half depth ordinal)
end CountedPaInitial.BornRSourceMethodHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
