import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornWholeStockRSource
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornWholeStockRConsumer
open Complex MeasureTheory Set
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CenteredGram.IntegralGraphJointAction
open scoped InnerProductSpace Topology
namespace F
export BornWholeStockRAction
 (born bornRaw retainedStock? retained_present bornStock born_environment code
  actionRoot actionVisit actionPoint reader result bornActed actual_whole_R)
end F
namespace C
export CompletedSourceRCalculation
 (Value Var sourceConfiguration settledSourceFrame sourceRegistered registeredMaterial
  actual_equation_registered registered_source_raw installed_raw_source
  code environment actual_source_value value actual_registered_next)
end C
namespace E
export CompletedPaEulerTateBoundary (currentSource next_source_even actual_value_source)
end E
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (nextBorn base runtime actual_next next presentation)
end S
namespace OF
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultLaw)
end I
end OF
namespace MathSource
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
 (frame residualMaterial residualRegistered residualTarget endpointState residual_first_receipt residual_frame_next)
end MathSource
namespace Clock
export SourceRegisteredClaimClock (suffixHistory source_suffix_factorizes)
end Clock
namespace G
export OriginalKFiniteOrderRelease.GenericSourceStepBAction (actual_forward_R_B firstNext secondNext)
end G
local notation "slot"=>CompletedSourceRCalculation.Slot.branches
local notation "R"=>burnolDirectRightResolventCLM
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "b"=>burnolAmbientMeanZeroFirstCorrection
local notation "d"=>burnolAmbientMeanZeroSecondCorrection

namespace Generic
variable {Sorts:Type} {U X:Sorts→Type} [∀s,AddCommGroup (U s)] {s:Sorts}
variable (frame:RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=U) (Var:=X) (sort:=s))
variable (cfg:SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=U) (PhysicalVar:=X) (sort:=s))
theorem born_expression : (S.nextBorn frame cfg).registered.input.expression=
 .add frame.registered.input.expression
  (.linear (-AddMonoidHom.id (U s)) frame.event.state.1) := by
 rfl

theorem eval_paid (env:Env U X) (expr:Expr U X s) :
 -(Expr.linear (-AddMonoidHom.id (U s)) expr).eval env=expr.eval env := by
 simp only [Expr.eval,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,neg_neg]
end Generic

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "oldFrame"=>C.settledSourceFrame observation nontrivial half depth ordinal
local notation "oldMaterial"=>C.registeredMaterial observation nontrivial half depth ordinal
local notation "stock"=>F.bornStock observation nontrivial half depth ordinal

theorem born_raw_expression : (F.bornRaw observation nontrivial half depth ordinal).expression=
 .add (C.sourceRegistered observation nontrivial half depth ordinal).input.expression
  (.linear (-AddMonoidHom.id (C.Value slot)) (oldFrame).event.state.1) :=
 Generic.born_expression oldFrame C.sourceConfiguration

theorem material_environment : (oldMaterial).environment=C.environment observation nontrivial half depth := by
 rfl

theorem material_raw : (oldMaterial).raw=C.code observation nontrivial half := by
 exact (C.registered_source_raw observation nontrivial half depth ordinal).trans
  (congrArg (fun raw:OF.Raw (Value:=C.Value) (Var:=C.Var) (sort:=slot)=>raw.expression)
   (C.installed_raw_source observation nontrivial half depth ordinal))

/-- The actual retained paid leg is recognized through its source Trace, before C.value is read. -/
theorem retained_payload : F.retainedStock? observation nontrivial half depth ordinal=
 some ((C.code observation nontrivial half).eval (C.environment observation nontrivial half depth)) := by
 unfold F.retainedStock?
 rw [born_raw_expression,C.actual_equation_registered]
 simp only [RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression]
 apply (congrArg some (Generic.eval_paid
  (F.bornRaw observation nontrivial half depth ordinal).environment (oldMaterial).state.1)).trans
 apply congrArg some
 exact (congrArg (fun env:Env C.Value C.Var=>(oldMaterial).state.1.eval env)
  ((F.born_environment observation nontrivial half depth ordinal).trans
   (material_environment observation nontrivial half depth ordinal).symm)).trans <|
  (oldMaterial).state.2.sound.symm.trans <|
   (congrArg (fun expr:Expr C.Value C.Var slot=>expr.eval (oldMaterial).environment)
    (material_raw observation nontrivial half depth ordinal)).trans <|
    congrArg (fun env:Env C.Value C.Var=>(C.code observation nontrivial half).eval env)
     (material_environment observation nontrivial half depth ordinal)

theorem born_stock_evaluation : stock=
 (C.code observation nontrivial half).eval (C.environment observation nontrivial half depth) :=
 Option.get_of_eq_some (F.retained_present observation nontrivial half depth ordinal)
  (retained_payload observation nontrivial half depth ordinal)

theorem born_stock_source : stock=C.value observation nontrivial half depth ordinal :=
 (born_stock_evaluation observation nontrivial half depth ordinal).trans
  (C.actual_source_value observation nontrivial half depth ordinal).symm

theorem stock_even : reflectL2 (stock.1.1)=stock.1.1 := by
 rw [born_stock_source,E.actual_value_source]
 exact E.next_source_even observation nontrivial half depth

/-- The calculation face is installed on this same born root and visit. -/
def calculationLaw := OF.I.resultLaw
 (F.actionRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
 (F.reader observation nontrivial half depth ordinal)
def installedRoot := (F.actionRoot observation nontrivial half depth ordinal).withProjectionCoface
 (calculationLaw observation nontrivial half depth ordinal)
def installedVisit : SourceNativeTemporalVisitAt
 (installedRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot :=
 F.actionVisit observation nontrivial half depth ordinal

def sourceFace : SourceNativeRootSemanticFaceAt (installedRoot observation nontrivial half depth ordinal)
 (installedVisit observation nontrivial half depth ordinal) where
 projection:=(SourceNativeProjectionLaw.InstallationAt.componentCoface
  (F.actionRoot observation nontrivial half depth ordinal).source.base
  (calculationLaw observation nontrivial half depth ordinal)).embed PUnit.unit
 active:=PUnit.unit
 classifier_eq:=rfl

theorem source_face_read : (sourceFace observation nontrivial half depth ordinal).rootRead=
 F.result observation nontrivial half depth ordinal := rfl

def installedRaw : OF.Raw (Value:=C.Value) (Var:=C.Var) (sort:=slot) :=
 (sourceFace observation nontrivial half depth ordinal).rootRead.1

def installedReader (_:(installedRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
 (installedVisit observation nontrivial half depth ordinal).current) :=
 installedRaw observation nontrivial half depth ordinal
abbrev sourceU7 := (S.base (F.born observation nontrivial half depth ordinal)).U7
abbrev sourceCalculus := (S.base (F.born observation nontrivial half depth ordinal)).calculus

def actionFrame := MathSource.frame
 (installedRoot observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev endpoint := MathSource.endpointState
 (installedRoot observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev registered := MathSource.residualRegistered
 (installedRoot observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
abbrev registeredMaterial := MathSource.residualMaterial
 (installedRoot observation nontrivial half depth ordinal) (installedVisit observation nontrivial half depth ordinal)
 (sourceU7 observation nontrivial half depth ordinal) (sourceCalculus observation nontrivial half depth ordinal)
 (installedReader observation nontrivial half depth ordinal)
 ((endpoint observation nontrivial half depth ordinal).root.emitted
  (endpoint observation nontrivial half depth ordinal).visit.current)

theorem actual_equation_registered : (registered observation nontrivial half depth ordinal).input.expression=
 RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression
  (registeredMaterial observation nontrivial half depth ordinal) := rfl

theorem registered_raw : (registeredMaterial observation nontrivial half depth ordinal).raw=
 F.code observation nontrivial half depth ordinal := rfl

/-- The direct consumer reads the newly registered whole paid state. -/
def registeredValue : C.Value slot := (registeredMaterial observation nontrivial half depth ordinal).state.1.eval
 (registeredMaterial observation nontrivial half depth ordinal).environment

theorem registered_whole_R : registeredValue observation nontrivial half depth ordinal=
 OriginalKFullSourceRAction.variableAction observation nontrivial half stock := by
 exact (registeredMaterial observation nontrivial half depth ordinal).state.2.sound.symm.trans
  (congrArg (fun expr:Expr C.Value C.Var slot=>expr.eval
   (registeredMaterial observation nontrivial half depth ordinal).environment)
   (registered_raw observation nontrivial half depth ordinal))

theorem registered_value_actual : registeredValue observation nontrivial half depth ordinal=
 F.bornActed observation nontrivial half depth ordinal :=
 (registered_whole_R observation nontrivial half depth ordinal).trans
  (F.actual_whole_R observation nontrivial half depth ordinal).symm

theorem registered_physical_R : (registeredValue observation nontrivial half depth ordinal).1.1=
 R c stock.1.1 := by
 rw [registered_whole_R]
 rfl

theorem actual_R_squared : (registeredValue observation nontrivial half depth ordinal).1.1=
 R c (R c (E.currentSource observation nontrivial half depth)) := by
 rw [registered_physical_R,born_stock_source,E.actual_value_source]

theorem actual_registered_B :
 b ((registeredValue observation nontrivial half depth ordinal).1.1)=G.secondNext (barC c) (fourierL2 stock.1.1) ∧
 d ((registeredValue observation nontrivial half depth ordinal).1.1)=G.firstNext (barC c) (fourierL2 stock.1.1) := by
 rw [registered_physical_R]
 exact G.actual_forward_R_B c stock.1.1 (stock_even observation nontrivial half depth ordinal)

theorem independent_four_term_consumer (shift:ℝ) :
 OriginalKCombCofinalTwoDirection.fourTerms observation nontrivial half shift
  (OriginalKFullSourceRAction.originalField stock)=
 burnolMultiplicativeDilation shift ((registeredValue observation nontrivial half depth ordinal).1.1) := by
 rw [registered_whole_R]
 exact OriginalKFullSourceRAction.complete_four_term_source observation nontrivial half shift stock

open private stop stop_next stop_from_suffix settlement from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.CompletedSourceRConsumer
abbrev settledActionFrame := stop (actionFrame observation nontrivial half depth ordinal)
abbrev sourceSuffix := Clock.suffixHistory (actionFrame observation nontrivial half depth ordinal)
abbrev suffixFactorizes := Clock.source_suffix_factorizes (actionFrame observation nontrivial half depth ordinal)
abbrev suffixStop := stop_from_suffix (actionFrame observation nontrivial half depth ordinal)
def registeredTick := (S.runtime (settledActionFrame observation nontrivial half depth ordinal) C.sourceConfiguration).tickAt 0

theorem actual_registered_next : (registeredTick observation nontrivial half depth ordinal).next.node=
 .active (S.presentation
  (S.nextBorn (settledActionFrame observation nontrivial half depth ordinal) C.sourceConfiguration)
  C.sourceConfiguration) := by
 have paid:=S.actual_next (settledActionFrame observation nontrivial half depth ordinal) C.sourceConfiguration 0
 change (registeredTick observation nontrivial half depth ordinal).next.node=
  .active (S.presentation (S.next (settledActionFrame observation nontrivial half depth ordinal) C.sourceConfiguration)
   C.sourceConfiguration) at paid
 rw [stop_next] at paid
 exact paid

def actual_born_whole_R_squared_consumer :=
 PProd.mk (C.actual_registered_next observation nontrivial half depth ordinal) <|
 PProd.mk (sourceFace observation nontrivial half depth ordinal).rootRead <|
 PProd.mk (born_stock_source observation nontrivial half depth ordinal) <|
 PProd.mk (registered_value_actual observation nontrivial half depth ordinal) <|
 PProd.mk (actual_R_squared observation nontrivial half depth ordinal) <|
 PProd.mk (actual_registered_B observation nontrivial half depth ordinal) <|
 PProd.mk (independent_four_term_consumer observation nontrivial half depth ordinal) <|
 PProd.mk (registered observation nontrivial half depth ordinal) <|
 PProd.mk (actual_equation_registered observation nontrivial half depth ordinal) <|
 PProd.mk (sourceSuffix observation nontrivial half depth ordinal) <|
 PProd.mk (suffixFactorizes observation nontrivial half depth ordinal) <|
 PProd.mk (suffixStop observation nontrivial half depth ordinal)
 (actual_registered_next observation nontrivial half depth ordinal)
end CountedPaInitial.BornWholeStockRConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
