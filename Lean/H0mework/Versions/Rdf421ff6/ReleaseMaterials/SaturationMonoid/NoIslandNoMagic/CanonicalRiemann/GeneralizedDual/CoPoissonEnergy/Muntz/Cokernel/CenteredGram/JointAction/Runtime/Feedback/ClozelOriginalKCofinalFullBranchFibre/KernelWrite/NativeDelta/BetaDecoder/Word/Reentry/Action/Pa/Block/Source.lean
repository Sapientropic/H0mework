import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Programme

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
 (base baseRoot root visit answeredState actualOccurrence queryRoot resultRoot consumerRoot
  queryLaw resultLaw consumerLaw compilationLaw target_root)
end S
namespace M
export SourceGeneratedInquiryReceiptAction.Configured.Material
 (programme prefixInstallation initial actual_receipt_next actual_receipt_compiles)
end M

local instance blockBaseGroups (initial : Nat) : ∀ target,AddCommGroup (BaseValue initial target) :=
 DR.L.groups (PairValue C.Value) initial
local instance blockOriginGroups (initial : Nat) : ∀ target,AddCommGroup (DR.L.Value (BaseValue initial) 2 target) :=
 DR.L.groups (BaseValue initial) 2
local instance blockRuntimeGroups (initial : Nat) : ∀ target,AddCommGroup
 (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 target) :=
 DR.L.groups (DR.L.Value (BaseValue initial) 2) 0

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))
variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))

def parentProgramme : A.Programme (PhysicalValue := CodeValue initial) (PhysicalVar := C.Var) (sort := ()) :=
 M.programme sourceFrame (Pa.programme observation nontrivial half initial frame base before oldEnvironment admissions)
  (Pa.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)

def completed : Reentry.A.M.Frame (Value := CodeValue initial) (Var := C.Var) (sort := ()) :=
 Pa.selected observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

def parentBorn : Reentry.A.M.Frame (Value := CodeValue initial) (Var := C.Var) (sort := ()) :=
 Pa.nativeBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

/-- The completed scope is the literal answered state retained by this birth. -/
def completedFace : SourceNativeRootSemanticFaceAt
 (parentBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).old.root
 (parentBorn observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).old.visit where
 projection := (M.prefixInstallation sourceFrame
  (Pa.programme observation nontrivial half initial frame base before oldEnvironment admissions)
  (Pa.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
  (completed observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl

theorem completed_paid_state : HEq
 (completedFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead.currentMaterial.paid.state
 (completed observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state := HEq.rfl

theorem completed_paid_trace : HEq
 (completedFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead.currentMaterial.paid.state.2
 (completed observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).event.state.2 := HEq.rfl

theorem completed_next : type_of% (M.actual_receipt_next sourceFrame
 (Pa.programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (Pa.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) :=
 M.actual_receipt_next _ _ _

theorem completed_compiles : type_of% (M.actual_receipt_compiles sourceFrame
 (Pa.programme observation nontrivial half initial frame base before oldEnvironment admissions)
 (Pa.lowBase observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)) :=
 M.actual_receipt_compiles _ _ _

def parentSplit := Pa.nextSplitAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame

abbrev BlockValue (initial : Nat) := PairValue (CodeValue initial)

def paAt (value : CodeValue initial ()) : Expr (BlockValue initial) C.Var () :=
 liftExpr (.linear (s:=()) (t:=()) (P.sourcePaLift initial 2 0) (.const value))

def nonPaAt (value : CodeValue initial ()) : Expr (BlockValue initial) C.Var () :=
 liftExpr (.linear (s:=()) (t:=()) (P.sourceNonPaLift initial 2 0) (.const value))

/-- The two parent actions keep their original order; each pays both projections. -/
def codeAt (pa nonPa : CodeValue initial ()) : Expr (BlockValue initial) C.Var () :=
 .add (.add (paAt initial pa) (nonPaAt initial pa))
  (.add (paAt initial nonPa) (nonPaAt initial nonPa))

theorem pa_at_read (value : CodeValue initial ()) (environment : Env (BlockValue initial) C.Var) :
 (paAt initial value).eval environment = (P.sourcePaLift initial 2 0 value,0) := by
 simp only [paAt,liftExpr,Expr.eval,pairLinear,AddMonoidHom.coe_prodMap,Prod.map_apply,map_zero]
 rfl

theorem nonPa_at_read (value : CodeValue initial ()) (environment : Env (BlockValue initial) C.Var) :
 (nonPaAt initial value).eval environment = (P.sourceNonPaLift initial 2 0 value,0) := by
 simp only [nonPaAt,liftExpr,Expr.eval,pairLinear,AddMonoidHom.coe_prodMap,Prod.map_apply,map_zero]
 rfl

theorem code_at_read (pa nonPa : CodeValue initial ()) (environment : Env (BlockValue initial) C.Var) :
 (codeAt initial pa nonPa).eval environment = (pa+nonPa,0) := by
 change ((paAt initial pa).eval environment+(nonPaAt initial pa).eval environment)+
  ((paAt initial nonPa).eval environment+(nonPaAt initial nonPa).eval environment) = _
 rw [pa_at_read,nonPa_at_read,pa_at_read,nonPa_at_read]
 change (P.sourcePaLift initial 2 0 pa+P.sourceNonPaLift initial 2 0 pa+
  (P.sourcePaLift initial 2 0 nonPa+P.sourceNonPaLift initial 2 0 nonPa),0+0+(0+0)) = _
 rw [P.source_lift_split_sum,P.source_lift_split_sum]
 simp only [add_zero]

variable (pa nonPa : CodeValue initial ()) (environment : Env (BlockValue initial) C.Var)
variable (total : BlockValue initial ())
variable (actual : Trace environment (codeAt initial pa nonPa) (.const total))

/-- All four receipts retain their positions in this actual paid history. -/
structure FourAt where
 whole : Trace.AddSplit actual
 pa : Trace.AddSplit whole.leftTrace
 nonPa : Trace.AddSplit whole.rightTrace

def fourAt : FourAt initial pa nonPa environment total actual :=
 let whole := actual.splitAdd
 ⟨whole,whole.leftTrace.splitAdd,whole.rightTrace.splitAdd⟩

namespace FourAt
variable (result : FourAt initial pa nonPa environment total actual)
def pp : BlockValue initial () := result.pa.leftValue
def np : BlockValue initial () := result.pa.rightValue
def pn : BlockValue initial () := result.nonPa.leftValue
def nn : BlockValue initial () := result.nonPa.rightValue

theorem pp_action : result.pp = (P.sourcePaLift initial 2 0 pa,0) :=
 (completed_trace_value environment result.pa.leftTrace).trans (pa_at_read initial pa environment)
theorem np_action : result.np = (P.sourceNonPaLift initial 2 0 pa,0) :=
 (completed_trace_value environment result.pa.rightTrace).trans (nonPa_at_read initial pa environment)
theorem pn_action : result.pn = (P.sourcePaLift initial 2 0 nonPa,0) :=
 (completed_trace_value environment result.nonPa.leftTrace).trans (pa_at_read initial nonPa environment)
theorem nn_action : result.nn = (P.sourceNonPaLift initial 2 0 nonPa,0) :=
 (completed_trace_value environment result.nonPa.rightTrace).trans (nonPa_at_read initial nonPa environment)

theorem sum : total = (result.pp+result.np)+(result.pn+result.nn) :=
 result.whole.total_eq.trans (congrArg₂ (· + ·) result.pa.total_eq result.nonPa.total_eq)

include actual in
theorem source_sum : total=(pa+nonPa,0) :=
 (completed_trace_value environment actual).trans (code_at_read initial pa nonPa environment)

theorem exact_cost : actual.length=7 := actual.length_to_const.trans rfl

theorem pp_cost : result.pa.leftTrace.length=1 := result.pa.leftTrace.length_to_const.trans rfl
theorem np_cost : result.pa.rightTrace.length=1 := result.pa.rightTrace.length_to_const.trans rfl
theorem pn_cost : result.nonPa.leftTrace.length=1 := result.nonPa.leftTrace.length_to_const.trans rfl
theorem nn_cost : result.nonPa.rightTrace.length=1 := result.nonPa.rightTrace.length_to_const.trans rfl
end FourAt

variable (receiver : Reentry.A.M.Frame (Value := CodeValue initial) (Var := C.Var) (sort := ()))
variable {current : J.Current receiver.registered}
variable (supplied : I.Occurrence receiver (current := current))

/-- The completed parent is fixed; only the last field follows the supplied current. -/
structure SourceAt where
 completedMaterial : type_of% (completedFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead
 legs : type_of% (parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame)
 currentMaterial : type_of% (I.materialAt receiver supplied)

def sourceAt : SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied :=
 ⟨(completedFace observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).rootRead,
  parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame,
  I.materialAt receiver supplied⟩

def sourceLaw : SourceNativeProjectionLaw
 (S.base receiver).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} occurrence _ =>
  SourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver occurrence
 project := fun _ {_current} occurrence _ =>
  sourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver occurrence

def codeReader : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := BlockValue initial) (Var := C.Var) (sort := ()) :=
 let material := sourceAt observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied
 ⟨pairEnvironment material.currentMaterial.raw.environment
   (material.currentMaterial.nextRaw.environment-material.currentMaterial.raw.environment),
  codeAt initial material.legs.updatedPa material.legs.updatedNonPa⟩

theorem code_reader_expression :
 (codeReader observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame receiver supplied).expression =
 codeAt initial
  (parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updatedPa
  (parentSplit observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame).updatedNonPa := rfl

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
