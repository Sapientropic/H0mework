import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.Reentry.Splice
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceDifferentialResidualAction.Physics

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
namespace SP
export Reentry.Splice (born bornProgramme generatedAction resultFace actualMaterial)
end SP
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (base root actualOccurrence)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence materialAt)
end I
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end J
namespace DR
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction
 (completeRSourceAction completeRSourceRead completeResidualTotalRole complete_R_source_action_read)
namespace L
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceDifferentialResidualAction.L (Value groups)
end L
end DR
namespace C
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction.C (Value Var)
end C
namespace RPhysical
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction (variableAction)
end RPhysical

abbrev BaseValue (initial : Nat) := DR.L.Value (PairValue C.Value) initial
local instance sourceGroups (initial : Nat) : ∀ target, AddCommGroup (BaseValue initial target) :=
 DR.L.groups (PairValue C.Value) initial
local instance bornGroups (initial : Nat) : ∀ target, AddCommGroup (DR.L.Value (BaseValue initial) 2 target) :=
 DR.L.groups (BaseValue initial) 2
local instance runtimeGroups (initial : Nat) : ∀ target, AddCommGroup
 (DR.L.Value (DR.L.Value (BaseValue initial) 2) 0 target) :=
 DR.L.groups (DR.L.Value (BaseValue initial) 2) 0

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
variable (initial : Nat)
private def rawCode
 (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ())) :
 Expr (PairValue (PairValue (PairValue (BaseValue initial)))) C.Var () :=
 .linear (s:=()) (t:=()) (DR.completeRSourceAction observation nontrivial half initial 2 0)
  (.linear (s:=()) (t:=()) (DR.completeResidualTotalRole initial 2 0) (liftExpr raw.expression))

private theorem full_raw_read
 (raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
  (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))
 (nextEnvironment : Env (PairValue (PairValue (BaseValue initial))) C.Var) :
 DR.completeRSourceRead initial 2 0
  ((rawCode observation nontrivial half initial raw).eval
   (pairEnvironment raw.environment (nextEnvironment-raw.environment))) =
 RPhysical.variableAction observation nontrivial half
  (DR.completeRSourceRead initial 2 0 (raw.expression.eval nextEnvironment,0)) := by
 change DR.completeRSourceRead initial 2 0 (DR.completeRSourceAction observation nontrivial half initial 2 0 _) = _
 refine (DR.complete_R_source_action_read observation nontrivial half initial 2 0 _).trans ?_
 change RPhysical.variableAction observation nontrivial half (DR.completeRSourceRead initial 2 0
  (((liftExpr raw.expression).eval (pairEnvironment raw.environment (nextEnvironment-raw.environment))).1+
   ((liftExpr raw.expression).eval (pairEnvironment raw.environment (nextEnvironment-raw.environment))).2,0)) = _
 rw [eval_liftExpr]
 apply congrArg (fun value => RPhysical.variableAction observation nontrivial half (DR.completeRSourceRead initial 2 0 (value,0)))
 have actual := (Expr.eval_update raw.expression raw.environment (nextEnvironment-raw.environment)).symm
 rw [add_sub_cancel] at actual
 exact actual

variable (frame : Reentry.A.M.Frame (Value := PairValue (BaseValue initial)) (Var := C.Var) (sort := ()))
variable (base : A.Programme (PhysicalValue := PairValue (BaseValue initial)) (PhysicalVar := C.Var) (sort := ()))
variable (before : Inventory (V := BaseValue initial) (X := C.Var) (s := ()))
variable (oldEnvironment : Env (BaseValue initial) C.Var)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))

abbrev target := (SP.generatedAction frame base before oldEnvironment admissions).target
abbrev material := SP.actualMaterial frame base before oldEnvironment admissions

/-- The retained prefix is read at its literal initial target occurrence; the current visit has already paid one step. -/
def prefixResultFace : SourceNativeRootSemanticFaceAt
 (target initial frame base before oldEnvironment admissions).targetRoot
 (target initial frame base before oldEnvironment admissions).targetInitialVisit where
 projection := (target initial frame base before oldEnvironment admissions).oldProjection
  (SP.resultFace frame base before oldEnvironment admissions).projection
 active := PUnit.unit
 classifier_eq := rfl

theorem prefix_raw : (prefixResultFace initial frame base before oldEnvironment admissions).rootRead.1.expression =
 (material initial frame base before oldEnvironment admissions).raw := rfl

theorem prefix_environment : (prefixResultFace initial frame base before oldEnvironment admissions).rootRead.1.environment =
 (material initial frame base before oldEnvironment admissions).environment := rfl

theorem prefix_state : (prefixResultFace initial frame base before oldEnvironment admissions).rootRead.2.1 =
 (material initial frame base before oldEnvironment admissions).state := rfl

variable (sourceFrame : Reentry.A.M.Frame (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()))
variable {current : J.Current sourceFrame.registered}
variable (supplied : I.Occurrence sourceFrame (current := current))

/-- The prefix receipt and the supplied current occurrence are distinct indexed source data. -/
structure SourceAt where
 prior : type_of% (prefixResultFace initial frame base before oldEnvironment admissions).rootRead
 currentMaterial : type_of% (I.materialAt sourceFrame supplied)

def sourceAt : SourceAt initial frame base before oldEnvironment admissions sourceFrame supplied :=
 ⟨(prefixResultFace initial frame base before oldEnvironment admissions).rootRead, I.materialAt sourceFrame supplied⟩

def sourceLaw : SourceNativeProjectionLaw (S.base sourceFrame).root.source.base.restructuringSource.toLedgerSource where
 Projection := PUnit
 ActiveAt := fun _ {_current} _ => PUnit
 InactiveAt := fun _ {_current} _ => PEmpty
 classify := fun _ {_current} _ => .inl PUnit.unit
 PayloadAt := fun _ {_current} occurrence _ => SourceAt initial frame base before oldEnvironment admissions sourceFrame occurrence
 project := fun _ {_current} occurrence _ => sourceAt initial frame base before oldEnvironment admissions sourceFrame occurrence

abbrev source := (sourceLaw initial frame base before oldEnvironment admissions sourceFrame).project PUnit.unit supplied PUnit.unit
def sourceRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value := PairValue (PairValue (BaseValue initial))) (Var := C.Var) (sort := ()) :=
 (source initial frame base before oldEnvironment admissions sourceFrame supplied).prior.1
def sourceEnvironment : Env (PairValue (PairValue (BaseValue initial))) C.Var :=
 (source initial frame base before oldEnvironment admissions sourceFrame supplied).currentMaterial.raw.environment

abbrev pairEnvironmentAt : Env (PairValue (PairValue (PairValue (BaseValue initial)))) C.Var := pairEnvironment
 (sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied).environment
 (sourceEnvironment initial frame base before oldEnvironment admissions sourceFrame supplied-
  (sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied).environment)

/-- The installed full raw syntax supplies old and effect before the original R acts on their sum. -/
abbrev code : Expr (PairValue (PairValue (PairValue (BaseValue initial)))) C.Var () :=
 rawCode observation nontrivial half initial
  (sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied)

theorem source_raw_expression :
 (sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied).expression =
 (prefixResultFace initial frame base before oldEnvironment admissions).rootRead.1.expression := rfl

theorem actual_source_environment : sourceEnvironment initial frame base before oldEnvironment admissions
 (SP.born frame base before oldEnvironment admissions)
 (S.actualOccurrence (SP.born frame base before oldEnvironment admissions)) =
 (material initial frame base before oldEnvironment admissions).environment+
 (material initial frame base before oldEnvironment admissions).increment := rfl

attribute [local irreducible] sourceRaw sourceEnvironment

theorem source_read : DR.completeRSourceRead initial 2 0
 ((code observation nontrivial half initial frame base before oldEnvironment admissions sourceFrame supplied).eval
  (pairEnvironmentAt initial frame base before oldEnvironment admissions sourceFrame supplied)) =
 RPhysical.variableAction observation nontrivial half
  (DR.completeRSourceRead initial 2 0
   ((sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied).expression.eval
    (sourceEnvironment initial frame base before oldEnvironment admissions sourceFrame supplied),0)) :=
 full_raw_read observation nontrivial half initial
  (sourceRaw initial frame base before oldEnvironment admissions sourceFrame supplied)
  (sourceEnvironment initial frame base before oldEnvironment admissions sourceFrame supplied)

theorem actual_full_update : DR.completeRSourceRead initial 2 0
 ((code observation nontrivial half initial frame base before oldEnvironment admissions
    (SP.born frame base before oldEnvironment admissions)
    (S.actualOccurrence (SP.born frame base before oldEnvironment admissions))).eval
  (pairEnvironmentAt initial frame base before oldEnvironment admissions
   (SP.born frame base before oldEnvironment admissions)
   (S.actualOccurrence (SP.born frame base before oldEnvironment admissions)))) =
 RPhysical.variableAction observation nontrivial half (DR.completeRSourceRead initial 2 0
  ((material initial frame base before oldEnvironment admissions).raw.eval
   ((material initial frame base before oldEnvironment admissions).environment+
    (material initial frame base before oldEnvironment admissions).increment),0)) := by
 refine (source_read observation nontrivial half initial frame base before oldEnvironment admissions _ _).trans ?_
 apply congrArg (fun value => RPhysical.variableAction observation nontrivial half (DR.completeRSourceRead initial 2 0 (value,0)))
 exact congrArg₂ (fun (expression : Expr (PairValue (PairValue (BaseValue initial))) C.Var ()) environment => expression.eval environment)
  ((source_raw_expression initial frame base before oldEnvironment admissions _ _).trans
   (prefix_raw initial frame base before oldEnvironment admissions))
  (actual_source_environment initial frame base before oldEnvironment admissions)

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
