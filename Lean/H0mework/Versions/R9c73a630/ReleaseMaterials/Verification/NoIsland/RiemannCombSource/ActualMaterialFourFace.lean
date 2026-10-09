import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Consumer
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceSuccessor

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation CofinalHistorySettlement
section Direct
attribute [local instance] SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.levelGroups
variable {W X : PUnit.{u+1} → Type u} [∀ t, AddCommGroup (W t)]
variable (factory : Actual.S.SF.Factory W X PUnit.unit) (n : Nat)
variable (data : Actual.S.SF.Packet (W := W) (X := X) (s := PUnit.unit) n)
variable (cfg : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
  (PhysicalValue := Actual.S.L.Value W n) (PhysicalVar := X) (sort := PUnit.unit))
variable (language : cfg.LowVar = X)
example : type_of% (Actual.actual_native factory n data cfg language) := Actual.actual_native _ _ _ _ _
example : type_of% (Actual.actual_native_inverse factory n data cfg language) := Actual.actual_native_inverse _ _ _ _ _
example : type_of% (Actual.actual_native_effect factory n data cfg language) := Actual.actual_native_effect _ _ _ _ _
example : type_of% (Actual.actual_whole_relation n data cfg) := Actual.actual_whole_relation _ _ _
example : type_of% (Actual.actual_generated_differential n data cfg) := Actual.actual_generated_differential _ _ _
example : type_of% (Actual.actual_complete_frame factory n data cfg language) := Actual.actual_complete_frame _ _ _ _ _
example (event) (present : event ∈ (P.exposure (Actual.material n data cfg).state.2).trace) :
    type_of% (Actual.source_trace_in_seed factory n data cfg language event present) :=
  Actual.source_trace_in_seed _ _ _ _ _ event present
example : type_of% (Actual.actual_boundary_in_born factory n data cfg language) := Actual.actual_boundary_in_born _ _ _ _ _
end Direct
section RSource
namespace R
export NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombSourceSuccessor
 (factory data configuration)
end R
open NoIslandNoMagic.CanonicalRiemann
attribute [local instance] SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.levelGroups
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
example : type_of% (Actual.actual_native R.factory 0 (R.data observation nontrivial depth half)
    (R.configuration observation nontrivial half) rfl) := Actual.actual_native _ _ _ _ _
example : type_of% (Actual.actual_native_effect R.factory 0 (R.data observation nontrivial depth half)
    (R.configuration observation nontrivial half) rfl) := Actual.actual_native_effect _ _ _ _ _
example : type_of% (Actual.actual_boundary_in_born R.factory 0 (R.data observation nontrivial depth half)
    (R.configuration observation nontrivial half) rfl) := Actual.actual_boundary_in_born _ _ _ _ _
end RSource

namespace Controls
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
  (oldPaid old_paid_value old_paid_const material programme initial selected receipt born nativeValue native_value born_environment)
end WB
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn actualOccurrence)
end S
namespace EnvLaw
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active epoch frames_constant)
end EnvLaw
abbrev ScalarValue := fun _ : Unit => ℤ
abbrev ScalarVar := fun _ : Unit => Unit
abbrev ScalarFrame := A.M.Frame (Value := ScalarValue) (Var := ScalarVar) (sort := ())
def sourceCfg : A.Programme (PhysicalValue := ScalarValue) (PhysicalVar := ScalarVar) (sort := ()) where
 LowVar := ScalarVar
 datum _ := { component := none, reader := fun {_current} _supplied => ⟨0, .const ((1 : ℤ), (0 : ℤ))⟩ }
def writePair (value : ℤ × ℤ) : Env (fun _ : Unit => ℤ × ℤ) ScalarVar := fun _ _ => value
variable (frame : ScalarFrame)
theorem first_old_paid : WB.oldPaid frame sourceCfg = ((1 : ℤ), (0 : ℤ)) :=
 (WB.old_paid_value frame sourceCfg).trans rfl
theorem first_native_zero : WB.nativeValue frame sourceCfg writePair = 0 := by
 have same : (N.input (WB.material frame sourceCfg)).environment = (WB.material frame sourceCfg).environment := by
   change (0 : Env (fun _ : Unit => ℤ × ℤ) ScalarVar) + (0 - 0) = 0
   abel
 exact (WB.native_value frame sourceCfg writePair).trans
   ((congrArg (fun environment => (N.expression (WB.material frame sourceCfg)).eval environment) same).trans
     (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.old_value (WB.material frame sourceCfg)))
theorem first_written : (WB.born frame sourceCfg writePair).activeEnvironment () () = ((1 : ℤ), (0 : ℤ)) := by
 have active := EnvLaw.active (WB.born_environment frame sourceCfg writePair)
 have point := congrArg (fun environment : Env (fun _ : Unit => ℤ × ℤ) ScalarVar => environment () ()) active
 exact point.trans ((congrArg (fun value : ℤ × ℤ => WB.oldPaid frame sourceCfg + value)
   (first_native_zero frame)).trans ((add_zero _).trans (first_old_paid frame)))
def current : A.M.Frame (Value := fun _ : Unit => ℤ × ℤ) (Var := ScalarVar) (sort := ()) :=
 WB.selected frame sourceCfg writePair
def positiveCfg : A.Programme (PhysicalValue := fun _ : Unit => ℤ × ℤ) (PhysicalVar := ScalarVar) (sort := ()) :=
 {WB.programme frame sourceCfg writePair with datum := fun owner =>
   {(WB.programme frame sourceCfg writePair).datum owner with
     calculationReader := some (fun {_current} _supplied =>
       ⟨(fun _ slot => (owner.activeEnvironment () slot, 0)), .var ()⟩)}}
def negativeCfg : A.Programme (PhysicalValue := fun _ : Unit => ℤ × ℤ) (PhysicalVar := ScalarVar) (sort := ()) :=
 {positiveCfg frame with datum := fun owner =>
   {(positiveCfg frame).datum owner with nextEnvironmentReadAt := some (fun {_current} _supplied _paid => 0)}}
def positive := SourceGeneratedInquiryReceiptAction.actualMaterial (current frame) (positiveCfg frame)
def negative := SourceGeneratedInquiryReceiptAction.actualMaterial (current frame) (negativeCfg frame)
def writeHigher (value : (ℤ × ℤ) × (ℤ × ℤ)) : Env (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar := fun _ _ => value

theorem current_zero : (current frame).activeEnvironment = 0 := by
 have initial : EnvLaw.At (WB.initial frame sourceCfg) 0 := by
   intro current occurrence
   rfl
 exact (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix.receipt_environment
   (WB.programme frame sourceCfg writePair) _ initial 0).trans rfl

theorem current_uniform : EnvLaw.At (current frame) 0 := by
 have initial : EnvLaw.At (WB.initial frame sourceCfg) 0 := by
   intro current occurrence
   rfl
 have same : EnvLaw.At (current frame) (current frame).activeEnvironment :=
   EnvLaw.frames_constant (WB.programme frame sourceCfg writePair) initial
     (0 + (WB.receipt frame sourceCfg writePair).1)
 exact fun {_current} occurrence => (same occurrence).trans (current_zero frame)

theorem positive_next_environment : EnvLaw.At (S.next (current frame) (positiveCfg frame)) (writePair ((1 : ℤ), (0 : ℤ))) := by
 have settled : (current frame).action = .inl (WB.receipt frame sourceCfg writePair).2.1 :=
   (WB.receipt frame sourceCfg writePair).2.2.2
 unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
 rw [settled]
 intro current occurrence
 change (WB.born frame sourceCfg writePair).activeEnvironment = writePair ((1 : ℤ), (0 : ℤ))
 have active := EnvLaw.active (WB.born_environment frame sourceCfg writePair)
 exact active.trans ((congrArg writePair (congrArg (fun value : ℤ × ℤ => WB.oldPaid frame sourceCfg + value)
   (first_native_zero frame))).trans (congrArg writePair ((add_zero _).trans (first_old_paid frame))))

theorem positive_old : (positive frame).environment = 0 := by
 have same := EnvLaw.epoch (current_uniform frame)
 change (fun _ slot => ((A.epoch (current frame)).activeEnvironment () slot, 0)) = 0
 rw [same]
 rfl

theorem positive_after : (N.input (positive frame)).environment () () = (((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) := by
 have same := SourceGeneratedInquiryReceiptAction.actual_updated_environment (current frame) (positiveCfg frame)
 have atSlot := congrArg (fun environment : Env (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar => environment () ()) same
 have next := EnvLaw.epoch (positive_next_environment frame)
 have point := congrArg (fun environment : Env (fun _ : Unit => ℤ × ℤ) ScalarVar => environment () ()) next
 exact atSlot.trans (congrArg (fun value : ℤ × ℤ => (value, (0 : ℤ × ℤ))) point)
theorem same_raw : (positive frame).raw = (negative frame).raw := rfl
theorem same_state : (positive frame).state = (negative frame).state := rfl
theorem same_boundary : boundary (positive frame) = boundary (negative frame) := by
 let f : (Expr (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar ()) ×
     (Expr (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar ()) →
     Formal ℤ (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar () :=
   fun pair => Finsupp.single pair.1 1 - Finsupp.single pair.2 1
 have samePair : ((positive frame).raw, (positive frame).state.1) =
     ((negative frame).raw, (negative frame).state.1) :=
   Prod.ext (same_raw frame) (congrArg Sigma.fst (same_state frame))
 exact (source_boundary (positive frame)).trans
   ((congrArg f samePair).trans (source_boundary (negative frame)).symm)
theorem same_literal : (positive frame).raw = (negative frame).raw ∧
    (positive frame).state = (negative frame).state ∧ boundary (positive frame) = boundary (negative frame) :=
 ⟨same_raw frame, same_state frame, same_boundary frame⟩
theorem positive_native : WB.nativeValue (current frame) (positiveCfg frame) writeHigher =
    (((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) := by
 have native := WB.native_value (current frame) (positiveCfg frame) writeHigher
 have paid := WB.old_paid_const (current frame) (positiveCfg frame)
 have zero : WB.oldPaid (current frame) (positiveCfg frame) = 0 :=
   (WB.old_paid_value _ _).trans
     ((congrArg (fun environment => (positive frame).raw.eval environment) (positive_old frame)).trans rfl)
 have expression := N.expression_eval (positive frame) (N.input (positive frame)).environment
 have old : (positive frame).state.1.eval (N.input (positive frame)).environment = 0 :=
   (congrArg (fun term : Expr (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar () => term.eval (N.input (positive frame)).environment) paid).trans zero
 exact native.trans (expression.trans ((congrArg (fun value : (ℤ × ℤ) × (ℤ × ℤ) => (N.input (positive frame)).environment () () - value) old).trans
   ((sub_zero _).trans (positive_after frame))))
theorem negative_after : (N.input (negative frame)).environment = 0 := by
 have same := SourceGeneratedInquiryReceiptAction.actual_updated_environment (current frame) (negativeCfg frame)
 have next : EnvLaw.At (S.next (current frame) (negativeCfg frame)) 0 := by
   have settled : (current frame).action = .inl (WB.receipt frame sourceCfg writePair).2.1 :=
     (WB.receipt frame sourceCfg writePair).2.2.2
   unfold SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
   rw [settled]
   intro current occurrence
   rfl
 have updated := EnvLaw.epoch next
 apply same.trans
 change (fun _ slot => ((A.epoch (S.next (current frame) (negativeCfg frame))).activeEnvironment () slot, 0)) = 0
 rw [updated]
 rfl

theorem negative_native : WB.nativeValue (current frame) (negativeCfg frame) writeHigher = 0 := by
 have same : (N.input (negative frame)).environment = (negative frame).environment :=
   (negative_after frame).trans (positive_old frame).symm
 exact (WB.native_value (current frame) (negativeCfg frame) writeHigher).trans
   ((congrArg (fun environment => (N.expression (negative frame)).eval environment) same).trans
     (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.old_value (negative frame)))

theorem positive_read : (effectFaces (positive frame)).embedding (paidCoordinate (positive frame)) =
    (((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) :=
 (actual_inverse (positive frame)).trans ((WB.native_value (current frame) (positiveCfg frame) writeHigher).symm.trans (positive_native frame))
theorem negative_read : (effectFaces (negative frame)).embedding (paidCoordinate (negative frame)) = 0 :=
 (actual_inverse (negative frame)).trans ((WB.native_value (current frame) (negativeCfg frame) writeHigher).symm.trans (negative_native frame))
example : paidCoordinate (positive frame) ≠ 0 := by
 intro same
 have impossible := positive_read frame
 rw [same, map_zero] at impossible
 have point := congrArg (fun value : (ℤ × ℤ) × (ℤ × ℤ) => value.1.1) impossible
 norm_num at point
example : paidCoordinate (negative frame) = 0 :=
 (native_zero_iff (negative frame)).mpr
   ((WB.native_value (current frame) (negativeCfg frame) writeHigher).symm.trans (negative_native frame))
example : type_of% (relation_recovery (negative frame)) := relation_recovery _
example : type_of% (And.intro (completion_zero (positive frame)) (positive_read frame)) :=
 ⟨completion_zero _, positive_read _⟩
example : (positive frame).increment () () = (((1 : ℤ), (0 : ℤ)), ((0 : ℤ), (0 : ℤ))) := by
 have after := positive_after frame
 change (positive frame).environment () () + (positive frame).increment () () = _ at after
 have oldAt := congrArg (fun environment : Env (fun _ : Unit => (ℤ × ℤ) × (ℤ × ℤ)) ScalarVar => environment () ())
   (positive_old frame)
 exact (zero_add ((positive frame).increment () ())).symm.trans
   ((congrArg (fun value : (ℤ × ℤ) × (ℤ × ℤ) => value + (positive frame).increment () ()) oldAt.symm).trans after)
example : paidCoordinate (negative frame) = 0 ∧ boundary (negative frame) ≠ 0 ∧
    SourceGeneratedCompleteWordDual.coimageRecovery ((wholeFaces (negative frame)).canonical (boundary (negative frame))) = boundary (negative frame) := by
 refine ⟨(native_zero_iff (negative frame)).mpr
   ((WB.native_value (current frame) (negativeCfg frame) writeHigher).symm.trans (negative_native frame)), ?_, relation_recovery _⟩
 intro absent
 have muZero : boundary (positive frame) = 0 := (same_literal frame).2.2.trans absent
 have impossible := positive_read frame
 unfold paidCoordinate at impossible
 rw [muZero, map_zero, map_zero] at impossible
 have point := congrArg (fun value : (ℤ × ℤ) × (ℤ × ℤ) => value.1.1) impossible
 norm_num at point
#print axioms positive_read
#print axioms negative_read
end Controls
#print axioms source_root
#print axioms source_trace
#print axioms full_paid_steps
#print axioms source_boundary
#print axioms generated_differential
#print axioms completion_zero
#print axioms same_source
#print axioms generated_relation
#print axioms generated_cochain
#print axioms whole_paid_trace
#print axioms actual_inverse
#print axioms actual_effect
#print axioms differential_effect
#print axioms whole_recovery
#print axioms relation_recovery
#print axioms native_zero_iff
#print axioms Actual.actual_native
#print axioms Actual.actual_whole_relation
#print axioms Actual.actual_generated_differential
#print axioms Actual.actual_complete_frame
#print axioms Actual.actual_native_inverse
#print axioms Actual.actual_native_effect
#print axioms Actual.source_trace_in_seed
#print axioms Actual.actual_boundary_in_born
end SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
