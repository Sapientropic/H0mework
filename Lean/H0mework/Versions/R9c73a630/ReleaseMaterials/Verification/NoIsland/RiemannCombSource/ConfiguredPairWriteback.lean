import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConfiguredPairWriteback

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombConfiguredPairWriteback
open SourceGeneratedInquiryReceiptAction.Configured.Writeback
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (depth : Nat)
variable (half : NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)
attribute [local irreducible] P.code

example : type_of% (native_effect (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  native_effect _ _ _
example : type_of% (native_inverse (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  native_inverse _ _ _
example : type_of% (source_target_next (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  source_target_next _ _ _
example : type_of% (actual_receipt_compiles (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  actual_receipt_compiles _ _ _
example : type_of% (actual_receipt_next (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  actual_receipt_next _ _ _
example : type_of% (F.next_paid_R_state observation nontrivial depth half) := F.next_paid_R_state _ _ _ _
example : type_of% (F.next_paid_trace observation nontrivial depth half) := F.next_paid_trace _ _ _ _
example : type_of% (F.next_complete_raw observation nontrivial depth half) := F.next_complete_raw _ _ _ _
example : type_of% (born_inventory (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  born_inventory _ _ _
example : type_of% (born_pair_inventory (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) :=
  born_pair_inventory _ _ _
example : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
    (sourceBorn observation nontrivial depth half)
    (fun _ _ =>
      (P.physicalProjection ((P.R observation nontrivial half) (F.projected observation nontrivial depth half)),
       P.physicalRemainder ((P.R observation nontrivial half) (F.projected observation nontrivial depth half)))) :=
  actual_born_pair observation nontrivial depth half

example : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
    (born (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half)
      (writePair observation nontrivial half))
    (writePair observation nontrivial half
      ((material (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half)).raw.eval
        (N.input (material (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half))).environment)) :=
  configured_actual_paid_pair_writeback _ _ _

example : (S.runtime (initial (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half))
    (programme (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half)
      (writePair observation nontrivial half))).initialState.engine.node =
    .active (Intake.targetPresentation (sourceFrame observation nontrivial depth half)
      (sourceConfiguration observation nontrivial half)
      (programme (sourceFrame observation nontrivial depth half) (sourceConfiguration observation nontrivial half)
        (writePair observation nontrivial half))) := rfl

example : type_of% (source_whole (sourceFrame observation nontrivial depth half)
    (sourceConfiguration observation nontrivial half) (writePair observation nontrivial half)) := source_whole _ _ _

#print axioms actual_born_pair
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCombConfiguredPairWriteback
namespace SourceGeneratedInquiryReceiptAction.Configured.Writeback
namespace Controls
abbrev ScalarFrame := SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := fun _ : Unit => ℤ) (Var := fun _ : Unit => Unit) (sort := ())

def constantConfiguration : A.Programme
    (PhysicalValue := fun _ : Unit => ℤ) (PhysicalVar := fun _ : Unit => Unit) (sort := ()) where
  LowVar := fun _ => Unit
  datum _ := { component := none, reader := fun {_current} _supplied =>
    ⟨0, .const ((1 : ℤ), (0 : ℤ))⟩ }

def writePair (value : ℤ × ℤ) : Env (fun _ : Unit => ℤ × ℤ) (fun _ : Unit => Unit) :=
  fun _ _ => value

variable (frame : ScalarFrame)

theorem old_one : oldPaid frame constantConfiguration = ((1 : ℤ), (0 : ℤ)) :=
  (old_paid_value frame constantConfiguration).trans rfl

theorem native_zero : nativeValue frame constantConfiguration writePair = (0 : ℤ × ℤ) := by
  have same : (N.input (material frame constantConfiguration)).environment =
      (material frame constantConfiguration).environment := by
    change (0 : Env (fun _ : Unit => ℤ × ℤ) (fun _ : Unit => Unit)) + (0 - 0) = 0
    abel
  exact (native_value frame constantConfiguration writePair).trans
    ((congrArg (fun environment => (N.expression (material frame constantConfiguration)).eval environment) same).trans
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.old_value (material frame constantConfiguration)))

theorem written_one :
    (born frame constantConfiguration writePair).activeEnvironment () () = ((1 : ℤ), (0 : ℤ)) := by
  have actual := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active
    (born_environment frame constantConfiguration writePair)
  have point := congrArg (fun environment : Env (fun _ : Unit => ℤ × ℤ) (fun _ : Unit => Unit) => environment () ()) actual
  exact point.trans ((congrArg (fun value : ℤ × ℤ => oldPaid frame constantConfiguration + value)
    (native_zero frame)).trans ((add_zero _).trans (old_one frame)))

example : nativeValue frame constantConfiguration writePair = 0 ∧
    (born frame constantConfiguration writePair).activeEnvironment () () = ((1 : ℤ), (0 : ℤ)) :=
  ⟨native_zero frame, written_one frame⟩

example : (born frame constantConfiguration writePair).activeEnvironment () () -
    (initial frame constantConfiguration).activeEnvironment () () ≠ (0 : ℤ × ℤ) := by
  have initialZero : (initial frame constantConfiguration).activeEnvironment () () = (0 : ℤ × ℤ) := rfl
  rw [written_one, initialZero]
  norm_num

example : type_of% (actual_receipt_next frame constantConfiguration writePair) :=
  actual_receipt_next frame constantConfiguration writePair
example : type_of% (source_compiles frame constantConfiguration writePair) := source_compiles _ _ _
example : type_of% (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (material frame constantConfiguration)) :=
  RootGeneratedDebtActivationJointSource.Native.ResidualRequest.budget (material frame constantConfiguration)
#print axioms written_one
end Controls

#print axioms updated_total
#print axioms born_environment
#print axioms source_compiles
#print axioms actual_receipt_next
#print axioms native_effect
#print axioms native_inverse
#print axioms configured_actual_paid_pair_writeback
end SourceGeneratedInquiryReceiptAction.Configured.Writeback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
