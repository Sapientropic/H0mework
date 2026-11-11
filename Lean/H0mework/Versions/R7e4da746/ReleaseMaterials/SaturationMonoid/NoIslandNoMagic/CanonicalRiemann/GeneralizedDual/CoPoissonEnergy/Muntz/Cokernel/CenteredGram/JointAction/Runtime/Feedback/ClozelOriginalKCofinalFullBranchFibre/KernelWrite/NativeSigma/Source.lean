import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Effect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Registered.Source
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Completion.Prefix

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement SourceGeneratedScalarDifferentialResidual
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt actionReader)
end R
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression expression_eval relation_boundary)
end N
namespace AN
export ActualNativeRelationTransport (paid paid_raw paid_environment bornHistory new_relation_in_born)
end AN
namespace RB
export ActualRegisteredBornEffect (delta transported actual_input registered_effect registered_inverse registered_pair)
end RB
namespace B
export ActualNativeBornSourceEffect (born)
end B
namespace FF
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (boundary source_boundary effectFaces paidCoordinate)
end FF
namespace CA
export ActualCofinalSourceAction (nativePacket native_packet_actual receiver_ast)
end CA
namespace Prefix
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion.Prefix (receipt_read)
end Prefix
namespace Projection
export OriginalKFiniteWardGram (code_effect_base collapseEnvironment)
end Projection
namespace Own
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (target_expression)
end Own
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot)
end Shared

section Receipt
variable {V X : Unit → Type} [∀ target, AddCommGroup (V target)]
variable (initial : A.M.Frame (Value := V) (Var := X) (sort := ()))
variable (cfg : A.Programme (PhysicalValue := V) (PhysicalVar := X) (sort := ()))

private theorem receipt_expression :
 (S.Complete.atReceipt cfg initial 0).registered.input.expression = initial.registered.input.expression := by
 apply Prefix.receipt_read cfg initial (fun stage => (S.frames initial cfg stage).registered.input.expression)
 intro stage paid actual
 have next : S.frames initial cfg (stage+1) = (S.frames initial cfg stage).mathNext := by
  change S.next _ _ = _
  unfold S.next
  rw [actual]
 exact (congrArg (fun frame : A.M.Frame (Value := V) (Var := X) (sort := ()) =>
  frame.registered.input.expression) next).trans rfl

private theorem receipt_boundary_effect (increment : Env V X) :
 effectEvaluator (R := ℤ) (AN.paid (S.Complete.atReceipt cfg initial 0)).environment increment
  (FF.boundary (AN.paid (S.Complete.atReceipt cfg initial 0))) =
 initial.registered.input.expression.effect
  (AN.paid (S.Complete.atReceipt cfg initial 0)).environment increment := by
 rw [FF.source_boundary]
 have endpoint : (AN.paid (S.Complete.atReceipt cfg initial 0)).state.1 =
  .const (S.Complete.receipt cfg initial 0).2.1.1 :=
  (S.Complete.receipt cfg initial 0).2.1.2.down
 rw [endpoint]
 simp only [effectEvaluator, map_sub, Finsupp.linearCombination_single, one_smul,
  Expr.effect, sub_zero]
 rw [AN.paid_raw, receipt_expression]

private theorem material_sigma_effect (old increment : Env (PairValue V) cfg.LowVar) :
 (N.expression (R.actualMaterial initial cfg)).effect old increment =
 (R.actualMaterial initial cfg).raw.effect old increment := by
 have endpoint : (R.actualMaterial initial cfg).state.1 =
  .const (R.actionResultAt initial cfg (S.actualOccurrence initial)).2.2.1 :=
  Own.target_expression (Shared.baseRoot initial cfg).toAuthoritativeRoot _
   (fun _ => R.actionReader initial cfg (S.actualOccurrence initial))
 rw [N.expression, endpoint]
 simp only [Expr.effect, AddMonoidHom.neg_apply, AddMonoidHom.id_apply, neg_zero, add_zero]
end Receipt

local instance nativeGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

abbrev NativePacket := AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())
abbrev NativeFactory := SF.Factory (PairValue C.Value) C.Var ()

def collapseNative (factory : NativeFactory) (packet : NativePacket)
 (value : L.Value (PairValue C.Value) (AS.nativeAfterAdmission factory packet).1 ()) :
 PairValue (PairValue C.Value) () :=
 CF.collapseValue packet.1
  (Eq.mp (congrArg (fun grade => L.Value (PairValue C.Value) grade ())
   (AS.nativeAfterAdmission_grade factory packet)) value)

abbrev selected (factory : NativeFactory) (packet : NativePacket) :=
 S.Complete.atReceipt (AS.stockCfg (AS.nativeAfterAdmission factory packet).2.2.1)
  (AS.nativeAfterAdmission factory packet).2.1.1 0
abbrev decoded (factory : NativeFactory) (packet : NativePacket) :=
 B.born (selected factory packet) (AS.nativeAfterAdmission factory packet).2.2.1
abbrev paid (factory : NativeFactory) (packet : NativePacket) := AN.paid (selected factory packet)
abbrev boundary (factory : NativeFactory) (packet : NativePacket) := FF.boundary (paid factory packet)
abbrev increment (factory : NativeFactory) (packet : NativePacket) :=
 RB.delta (selected factory packet) (AS.nativeAfterAdmission factory packet).2.2.1
def collapsedOld (factory : NativeFactory) (packet : NativePacket) : Env (PairValue (PairValue C.Value)) C.Var :=
 fun target name => collapseNative factory packet ((paid factory packet).environment target name)
def collapsedIncrement (factory : NativeFactory) (packet : NativePacket) : Env (PairValue (PairValue C.Value)) C.Var :=
 fun target name => collapseNative factory packet (increment factory packet target name)

private theorem actual_code_effect (factory : NativeFactory) (packet : NativePacket)
 (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
 collapseNative factory packet
  (effectEvaluator (R := ℤ) (paid factory packet).environment (increment factory packet)
   (boundary factory packet)) =
 code.effect (collapsedOld factory packet) (collapsedIncrement factory packet) := by
 rcases packet with ⟨grade, data, programme, ⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar = C.Var at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
   ⟨C.Var, datum, inventory, pairInventory⟩
  let packet : NativePacket := ⟨grade, data, cfg, ⟨rfl⟩⟩
  let native := CA.nativePacket factory packet
  let receiver := native.2.1.1
  let nativeCfg := AS.stockCfg native.2.2.1
  let stop := S.Complete.atReceipt nativeCfg receiver 0
  let old := (AN.paid stop).environment
  let delta := RB.delta stop native.2.2.1
  have receiverRaw : receiver.registered.input.expression = N.expression (R.actualMaterial data.1 cfg) :=
   CA.receiver_ast factory packet
  have raw : (R.actualMaterial data.1 cfg).raw = CF.codeAt code grade := by
   have source := (AS.stock_action_reader data.1 cfg (S.actualOccurrence data.1)).symm.trans
    (generated data.1 (S.actualOccurrence data.1))
   exact congrArg (fun input => input.expression) source
  have effect : effectEvaluator (R := ℤ) old delta (FF.boundary (AN.paid stop)) =
   (CF.codeAt code grade).effect old delta := by
   exact (receipt_boundary_effect receiver nativeCfg delta).trans
    ((congrArg (fun expression => expression.effect old delta) receiverRaw).trans
     ((material_sigma_effect data.1 cfg old delta).trans
      (congrArg (fun expression => expression.effect old delta) raw)))
  change CF.collapseValue grade (effectEvaluator (R := ℤ) old delta (FF.boundary (AN.paid stop))) = _
  exact (congrArg (CF.collapseValue grade) effect).trans (Projection.code_effect_base code grade old delta)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev originalFactory := D.factory observation nontrivial half
abbrev originalPacket := originalPredecessor observation nontrivial half depth ordinal
abbrev originalPaid := paid (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
abbrev originalBoundary := boundary (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
abbrev originalIncrement := collapsedIncrement (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
abbrev originalOld := collapsedOld (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
abbrev originalDecoded := decoded (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
abbrev originalInverse :=
 (FF.effectFaces (RB.transported (writerSelected observation nontrivial half depth ordinal)
  (originalNative observation nontrivial half depth ordinal).2.2.1)).rangeEquiv
 (FF.paidCoordinate (RB.transported (writerSelected observation nontrivial half depth ordinal)
  (originalNative observation nontrivial half depth ordinal).2.2.1))

/-- The actual native paid boundary generates the original complete R action on its decoded increment. -/
theorem original_native_sigma_effect :
 collapseNative (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
  (effectEvaluator (R := ℤ) (originalPaid observation nontrivial half depth ordinal).environment
   (increment (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal))
   (originalBoundary observation nontrivial half depth ordinal)) =
 Full.branches observation nontrivial half
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation.completeInput
   (originalIncrement observation nontrivial half depth ordinal) () ()) :=
 (actual_code_effect (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
  (FR.jointCode (RSource.code observation nontrivial half))
  (original_predecessor_actual_input observation nontrivial half depth ordinal)).trans rfl

/-- The existing complete range inverse reads that same generated full four-branch action. -/
theorem original_native_sigma_inverse :
 collapseNative (originalFactory observation nontrivial half) (originalPacket observation nontrivial half depth ordinal)
  (originalInverse observation nontrivial half depth ordinal).val =
 Full.branches observation nontrivial half
  (SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation.completeInput
   (originalIncrement observation nontrivial half depth ordinal) () ()) := by
 have inverse := RB.registered_inverse (writerSelected observation nontrivial half depth ordinal)
  (originalNative observation nontrivial half depth ordinal).2.2.1
 have effect := RB.registered_effect (writerSelected observation nontrivial half depth ordinal)
  (originalNative observation nontrivial half depth ordinal).2.2.1
 exact (congrArg (collapseNative (originalFactory observation nontrivial half)
  (originalPacket observation nontrivial half depth ordinal)) (inverse.trans effect)).trans
  (original_native_sigma_effect observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
