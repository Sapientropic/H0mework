import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PrimeThreeWholeSource.Action

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Install
open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open OriginalKCofinalFullBranchFibre.KernelWrite
open private raw_environment raw_environment_congr constant_environment_read environment_read_congr after_environment_of_reader from
  H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryNativeKAction
namespace K
export BoundaryNativeKAction (environment sourceValue receiptValue originalResult sourceLaw fullSource original_receipt origin_value
  decodedTotal decoded_source total)
end K
namespace U
export BoundaryCountedNativeUpdate (selected base)
end U
namespace N
export BoundaryCountedNativeWord (NextValues)
end N
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (baseRoot actualOccurrence)
end S
namespace I
export SourceOperationInquiry.Context.Installation (Occurrence)
end I
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw (Current)
end J
namespace R
export SourceGeneratedInquiryReceiptAction (actualMaterial actionResultAt actionReader afterEnvironment occurrence)
end R
namespace MR
export SourceGeneratedInquiryReceiptAction.Read
 (raw_source environment_source updated_environment_source occurrence_source value_source paid_source state_source after_environment_source)
end MR
namespace WB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
 (born configured_actual_paid_pair_writeback source_whole source_target_next)
end WB
local instance groups (grade : Nat) : ∀ slot, AddCommGroup (L.Value (PairValue C.Value) grade slot) :=
  L.groups (PairValue C.Value) grade
variable (coordinate : BurnolCompletedMellinCoordinate) (n : Nat)
variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
local notation "V" => N.NextValues factory native
local notation "f" => U.selected factory native
local notation "grade" => Sigma.fst (NativeDelta.BetaDecoder.nextNative factory native)

def sourceRaw
    (receiver : A.M.Frame (Value := V) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (_supplied : I.Occurrence receiver (current := current)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := PairValue V) (Var := C.Var) (sort := ()) :=
  ⟨K.environment coordinate n factory native, Program.code coordinate n grade⟩

theorem source_environment
    (receiver : A.M.Frame (Value := V) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
    (sourceRaw coordinate n factory native receiver supplied).environment = K.environment coordinate n factory native :=
  @raw_environment (PairValue V) C.Var
    (fun slot => @Prod.instAddCommGroup (V slot) (V slot) (groups grade slot) (groups grade slot))
    (K.environment coordinate n factory native) (Program.code coordinate n grade)

def configuration : A.Programme (PhysicalValue := V) (PhysicalVar := C.Var) (sort := ()) :=
  let original := BoundaryCountedNativeQuery.configuration factory native
  let language : original.LowVar = C.Var := (NativeDelta.BetaDecoder.nextNative factory native).2.2.2.down
  { LowVar := C.Var
    datum := fun receiver =>
      let prior : SourceOperationInquiry.Context.Faces.Execution.Activation.SourceDatum C.Var receiver :=
        Eq.mp (congrArg (fun vars => SourceOperationInquiry.Context.Faces.Execution.Activation.SourceDatum vars receiver)
          language) (original.datum receiver)
      { prior with
        component := some (K.fullSource coordinate n factory native receiver).projectionLaw
        reader := sourceRaw coordinate n factory native receiver
        calculationReader := none }
    nextInventory := original.nextInventory
    nextPairInventory := original.nextPairInventory }

abbrev material := R.actualMaterial f (configuration coordinate n factory native)
abbrev result := R.actionResultAt f (configuration coordinate n factory native)
  (R.occurrence f (configuration coordinate n factory native))

theorem original_ledger : (S.baseRoot f (configuration coordinate n factory native)).toAuthoritativeRoot.toLedgerRoot =
    (U.base factory native).root.toAuthoritativeRoot.toLedgerRoot := rfl

theorem original_occurrence : HEq (R.occurrence f (configuration coordinate n factory native))
    ((U.base factory native).root.emitted (U.base factory native).visit.current) :=
  (heq_of_eq (MR.occurrence_source f (configuration coordinate n factory native))).trans HEq.rfl

theorem source_reader (receiver : A.M.Frame (Value := V) (Var := C.Var) (sort := ()))
    {current : J.Current receiver.registered} (supplied : I.Occurrence receiver (current := current)) :
    R.actionReader receiver (configuration coordinate n factory native) supplied =
      sourceRaw coordinate n factory native (A.epoch receiver) supplied := rfl

theorem material_raw : (material coordinate n factory native).raw = Program.code coordinate n grade :=
  (MR.raw_source f (configuration coordinate n factory native)).trans
    (congrArg (fun raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue V) (Var := C.Var) (sort := ()) => raw.expression)
      (source_reader coordinate n factory native f (R.occurrence f (configuration coordinate n factory native))))

theorem material_environment : (material coordinate n factory native).environment = K.environment coordinate n factory native :=
  (MR.environment_source f (configuration coordinate n factory native)).trans
    ((raw_environment_congr (source_reader coordinate n factory native f (R.occurrence f (configuration coordinate n factory native)))).trans
      (source_environment coordinate n factory native (A.epoch f) (R.occurrence f (configuration coordinate n factory native))))

attribute [local irreducible] SourceGeneratedInquiryReceiptAction.material SourceGeneratedInquiryReceiptAction.actionResultAt

theorem original_input : (material coordinate n factory native).environment () () = K.sourceValue coordinate n factory native :=
  (environment_read_congr (material_environment coordinate n factory native) ()).trans
    (constant_environment_read (X := C.Var) (K.sourceValue coordinate n factory native) ())

theorem input_from_original_receipt : (material coordinate n factory native).environment () () =
    K.receiptValue coordinate n factory native
      (((K.sourceLaw coordinate n factory native (A.epoch f)).project PUnit.unit (S.actualOccurrence f) PUnit.unit).original) :=
  (original_input coordinate n factory native).trans (K.origin_value coordinate n factory native).symm

theorem actual_equation : (result coordinate n factory native).2.2.1 =
    (Program.code coordinate n grade).eval (K.environment coordinate n factory native) :=
  (MR.value_source f (configuration coordinate n factory native)).trans
    (congrArg₂ (fun term environment => Expr.eval term environment)
      (material_raw coordinate n factory native) (material_environment coordinate n factory native))

theorem actual_paid : (material coordinate n factory native).state.2.length = 10 :=
  (MR.paid_source f (configuration coordinate n factory native)).trans
    ((congrArg remaining (material_raw coordinate n factory native)).trans (Program.budget coordinate n grade))

theorem after_environment : R.afterEnvironment f (configuration coordinate n factory native) = K.environment coordinate n factory native := by
  apply after_environment_of_reader f (configuration coordinate n factory native) (K.environment coordinate n factory native)
  intro receiver current supplied
  exact (raw_environment_congr (source_reader coordinate n factory native receiver supplied)).trans
    (source_environment coordinate n factory native (A.epoch receiver) supplied)

theorem input_environment : (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input
    (material coordinate n factory native)).environment = (material coordinate n factory native).environment :=
  (MR.updated_environment_source f (configuration coordinate n factory native)).trans
    ((after_environment coordinate n factory native).trans (material_environment coordinate n factory native).symm)

def write (value : PairValue V ()) : Env (PairValue V) C.Var := fun target _ => by cases target; exact value
abbrev born := WB.born f (configuration coordinate n factory native) (write factory native)

theorem actual_born_write : SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.At
    (born coordinate n factory native)
    (write factory native ((material coordinate n factory native).raw.eval
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material coordinate n factory native)).environment)) :=
  WB.configured_actual_paid_pair_writeback f (configuration coordinate n factory native) (write factory native)

theorem born_value : (born coordinate n factory native).activeEnvironment () () = (result coordinate n factory native).2.2.1 := by
  have written := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment.active (actual_born_write coordinate n factory native)
  have read := congrArg (fun environment : Env (PairValue V) C.Var => environment () ()) written
  have paid : (material coordinate n factory native).raw.eval
      (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.input (material coordinate n factory native)).environment =
        (result coordinate n factory native).2.2.1 :=
    (congrArg (Expr.eval (material coordinate n factory native).raw) (input_environment coordinate n factory native)).trans
      (MR.value_source f (configuration coordinate n factory native)).symm
  exact read.trans paid

def value : BurnolL2 := K.total (grade+1) ((born coordinate n factory native).activeEnvironment () ())

theorem value_source : value coordinate n factory native = Math.action (K.decodedTotal coordinate n factory native) :=
  (congrArg (K.total (grade+1)) (born_value coordinate n factory native)).trans
    ((congrArg (K.total (grade+1)) (actual_equation coordinate n factory native)).trans
      (Program.code_total coordinate n grade (K.environment coordinate n factory native)))

theorem source_trace : SourceGeneratedInquiryReceiptAction.Configured.lowStock f (configuration coordinate n factory native) =
    SourceOperationPaidRelations.exposure (material coordinate n factory native).state.2 ∧
    type_of% (MR.state_source f (configuration coordinate n factory native)) :=
  ⟨rfl, MR.state_source f (configuration coordinate n factory native)⟩

theorem born_inventory : type_of% (SourceGeneratedInquiryReceiptAction.Configured.Writeback.born_inventory
    f (configuration coordinate n factory native) (write factory native)) :=
  SourceGeneratedInquiryReceiptAction.Configured.Writeback.born_inventory f (configuration coordinate n factory native) (write factory native)

theorem actual_receipt_next : type_of% (SourceGeneratedInquiryReceiptAction.Configured.Writeback.actual_receipt_next
    f (configuration coordinate n factory native) (write factory native)) :=
  SourceGeneratedInquiryReceiptAction.Configured.Writeback.actual_receipt_next f (configuration coordinate n factory native) (write factory native)

theorem whole_first : type_of% (WB.source_whole f (configuration coordinate n factory native) (write factory native)) :=
  WB.source_whole f (configuration coordinate n factory native) (write factory native)

theorem generated_next : type_of% (WB.source_target_next f (configuration coordinate n factory native) (write factory native)) :=
  WB.source_target_next f (configuration coordinate n factory native) (write factory native)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PrimeThreeWholeSource.Install
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
