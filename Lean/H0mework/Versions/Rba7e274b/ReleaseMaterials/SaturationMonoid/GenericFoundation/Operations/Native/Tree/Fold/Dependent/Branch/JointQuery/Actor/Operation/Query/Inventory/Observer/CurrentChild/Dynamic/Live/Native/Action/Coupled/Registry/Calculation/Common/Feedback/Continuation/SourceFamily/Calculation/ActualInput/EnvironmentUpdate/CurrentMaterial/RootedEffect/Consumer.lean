import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Native.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Calculation.ActualInput.EnvironmentUpdate.CurrentMaterial.RootedEffect.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFamilyActualCurrentMaterialRootedEffect

section
open SourceOperationScalarInventoryLift
namespace RC
export ActualCofinalRootResidualConsumer
 (rootedRequest rootedMaterial rooted_material_source source material selected base)
end RC
namespace Native
export ActualCofinalSourceAction (sourceBorn packetTransport actual_next_packet)
end Native
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
end A
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)] {s : Sorts}
local instance canonicalGroups (n : Nat) (t : Sorts) : AddCommGroup (L.Value W n t) := L.groups W n t
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance requestGroups : (t : Sorts) → AddCommGroup
 (ActualCofinalNativeTower.NativeValue (P.queryFactory factory) initial sourceCfg language (ordinal+1) t) :=
 fun t => L.groups W (RC.source (P.queryFactory factory) initial sourceCfg language (ordinal+1)).1 t

private def packetValue (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :=
 packet.2.1.1.registered.input.expression.eval packet.2.1.1.registered.input.environment

private theorem packet_value_same {first second : AS.AdmissionPacket (W := W) (X := X) (s := s)}
 (same : first = second) : HEq (packetValue first) (packetValue second) := by cases same; rfl

private theorem packet_value_language {Y Z : Sorts → Type u} (same : Y = Z)
 (packet : AS.AdmissionPacket (W := W) (X := Y) (s := s)) :
 HEq (packetValue (Native.packetTransport same packet)) (packetValue packet) := by cases same; rfl

private theorem native_born_value (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 packetValue (Native.sourceBorn (P.queryFactory factory) packet) =
 (AN.paid (Native.selected (P.queryFactory factory) packet)).raw.effect
  (AN.paid (Native.selected (P.queryFactory factory) packet)).environment
  (AN.paid (Native.selected (P.queryFactory factory) packet)).increment := by
 have born := born_request_input (Native.selected (P.queryFactory factory) packet)
  (ActualCofinalSourceAction.nativePacket (P.queryFactory factory) packet).2.2.1
 change (B.born (Native.selected (P.queryFactory factory) packet)
  (ActualCofinalSourceAction.nativePacket (P.queryFactory factory) packet).2.2.1).registered.input.expression.eval
  (B.born (Native.selected (P.queryFactory factory) packet)
  (ActualCofinalSourceAction.nativePacket (P.queryFactory factory) packet).2.2.1).registered.input.environment = _
 rw [born.1, born.2]
 exact native_residual_effect factory packet

private theorem source_pair_effect (packet : AS.AdmissionPacket (W := W) (X := X) (s := s)) :
 (SourceOperationInquiry.Context.Installation.materialAt
  (A.epoch (Native.selected (P.queryFactory factory) packet))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
   (Native.selected (P.queryFactory factory) packet))).pair.2 =
 (AN.paid (Native.selected (P.queryFactory factory) packet)).raw.effect
 (AN.paid (Native.selected (P.queryFactory factory) packet)).environment
 (AN.paid (Native.selected (P.queryFactory factory) packet)).increment := by
 let frame := Native.selected (P.queryFactory factory) packet
 let supplied := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence frame
 have settling := (Native.receipt (P.queryFactory factory) packet).2.2.2
 have phase : frame.action.isLeft = true := congrArg Sum.isLeft settling
 have paired := P.reader_pair (A.epoch frame) supplied
 have environment := P.reader_paid_environment frame ((P.actual_action_isLeft frame).trans phase)
 have raw := SourceFamilyActualCurrentMaterialEnvironmentUpdate.reader_paid_raw frame supplied
 rw [environment, raw] at paired
 exact congrArg Prod.snd (paired.symm.trans (eval_liftExpr _ _ _))

theorem canonical_request_effect :
 HEq ((RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).expression.eval
  (RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).environment)
 ((RC.material (P.queryFactory factory) initial sourceCfg language ordinal).raw.effect
  (RC.material (P.queryFactory factory) initial sourceCfg language ordinal).environment
  (RC.material (P.queryFactory factory) initial sourceCfg language ordinal).increment) := by
 have source := RC.rooted_material_source (P.queryFactory factory) initial sourceCfg language ordinal
 have own : (RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).expression.eval
   (RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).environment =
   packetValue (RC.source (P.queryFactory factory) initial sourceCfg language (ordinal+1)) := by
  change (RC.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).raw.eval
   (RC.rootedMaterial (P.queryFactory factory) initial sourceCfg language ordinal).environment = _
  rw [source.1, source.2.1]
  rfl
 exact (heq_of_eq own).trans
  ((packet_value_same (Native.actual_next_packet (P.queryFactory factory) initial sourceCfg language ordinal)).trans
   ((packet_value_language (RC.source (P.queryFactory factory) initial sourceCfg language ordinal).2.2.2.down
     (Native.sourceBorn (P.queryFactory factory) (RC.source (P.queryFactory factory) initial sourceCfg language ordinal))).trans
    (heq_of_eq (native_born_value factory (RC.source (P.queryFactory factory) initial sourceCfg language ordinal)))))


theorem canonical_request_pair :
 HEq ((RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).expression.eval
  (RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).environment)
 (SourceOperationInquiry.Context.Installation.materialAt
  (A.epoch (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal))
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualOccurrence
   (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal))).pair.2 :=
 (canonical_request_effect factory initial sourceCfg language ordinal).trans
  (heq_of_eq (source_pair_effect factory
   (RC.source (P.queryFactory factory) initial sourceCfg language ordinal)).symm)
end

section
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation (authority)
end SO
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget (target_current targetAt)
end ST
namespace RC
export ActualCofinalRootResidualConsumer
 (generatedCurrent generated original_whole original_compiles actual_root_eliminate boundaryWord rooted_request_model)
end RC
namespace Future
export ActualCofinalCommonAction (projection actions model_fibre)
export ActualCofinalNativeTower (stageInventory NativeValue)
end Future
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ t, AddCommGroup (Value t)] {s : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := s))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := s))

structure BornWholeWrite where
 payment : SourceNativeRootDebtPaymentStepAt (Pay.debtCurrent (B.born frame cfg))
 actual_step : payment.step = Pay.debtStep (B.born frame cfg)
 same_ledger : type_of% (born_payment_ledger frame cfg)
 same_visit : type_of% (born_payment_visit frame cfg)
 entry : type_of% (born_payment_entry frame cfg)
 whole_destination : HEq payment.step.evolution
  ((born_whole_successor frame cfg).ledgerEvolution.destination (Pay.debtCurrent (B.born frame cfg)).entry).2
 authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
  (SO.root (B.born frame cfg) (AS.stockCfg cfg)) (SO.visit (B.born frame cfg) (AS.stockCfg cfg))
  (Pay.debtCurrent (B.born frame cfg)).entry
 source_environment : (B.born frame cfg).registered.input.environment = (N.input (AN.paid frame)).environment
 source_expression : (B.born frame cfg).registered.input.expression = N.expression (AN.paid frame)

def bornWholeWrite : BornWholeWrite frame cfg where
 payment := born_actual_payment frame cfg
 actual_step := born_payment_step frame cfg
 same_ledger := born_payment_ledger frame cfg
 same_visit := born_payment_visit frame cfg
 entry := born_payment_entry frame cfg
 whole_destination := born_payment_whole_destination frame cfg
 authority := (born_payment_entry frame cfg).symm ▸ SO.authority (B.born frame cfg) (AS.stockCfg cfg)
 source_environment := (born_request_input frame cfg).1
 source_expression := (born_request_input frame cfg).2

section Rooted
variable {W X : Sorts → Type u} [∀ t, AddCommGroup (W t)]
local instance writeGroups (grade : Nat) (t : Sorts) : AddCommGroup (L.Value W grade t) := L.groups W grade t
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (sourceCfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : sourceCfg.LowVar = X) (ordinal : Nat)
local instance rootedGroups : (t : Sorts) → AddCommGroup
 (Future.NativeValue (P.queryFactory factory) initial sourceCfg language (ordinal+1) t) :=
 fun t => L.groups W (RC.source (P.queryFactory factory) initial sourceCfg language (ordinal+1)).1 t

theorem canonical_born_current :
 SO.current (B.born (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
   (RC.base (P.queryFactory factory) initial sourceCfg language ordinal))
  (AS.stockCfg (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)) =
 RC.generatedCurrent (P.queryFactory factory) initial sourceCfg language ordinal := by
 symm
 exact congrArg (fun current =>
  (⟨(ST.targetAt (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
     (AS.stockCfg (RC.base (P.queryFactory factory) initial sourceCfg language ordinal))
     (ActualCofinalRootResidualConsumer.sourceEvent (P.queryFactory factory) initial sourceCfg language ordinal)).TargetN,
   current⟩ : AnyAuthoritativeRootCurrent.{u}))
  (ST.target_current (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
   (AS.stockCfg (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)) _)

structure RootedWholeEffect where
 write : BornWholeWrite (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
  (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)
 current : type_of% (canonical_born_current factory initial sourceCfg language ordinal)
 effect : type_of% (canonical_request_pair factory initial sourceCfg language ordinal)

def rootedWholeEffect : RootedWholeEffect factory initial sourceCfg language ordinal where
 write := bornWholeWrite (RC.selected (P.queryFactory factory) initial sourceCfg language ordinal)
  (RC.base (P.queryFactory factory) initial sourceCfg language ordinal)
 current := canonical_born_current factory initial sourceCfg language ordinal
 effect := canonical_request_pair factory initial sourceCfg language ordinal

def consume_rooted {Result : Sort v}
 (consumer : RootedWholeEffect factory initial sourceCfg language ordinal →
  type_of% (RC.rooted_request_model (P.queryFactory factory) initial sourceCfg language ordinal) →
  ((history : List PUnit.{u+1}) → (target : Nat) →
   Future.stageInventory (P.queryFactory factory) initial sourceCfg language target
    (SourceGeneratedActionWords.run (Future.actions (P.queryFactory factory) initial sourceCfg language) history
     (DFinsupp.single (ordinal+1) (Finsupp.single
      (RC.rootedRequest (P.queryFactory factory) initial sourceCfg language ordinal).expression 1))) =
   Future.stageInventory (P.queryFactory factory) initial sourceCfg language target
    (SourceGeneratedActionWords.run (Future.actions (P.queryFactory factory) initial sourceCfg language) history
     (DFinsupp.single (ordinal+1) (RC.boundaryWord (P.queryFactory factory) initial sourceCfg language ordinal)))) →
  type_of% (RC.original_compiles (P.queryFactory factory) initial sourceCfg language ordinal) →
  type_of% (RC.original_whole (P.queryFactory factory) initial sourceCfg language ordinal) → Result) : Result :=
 let original := ActualCofinalRootResidualConsumer.consume (P.queryFactory factory)
  initial sourceCfg language ordinal
 consumer (rootedWholeEffect factory initial sourceCfg language ordinal)
  original.2.1.down (fun history target =>
   (Future.model_fibre _ _ _ _ _ _).mp original.2.1.down history target)
  original.2.2.1.down original.2.2.2.down

end Rooted
end

end SourceFamilyActualCurrentMaterialRootedEffect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
