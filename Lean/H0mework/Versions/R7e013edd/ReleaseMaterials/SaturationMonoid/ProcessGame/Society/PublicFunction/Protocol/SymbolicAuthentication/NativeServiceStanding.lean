import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PrimitiveRecoverySource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceStanding

open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)

variable (past : JointResponse.Stages model) (worker : Fin model.source.code.sites)
structure Local : Prop where
  uniform : ∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker (PrimitiveRecoveryPair.signal model start past worker),
    WithdrawalState.request model state worker = PrimitiveRecoveryPair.request model start past worker
  member : model.source.code.siteParty worker ∈ Delegation.members model.scope.task
  capacity : 2 ≤ model.source.code.actionLimit
  activation : Event.activate worker ∈ model.source.code.eventAlphabet
  memory : model.source.code.memoryReady (PrimitiveRecoveryPair.signal model start past worker) = true
  requestSupported : PrimitiveRecoveryPair.request model start past worker ∈ model.source.code.actions
  reaffirmSupported : WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions

instance : Decidable (Local model start past worker) :=
  decidable_of_iff
    ((∀ state ∈ WithdrawalState.fibre model start (past.map Prod.fst) worker (PrimitiveRecoveryPair.signal model start past worker),
      WithdrawalState.request model state worker = PrimitiveRecoveryPair.request model start past worker) ∧
      model.source.code.siteParty worker ∈ Delegation.members model.scope.task ∧
      2 ≤ model.source.code.actionLimit ∧ Event.activate worker ∈ model.source.code.eventAlphabet ∧
      model.source.code.memoryReady (PrimitiveRecoveryPair.signal model start past worker) = true ∧
      PrimitiveRecoveryPair.request model start past worker ∈ model.source.code.actions ∧
      WithdrawalInquiry.reaffirm model worker ∈ model.source.code.actions)
    ⟨fun h => by rcases h with ⟨a,b,c,d,e,f,g⟩; exact ⟨a,b,c,d,e,f,g⟩,
      fun h => ⟨h.uniform,h.member,h.capacity,h.activation,h.memory,h.requestSupported,h.reaffirmSupported⟩⟩

abbrev Original := PrimitiveRecoverySource.Original model start past worker
abbrev current := PrimitiveRecoveryPair.current model start past

structure Standing (original : Original model start past worker) : Prop where
  support : Local model start past worker
  signature : model.source.code.law.Valid (current model start past).current (WithdrawalInquiry.reaffirm model worker)
  withdrawal : model.source.code.law.Valid (current model start past).current (PrimitiveRecoveryPair.request model start past worker)
  active : (current model start past).current.technology.holder.isSome = true ∨
    (current model start past).current.technology.offered.isSome = true
  old : original.position.ordinal < PrimitiveRecoverySource.cut model start past
  pending : (PrimitiveRecoverySource.before model start past worker original).isPending
    (PrimitiveRecoverySource.family model start past worker) (PrimitiveRecoverySource.inputs model start past worker) = true
  signer : model.source.code.siteParty worker = original.signer
    (PrimitiveRecoverySource.family model start past worker) (PrimitiveRecoverySource.inputs model start past worker)
  stale : PrimitiveRecoverySource.stale model start past worker original = true

instance (original : Original model start past worker) : Decidable (Standing model start past worker original) :=
  decidable_of_iff
    (Local model start past worker ∧
      model.source.code.law.Valid (current model start past).current (WithdrawalInquiry.reaffirm model worker) ∧
      model.source.code.law.Valid (current model start past).current (PrimitiveRecoveryPair.request model start past worker) ∧
      ((current model start past).current.technology.holder.isSome = true ∨
        (current model start past).current.technology.offered.isSome = true) ∧
      original.position.ordinal < PrimitiveRecoverySource.cut model start past ∧
      (PrimitiveRecoverySource.before model start past worker original).isPending
        (PrimitiveRecoverySource.family model start past worker) (PrimitiveRecoverySource.inputs model start past worker) = true ∧
      model.source.code.siteParty worker = original.signer
        (PrimitiveRecoverySource.family model start past worker) (PrimitiveRecoverySource.inputs model start past worker) ∧
      PrimitiveRecoverySource.stale model start past worker original = true)
    ⟨fun h => by rcases h with ⟨a,b,c,d,e,f,g,h⟩; exact ⟨a,b,c,d,e,f,g,h⟩,
      fun h => ⟨h.support,h.signature,h.withdrawal,h.active,h.old,h.pending,h.signer,h.stale⟩⟩

structure Offer where
  private mk ::
  original : Original model start past worker
  member : original ∈ PrimitiveRecoverySource.originals model start past worker
  standing : Standing model start past worker original

-- The material offer deliberately contains no owner slot, live fuel, Ready, receipt or terminal row.
def offer : Option (Offer model start past worker) :=
  (PrimitiveRecoverySource.originals model start past worker).attach.findSome? fun original =>
    if standing : Standing model start past worker original.val then some ⟨original.val, original.property, standing⟩ else none

variable (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem an_actual_offer_at_its_generated_owner_slot_produces_raw_admission
    (offered : Offer model start past worker)
    (unfinished : ¬ JointResponse.Clear model start vocabulary encoding law past)
    (communication : UnifiedResponse.Clear model start vocabulary encoding law past)
    (queue : JointResponse.queueClear model start past = true)
    (live : 0 < JointResponse.fuel model start past)
    (owned : Distributed.Recall.Information.Agency.ownerAt model.source.code (EventHistory.execute start past).ownerStart
      (current model start past).history.length = some worker) :
    (RawNativeService.produce model start past vocabulary encoding law).isSome = true := by
  have support := offered.standing.support
  have resources : PrimitiveRecoveryPair.Resources model start past worker :=
    ⟨support.uniform, support.member, support.capacity, support.activation, support.memory,
      support.requestSupported, support.reaffirmSupported, live, owned⟩
  have conditions : PrimitiveRecoverySource.Conditions model start past worker offered.original :=
    ⟨resources, offered.standing.signature, offered.standing.withdrawal, offered.standing.active,
      offered.standing.old, offered.standing.pending, offered.standing.signer, offered.standing.stale⟩
  have generated := PrimitiveRecoverySource.every_actual_primitive_claim_is_found model start past vocabulary encoding law
    unfinished communication queue worker offered.original offered.member conditions
  cases actual : PrimitiveRecoverySource.produce model start past vocabulary encoding law with
  | none => rw [actual] at generated; cases generated
  | some source => exact PrimitiveRecoverySource.actual_source_primitives_generate_raw_admission model start past vocabulary encoding law source

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeServiceStanding
