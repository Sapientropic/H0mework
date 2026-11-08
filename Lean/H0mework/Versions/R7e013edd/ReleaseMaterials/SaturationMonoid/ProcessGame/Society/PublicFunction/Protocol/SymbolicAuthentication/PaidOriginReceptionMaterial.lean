import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginQueueChecks
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 80000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginReceptionMaterial
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedDispatchTrace PaidOriginQueueMemo PaidOriginQueueChecks

@[irreducible] def packetCheck (point : Cursor DispatchWindowSource.code) : Bool :=
 let wire := wireAt point
 decide (wire.serial = 7 ∧ wire.sendCut = 84 ∧ wire.ballot.cut = 76 ∧ wire.ballot.actor = false ∧
  wire.ballot.scope = RenewedDispatchSource.scope point ∧
  decide (wire ∈ CachedWorkDispatch.wires (RenewedDispatchSource.vocabulary point) (traceAt point).rows) = true)

theorem packet_source_checked : packetCheck point = true :=
 (congrArg packetCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)


@[irreducible] def contextCheck (point : Cursor DispatchWindowSource.code) : Bool :=
 let wire := wireAt point
 let forged := {wire with ballot := {wire.ballot with actor := true}}
 let issued := CachedWorkDispatch.wires (RenewedDispatchSource.vocabulary point) (traceAt point).rows
 let receiver := RenewedDispatchSource.one point
 let compatible : StageReception.Law (PaidInvocationSource.code (RenewedDispatchSource.code point) contract) :=
  ⟨fun _ _ => RenewedDispatchSource.scope point,5⟩
 let short : StageReception.Law (PaidInvocationSource.code (RenewedDispatchSource.code point) contract) :=
  ⟨fun _ _ => RenewedDispatchSource.scope point,1⟩
 let relabelled : StageReception.Law (PaidInvocationSource.code (RenewedDispatchSource.code point) contract) :=
  ⟨fun _ _ => {RenewedDispatchSource.scope point with phase := (fundedAt point).cut},5⟩
 decide (
  PaidOriginHeader.checkIssued contract compatible issued receiver (secondAt point) [] wire = .accepted wire ∧
  PaidOriginHeader.checkIssued contract short issued receiver (secondAt point) [] wire = .rejected .late ∧
  PaidOriginHeader.checkIssued contract relabelled issued receiver (secondAt point) [] wire = .rejected .staleScope ∧
  PaidOriginHeader.checkIssued contract compatible issued receiver (firstAt point) [] wire = .rejected .missingDelivery ∧
  PaidOriginHeader.checkIssued contract compatible issued receiver (secondAt point) [(wire.ballot.cut,wire.ballot.position)] wire = .rejected .duplicate ∧
  PaidOriginHeader.checkIssued contract compatible issued receiver (secondAt point) [] forged = .rejected .unauthenticated ∧
  PaidOriginHeader.checkIssued contract compatible [] receiver (secondAt point) [] wire = .rejected .unauthenticated)

theorem context_source_checked : contextCheck point = true :=
 (congrArg contextCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)


@[irreducible] def initialAt (point : Cursor DispatchWindowSource.code) :=
 CachedWorkDispatch.run (RenewedDispatchSource.vocabulary point) (RenewedDispatchSource.law point)
  (traceAt point).rows (RenewedDispatchSource.one point) (traceAt point).rows.length

@[irreducible] def replayedAt (point : Cursor DispatchWindowSource.code) :=
 let law : StageReception.Law (PaidInvocationSource.code (RenewedDispatchSource.code point) contract) :=
  ⟨fun _ _ => RenewedDispatchSource.scope point,5⟩
 let issued := CachedWorkDispatch.wires (RenewedDispatchSource.vocabulary point) (traceAt point).rows
 let receiver := RenewedDispatchSource.one point
 PaidOriginHeader.receiveIssued contract law issued receiver 1 (secondAt point)
  (PaidOriginHeader.receiveIssued contract law issued receiver 0 (firstAt point) (initialAt point))

@[irreducible] def producedAt (point : Cursor DispatchWindowSource.code) : ProspectiveQuorum.Result :=
 let roster := ActorEnvelope.roster (RenewedDispatchSource.start point).source
 let affected := CachedWorkDispatch.affected (RenewedDispatchSource.vocabulary point)
  (RenewedDispatchSource.start point) (traceAt point).rows (RenewedDispatchSource.scope point)
 if ¬ roster.card+affected.card < 2+2 then .blocked .unsafeSourceBudget
 else match ActorQuorum.readout (replayedAt point) (RenewedDispatchSource.scope point) 2 with
  | .blocked => .blocked .missingQuorum
  | .decided value => .decided value


@[irreducible] def quorumCheck (point : Cursor DispatchWindowSource.code) : Bool :=
 decide ((initialAt point).receipts.length = 1 ∧
  ActorQuorum.readout (initialAt point) (RenewedDispatchSource.scope point) 2 = .blocked ∧
  (replayedAt point).receipts.length = 2 ∧
  ActorQuorum.support (replayedAt point) (RenewedDispatchSource.scope point) true = {false,true} ∧
  producedAt point = .decided true)

theorem quorum_source_checked : quorumCheck point = true :=
 (congrArg quorumCheck point_is_the_incrementally_computed_paid_successor).trans (by decide +kernel)


end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PaidOriginReceptionMaterial
