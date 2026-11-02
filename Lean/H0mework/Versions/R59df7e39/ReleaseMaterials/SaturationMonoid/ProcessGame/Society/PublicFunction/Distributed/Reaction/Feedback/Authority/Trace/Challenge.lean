import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Grant
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Migration.Challenge

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

structure PositionImage (Party Good Port Technology Instrument : Type) where
  origin : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  ordinal : Nat
  item : ItemImage Party Good Port (Mandate.State Party Technology) Instrument
  deriving DecidableEq

structure ChallengeImage (Party Good Port Technology Instrument : Type) where
  position : PositionImage Party Good Port Technology Instrument
  actor : Identity.ActorImage Party Good Port (Mandate.State Party Technology) Instrument
  deriving DecidableEq

structure TaskImage (Party Good : Type) where
  slots : List (Party × Bundle Good × Use)
  earliest : ℚ
  deadline : ℚ
  deriving DecidableEq

def taskImage (task : PublicTaskSpec Party Good) : TaskImage Party Good :=
  ⟨task.slots.map (fun slot => (slot.bearer, slot.goods, slot.purpose)), task.earliest, task.deadline⟩

structure ScopeBoundaryImage (Party Good Port Technology Instrument : Type) where
  task : TaskImage Party Good
  service : Port
  challenge : Port
  revisionCost : Bundle Good
  ordinal : Nat
  initial : Identity.Snapshot (Mandate.State Party Technology)
  words : List (RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
  current : Identity.Snapshot (Mandate.State Party Technology)
  item : ItemImage Party Good Port (Mandate.State Party Technology) Instrument
  command : Mandate.Command Party
  accepted : Bool
  deriving DecidableEq

inductive ChallengeEventImage (Party Good Port Technology Instrument : Type) where
  | birth (claim : ChallengeImage Party Good Port Technology Instrument)
  | reaffirm (isLocal : Bool) (original previous next : ChallengeImage Party Good Port Technology Instrument)
  | attempt (isLocal : Bool) (original target : ChallengeImage Party Good Port Technology Instrument)
      (receipt : PositionImage Party Good Port Technology Instrument) (accepted : Bool)
  | scopeBoundary (original : ChallengeImage Party Good Port Technology Instrument)
      (receipt : ScopeBoundaryImage Party Good Port Technology Instrument)
  deriving DecidableEq

structure ChallengeObligationImage (Party Good Port Technology Instrument : Type) where
  admission : ChallengeEventImage Party Good Port Technology Instrument
  admittedBearer : Identity.ActorImage Party Good Port (Mandate.State Party Technology) Instrument
  admittedScope : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  content : ChallengeImage Party Good Port Technology Instrument
  residual : Mandate.State Party Technology
  bearer : Identity.ActorImage Party Good Port (Mandate.State Party Technology) Instrument
  beneficiary : TaskImage Party Good
  scope : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  lineage : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  deriving DecidableEq

inductive ChallengeSlotImage (Party Good Port Technology Instrument : Type) where
  | live (obligation : ChallengeObligationImage Party Good Port Technology Instrument)
  | terminal (obligation : ChallengeObligationImage Party Good Port Technology Instrument)
      (source : ChallengeEventImage Party Good Port Technology Instrument)
  deriving DecidableEq

structure ChallengeRecordImage (Party Good Port Technology Instrument : Type) where
  slot : Nat
  kind : LifecycleKind
  before : Option (ChallengeSlotImage Party Good Port Technology Instrument)
  after : ChallengeSlotImage Party Good Port Technology Instrument
  source : ChallengeEventImage Party Good Port Technology Instrument
  deriving DecidableEq

structure ChallengeStateImage (Party Good Port Technology Instrument : Type) where
  slots : List (ChallengeSlotImage Party Good Port Technology Instrument)
  history : List (ChallengeRecordImage Party Good Port Technology Instrument)
  deriving DecidableEq

variable {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (family : ProgrammeFamily base scope Index)

def positionImage (input : Index) (position : Position family input) : PositionImage Party Good Port Technology Instrument :=
  ⟨Identity.originImage code (I family input) (position.origin family input), position.ordinal,
    itemImage code (position.item family input)⟩

def challengeImage (input : Index) (claim : Claim family input) : ChallengeImage Party Good Port Technology Instrument :=
  ⟨positionImage code family input claim.position, Identity.actorImage code (I family input) (claim.actor family input)⟩

def scopeBoundaryImage (source : ScopeBoundary.Source base) (receipt : ScopeBoundary.Receipt source) :
    ScopeBoundaryImage Party Good Port Technology Instrument :=
  ⟨taskImage source.scope.task, source.scope.service, source.scope.challenge, source.scope.revisionCost,
    receipt.ordinal source, Identity.snapshot code (ScopeBoundary.current source 0),
    (List.range (receipt.ordinal source + 1)).map (ScopeBoundary.wordAt source),
    Identity.snapshot code (ScopeBoundary.current source (receipt.ordinal source)),
    itemImage code (receipt.item source).val, receipt.command source, receipt.accepted source⟩

def challengeEventImage (input : Index) : Mandate.Challenge.Event family input → ChallengeEventImage Party Good Port Technology Instrument
  | .birth claim => .birth (challengeImage code family input claim)
  | .reaffirm original previous receipt =>
      .reaffirm true (challengeImage code family input original)
        (challengeImage code family input (previous.claim family input)) (challengeImage code family input receipt.target)
  | .attempt original target receipt =>
      .attempt true (challengeImage code family input original) (challengeImage code family input (target.claim family input))
        (positionImage code family input receipt.position)
        (decide ((Mandate.law base scope).Valid (receipt.position.item family input).before (receipt.position.item family input).request))
  | .remoteReaffirm original actual previous receipt =>
      .reaffirm false (challengeImage code family input original) (challengeImage code family actual previous.claim)
        (challengeImage code family actual receipt.claim)
  | .remoteAttempt original actual target receipt =>
      .attempt false (challengeImage code family input original) (challengeImage code family actual target.claim)
        (positionImage code family actual receipt.position)
        (decide ((Mandate.law base scope).Valid (receipt.position.item family actual).before (receipt.position.item family actual).request))
  | .scopeBoundary original source _ receipt =>
      .scopeBoundary (challengeImage code family input original) (scopeBoundaryImage code source receipt)

def challengeObligationImage (input : Index) (obligation : AdmittedObligation (V family input)) :
    ChallengeObligationImage Party Good Port Technology Instrument :=
  ⟨challengeEventImage code family input obligation.admission.sourceEvent,
    Identity.actorImage code (I family input) obligation.admission.admittedBearer,
    Identity.originImage code (I family input) obligation.admission.admittedScope,
    challengeImage code family input obligation.content, obligation.residual,
    Identity.actorImage code (I family input) obligation.bearer, taskImage obligation.beneficiary,
    Identity.originImage code (I family input) obligation.scope, Identity.originImage code (I family input) obligation.lineage⟩

def challengeSlotImage (input : Index) : ObligationSlot (V family input) → ChallengeSlotImage Party Good Port Technology Instrument
  | .live obligation => .live (challengeObligationImage code family input obligation)
  | .terminal archive => .terminal (challengeObligationImage code family input archive.obligation)
      (challengeEventImage code family input archive.sourceEvent)

def challengeRecordImage (input : Index) : LifecycleEvent (V family input) → ChallengeRecordImage Party Good Port Technology Instrument
  | .admitted slot payload => ⟨slot, .admitted, none, challengeSlotImage code family input (.live payload.toObligation),
      challengeEventImage code family input payload.sourceEvent⟩
  | .carried slot obligation source carry =>
      ⟨slot, (LifecycleEvent.carried slot obligation source carry).kind,
        some (challengeSlotImage code family input (.live obligation)),
        challengeSlotImage code family input (BoundaryDisposition.carry carry).targetSlot,
        challengeEventImage code family input source⟩
  | .terminal slot obligation source receipt =>
      ⟨slot, .obligationTerminal, some (challengeSlotImage code family input (.live obligation)),
        challengeSlotImage code family input (BoundaryDisposition.terminal (.final receipt)).targetSlot,
        challengeEventImage code family input source⟩
  | .superseded slot obligation source receipt =>
      ⟨slot, .superseded, some (challengeSlotImage code family input (.live obligation)),
        challengeSlotImage code family input (BoundaryDisposition.terminal (.superseded receipt)).targetSlot,
        challengeEventImage code family input source⟩
  | .bearerReleased slot obligation source receipt =>
      ⟨slot, .bearerRelease, some (challengeSlotImage code family input (.live obligation)),
        challengeSlotImage code family input (BoundaryDisposition.bearerRelease receipt).targetSlot,
        challengeEventImage code family input source⟩
  | .reopened slot archive payload =>
      ⟨slot, .reopened, some (challengeSlotImage code family input (.terminal archive)),
        challengeSlotImage code family input (.live payload.admission.toObligation),
        challengeEventImage code family input payload.sourceEvent⟩

def challengeStateImage (input : Index) (state : ResponsibilityState (V family input)) :
    ChallengeStateImage Party Good Port Technology Instrument :=
  ⟨state.slots.map (challengeSlotImage code family input), state.history.map (challengeRecordImage code family input)⟩

theorem challenge_records_every_native_event (input : Index) (state : ResponsibilityState (V family input)) :
    ((challengeStateImage code family input state).history.map ChallengeRecordImage.kind) = state.history.map LifecycleEvent.kind := by
  simp only [challengeStateImage, List.map_map]
  apply List.map_congr_left
  intro event _
  cases event with
  | carried _ _ _ carry => cases carry <;> rfl
  | admitted => rfl
  | terminal => rfl
  | superseded => rfl
  | bearerReleased => rfl
  | reopened => rfl

theorem equal_position_images_recover_the_actual_item (firstInput secondInput : Index)
    (first : Position family firstInput) (second : Position family secondInput)
    (same : positionImage code family secondInput second = positionImage code family firstInput first) :
    second.ordinal = first.ordinal ∧ second.item family secondInput = first.item family firstInput := by
  have items := congrArg PositionImage.item same
  refine ⟨congrArg PositionImage.ordinal same, ?_⟩
  exact itemImage_injective code items

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
