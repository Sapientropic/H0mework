import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Migration.Grant

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

structure ElectionImage (Party Port : Type) where
  period : Nat
  office : Port
  controller : Party
  exited : Bool
  deriving DecidableEq

def electionImage (event : Election.MandateEvent Nat Port Party) : ElectionImage Party Port :=
  ⟨event.period, event.officeSeed, event.controllerSeed, match event.disposition with | .continue => false | .exit => true⟩

structure GrantObligationImage (Party Port : Type) where
  admission : ElectionImage Party Port
  admittedBearer : Party
  admittedScope : Port
  content : ElectionImage Party Port
  residual : ElectionImage Party Port
  bearer : Party
  beneficiary : Port
  scope : Port
  lineage : Port × Party × Bool
  deriving DecidableEq

def grantObligationImage
    (obligation : AdmittedObligation (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port))) : GrantObligationImage Party Port :=
  ⟨electionImage obligation.admission.sourceEvent, obligation.admission.admittedBearer,
    obligation.admission.admittedScope, electionImage obligation.content, electionImage obligation.residual,
    obligation.bearer, obligation.beneficiary, obligation.scope,
    ⟨obligation.lineage.office, obligation.lineage.controller,
      match obligation.lineage.disposition with | .continue => false | .exit => true⟩⟩

structure ItemImage (Party Good Port Technology Instrument : Type) where
  index : Nat
  before : Identity.Snapshot Technology
  request : Request Party Good Port Technology Instrument
  deriving DecidableEq

variable (code : Code Party Good Port (Mandate.State Party Technology) Instrument)

def itemImage (item : ExecutionItem Party Good Port (Mandate.State Party Technology) Instrument) :
    ItemImage Party Good Port (Mandate.State Party Technology) Instrument :=
  ⟨item.index, Identity.snapshot code item.before, item.request⟩

omit [DecidableEq Port] [DecidableEq Technology] in
theorem itemImage_injective : Function.Injective (itemImage code) := by
  rintro ⟨firstIndex, firstBefore, firstRequest⟩ ⟨secondIndex, secondBefore, secondRequest⟩ same
  have index := congrArg ItemImage.index same
  have before := Identity.snapshot_injective code (congrArg ItemImage.before same)
  have request := congrArg ItemImage.request same
  dsimp only [itemImage] at index before request
  cases index; cases before; cases request; rfl

inductive GrantEvidenceImage (Party Good Port Technology Instrument : Type) where
  | command (visit birth acceptedIndex : Nat) (current : Identity.Snapshot (Mandate.State Party Technology))
      (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (item : ItemImage Party Good Port (Mandate.State Party Technology) Instrument)
      (operator : Party) (target : Mandate.State Party Technology) (command : Mandate.Command Party)
  | handoff (visit birth acceptedIndex : Nat) (current : Identity.Snapshot (Mandate.State Party Technology))
      (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (proposal acceptance : ItemImage Party Good Port (Mandate.State Party Technology) Instrument) (candidate : Party)
  | refused (visit birth acceptedIndex : Nat) (current : Identity.Snapshot (Mandate.State Party Technology))
      (word : RawEvent Party Good Port (Mandate.State Party Technology) Instrument)
      (item : ItemImage Party Good Port (Mandate.State Party Technology) Instrument)
      (operator : Party) (target : Mandate.State Party Technology) (command : Mandate.Command Party)
  deriving DecidableEq

def grantEvidenceImage {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope} :
    Mandate.Lifecycle.Observed.BoundaryEvidence base scope → GrantEvidenceImage Party Good Port Technology Instrument
  | .command visit birth accepted current word actual _ _ =>
      .command visit birth accepted (Identity.snapshot code current) word (itemImage code actual.item.val)
        actual.operator actual.target actual.command
  | .handoff visit birth accepted current word next _ =>
      .handoff visit birth accepted (Identity.snapshot code current) word (itemImage code next.proposal.item.val)
        (itemImage code next.acceptance.item.val) next.candidate
  | .refused visit birth accepted current word item operator target command _ _ _ _ _ _ =>
      .refused visit birth accepted (Identity.snapshot code current) word (itemImage code item.val) operator target command

def boundaryKind {V : Vocabulary} {obligation : AdmittedObligation V} {source : V.SourceEvent} :
    BoundaryDisposition V obligation source → LifecycleKind
  | .carry (.progressed ..) => .progressed
  | .carry (.progressedAndTransferred ..) => .progressedAndTransferred
  | .carry (.maintained ..) => .maintained
  | .carry (.deferred ..) => .deferred
  | .carry (.narrowed ..) => .narrowed
  | .carry (.transferred ..) => .transferred
  | .terminal (.final _) => .obligationTerminal
  | .terminal (.superseded _) => .superseded
  | .bearerRelease _ => .bearerRelease

structure GrantRecordImage (Party Good Port Technology Instrument : Type) where
  slot : Nat
  kind : LifecycleKind
  before : GrantObligationImage Party Port
  after : GrantObligationImage Party Port
  evidence : GrantEvidenceImage Party Good Port Technology Instrument
  deriving DecidableEq

variable {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {currentAt : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument}
  {wordAt : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
  {birth : Nat} {grant : Mandate.Grant base scope (currentAt birth) (wordAt birth)}

private def grantEffectImage (slot : Nat)
    (obligation : AdmittedObligation (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port)))
    (effect : Mandate.Lifecycle.Observed.BoundaryEvidence base scope ×
      BoundaryDisposition (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port)) obligation obligation.admission.sourceEvent ×
      AdmittedObligation (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port))) :
    GrantRecordImage Party Good Port Technology Instrument :=
  ⟨slot, boundaryKind effect.2.1, grantObligationImage obligation, grantObligationImage effect.2.2,
    grantEvidenceImage code effect.1⟩

def grantRecordImage (slot : Nat)
    {obligation : AdmittedObligation (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port))}
    (event : Mandate.Lifecycle.Observed.Event base scope currentAt wordAt birth grant obligation) :
    GrantRecordImage Party Good Port Technology Instrument :=
  grantEffectImage code slot obligation (Mandate.Lifecycle.Observed.effect event)

theorem grant_read_images_congr
    {otherCurrent : Nat → RawCurrent Party Good (Mandate.State Party Technology) Instrument}
    {otherWord : Nat → RawEvent Party Good Port (Mandate.State Party Technology) Instrument}
    {otherGrant : Mandate.Grant base scope (otherCurrent birth) (otherWord birth)}
    (sameIndex : otherGrant.acceptance.item.val.index = grant.acceptance.item.val.index)
    (obligation : AdmittedObligation (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port)))
    (oldOrigin : obligation = {Mandate.Lifecycle.original base scope currentAt wordAt birth grant with bearer := obligation.bearer})
    (newOrigin : obligation = {Mandate.Lifecycle.original base scope otherCurrent otherWord birth otherGrant with bearer := obligation.bearer})
    (visit slot : Nat) (sameCurrent : otherCurrent visit = currentAt visit) (sameWord : otherWord visit = wordAt visit)
    (oldItem : {item // item ∈ (Mandate.law base scope).rawItems (currentAt visit) (wordAt visit)})
    (newItem : {item // item ∈ (Mandate.law base scope).rawItems (otherCurrent visit) (otherWord visit)})
    (sameItem : newItem.val = oldItem.val) :
    (Mandate.Lifecycle.Observed.readEvent obligation newOrigin visit newItem).map (grantRecordImage code slot) =
      (Mandate.Lifecycle.Observed.readEvent obligation oldOrigin visit oldItem).map (grantRecordImage code slot) := by
  have effects := Mandate.Lifecycle.Observed.read_effect_congr sameIndex obligation oldOrigin newOrigin
    visit sameCurrent sameWord oldItem newItem sameItem
  cases oldRead : Mandate.Lifecycle.Observed.readEvent obligation oldOrigin visit oldItem <;>
    cases newRead : Mandate.Lifecycle.Observed.readEvent obligation newOrigin visit newItem <;>
    simp only [oldRead, newRead, Option.map_none, Option.map_some] at effects ⊢
  · cases effects
  · cases effects
  · exact congrArg (fun effect => some (grantEffectImage code slot obligation effect)) (Option.some.inj effects)

def grantRunImage {first last : ResponsibilityState (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port))} :
    (Mandate.Lifecycle.Observed.process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run first last →
    List (GrantRecordImage Party Good Port Technology Instrument)
  | .nil => []
  | .step _ (.admit impossible) => nomatch impossible
  | .step prior (.cross slot _ _ event) => grantRunImage prior ++ [grantRecordImage code slot.val event]
  | .step _ (.reopen _ _ _ impossible) => nomatch impossible

def grantHistoryImage (history : Mandate.Lifecycle.Observed.History base scope currentAt wordAt birth grant) :=
  grantRunImage code history.generated

private theorem boundaryKind_eq_event_kind {V : Vocabulary} (process : NativeResponsibilityProcess V)
    (state : ResponsibilityState V) (slot : Fin state.slots.length) (obligation : AdmittedObligation V)
    (present : state.slots.get slot = .live obligation) (event : process.BoundaryEvent obligation) :
    boundaryKind (process.boundaryDisposition event) =
      (NativeResponsibilityProcess.Edge.cross (P := process) slot obligation present event).lifecycleEvent.kind := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent]
  generalize process.boundaryDisposition event = disposition
  cases disposition with
  | carry carry => cases carry <;> rfl
  | terminal receipt => cases receipt <;> rfl
  | bearerRelease => rfl

/-- The image reads the actual dependent Run, including its boundary receipt. -/
theorem grant_run_records_every_native_event
    {first last : ResponsibilityState (Mandate.Lifecycle.vocabulary (Party := Party) (Port := Port))}
    (run : (Mandate.Lifecycle.Observed.process (base := base) (scope := scope) (currentAt := currentAt)
      (wordAt := wordAt) (birth := birth) (grant := grant)).Run first last) :
    (grantRunImage code run).map GrantRecordImage.kind = run.events.map LifecycleEvent.kind := by
  induction run with
  | nil => rfl
  | step prior edge ih =>
    cases edge with
    | admit impossible => exact nomatch impossible
    | reopen _ _ _ impossible => exact nomatch impossible
    | cross slot obligation present event =>
        simp only [grantRunImage, NativeResponsibilityProcess.Run.events, List.map_append, List.map_cons, List.map_nil, ih]
        exact congrArg (List.append _) (congrArg (fun kind => [kind]) (boundaryKind_eq_event_kind _ _ slot obligation present event))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
