import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentReentryIO

/-! The reentered implementation applies the unchanged native source law to
the complete latest Current. All six original responsibility names, physical
source identity and registered visit continue into the same generated next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace ContentReentryRoot

open ContentReentryIO
abbrev Responsibility := Fin 6

inductive CycleAt (source : ContentReentryIO.Source) (current : Current source.material)
  | ready
  | completed (reply : Reply source current)
def CycleAt.next {source : ContentReentryIO.Source} {current : Current source.material} :
    CycleAt source current → Current source.material
  | .ready => current | .completed reply => reply.after

def network (source : ContentReentryIO.Source) : WorldRelationNetwork where
  Support := Current source.material
  Anchor := String
  Incidence := Nat
  Lineage := String
  Responsibility := Responsibility
  Claim := Responsibility
  anchorAt := fun _ => source.material.instanceId
  incidenceAt := Current.visit
  lineageAt := fun _ => source.material.instanceId
  OpenAt := fun _ _ => Unit
  openClaimAt := fun {_support} {responsibility} _ => responsibility
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun current _ => CycleAt source current

def vocabulary (source : ContentReentryIO.Source) : Vocabulary where
  Current := Current source.material
  Anchor := String
  Incidence := Nat
  Lineage := String
  anchorAt := fun _ => source.material.instanceId
  incidenceAt := Current.visit
  lineageAt := fun _ => source.material.instanceId
  NativeWriteAt := CycleAt source
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := CycleAt.next
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

variable (source : ContentReentryIO.Source)

def entry (current : Current source.material) (responsibility : Responsibility) :
    OpenResponsibilityAt (network source) current := ⟨responsibility, ()⟩
def inventory (current : Current source.material) :
    ConstructivePresentation Responsibility (OpenResponsibilityAt (network source) current) where
  forward := entry source current
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl

inductive EventAt : Current source.material → Current source.material → Type
  | ready (current : Current source.material) : EventAt current current
  | completed (current : Current source.material) (reply : Reply source current) : EventAt current current
def eventCycle {current support : Current source.material} (event : EventAt source current support) :
    CycleAt source current := by
  cases event with
  | ready => exact .ready
  | completed reply => exact .completed reply

def eventLaw : SourceNativeEventAlgebra (network source) (vocabulary source) where
  EventAt := EventAt source
  compile := fun {_current} {_support} event => .nativeWrite (eventCycle source event)
  AffectedInventoryAt := fun _ => Responsibility
  affectedInventoryPresentation := fun {_current} {_support} _ => inventory source _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => by cases event <;> rfl
  lineage_commutes := fun _ => rfl
def nativeSource : SourceNativeSource (network source) (vocabulary source) where
  initial := source.initial
  law := eventLaw source
def readyOccurrence (current : Current source.material) :
    (nativeSource source).toRootSource.actual.OccurrenceAt current := ⟨current, .ready current⟩
def completedOccurrence (current : Current source.material) (reply : Reply source current) :
    (nativeSource source).toRootSource.actual.OccurrenceAt current := ⟨current, .completed current reply⟩
def target {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) : Current source.material :=
  (eventCycle source occurrence.2).next

structure ExactRowAt {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current)
    {destination : Current source.material}
    (old : OpenResponsibilityAt (network source) occurrence.1)
    (new : OpenResponsibilityAt (network source) destination) : Type where
  target_eq : destination = target source occurrence
  responsibility_eq : old.1 = new.1
def writeRowSource : LedgerWriteRowSourceAt (nativeSource source) (ExactRowAt source) where
  IncidenceOccurrenceAt := ExactRowAt source
  compileEvolution := fun {_current} {_occurrence} {_target} {_old} {_new} exact => by
    cases _occurrence with
    | mk support event =>
      cases event with
      | ready => exact .transferred .ready rfl exact.responsibility_eq (Nat.le_refl _)
      | completed reply => exact .transferred (.completed reply) rfl exact.responsibility_eq (Nat.le_refl _)
  compileExact := id
def completePatch {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource source) occurrence ⟨target source occurrence⟩ :=
  .complete
    { size := 6
      sourceEntryAt := entry source occurrence.1
      targetEntryAt := entry source (target source occurrence)
      rowAt := fun responsibility => (writeRowSource source).generate ⟨rfl, rfl⟩ }
    { destinationIndex := Sigma.fst
      originIndex := Sigma.fst
      destination_sound := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl
      origin_sound := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl }
def ledgerCompiler : SourceNativeLedgerCompiler (nativeSource source) where
  IncidenceTransitionAt := fun {_current} _ (old : Nat) (new : Nat) => PLift (old ≤ new)
  ExactTransitionAt := ExactRowAt source
  exact_incidence := fun {_current} {_occurrence} {_target} {_old} {_new} exact => by
    refine ⟨?_⟩
    change _occurrence.1.visit ≤ _target.visit
    rw [exact.target_eq]
    cases _occurrence with
    | mk support event =>
      cases event with
      | ready => exact Nat.le_refl _
      | completed reply =>
        change _current.visit ≤ reply.after.visit
        rw [reply.next_visit]
        exact Nat.le_succ _
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource source
  terminalRowSource := LedgerTerminalRowSourceAt.empty (nativeSource source)
  compile := fun {current} occurrence => by
    cases occurrence with
    | mk support event =>
      cases event with
      | ready =>
        exact .nativeWrite .ready rfl (readyOccurrence source current)
          (completePatch source (readyOccurrence source current)).toLedgerWriteEvolution
      | completed reply =>
        exact .nativeWrite (.completed reply) rfl (readyOccurrence source reply.after)
          (completePatch source (completedOccurrence source current reply)).toLedgerWriteEvolution
  compilePatch := fun {current} occurrence => by
    cases occurrence with
    | mk support event =>
      cases event with
      | ready => exact ⟨completePatch source (readyOccurrence source current), rfl⟩
      | completed reply => exact ⟨completePatch source (completedOccurrence source current reply), rfl⟩

structure GeneratedAt (current : Current source.material) where
  private mk ::
  reply : Reply source current
def GeneratedAt.occurrence {current : Current source.material} (generated : GeneratedAt source current) :=
  completedOccurrence source current generated.reply
def GeneratedAt.patch {current : Current source.material} (generated : GeneratedAt source current) :=
  completePatch source generated.occurrence
def GeneratedAt.ledger {current : Current source.material} (generated : GeneratedAt source current) :=
  (ledgerCompiler source).compile generated.occurrence
def GeneratedAt.next {current : Current source.material} (generated : GeneratedAt source current) := generated.reply.after
def emit (current : Current source.material) : IO (GeneratedAt source current) := do
  return ⟨← invoke source current⟩

/-- Same original occurrence and six-row compiler consume the internally
generated pure numerical successor; no after or evaluator is supplied. -/
def emitPure (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) : IO (GeneratedAt source current) := do
  return ⟨← ContentReentryIO.replyPure source installed current⟩

def readRegistered (current : Current source.material) : IO (GeneratedAt source current) := do
  return ⟨← ContentReentryIO.readOriginalReply source current⟩

def readImplementation (current : Current source.material) :
    IO (GeneratedAt source current) := do
  return ⟨← ContentReentryIO.readImplementationReply source current⟩

def readImplementationReopened (current : Current source.material) :
    IO (GeneratedAt source current) := do
  return ⟨← ContentReentryIO.readImplementationReply source current true⟩

theorem actual_support {current : Current source.material} (generated : GeneratedAt source current) :
    generated.occurrence.1 = current := rfl
theorem actual_target {current : Current source.material} (generated : GeneratedAt source current) :
    target source generated.occurrence = generated.next := rfl
theorem actual_six_rows {current : Current source.material} (generated : GeneratedAt source current)
    (responsibility : Responsibility) :
    (generated.patch.toLedgerWriteEvolution.destination (entry source current responsibility)).1 =
      entry source generated.next responsibility := rfl

structure PublishedAt (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) where
  private mk ::
  sourceReply : ContentReentryIO.PublishedReplyAt source installed current

def PublishedAt.original {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {current : Current source.material} (event : PublishedAt source installed current) : GeneratedAt source current :=
  ⟨event.sourceReply.reply⟩

def emitPublished (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) : IO (PublishedAt source installed current) := do
  return ⟨← ContentReentryIO.replyPublished source installed current⟩

theorem published_original_next {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {current : Current source.material} (event : PublishedAt source installed current) :
    event.original.next=event.sourceReply.reply.after := rfl

theorem published_all_original_rows {installed : _root_.FlyCNS.C3BoundKernel.Installation}
    {current : Current source.material} (event : PublishedAt source installed current) (r : Responsibility) :
    (event.original.patch.toLedgerWriteEvolution.destination (entry source current r)).1=
      entry source event.original.next r := actual_six_rows source event.original r

end ContentReentryRoot
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
