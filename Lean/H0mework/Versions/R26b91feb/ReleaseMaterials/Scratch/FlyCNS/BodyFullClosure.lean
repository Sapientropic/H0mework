import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceBodyFullIO
import H0mework.Cognition.Selfhood.PointedClosure

/-! Source-born operational closure of one actual body IO boundary.  Observer
and receiver presentations concern the same occurrence, not the full history
of every biological tick.  Reopen and continuation are executed by this source;
their results are data, never initialization targets or six-point premises. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace BodyFullClosure

open BodyFullIO
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical

structure FullImage (count : Nat) where
  words : Vector ByteArray count
  backend : Vector ByteArray 4
  header : ByteArray
  visit : Nat
  deriving DecidableEq

def fullImage {material : Material} (current : Current material) : FullImage material.count :=
  ⟨current.words.map BodyIO.Word.bytes, current.backend, current.header, current.visit⟩

structure ObserverReport where
  neural : Vector ByteArray 14
  plastic : Vector ByteArray 8
  inputs : Vector ByteArray 4
  generatedEvents : ByteArray
  deriving DecidableEq

structure ReceivedEffectReport where
  body : Vector ByteArray 25
  world : Vector ByteArray 6
  neuralTick : Nat
  physicsTick : Nat
  deriving DecidableEq

variable {source : BodyFullIO.Source} {current : Current source.material}

def observerRead (generated : GeneratedAt source current) : ObserverReport :=
  ⟨intervalBytes source generated.next 0 14 (by decide),
    intervalBytes source generated.next 43 8 (by decide),
    intervalBytes source generated.next 39 4 (by decide), generated.reply.generatedEvents⟩

def receivedRead (generated : GeneratedAt source current) : ReceivedEffectReport :=
  ⟨intervalBytes source generated.next 14 25 (by decide),
    readCompleted source .world generated.next ⟨generated.reply.generatedEvents, generated.reply.learningTrace, generated.reply.physicsTrace⟩, generated.next.tick,
    BodyFullIO.physicsTick source.material generated.next.words⟩

/-- This producer really writes/reads and re-emits the same source current.
The private constructor prevents replacing execution with a caller receipt. -/
structure ReopenedAt (generated : GeneratedAt source current) where
  private mk ::
  reopened : Current source.material
  completeImage : fullImage reopened = fullImage generated.next
  continuation : GeneratedAt source generated.next
  fromReopened : GeneratedAt source reopened
  futureImage : fullImage fromReopened.next = fullImage continuation.next
  futureEvents : fromReopened.reply.generatedEvents = continuation.reply.generatedEvents

def reopen (generated : GeneratedAt source current) : IO (ReopenedAt generated) := do
  let nonce ← IO.monoNanosNow
  let path := source.material.directory / ("closure-reopen-" ++ toString nonce)
  BodyFullIO.writeCurrent source.material generated.next path
  let reopened ← BodyFullIO.readCurrent source.material path
  if same : fullImage reopened = fullImage generated.next then
    let continuation ← BodyFullIO.emitIO source generated.next
    let fromReopened ← BodyFullIO.emitIO source reopened
    if future : fullImage fromReopened.next = fullImage continuation.next then
      if events : fromReopened.reply.generatedEvents = continuation.reply.generatedEvents then
        return ⟨reopened, same, continuation, fromReopened, future, events⟩
      else throw (IO.userError "same-source reopened neural events differ")
    else throw (IO.userError "same-source reopened complete next differs")
  else throw (IO.userError "same-source complete persistent material did not reopen")

def persistentDelta (generated : GeneratedAt source current) (site : Fin PlasticAdmission.sourceSites) : Int :=
  deltaAt source generated.next site

/-- Original-edge address and weight come from the retained full CSR, while
the local delta is the actual returned Q20 coordinate. -/
def originalEdgeWriteBack (generated : GeneratedAt source current) : Prop :=
  ∀ site : Fin PlasticAdmission.sourceSites,
    originalWeight source generated.next (source.material.admitted.wiring.candidate.siteEdge site) =
      275 * Int.ofNat (source.material.admitted.base.graph.rawGraph.contacts
        (source.material.admitted.wiring.candidate.siteEdge site)) + persistentDelta generated site

theorem generated_original_edge_writeback (generated : GeneratedAt source current) :
    originalEdgeWriteBack generated := by
  intro site
  unfold originalWeight persistentDelta
  rw [source.material.admitted.wiring.candidate.site_inverse site]
  have positive := (source.material.admitted.wiring.rawWiring
    source.material.admitted.base.graph.originalSourceRow).site_positive site
  change source.material.admitted.base.graph.rawGraph.transmitterSign
    (source.material.admitted.base.graph.rawGraph.pre
      (source.material.admitted.wiring.candidate.siteEdge site)) = 1 at positive
  simp [positive]

/-- Raw independent consumer output.  It contains no closure verdict. -/
structure IndependentRead where
  observer : ObserverReport
  receiver : ReceivedEffectReport

structure PresentationAt (generated : GeneratedAt source current) where
  observer : ObserverReport
  receiver : ReceivedEffectReport

def witness (generated : GeneratedAt source current) : PresentationAt generated :=
  ⟨observerRead generated, receivedRead generated⟩

inductive Consumer where
  | observer
  | receiver
  deriving DecidableEq

def consumers (generated : GeneratedAt source current) : IndependentConsumerSystem (PresentationAt generated) where
  Consumer := Consumer
  Output := fun consumer => match consumer with
    | .observer => ObserverReport
    | .receiver => ReceivedEffectReport
  read := fun consumer presentation => match consumer with
    | .observer => presentation.observer
    | .receiver => presentation.receiver
  positive := ⟨.observer⟩

def ObserverContractAt (generated : GeneratedAt source current) (read : IndependentRead)
    (presentation : PresentationAt generated) : Prop :=
  presentation.observer = read.observer

def ReceiverContractAt (generated : GeneratedAt source current) (read : IndependentRead)
    (presentation : PresentationAt generated) : Prop :=
  presentation.receiver = read.receiver

structure AcceptedIndependentAt (generated : GeneratedAt source current) where
  private mk ::
  reference : Current source.material
  completeImage : fullImage reference = fullImage generated.next
  read : IndependentRead
  observer_exact : observerRead generated = read.observer
  receiver_exact : receivedRead generated = read.receiver

/-- This is a consumer comparison, not a source initialization premise. -/
def readIndependent (generated : GeneratedAt source current) : IO (AcceptedIndependentAt generated) := do
  let path := source.material.directory / ("independent-" ++ toString generated.next.visit)
  let reference ← BodyFullIO.readCurrent source.material path
  if complete : fullImage reference = fullImage generated.next then
    let events ← IO.FS.readBinFile (path / "generated-events.npz")
    let read : IndependentRead :=
      ⟨⟨intervalBytes source reference 0 14 (by decide), intervalBytes source reference 43 8 (by decide),
          intervalBytes source reference 39 4 (by decide), events⟩,
        ⟨intervalBytes source reference 14 25 (by decide), readCompleted source .world reference ⟨events, ByteArray.empty, ByteArray.empty⟩,
          reference.tick, BodyFullIO.physicsTick source.material reference.words⟩⟩
    if observer : observerRead generated = read.observer then
      if receiver : receivedRead generated = read.receiver then return ⟨reference, complete, read, observer, receiver⟩
      else throw (IO.userError "independent actual effect differs at the same source boundary")
    else throw (IO.userError "independent neural/input observer differs at the same source boundary")
  else throw (IO.userError "independent complete 52-word/backend/header/visit image differs")

/-- The installed receiver stores nonnegative binary64 traces. Magnitude,
sign and exponent are checked explicitly: signed zero and NaN cannot activate
the operational witness. -/
def PositiveFiniteTrace (word : Nat) : Prop :=
  word < 2 ^ 63 ∧ word % (2 ^ 63) ≠ 0 ∧ word / (2 ^ 52) % 2048 < 2047

instance (word : Nat) : Decidable (PositiveFiniteTrace word) := by
  unfold PositiveFiniteTrace
  infer_instance

def NeuralReceptionAt (generated : GeneratedAt source current) : Prop :=
  (∃ side : Fin 2, PositiveFiniteTrace ((requiredWord source.material generated.next.words ⟨25, by decide⟩).vector.word side.val)) ∨
  (∃ side : Fin 2, PositiveFiniteTrace ((requiredWord source.material generated.next.words ⟨26, by decide⟩).vector.word side.val)) ∨
  PositiveFiniteTrace ((requiredWord source.material generated.next.words ⟨27, by decide⟩).vector.word 0)

instance (generated : GeneratedAt source current) : Decidable (NeuralReceptionAt generated) := by
  unfold NeuralReceptionAt
  infer_instance

/-- A concrete original-edge trace coordinate, generated by the actual
source, selects the witness.  No closure bit is supplied to the emitter. -/
structure PersistentSiteAt (generated : GeneratedAt source current) where
  private mk ::
  site : Fin PlasticAdmission.sourceSites
  nonzero : persistentDelta generated site ≠ 0

def firstPersistentSite (generated : GeneratedAt source current) : Option (PersistentSiteAt generated) :=
  (List.finRange PlasticAdmission.sourceSites).findSome? fun site =>
    if active : persistentDelta generated site ≠ 0 then some ⟨site, active⟩ else none

structure AcquiredAt (generated : GeneratedAt source current) where
  private mk ::
  independent : AcceptedIndependentAt generated
  persisted : ReopenedAt generated
  site : PersistentSiteAt generated
  neuralReception : NeuralReceptionAt generated
  neuralOperation : operationAt current.visit = .neural

def acquire (generated : GeneratedAt source current) : IO (AcquiredAt generated) := do
  if neural : operationAt current.visit = .neural then
    if reception : NeuralReceptionAt generated then
      match firstPersistentSite generated with
      | none => throw (IO.userError "source has not generated an original-edge persistent trace")
      | some site =>
        let independent ← readIndependent generated
        let persisted ← reopen generated
        return ⟨independent, persisted, site, reception, neural⟩
    else throw (IO.userError "passive body/world settling does not discharge neural reception")
  else throw (IO.userError "a gate-only operation does not replace the actual neural living witness")

def RootedAt (generated : GeneratedAt source current) : Prop :=
  source.initial.tick = 0 ∧ generated.occurrence.1 = current

def PersistentTraceAt (generated : GeneratedAt source current) : Prop :=
  Nonempty (ReopenedAt generated) ∧ ∃ site, persistentDelta generated site ≠ 0

def RecursiveWriteBackAt (generated : GeneratedAt source current) : Prop :=
  originalEdgeWriteBack generated ∧ Nonempty (GeneratedAt source generated.next) ∧ NeuralReceptionAt generated

def NextAt (generated : GeneratedAt source current) : Prop :=
  BodyFullIO.target source generated.occurrence = generated.next ∧ generated.next.visit = current.visit + 1 ∧ generated.next.tick = current.tick + (operationAt current.visit).microTicks

def closure (generated : GeneratedAt source current) (independent : AcceptedIndependentAt generated) :
    LivingClosureStructure (PresentationAt generated) where
  responsibility coordinate presentation := match coordinate with
    | .rootedSource => RootedAt generated
    | .observerExperience => ObserverContractAt generated independent.read presentation
    | .receivedActualEffect => ReceiverContractAt generated independent.read presentation
    | .reopenablePersistentTrace => PersistentTraceAt generated
    | .recursiveSuccessorSelfWriteBack => RecursiveWriteBackAt generated
    | .generatedNext => NextAt generated

theorem source_born_witness_closure (generated : GeneratedAt source current) (acquired : AcquiredAt generated) :
    SixPointLivingClosureAt (closure generated acquired.independent) (witness generated) where
  rootedSource := ⟨source.initial_tick, BodyFullIO.actual_support source generated⟩
  observerExperience := acquired.independent.observer_exact
  receivedActualEffect := acquired.independent.receiver_exact
  reopenablePersistentTrace := ⟨⟨acquired.persisted⟩, acquired.site.site, acquired.site.nonzero⟩
  recursiveSuccessorSelfWriteBack :=
    ⟨generated_original_edge_writeback generated, ⟨acquired.persisted.continuation⟩, acquired.neuralReception⟩
  generatedNext := ⟨BodyFullIO.actual_target_is_generated_next source generated, BodyFullIO.actual_next_visit source generated, BodyFullIO.actual_next_clock source generated⟩

theorem operational_anchor_exact (generated : GeneratedAt source current) (independent : AcceptedIndependentAt generated)
    (presentation : PresentationAt generated) :
    OperationalAnchorAt (closure generated independent) presentation ↔
      (consumers generated).Indistinguishable presentation (witness generated) := by
  constructor
  · rintro ⟨observer, receiver⟩ consumer
    cases consumer with
    | observer => exact observer.trans independent.observer_exact.symm
    | receiver => exact receiver.trans independent.receiver_exact.symm
  · intro reads
    exact ⟨(reads .observer).trans independent.observer_exact,
      (reads .receiver).trans independent.receiver_exact⟩

theorem kernel_stable (generated : GeneratedAt source current) (independent : AcceptedIndependentAt generated) :
    LivingClosureKernelStableAtWitness (consumers generated) (closure generated independent) (witness generated) := by
  intro coordinate presentation same
  cases coordinate with
  | rootedSource | reopenablePersistentTrace | recursiveSuccessorSelfWriteBack | generatedNext => exact Iff.rfl
  | observerExperience =>
    change (presentation.observer = independent.read.observer) ↔
      (observerRead generated = independent.read.observer)
    have equal : presentation.observer = observerRead generated := same .observer
    rw [equal]
  | receivedActualEffect =>
    change (presentation.receiver = independent.read.receiver) ↔
      (receivedRead generated = independent.read.receiver)
    have equal : presentation.receiver = receivedRead generated := same .receiver
    rw [equal]

theorem classifier (generated : GeneratedAt source current) (acquired : AcquiredAt generated) :
    OperationalLivingClassifierAt (consumers generated) (closure generated acquired.independent) (witness generated) where
  witnessClosure := source_born_witness_closure generated acquired
  anchorExact := operational_anchor_exact generated acquired.independent

theorem same_occurrence_sixPoint_iff_canonical_read (generated : GeneratedAt source current)
    (acquired : AcquiredAt generated) (presentation : PresentationAt generated) :
    SixPointLivingClosureAt (closure generated acquired.independent) presentation ↔
      (consumers generated).canonicalRead presentation = (consumers generated).canonicalRead (witness generated) :=
  (classifier generated acquired).sixPoint_iff_canonicalRead_eq_of_kernelStable
    (kernel_stable generated acquired.independent) presentation

end BodyFullClosure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
