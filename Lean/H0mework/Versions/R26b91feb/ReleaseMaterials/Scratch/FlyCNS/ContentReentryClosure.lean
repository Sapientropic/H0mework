import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentReentryRoot
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.BodyFullClosure

/-! The independent observer consumes all 21 neural coordinates; the body
consumer consumes all 25 coordinates and the same emitted microtraces.
No closure verdict is accepted by source birth or its emitter. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace ContentReentryClosure

open ContentReentryIO ContentReentryRoot
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Canonical

def intervalBytes {material : Material} (current : Current material) (offset count : Nat)
    (bounded : offset + count ≤ 59) : Vector ByteArray count :=
  Vector.ofFn fun field => (wordAt material current.words ⟨offset + field.val, by omega⟩).bytes
def neuralRead {material : Material} (current : Current material) : Vector ByteArray 21 :=
  intervalBytes current 0 14 (by decide) ++ intervalBytes current 52 7 (by decide)

structure ObserverReport where
  neural : Vector ByteArray 21
  plastic : Vector ByteArray 8
  inputs : Vector ByteArray 4
  events : ByteArray
  learning : ByteArray
  deriving DecidableEq
structure ReceiverReport where
  body : Vector ByteArray 25
  physics : ByteArray
  neuralTick : Nat
  physicsTick : Nat
  deriving DecidableEq

variable {source : ContentReentryIO.Source} {current : Current source.material}

def observerRead (generated : GeneratedAt source current) : ObserverReport :=
  ⟨neuralRead generated.next, intervalBytes generated.next 43 8 (by decide),
    intervalBytes generated.next 39 4 (by decide), generated.reply.events, generated.reply.learning⟩
def receivedRead (generated : GeneratedAt source current) : ReceiverReport :=
  ⟨intervalBytes generated.next 14 25 (by decide), generated.reply.physics,
    generated.next.tick, physicsTick source.material generated.next.words⟩

structure ReopenedAt (generated : GeneratedAt source current) where
  private mk ::
  reopened : Current source.material
  image : capture reopened = capture generated.next
  continuation : GeneratedAt source generated.next
  fromReopened : GeneratedAt source reopened
  future : capture fromReopened.next = capture continuation.next
  events : fromReopened.reply.events = continuation.reply.events
  learning : fromReopened.reply.learning = continuation.reply.learning
  physics : fromReopened.reply.physics = continuation.reply.physics
def reopen (generated : GeneratedAt source current) : IO (ReopenedAt generated) := do
  let path := source.material.directory / ("closure-reopen-" ++ toString (← IO.monoNanosNow))
  writeCurrent generated.next path
  let reopened ← readCurrent source.material path
  if image : capture reopened = capture generated.next then
    let continuation ← emit source generated.next
    let fromReopened ← emit source reopened
    if future : capture fromReopened.next = capture continuation.next then
      if events : fromReopened.reply.events = continuation.reply.events then
        if learning : fromReopened.reply.learning = continuation.reply.learning then
          if physics : fromReopened.reply.physics = continuation.reply.physics then
            return ⟨reopened, image, continuation, fromReopened, future, events, learning, physics⟩
          else throw (IO.userError "the complete reopened physical microtrace differs")
        else throw (IO.userError "the complete reopened learning microtrace differs")
      else throw (IO.userError "the complete reopened neural events differ")
    else throw (IO.userError "the complete reopened 59-field next differs")
  else throw (IO.userError "the complete persistent source does not reopen")

structure IndependentRead where
  observer : ObserverReport
  receiver : ReceiverReport
structure AcceptedIndependentAt (generated : GeneratedAt source current) where
  private mk ::
  reference : Current source.material
  image : capture reference = capture generated.next
  read : IndependentRead
  observer_exact : observerRead generated = read.observer
  receiver_exact : receivedRead generated = read.receiver

def readIndependent (generated : GeneratedAt source current) : IO (AcceptedIndependentAt generated) := do
  let path := source.material.directory / ("independent-" ++ toString generated.next.visit)
  let reference ← readCurrent source.material path
  if image : capture reference = capture generated.next then
    let events ← IO.FS.readBinFile (path / "generated-events.npz")
    let learning ← IO.FS.readBinFile (path / "learning-trace.npz")
    let physics ← IO.FS.readBinFile (path / "physics-trace.npz")
    let read : IndependentRead :=
      ⟨⟨neuralRead reference, intervalBytes reference 43 8 (by decide), intervalBytes reference 39 4 (by decide), events, learning⟩,
        ⟨intervalBytes reference 14 25 (by decide), physics, reference.tick, physicsTick source.material reference.words⟩⟩
    if observer : observerRead generated = read.observer then
      if receiver : receivedRead generated = read.receiver then return ⟨reference, image, read, observer, receiver⟩
      else throw (IO.userError "the independent body/physics receiver differs")
    else throw (IO.userError "the independent complete 21-state neural observer differs")
  else throw (IO.userError "the independent complete word/backend/header/visit image differs")

def deltaAt (generated : GeneratedAt source current) (site : Fin PlasticAdmission.sourceSites) : Int :=
  BodyFullIO.signedWord ((wordAt source.material generated.next.words ⟨47, by decide⟩).vector.word site.val)
def siteEdge (source : ContentReentryIO.Source) (site : Fin PlasticAdmission.sourceSites) : Fin Admission.edgeCount :=
  ⟨source.material.sites.word site.val, source.material.site_bounds site⟩
def originalWeight (generated : GeneratedAt source current) (site : Fin PlasticAdmission.sourceSites) : Int :=
  let graph := source.material.graph.graph.rawGraph
  let edge := siteEdge source site
  graph.transmitterSign (graph.pre edge) * (275 * Int.ofNat (graph.contacts edge) + deltaAt generated site)
theorem original_edge_writeback (generated : GeneratedAt source current) (site : Fin PlasticAdmission.sourceSites) :
    originalWeight generated site =
      275 * Int.ofNat (source.material.graph.graph.rawGraph.contacts (siteEdge source site)) + deltaAt generated site := by
  unfold originalWeight
  have positive := source.material.site_positive site
  change source.material.graph.graph.rawGraph.transmitterSign
    (source.material.graph.graph.rawGraph.pre (siteEdge source site)) = 1 at positive
  simp [positive]
def NeuralReceptionAt (generated : GeneratedAt source current) : Prop :=
  (∃ side : Fin 2, BodyFullClosure.PositiveFiniteTrace ((wordAt source.material generated.next.words ⟨25, by decide⟩).vector.word side.val)) ∨
  (∃ side : Fin 2, BodyFullClosure.PositiveFiniteTrace ((wordAt source.material generated.next.words ⟨26, by decide⟩).vector.word side.val)) ∨
  BodyFullClosure.PositiveFiniteTrace ((wordAt source.material generated.next.words ⟨27, by decide⟩).vector.word 0)
instance (generated : GeneratedAt source current) : Decidable (NeuralReceptionAt generated) := by
  unfold NeuralReceptionAt
  infer_instance

structure AcquiredAt (generated : GeneratedAt source current) where
  private mk ::
  independent : AcceptedIndependentAt generated
  reopened : ReopenedAt generated
  site : Fin PlasticAdmission.sourceSites
  nonzero : deltaAt generated site ≠ 0
  reception : NeuralReceptionAt generated
  neural : BodyFullIO.operationAt current.visit = .neural
def acquire (generated : GeneratedAt source current) : IO (AcquiredAt generated) := do
  if neural : BodyFullIO.operationAt current.visit = .neural then
    if reception : NeuralReceptionAt generated then
      let site := (List.finRange PlasticAdmission.sourceSites).findSome? fun site =>
        if changed : deltaAt generated site ≠ 0 then some (⟨site, changed⟩ : {site // deltaAt generated site ≠ 0}) else none
      match site with
      | none => throw (IO.userError "the actual source has not generated a persistent original-edge trace")
      | some site => return ⟨← readIndependent generated, ← reopen generated, site.val, site.property, reception, neural⟩
    else throw (IO.userError "passive physical settling does not discharge actual neural reception")
  else throw (IO.userError "a gate-only operation cannot discharge neural closure")

/-- Consume the two already occurred following operations. These are
source-owned record readouts, so decoding the same current does not repeat
the neural or physical generation. -/
def reopenRecorded (generated : GeneratedAt source current) :
    IO (ReopenedAt generated) := do
  let path := source.material.directory / ("recorded-reopen-" ++ toString (← IO.monoNanosNow))
  writeCurrent generated.next path
  let reopened ← readCurrent source.material path
  if image : capture reopened = capture generated.next then
    let continuation ← readImplementation source generated.next
    let fromReopened ← readImplementationReopened source reopened
    if future : capture fromReopened.next = capture continuation.next then
      if events : fromReopened.reply.events = continuation.reply.events then
        if learning : fromReopened.reply.learning = continuation.reply.learning then
          if physics : fromReopened.reply.physics = continuation.reply.physics then
            return ⟨reopened, image, continuation, fromReopened, future, events, learning, physics⟩
          else throw (IO.userError "recorded physical followings differ")
        else throw (IO.userError "recorded learning followings differ")
      else throw (IO.userError "recorded neural followings differ")
    else throw (IO.userError "recorded complete source followings differ")
  else throw (IO.userError "recorded latest current does not reopen completely")

def acquireRecorded (generated : GeneratedAt source current) :
    IO (AcquiredAt generated) := do
  if neural : BodyFullIO.operationAt current.visit = .neural then
    if reception : NeuralReceptionAt generated then
      let site := (List.finRange PlasticAdmission.sourceSites).findSome? fun site =>
        if changed : deltaAt generated site ≠ 0 then some (⟨site, changed⟩ : {site // deltaAt generated site ≠ 0}) else none
      match site with
      | none => throw (IO.userError "the recorded source has no persistent original-edge trace")
      | some site => return ⟨← readIndependent generated, ← reopenRecorded generated,
          site.val, site.property, reception, neural⟩
    else throw (IO.userError "recorded neural reception is absent")
  else throw (IO.userError "recorded gate operation cannot discharge neural closure")

structure PresentationAt (generated : GeneratedAt source current) where
  observer : ObserverReport
  receiver : ReceiverReport
def witness (generated : GeneratedAt source current) : PresentationAt generated := ⟨observerRead generated, receivedRead generated⟩
inductive Consumer | observer | receiver
def consumers (generated : GeneratedAt source current) : IndependentConsumerSystem (PresentationAt generated) where
  Consumer := Consumer
  Output := fun | .observer => ObserverReport | .receiver => ReceiverReport
  read := fun consumer presentation => match consumer with
    | .observer => presentation.observer | .receiver => presentation.receiver
  positive := ⟨.observer⟩
def closure (generated : GeneratedAt source current) (independent : AcceptedIndependentAt generated) :
    LivingClosureStructure (PresentationAt generated) where
  responsibility coordinate presentation := match coordinate with
    | .rootedSource => source.born.tick = 0 ∧ generated.occurrence.1 = current
    | .observerExperience => presentation.observer = independent.read.observer
    | .receivedActualEffect => presentation.receiver = independent.read.receiver
    | .reopenablePersistentTrace => Nonempty (ReopenedAt generated) ∧ ∃ site, deltaAt generated site ≠ 0
    | .recursiveSuccessorSelfWriteBack =>
        (∀ site, originalWeight generated site =
          275 * Int.ofNat (source.material.graph.graph.rawGraph.contacts
            (siteEdge source site)) + deltaAt generated site) ∧
        Nonempty (GeneratedAt source generated.next) ∧ NeuralReceptionAt generated
    | .generatedNext => target source generated.occurrence = generated.next ∧
        generated.next.visit = current.visit + 1 ∧
        generated.next.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks

theorem source_born_six (generated : GeneratedAt source current) (acquired : AcquiredAt generated) :
    SixPointLivingClosureAt (closure generated acquired.independent) (witness generated) where
  rootedSource := ⟨source.born_tick, actual_support source generated⟩
  observerExperience := acquired.independent.observer_exact
  receivedActualEffect := acquired.independent.receiver_exact
  reopenablePersistentTrace := ⟨⟨acquired.reopened⟩, acquired.site, acquired.nonzero⟩
  recursiveSuccessorSelfWriteBack := ⟨original_edge_writeback generated, ⟨acquired.reopened.continuation⟩, acquired.reception⟩
  generatedNext := ⟨actual_target source generated, generated.reply.next_visit, generated.reply.next_tick⟩
theorem anchor_exact (generated : GeneratedAt source current) (independent : AcceptedIndependentAt generated)
    (presentation : PresentationAt generated) :
    OperationalAnchorAt (closure generated independent) presentation ↔
      (consumers generated).Indistinguishable presentation (witness generated) := by
  constructor
  · rintro ⟨observer, receiver⟩ consumer
    cases consumer with
    | observer => exact observer.trans independent.observer_exact.symm
    | receiver => exact receiver.trans independent.receiver_exact.symm
  · intro reads
    exact ⟨(reads .observer).trans independent.observer_exact, (reads .receiver).trans independent.receiver_exact⟩
theorem kernel_stable (generated : GeneratedAt source current) (independent : AcceptedIndependentAt generated) :
    LivingClosureKernelStableAtWitness (consumers generated) (closure generated independent) (witness generated) := by
  intro coordinate presentation same
  cases coordinate with
  | rootedSource | reopenablePersistentTrace | recursiveSuccessorSelfWriteBack | generatedNext => exact Iff.rfl
  | observerExperience =>
    have equal : presentation.observer = observerRead generated := same .observer
    change (presentation.observer = independent.read.observer) ↔ (observerRead generated = independent.read.observer)
    rw [equal]
  | receivedActualEffect =>
    have equal : presentation.receiver = receivedRead generated := same .receiver
    change (presentation.receiver = independent.read.receiver) ↔ (receivedRead generated = independent.read.receiver)
    rw [equal]
theorem sixPoint_iff_canonical_read (generated : GeneratedAt source current)
    (acquired : AcquiredAt generated) (presentation : PresentationAt generated) :
    SixPointLivingClosureAt (closure generated acquired.independent) presentation ↔
      (consumers generated).canonicalRead presentation = (consumers generated).canonicalRead (witness generated) :=
  (OperationalLivingClassifierAt.mk (source_born_six generated acquired)
    (anchor_exact generated acquired.independent)).sixPoint_iff_canonicalRead_eq_of_kernelStable
      (kernel_stable generated acquired.independent) presentation

end ContentReentryClosure
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
