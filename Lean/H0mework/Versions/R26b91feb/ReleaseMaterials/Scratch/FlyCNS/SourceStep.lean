import H0mework.Versions.R2.Realization.Operations.ObservationNative

/-! A bounded source-native integer LIF producer. Source input is raw graph,
initial material and registered external pulses. The root compiler computes
the complete neural next; it does not accept a target snapshot. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

structure RawGraph (neurons edges : Nat) where
  bodyId : Fin neurons → Nat
  pre : Fin edges → Fin neurons
  post : Fin edges → Fin neurons
  contacts : Fin edges → Nat
  transmitterSign : Fin neurons → Int

structure BodyState where
  position : Int
  velocity : Int
  energy : Int
  deriving DecidableEq

structure WorldState where
  foodX : Int
  foodY : Int
  valueX : Int
  valueY : Int
  deriving DecidableEq

structure MaterialState (neurons edges : Nat) where
  membrane : Fin neurons → Int
  conductance : Fin neurons → Int
  refractory : Fin neurons → Nat
  delayQueue : Fin 2 → Fin neurons → Bool
  delayCursor : Fin 2
  weightDelta : Fin edges → Int
  eligibility : Fin edges → Int
  body : BodyState
  world : WorldState
  noiseState : Nat
  tick : Nat

abbrev RawPulse (neurons : Nat) := Fin neurons → Int

structure SourceSpec (neurons edges : Nat) where
  graph : RawGraph neurons edges
  initial : MaterialState neurons edges
  pulses : List (RawPulse neurons)

variable {neurons edges : Nat}

def pulseAt (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) : RawPulse neurons :=
  source.pulses[current.tick]?.getD (fun _ => 0)

def incoming (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) (neuron : Fin neurons) : Int :=
  ∑ edge : Fin edges,
    if source.graph.post edge = neuron ∧
        current.delayQueue current.delayCursor (source.graph.pre edge) = true then
      source.graph.transmitterSign (source.graph.pre edge) *
        (275 * Int.ofNat (source.graph.contacts edge) + current.weightDelta edge)
    else 0

def drivenMembrane (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) (neuron : Fin neurons) : Int :=
  current.membrane neuron + pulseAt source current neuron

def drivenConductance (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) (neuron : Fin neurons) : Int :=
  current.conductance neuron + incoming source current neuron

def integratedMembrane (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) (neuron : Fin neurons) : Int :=
  if current.refractory neuron = 0 then
    drivenMembrane source current neuron +
      Int.ediv (-52000 - drivenMembrane source current neuron +
        drivenConductance source current neuron) 20
  else drivenMembrane source current neuron

def decayedConductance (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) (neuron : Fin neurons) : Int :=
  if current.refractory neuron = 0 then
    let conductance := drivenConductance source current neuron
    if conductance ≥ 0 then Int.ediv (conductance * 4) 5
    else -Int.ediv (-conductance * 4) 5
  else drivenConductance source current neuron

def fired (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) (neuron : Fin neurons) : Bool :=
  decide (current.refractory neuron = 0 ∧
    integratedMembrane source current neuron > -45000)

def neuralStep (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) : MaterialState neurons edges where
  membrane := fun neuron =>
    if fired source current neuron then -52000
    else integratedMembrane source current neuron
  conductance := fun neuron =>
    if fired source current neuron then 0
    else decayedConductance source current neuron
  refractory := fun neuron =>
    if fired source current neuron then 3 else current.refractory neuron - 1
  delayQueue := fun slot neuron =>
    if slot = current.delayCursor then fired source current neuron
    else current.delayQueue slot neuron
  delayCursor := current.delayCursor + 1
  weightDelta := current.weightDelta
  eligibility := current.eligibility
  body := current.body
  world := current.world
  noiseState := current.noiseState
  tick := current.tick + 1

def initialState (neurons edges : Nat) (seed : Nat) : MaterialState neurons edges where
  membrane := fun _ => -52000
  conductance := fun _ => 0
  refractory := fun _ => 0
  delayQueue := fun _ _ => false
  delayCursor := 0
  weightDelta := fun _ => 0
  eligibility := fun _ => 0
  body := ⟨0, 0, 0⟩
  world := ⟨0, 0, 0, 0⟩
  noiseState := seed
  tick := 0

/-- The private singleton is the actual operation fixed by the source. Its
material next is computed by `neuralStep`, with no outcome field. -/
structure NeuralEventAt (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) where
  private mk ::

def NeuralEventAt.generate (source : SourceSpec neurons edges)
    (current : MaterialState neurons edges) : NeuralEventAt source current := ⟨⟩

def NeuralEventAt.materialNext {source : SourceSpec neurons edges}
    {current : MaterialState neurons edges} (_event : NeuralEventAt source current) :
    MaterialState neurons edges := neuralStep source current

/-- The ledger registers four neural-update responsibilities. Plasticity and
embodiment are retained state here and receive no completed consumer claim. -/
abbrev NeuralResponsibility := Fin 4

def neuralNetwork (source : SourceSpec neurons edges) : WorldRelationNetwork where
  Support := MaterialState neurons edges
  Anchor := Unit
  Incidence := Nat
  Lineage := Unit
  Responsibility := NeuralResponsibility
  Claim := NeuralResponsibility
  anchorAt := fun _ => ()
  incidenceAt := MaterialState.tick
  lineageAt := fun _ => ()
  OpenAt := fun _ _ => Unit
  openClaimAt := fun {_support} {responsibility} _ => responsibility
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun current _ => NeuralEventAt source current

def neuralVocabulary (source : SourceSpec neurons edges) : Vocabulary where
  Current := MaterialState neurons edges
  Anchor := Unit
  Incidence := Nat
  Lineage := Unit
  anchorAt := fun _ => ()
  incidenceAt := MaterialState.tick
  lineageAt := fun _ => ()
  NativeWriteAt := NeuralEventAt source
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := NeuralEventAt.materialNext
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

variable (source : SourceSpec neurons edges)

def entry (current : MaterialState neurons edges) (responsibility : NeuralResponsibility) :
    OpenResponsibilityAt (neuralNetwork source) current := ⟨responsibility, ()⟩

def inventoryPresentation (current : MaterialState neurons edges) :
    ConstructivePresentation NeuralResponsibility
      (OpenResponsibilityAt (neuralNetwork source) current) where
  forward := entry source current
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases receipt
    rfl

inductive SupportedNeuralEventAt : MaterialState neurons edges →
    MaterialState neurons edges → Type
  | emitted (current : MaterialState neurons edges) :
      SupportedNeuralEventAt current current

def neuralEventLaw : SourceNativeEventAlgebra (neuralNetwork source) (neuralVocabulary source) where
  EventAt := SupportedNeuralEventAt
  compile := fun {_current} {_support} event => by
    cases event
    exact .nativeWrite (.generate source _)
  AffectedInventoryAt := fun _ => NeuralResponsibility
  affectedInventoryPresentation := fun {_current} {_support} _ => inventoryPresentation source _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => by cases event; rfl
  lineage_commutes := fun _ => rfl

def nativeSource : SourceNativeSource (neuralNetwork source) (neuralVocabulary source) where
  initial := source.initial
  law := neuralEventLaw source

def emitted (current : MaterialState neurons edges) :
    (nativeSource source).toRootSource.actual.OccurrenceAt current :=
  ⟨current, .emitted current⟩

structure ExactNeuralRowAt
    {current : MaterialState neurons edges}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current)
    {targetSupport : MaterialState neurons edges}
    (oldEntry : OpenResponsibilityAt (neuralNetwork source) occurrence.1)
    (newEntry : OpenResponsibilityAt (neuralNetwork source) targetSupport) : Type where
  source_eq : occurrence.1 = current
  target_eq : targetSupport = neuralStep source current
  responsibility_eq : oldEntry.1 = newEntry.1

def writeRowSource : LedgerWriteRowSourceAt (nativeSource source) (ExactNeuralRowAt source) where
  IncidenceOccurrenceAt := ExactNeuralRowAt source
  compileEvolution := fun {_current} {_occurrence} {_target} {_old} {_new} event =>
    .transferred (.generate source _) rfl event.responsibility_eq (Nat.le_refl _)
  compileExact := id

def completePatch {current : MaterialState neurons edges}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource source) occurrence
      ⟨neuralStep source current⟩ :=
  .complete
    { size := 4
      sourceEntryAt := entry source occurrence.1
      targetEntryAt := entry source (neuralStep source current)
      rowAt := fun responsibility =>
        (writeRowSource source).generate
          ⟨by cases occurrence with
              | mk support event => cases event; rfl,
            rfl, rfl⟩ }
    { destinationIndex := Sigma.fst
      originIndex := Sigma.fst
      destination_sound := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl
      origin_sound := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl }

def ledgerCompiler : SourceNativeLedgerCompiler (nativeSource source) where
  IncidenceTransitionAt := fun {_current} _ (old : Nat) (new : Nat) => PLift (new = old + 1)
  ExactTransitionAt := ExactNeuralRowAt source
  exact_incidence := fun {_current} {_occurrence} {_target} {_old} {_new} exact =>
    ⟨by
      change _target.tick = _occurrence.1.tick + 1
      rw [exact.target_eq, exact.source_eq]
      rfl⟩
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource source
  terminalRowSource := LedgerTerminalRowSourceAt.empty (nativeSource source)
  compile := fun {current} occurrence => by
    cases occurrence with
    | mk support event =>
      cases event
      exact .nativeWrite (.generate source current) rfl (emitted source (neuralStep source current))
        (completePatch source (emitted source current)).toLedgerWriteEvolution
  compilePatch := fun {current} occurrence => by
    cases occurrence with
    | mk support event => cases event; exact ⟨completePatch source (emitted source current), rfl⟩

def restructuringLaw : SourceNativeLedgerRestructuringLaw (nativeSource source) :=
  identityOnlyWorldLedgerRestructuringLaw (nativeSource source) () (by
    intro _ _
    change Subsingleton Unit
    infer_instance)

def restructuringCertification {current : MaterialState neurons edges}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw source)
      ((ledgerCompiler source).compile occurrence) := by
  cases occurrence with
  | mk support event =>
    cases event
    apply ExactLedgerRestructuringCertificationAt.ofInjective
    · rintro ⟨left, leftReceipt⟩ ⟨right, rightReceipt⟩ same
      cases leftReceipt
      cases rightReceipt
      have sameResponsibility := congrArg Sigma.fst same
      change left = right at sameResponsibility
      cases sameResponsibility
      rfl
    · rintro ⟨left, leftReceipt⟩ ⟨right, rightReceipt⟩ same
      cases leftReceipt
      cases rightReceipt
      have sameResponsibility := congrArg Sigma.fst same
      change left = right at sameResponsibility
      cases sameResponsibility
      rfl

def restructuringSource :
    SourceNativeRestructuringLedgerSource (neuralNetwork source) (neuralVocabulary source) where
  source := nativeSource source
  compiler :=
    { ledgerCompiler := ledgerCompiler source
      restructuringLaw := restructuringLaw source
      certifyRestructuring := restructuringCertification source }

inductive NeuralFace where
  | before
  | fired
  | after
  deriving DecidableEq

def neuralProjectionLaw : SourceNativeProjectionLaw (restructuringSource source).toLedgerSource where
  Projection := NeuralFace
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun face {_} _ _ =>
    match face with
    | .before | .after => MaterialState neurons edges
    | .fired => Fin neurons → Bool
  project := fun face {current} _ _ =>
    match face with
    | .before => current
    | .after => neuralStep source current
    | .fired => fired source current

def authoritySource : SourceNativeAuthoritySource (neuralNetwork source) (neuralVocabulary source) where
  restructuringSource := restructuringSource source
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource source)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (neuralNetwork source)
  projectionLaw := neuralProjectionLaw source

def authoritativeRoot :
    SourceNativeAuthoritativeRootClosure (neuralNetwork source) (neuralVocabulary source) where
  source := authoritySource source
  emitted := emitted source
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure (neuralNetwork source) (neuralVocabulary source) :=
  (authoritativeRoot source).toLivingWithoutFaithfulTerminal (by
    intro _
    change IsEmpty PEmpty
    infer_instance)

abbrev Visit := RootVisit (livingRoot source).toAuthoritativeRoot.toRoot

def currentAt (visit : Visit source) : SourceNativeLivingRootCurrentAt (neuralNetwork source) :=
  ⟨neuralVocabulary source, livingRoot source, .finite visit⟩

theorem currentAt_injective : Function.Injective (currentAt source) := by
  intro left right same
  injection same with sameV sameRoot sameVisit
  cases left with
  | mk leftCurrent leftHistory =>
    cases right with
    | mk rightCurrent rightHistory =>
      have currentEq := congrArg SourceNativeTemporalVisitAt.current sameVisit
      cases currentEq
      injection sameVisit with currentAgain historyEq
      injection historyEq with exactHistoryEq
      cases exactHistoryEq
      rfl

def nextVisit (visit : Visit source) : Visit source := visit.next rfl

def process : SourceNativeLivingRootProcess (neuralNetwork source) where
  State := Visit source
  stateAt := currentAt source
  stateAt_injective := currentAt_injective source
  initial := (livingRoot source).toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨nextVisit source visit, rfl, by rfl⟩

def runtimeFacade : SourceNativeLivingRuntimeFacade (neuralNetwork source) where
  process := process source
  FaceAt := fun _ => NeuralFace
  componentAt := fun _ _ => neuralProjectionLaw source
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ face => face

theorem runtime_material_next (runtime : LivingRuntimeState (process source)) :
    runtime.tick.next.state.current = neuralStep source runtime.state.current := rfl

theorem runtime_fired_readout (runtime : LivingRuntimeState (process source)) :
    (runtimeFacade source).readoutAt runtime .fired =
      .inl ⟨(), fired source runtime.state.current⟩ := rfl

theorem runtime_after_readout (runtime : LivingRuntimeState (process source)) :
    (runtimeFacade source).readoutAt runtime .after =
      .inl ⟨(), runtime.tick.next.state.current⟩ := rfl

set_option linter.defProp false in
def native_operation_factorizes (runtime : LivingRuntimeState (process source)) :=
  SourceOperationNative.point_factorizes runtime

set_option linter.defProp false in
def installed_neural_face_factorizes
    (runtime : LivingRuntimeState (process source)) (face : NeuralFace) :=
  (runtimeFacade source).readoutAt_factorizes runtime face

noncomputable section

def materialRead (visit : Visit source) : Int := visit.current.body.position

set_option linter.defProp false in
def autonomous_observation_consumer (runtime : LivingRuntimeState (process source)) :=
  SourceOperationNative.Observed.model_factorizes (materialRead source) runtime

end

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
