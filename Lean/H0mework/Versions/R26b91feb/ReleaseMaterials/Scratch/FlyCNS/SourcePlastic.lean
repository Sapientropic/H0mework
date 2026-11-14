import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceStep

/-! A source-native neural/plastic update. Anatomical addresses and rule rows
are fixed before the emitter. The source computes its own neural fired vector,
then every Q20 trace and original-edge weight, then its one complete next. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.Plastic

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

def q20 : Int := 1048576

structure Rule where
  eligibilityTau : Nat := 1000
  dopamineTau : Nat := 200
  eligibilityImpulse : Int := 65536
  forwardDivisor : Nat := 64
  reverseDivisor : Nat := 256
  forgettingDivisor : Nat := 0
  labileDecayTicks : Nat := 0
  consolidationDivisor : Nat := 0
  stableDecayTicks : Nat := 0
  minGain : Int := 104857
  maxGain : Int := 2097152
  eligibilityTau_positive : 0 < eligibilityTau := by decide
  dopamineTau_positive : 0 < dopamineTau := by decide
  eligibilityImpulse_positive : 0 < eligibilityImpulse := by decide
  eligibilityImpulse_bounded : eligibilityImpulse ≤ q20 := by decide
  minGain_nonnegative : 0 ≤ minGain := by decide
  minGain_le_untrained : minGain ≤ q20 := by decide
  untrained_le_maxGain : q20 ≤ maxGain := by decide
  maxGain_bounded : maxGain ≤ 4 * q20 := by decide

/-- The original-row finite wiring, including its inverse scatter addresses.
Endpoint, positive KC weight and complete source-index inventories are raw
anatomical obligations; no learned state or firing result is an input. -/
structure RawWiring {neurons edges : Nat} (graph : RawGraph neurons edges)
    (sites domains danInputs : Nat) where
  sourceRow : Fin edges → Nat
  isKC : Fin neurons → Bool
  isDAN : Fin neurons → Bool
  isMBON : Fin neurons → Bool
  domainNeuron : Fin domains → Fin neurons
  domainAt : Fin neurons → Option (Fin domains)
  domain_inverse : (domain : Fin domains) → domainAt (domainNeuron domain) = some domain
  domain_sound : {neuron : Fin neurons} → {domain : Fin domains} →
    domainAt neuron = some domain → domainNeuron domain = neuron
  domain_isMBON : (domain : Fin domains) → isMBON (domainNeuron domain) = true
  domain_inventory : (neuron : Fin neurons) → isMBON neuron = true →
    ∃ domain, domainNeuron domain = neuron
  siteEdge : Fin sites → Fin edges
  siteDomain : Fin sites → Fin domains
  siteAt : Fin edges → Option (Fin sites)
  site_inverse : (site : Fin sites) → siteAt (siteEdge site) = some site
  site_sound : {edge : Fin edges} → {site : Fin sites} →
    siteAt edge = some site → siteEdge site = edge
  site_isKC : (site : Fin sites) → isKC (graph.pre (siteEdge site)) = true
  site_positive : (site : Fin sites) → graph.transmitterSign (graph.pre (siteEdge site)) = 1
  site_endpoint : (site : Fin sites) → graph.post (siteEdge site) = domainNeuron (siteDomain site)
  danEdge : Fin danInputs → Fin edges
  danDomain : Fin danInputs → Fin domains
  dan_injective : Function.Injective danEdge
  dan_isDAN : (input : Fin danInputs) → isDAN (graph.pre (danEdge input)) = true
  dan_endpoint : (input : Fin danInputs) → graph.post (danEdge input) = domainNeuron (danDomain input)
  dan_inventory : (edge : Fin edges) → isDAN (graph.pre edge) = true →
    isMBON (graph.post edge) = true → ∃ input, danEdge input = edge
  site_hasDAN : (site : Fin sites) → ∃ input,
    danDomain input = siteDomain site ∧ 0 < graph.contacts (danEdge input)
  site_inventory : (edge : Fin edges) → isKC (graph.pre edge) = true →
    graph.transmitterSign (graph.pre edge) = 1 →
    (∃ input, graph.post (danEdge input) = graph.post edge ∧
      0 < graph.contacts (danEdge input)) → ∃ site, siteEdge site = edge

structure PlasticState (sites domains : Nat) where
  eligibility : Fin sites → Int
  dopamine : Fin domains → Int
  labile : Fin sites → Int
  stable : Fin sites → Int
  deltaUv : Fin sites → Int
  lastUpdateTick : Fin sites → Int
  modulationScratch : Fin domains → Int

structure JointState (neurons edges sites domains : Nat) where
  neural : MaterialState neurons edges
  plastic : PlasticState sites domains
  plasticTick : Nat
  plasticChanges : Nat

structure Source {neurons edges : Nat} (sites domains danInputs : Nat) where
  graph : RawGraph neurons edges
  wiring : RawWiring graph sites domains danInputs
  rules : Fin domains → Rule
  initial : JointState neurons edges sites domains
  pulses : List (RawPulse neurons)
  instanceId : String

variable {neurons edges sites domains danInputs : Nat}

def initialPlasticState (sites domains : Nat) : PlasticState sites domains where
  eligibility := fun _ => 0
  dopamine := fun _ => 0
  labile := fun _ => 0
  stable := fun _ => 0
  deltaUv := fun _ => 0
  lastUpdateTick := fun _ => -1
  modulationScratch := fun _ => 0

def initialJointState (neurons edges sites domains seed : Nat) :
    JointState neurons edges sites domains where
  neural := initialState neurons edges seed
  plastic := initialPlasticState sites domains
  plasticTick := 0
  plasticChanges := 0

def neuralSource (source : Source (neurons := neurons) (edges := edges) sites domains danInputs) :
    SourceSpec neurons edges where
  graph := source.graph
  initial := source.initial.neural
  pulses := source.pulses

def tickFired (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) : Fin neurons → Bool :=
  fired (neuralSource source) current.neural

def decay (value : Int) (ticks : Nat) : Int :=
  if ticks = 0 ∨ value = 0 then value
  else
    let decrement := Int.ediv (Int.ofNat value.natAbs + Int.ofNat ticks - 1) (Int.ofNat ticks)
    if value > 0 then value - decrement else value + decrement

def domainContacts (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (domain : Fin domains) : Nat :=
  ∑ input : Fin danInputs,
    if source.wiring.danDomain input = domain then source.graph.contacts (source.wiring.danEdge input)
    else 0

def danContactQ (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (input : Fin danInputs) : Int :=
  Int.ediv (Int.ofNat (source.graph.contacts (source.wiring.danEdge input)) * q20)
    (Int.ofNat (domainContacts source (source.wiring.danDomain input)))

def modulationScratch (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (domain : Fin domains) : Int :=
  ∑ input : Fin danInputs,
    if source.wiring.danDomain input = domain ∧
      tickFired source current (source.graph.pre (source.wiring.danEdge input)) = true then
      danContactQ source input else 0

def decayedDopamine (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (domain : Fin domains) : Int :=
  decay (current.plastic.dopamine domain) (source.rules domain).dopamineTau

structure EdgeUpdate where
  eligibility : Int
  labile : Int
  stable : Int
  deltaUv : Int
  lastUpdateTick : Int

def baseWeight (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (site : Fin sites) : Int :=
  275 * Int.ofNat (source.graph.contacts (source.wiring.siteEdge site))

def edgeUpdate (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (site : Fin sites) : EdgeUpdate :=
  let domain := source.wiring.siteDomain site
  let rule := source.rules domain
  let decayedEligibility := decay (current.plastic.eligibility site) rule.eligibilityTau
  let preSpike := tickFired source current (source.graph.pre (source.wiring.siteEdge site))
  let eligibility := if preSpike then min q20 (decayedEligibility + rule.eligibilityImpulse)
    else decayedEligibility
  let modulation := min q20 (modulationScratch source current domain)
  let oldLabile := current.plastic.labile site
  let oldStable := current.plastic.stable site
  let labile0 := decay oldLabile rule.labileDecayTicks
  let stable0 := decay oldStable rule.stableDecayTicks
  let labile1 := if rule.forwardDivisor = 0 then labile0 else
    labile0 - Int.ediv (Int.ediv (eligibility * modulation) q20) (Int.ofNat rule.forwardDivisor)
  let labile2 := if preSpike ∧ rule.reverseDivisor ≠ 0 then
    labile1 + Int.ediv (decayedDopamine source current domain) (Int.ofNat rule.reverseDivisor)
    else labile1
  let forgetting := Int.ediv (Int.ediv (Int.ofNat labile2.natAbs * modulation) q20)
    (Int.ofNat rule.forgettingDivisor)
  let labile3 := if rule.forgettingDivisor ≠ 0 ∧ eligibility = 0 ∧ modulation ≠ 0 then
    if labile2 > 0 then labile2 - forgetting else labile2 + forgetting
    else labile2
  let amount := Int.ediv (Int.ofNat labile3.natAbs) (Int.ofNat rule.consolidationDivisor)
  let transfer := if rule.consolidationDivisor = 0 then 0 else
    if labile3 > 0 then amount else -amount
  let labile4 := labile3 - transfer
  let stable := stable0 + transfer
  let gain := q20 + labile4 + stable
  let labile := if gain < rule.minGain then labile4 + rule.minGain - gain
    else if gain > rule.maxGain then labile4 - (gain - rule.maxGain) else labile4
  { eligibility := eligibility
    labile := labile
    stable := stable
    deltaUv := Int.ediv (baseWeight source site * (q20 + labile + stable)) q20 - baseWeight source site
    lastUpdateTick := if labile ≠ oldLabile ∨ stable ≠ oldStable then
      Int.ofNat current.neural.tick else current.plastic.lastUpdateTick site }

def updatedPlastic (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) : PlasticState sites domains where
  eligibility := fun site => (edgeUpdate source current site).eligibility
  dopamine := fun domain => min q20
    (decayedDopamine source current domain + modulationScratch source current domain)
  labile := fun site => (edgeUpdate source current site).labile
  stable := fun site => (edgeUpdate source current site).stable
  deltaUv := fun site => (edgeUpdate source current site).deltaUv
  lastUpdateTick := fun site => (edgeUpdate source current site).lastUpdateTick
  modulationScratch := modulationScratch source current

def writtenDelta (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (edge : Fin edges) : Int :=
  match source.wiring.siteAt edge with
  | none => current.neural.weightDelta edge
  | some site => (edgeUpdate source current site).deltaUv

def changedEdges (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) : Nat :=
  ∑ site : Fin sites,
    if (edgeUpdate source current site).deltaUv ≠ current.plastic.deltaUv site then 1 else 0

def step (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) : JointState neurons edges sites domains where
  neural := { neuralStep (neuralSource source) current.neural with
    weightDelta := writtenDelta source current }
  plastic := updatedPlastic source current
  plasticTick := current.neural.tick + 1
  plasticChanges := current.plasticChanges + changedEdges source current

def signedWeight (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (edge : Fin edges) : Int :=
  source.graph.transmitterSign (source.graph.pre edge) *
    (275 * Int.ofNat (source.graph.contacts edge) + current.neural.weightDelta edge)

theorem step_neural_membrane
    (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) :
    (step source current).neural.membrane =
      (neuralStep (neuralSource source) current.neural).membrane := rfl

theorem original_edge_delta_writeback
    (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (site : Fin sites) :
    (step source current).neural.weightDelta (source.wiring.siteEdge site) =
      (step source current).plastic.deltaUv site := by
  change (match source.wiring.siteAt (source.wiring.siteEdge site) with
    | none => current.neural.weightDelta (source.wiring.siteEdge site)
    | some selected => (edgeUpdate source current selected).deltaUv) = _
  rw [source.wiring.site_inverse]
  rfl

theorem original_edge_signed_weight_writeback
    (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (site : Fin sites) :
    signedWeight source (step source current) (source.wiring.siteEdge site) =
      baseWeight source site + (step source current).plastic.deltaUv site := by
  unfold signedWeight
  rw [source.wiring.site_positive, one_mul, original_edge_delta_writeback]
  rfl

theorem nonplastic_edge_preserved
    (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) (edge : Fin edges)
    (notSelected : source.wiring.siteAt edge = none) :
    (step source current).neural.weightDelta edge = current.neural.weightDelta edge := by
  change (match source.wiring.siteAt edge with
    | none => current.neural.weightDelta edge
    | some selected => (edgeUpdate source current selected).deltaUv) = _
  rw [notSelected]

structure PlasticEventAt (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) where
  private mk ::

def PlasticEventAt.generate (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)
    (current : JointState neurons edges sites domains) : PlasticEventAt source current := ⟨⟩

def PlasticEventAt.materialNext {source : Source (neurons := neurons) (edges := edges) sites domains danInputs}
    {current : JointState neurons edges sites domains} (_event : PlasticEventAt source current) :
    JointState neurons edges sites domains := step source current

/-- Complete standing inventory for neural firing, domain modulation, edge
traces, original-edge write-back, and the material next. -/
abbrev JointResponsibility := Fin 5

def network (source : Source (neurons := neurons) (edges := edges) sites domains danInputs) : WorldRelationNetwork where
  Support := JointState neurons edges sites domains
  Anchor := String
  Incidence := Nat
  Lineage := String
  Responsibility := JointResponsibility
  Claim := JointResponsibility
  anchorAt := fun _ => source.instanceId
  incidenceAt := fun current => current.neural.tick
  lineageAt := fun _ => source.instanceId
  OpenAt := fun _ _ => Unit
  openClaimAt := fun {_support} {responsibility} _ => responsibility
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun current _ => PlasticEventAt source current

def vocabulary (source : Source (neurons := neurons) (edges := edges) sites domains danInputs) : Vocabulary where
  Current := JointState neurons edges sites domains
  Anchor := String
  Incidence := Nat
  Lineage := String
  anchorAt := fun _ => source.instanceId
  incidenceAt := fun current => current.neural.tick
  lineageAt := fun _ => source.instanceId
  NativeWriteAt := PlasticEventAt source
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := PlasticEventAt.materialNext
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

variable (source : Source (neurons := neurons) (edges := edges) sites domains danInputs)

def entry (current : JointState neurons edges sites domains) (responsibility : JointResponsibility) :
    OpenResponsibilityAt (network source) current := ⟨responsibility, ()⟩

def inventoryPresentation (current : JointState neurons edges sites domains) :
    ConstructivePresentation JointResponsibility
      (OpenResponsibilityAt (network source) current) where
  forward := entry source current
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by
    rintro ⟨responsibility, receipt⟩
    cases receipt
    rfl

inductive SupportedPlasticEventAt : JointState neurons edges sites domains →
    JointState neurons edges sites domains → Type
  | emitted (current : JointState neurons edges sites domains) :
      SupportedPlasticEventAt current current

def eventLaw : SourceNativeEventAlgebra (network source) (vocabulary source) where
  EventAt := SupportedPlasticEventAt
  compile := fun {_current} {_support} event => by
    cases event
    exact .nativeWrite (.generate source _)
  AffectedInventoryAt := fun _ => JointResponsibility
  affectedInventoryPresentation := fun {_current} {_support} _ => inventoryPresentation source _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => by cases event; rfl
  lineage_commutes := fun _ => rfl

def nativeSource : SourceNativeSource (network source) (vocabulary source) where
  initial := source.initial
  law := eventLaw source

def emitted (current : JointState neurons edges sites domains) :
    (nativeSource source).toRootSource.actual.OccurrenceAt current :=
  ⟨current, .emitted current⟩

structure ExactJointRowAt
    {current : JointState neurons edges sites domains}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current)
    {targetSupport : JointState neurons edges sites domains}
    (oldEntry : OpenResponsibilityAt (network source) occurrence.1)
    (newEntry : OpenResponsibilityAt (network source) targetSupport) : Type where
  source_eq : occurrence.1 = current
  target_eq : targetSupport = step source current
  responsibility_eq : oldEntry.1 = newEntry.1

def writeRowSource : LedgerWriteRowSourceAt (nativeSource source) (ExactJointRowAt source) where
  IncidenceOccurrenceAt := ExactJointRowAt source
  compileEvolution := fun {_current} {_occurrence} {_target} {_old} {_new} event =>
    .transferred (.generate source _) rfl event.responsibility_eq (Nat.le_refl _)
  compileExact := id

def completePatch {current : JointState neurons edges sites domains}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource source) occurrence
      ⟨step source current⟩ :=
  .complete
    { size := 5
      sourceEntryAt := entry source occurrence.1
      targetEntryAt := entry source (step source current)
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
  ExactTransitionAt := ExactJointRowAt source
  exact_incidence := fun {_current} {_occurrence} {_target} {_old} {_new} exact =>
    ⟨by
      change _target.neural.tick = _occurrence.1.neural.tick + 1
      rw [exact.target_eq, exact.source_eq]
      rfl⟩
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource source
  terminalRowSource := LedgerTerminalRowSourceAt.empty (nativeSource source)
  compile := fun {current} occurrence => by
    cases occurrence with
    | mk support event =>
      cases event
      exact .nativeWrite (.generate source current) rfl (emitted source (step source current))
        (completePatch source (emitted source current)).toLedgerWriteEvolution
  compilePatch := fun {current} occurrence => by
    cases occurrence with
    | mk support event => cases event; exact ⟨completePatch source (emitted source current), rfl⟩

def restructuringLaw : SourceNativeLedgerRestructuringLaw (nativeSource source) :=
  identityOnlyWorldLedgerRestructuringLaw (nativeSource source) source.instanceId (by
    intro _ _
    change Subsingleton Unit
    infer_instance)

def restructuringCertification {current : JointState neurons edges sites domains}
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
    SourceNativeRestructuringLedgerSource (network source) (vocabulary source) where
  source := nativeSource source
  compiler :=
    { ledgerCompiler := ledgerCompiler source
      restructuringLaw := restructuringLaw source
      certifyRestructuring := restructuringCertification source }

inductive PlasticFace where
  | before
  | fired
  | after
  | plastic
  | weights
  deriving DecidableEq

def projectionLaw : SourceNativeProjectionLaw (restructuringSource source).toLedgerSource where
  Projection := PlasticFace
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun face {_} _ _ =>
    match face with
    | .before | .after => JointState neurons edges sites domains
    | .fired => Fin neurons → Bool
    | .plastic => PlasticState sites domains
    | .weights => Fin edges → Int
  project := fun face {current} _ _ =>
    match face with
    | .before => current
    | .after => step source current
    | .fired => tickFired source current
    | .plastic => (step source current).plastic
    | .weights => signedWeight source (step source current)

def authoritySource : SourceNativeAuthoritySource (network source) (vocabulary source) where
  restructuringSource := restructuringSource source
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource source)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (network source)
  projectionLaw := projectionLaw source

def authoritativeRoot :
    SourceNativeAuthoritativeRootClosure (network source) (vocabulary source) where
  source := authoritySource source
  emitted := emitted source
  compiler_commutes := fun _ => rfl

def livingRoot : SourceNativeLivingRootClosure (network source) (vocabulary source) :=
  (authoritativeRoot source).toLivingWithoutFaithfulTerminal (by
    intro _
    change IsEmpty PEmpty
    infer_instance)

abbrev Visit := RootVisit (livingRoot source).toAuthoritativeRoot.toRoot

def currentAt (visit : Visit source) : SourceNativeLivingRootCurrentAt (network source) :=
  ⟨vocabulary source, livingRoot source, .finite visit⟩

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

def process : SourceNativeLivingRootProcess (network source) where
  State := Visit source
  stateAt := currentAt source
  stateAt_injective := currentAt_injective source
  initial := (livingRoot source).toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨nextVisit source visit, rfl, by rfl⟩

def runtimeFacade : SourceNativeLivingRuntimeFacade (network source) where
  process := process source
  FaceAt := fun _ => PlasticFace
  componentAt := fun _ _ => projectionLaw source
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ face => face

theorem runtime_joint_next (runtime : LivingRuntimeState (process source)) :
    runtime.tick.next.state.current = step source runtime.state.current := rfl

theorem runtime_fired_readout (runtime : LivingRuntimeState (process source)) :
    (runtimeFacade source).readoutAt runtime .fired =
      .inl ⟨(), tickFired source runtime.state.current⟩ := rfl

theorem runtime_joint_after_readout (runtime : LivingRuntimeState (process source)) :
    (runtimeFacade source).readoutAt runtime .after =
      .inl ⟨(), runtime.tick.next.state.current⟩ := rfl

theorem runtime_plastic_readout (runtime : LivingRuntimeState (process source)) :
    (runtimeFacade source).readoutAt runtime .plastic =
      .inl ⟨(), runtime.tick.next.state.current.plastic⟩ := rfl

theorem runtime_original_weight_readout (runtime : LivingRuntimeState (process source)) :
    (runtimeFacade source).readoutAt runtime .weights =
      .inl ⟨(), signedWeight source runtime.tick.next.state.current⟩ := rfl

theorem runtime_same_tick_source_weight
    (runtime : LivingRuntimeState (process source)) (site : Fin sites) :
    signedWeight source runtime.tick.next.state.current (source.wiring.siteEdge site) =
      baseWeight source site + runtime.tick.next.state.current.plastic.deltaUv site :=
  original_edge_signed_weight_writeback source runtime.state.current site

theorem runtime_plastic_delta_is_generated
    (runtime : LivingRuntimeState (process source)) (site : Fin sites) :
    runtime.tick.next.state.current.plastic.deltaUv site =
      (edgeUpdate source runtime.state.current site).deltaUv := rfl

theorem runtime_domain_dopamine_is_generated
    (runtime : LivingRuntimeState (process source)) (domain : Fin domains) :
    runtime.tick.next.state.current.plastic.dopamine domain = min q20
      (decayedDopamine source runtime.state.current domain +
        modulationScratch source runtime.state.current domain) := rfl

set_option linter.defProp false in
def native_operation_factorizes (runtime : LivingRuntimeState (process source)) :=
  SourceOperationNative.point_factorizes runtime

set_option linter.defProp false in
def installed_joint_face_factorizes
    (runtime : LivingRuntimeState (process source)) (face : PlasticFace) :=
  (runtimeFacade source).readoutAt_factorizes runtime face

set_option linter.defProp false in
def plastic_writeback_and_next_factorizes
    (runtime : LivingRuntimeState (process source)) (site : Fin sites) :=
  And.intro (runtime_same_tick_source_weight source runtime site)
    ((runtimeFacade source).readoutAt_factorizes runtime .plastic)

set_option linter.defProp false in
def original_weight_and_next_factorizes
    (runtime : LivingRuntimeState (process source)) (site : Fin sites) :=
  And.intro (runtime_same_tick_source_weight source runtime site)
    ((runtimeFacade source).readoutAt_factorizes runtime .weights)


end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.Plastic
