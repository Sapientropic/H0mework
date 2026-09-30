import H0mework.Chemistry.LAlanineSource.GeneratedPhysicalChemicalBondIncidence
import H0mework.Chemistry.LAlanineEnergy.GeneratedEnergyLedger
import H0mework.Chemistry.LAlanineForce.GeneratedForceUpdate
import H0mework.Chemistry.LAlaninePropagation.NativeElectronicEffect
import H0mework.Society.Renewal.InstalledRenewalProjection

/-! # One-row generic living root for the L-alanine bond-density occurrence -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Root

noncomputable section

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open _root_.SaturationMonoid.ProcessGame
open _root_.SaturationMonoid.ProcessGame.Society.Renewal
open Interface Source Calculation Producer

inductive LAlanineStage where
  | targetErasedDensityBCPCensusFrozen
  | physicalChemicalBondIncidenceCertified
  | molecularEnergyLedgerCertified
  | forceDrivenMaterialNextCertified
  | electronicPropagationCertified
  | nativeElectronicCurrent (time : ℚ)
  deriving DecidableEq, Repr

def nextStage : LAlanineStage → LAlanineStage
  | .targetErasedDensityBCPCensusFrozen =>
      .physicalChemicalBondIncidenceCertified
  | .physicalChemicalBondIncidenceCertified =>
      .molecularEnergyLedgerCertified
  | .molecularEnergyLedgerCertified => .forceDrivenMaterialNextCertified
  | .forceDrivenMaterialNextCertified => .electronicPropagationCertified
  | .electronicPropagationCertified =>
      .nativeElectronicCurrent (1 + Propagation.Producer.nativeClockStep)
  | .nativeElectronicCurrent time =>
      .nativeElectronicCurrent (time + Propagation.Producer.nativeClockStep)

/-- The old local game records its finite renewal prefix; native effects use the root emitter. -/
def localOccurrence : RootedAccountedUnfolding LAlanineStage :=
  .occur .targetErasedDensityBCPCensusFrozen <| .singleton <|
    .occur .physicalChemicalBondIncidenceCertified <| .singleton <|
      .occur .molecularEnergyLedgerCertified <| .singleton <|
        .occur .forceDrivenMaterialNextCertified <| .singleton <|
          .zero .electronicPropagationCertified

abbrev LocalSource := LAlanine40KSourceKey

def occurrenceOf (_source : LocalSource) :
    RootedAccountedUnfolding LAlanineStage :=
  localOccurrence

def game : SaturationMonoid.ProcessGame occurrenceOf :=
  ⟨key⟩

inductive LAlanineRenewalSeed where
  | adjudicatePhysicalChemicalIncidence
  deriving DecidableEq, Repr

def seedAt (source : LocalSource) (stage : LAlanineStage)
    (_seed : LAlanineRenewalSeed) : Prop :=
  source = key ∧ stage = .targetErasedDensityBCPCensusFrozen

def sourceSeed :
    SourceSeed occurrenceOf LAlanineRenewalSeed seedAt game.source := by
  refine ⟨.adjudicatePhysicalChemicalIncidence, ?_⟩
  refine ⟨.targetErasedDensityBCPCensusFrozen, ?_, rfl, rfl⟩
  convert RootedAccountedUnfolding.root_mem_trace localOccurrence using 1 <;>
    rfl

abbrev LAlanineGeneratedLineage (source : LocalSource) :=
  { candidate : LAlanine40KSourceKey // candidate = source }

def lineageOf (source : LocalSource)
    (_seed : SourceSeed occurrenceOf LAlanineRenewalSeed seedAt source) :
    LAlanineGeneratedLineage source :=
  ⟨source, rfl⟩

abbrev LAlanineStanding := LAlanineStage

def standingOf
    (_seed : SourceSeed occurrenceOf LAlanineRenewalSeed seedAt game.source) :
    LAlanineStanding :=
  .physicalChemicalBondIncidenceCertified

structure LAlanineRootActivationReceiptAt
    (_seed : SourceSeed occurrenceOf LAlanineRenewalSeed seedAt game.source) :
    Type where
  sourceExact : sourceRecorded.source = key
  physicalDensity : SourceGeneratedTargetErasedLAlanine40KBondDensityCrown

structure LAlanineRenewalConsumerAt
    (seed : SourceSeed occurrenceOf LAlanineRenewalSeed seedAt game.source) :
    Type where
  receipt : LAlanineRootActivationReceiptAt seed

structure LAlanineRenewalDispositionAt
    (_seed : SourceSeed occurrenceOf LAlanineRenewalSeed seedAt game.source) :
    Type where
  target : LAlanineStage
  targetExact : target = .physicalChemicalBondIncidenceCertified
  incidence : SourceGeneratedLAlanine40KPhysicalChemicalBondIncidenceCrown
  carriedPromoleculeCollision :
    densityArmTopology .molecularBLYP =
      densityArmTopology .independentAtomSAD
  carriedGeometryGap : postFreezeAdjudication.geometryGapMicroangstrom = 705747

def activationReceipt : LAlanineRootActivationReceiptAt sourceSeed :=
  { sourceExact := rfl
    physicalDensity := sourceGeneratedTargetErasedLAlanine40KBondDensity_crown }

def renewalConsumer : LAlanineRenewalConsumerAt sourceSeed :=
  ⟨activationReceipt⟩

def renewalDisposition : LAlanineRenewalDispositionAt sourceSeed :=
  { target := .physicalChemicalBondIncidenceCertified
    targetExact := rfl
    incidence := sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown
    carriedPromoleculeCollision := rfl
    carriedGeometryGap := rfl }

structure LAlanineSourceEntryReceiptAt : Type where
  physicalDensity : SourceGeneratedTargetErasedLAlanine40KBondDensityCrown

structure LAlanineTargetEntryReceiptAt : Type where
  incidence : SourceGeneratedLAlanine40KPhysicalChemicalBondIncidenceCrown

structure LAlanineEnergyEntryReceiptAt : Type where
  energy : Energy.Producer.SourceGeneratedLAlanineEnergyCrown

structure LAlanineForceEntryReceiptAt : Type where
  update : Force.Interface.NuclearUpdateReadout
  updateExact : update = Force.Source.updateReadout
  forceUpdate : Force.Producer.SourceGeneratedLAlanineForceUpdateCrown

/-- The target standing retains its source and one native density slice. -/
structure LAlanineElectronicEntryReceiptAt : Type where
  sourceMatrices : Propagation.Interface.ElectronicPropagationSource
  sourceMatricesExact : sourceMatrices = Propagation.Source.electronicSource
  nativeTarget : Propagation.Dynamics.ElectronicOperator
  nativeTargetExact : nativeTarget = Propagation.Dynamics.densityEvolution sourceMatrices 1
  electronicPropagation : Propagation.Producer.SourceGeneratedLAlanineElectronicPropagationCrown

inductive LAlanineLedgerResponsibility where
  | bondDensityIncidenceAdjudication
  deriving DecidableEq, Repr

inductive LAlanineClaim where
  | registeredExperimentalGeometryModelBondTopology
  deriving DecidableEq, Repr

def LAlanineOpenAt (stage : LAlanineStage) :
    LAlanineLedgerResponsibility → Type
  | .bondDensityIncidenceAdjudication =>
      match stage with
      | .targetErasedDensityBCPCensusFrozen => LAlanineSourceEntryReceiptAt
      | .physicalChemicalBondIncidenceCertified => LAlanineTargetEntryReceiptAt
      | .molecularEnergyLedgerCertified => LAlanineEnergyEntryReceiptAt
      | .forceDrivenMaterialNextCertified => LAlanineForceEntryReceiptAt
      | .electronicPropagationCertified => LAlanineElectronicEntryReceiptAt
      | .nativeElectronicCurrent time => Propagation.Runtime.NativeElectronicStandingAt time

instance openAtSubsingleton (stage : LAlanineStage)
    (responsibility : LAlanineLedgerResponsibility) :
    Subsingleton (LAlanineOpenAt stage responsibility) := by
  cases responsibility
  cases stage
  case nativeElectronicCurrent time =>
    exact Propagation.Runtime.nativeElectronicStanding_subsingleton time
  case electronicPropagationCertified =>
    constructor
    intro left right
    rcases left with ⟨leftSource, leftSourceExact, leftTarget, leftTargetExact, leftCrown⟩
    rcases right with ⟨rightSource, rightSourceExact, rightTarget, rightTargetExact, rightCrown⟩
    cases leftSourceExact
    cases rightSourceExact
    cases leftTargetExact
    cases rightTargetExact
    rfl
  case forceDrivenMaterialNextCertified =>
    constructor
    intro left right
    rcases left with ⟨leftUpdate, leftExact, leftCrown⟩
    rcases right with ⟨rightUpdate, rightExact, rightCrown⟩
    cases leftExact
    cases rightExact
    rfl
  all_goals
    constructor
    intro left right
    rcases left with ⟨leftCrown⟩
    rcases right with ⟨rightCrown⟩
    cases Subsingleton.elim leftCrown rightCrown
    rfl

def network : WorldRelationNetwork where
  Support := LAlanineStage
  Anchor := LAlanine40KSourceKey
  Incidence := LAlanineStage
  Lineage := LAlanine40KSourceKey
  Responsibility := LAlanineLedgerResponsibility
  Claim := LAlanineClaim
  anchorAt := fun _stage => key
  incidenceAt := id
  lineageAt := fun _stage => key
  OpenAt := LAlanineOpenAt
  openClaimAt := fun _receipt => .registeredExperimentalGeometryModelBondTopology
  openProgressBudgetAt := fun {support} {_responsibility} _receipt =>
    match support with
    | .targetErasedDensityBCPCensusFrozen => 1
    | .physicalChemicalBondIncidenceCertified => 0
    | .molecularEnergyLedgerCertified => 0
    | .forceDrivenMaterialNextCertified => 0
    | .electronicPropagationCertified => 0
    | .nativeElectronicCurrent _time => 0
  HoldsAt := fun _entry claim =>
    PLift (claim = .registeredExperimentalGeometryModelBondTopology)
  ObstructionAt := fun _entry => PEmpty
  obstructionClaim := fun obstruction => nomatch obstruction
  SemanticChangeAt := fun _source _target _claim => PUnit
  DispositionAt := fun _source _target => PUnit

abbrev N := network

instance networkOpenAtSubsingleton (stage : LAlanineStage)
    (responsibility : LAlanineLedgerResponsibility) :
    Subsingleton (N.OpenAt stage responsibility) :=
  openAtSubsingleton stage responsibility

def entryAt : (stage : LAlanineStage) → OpenResponsibilityAt N stage
  | .targetErasedDensityBCPCensusFrozen =>
      ⟨.bondDensityIncidenceAdjudication,
        ⟨sourceGeneratedTargetErasedLAlanine40KBondDensity_crown⟩⟩
  | .physicalChemicalBondIncidenceCertified =>
      ⟨.bondDensityIncidenceAdjudication,
        ⟨sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown⟩⟩
  | .molecularEnergyLedgerCertified =>
      ⟨.bondDensityIncidenceAdjudication,
        ⟨Energy.Producer.sourceGeneratedLAlanineEnergy_crown⟩⟩
  | .forceDrivenMaterialNextCertified =>
      ⟨.bondDensityIncidenceAdjudication,
        ⟨Force.Source.updateReadout, rfl,
          Force.Producer.sourceGeneratedLAlanineForceUpdate_crown⟩⟩
  | .electronicPropagationCertified =>
      ⟨.bondDensityIncidenceAdjudication,
        ⟨Propagation.Source.electronicSource, rfl,
          Propagation.Producer.nativeElectronicNext, rfl,
          Propagation.Producer.sourceGeneratedLAlanineElectronicPropagation_crown⟩⟩
  | .nativeElectronicCurrent time =>
      ⟨.bondDensityIncidenceAdjudication, Propagation.Runtime.nativeElectronicStanding time⟩

theorem entryAt_unique {stage : LAlanineStage}
    (candidate : OpenResponsibilityAt N stage) : candidate = entryAt stage := by
  rcases candidate with ⟨responsibility, receipt⟩
  cases stage <;> cases responsibility
  all_goals exact Sigma.eq rfl (Subsingleton.elim receipt _)

/-- The native row computes collision and retained-pair writes from the received material. -/
def generatedNextEntry : (stage : LAlanineStage) → OpenResponsibilityAt N (nextStage stage)
  | .nativeElectronicCurrent time =>
      ⟨.bondDensityIncidenceAdjudication,
        Propagation.Runtime.nativeElectronicStandingAfter (entryAt (.nativeElectronicCurrent time)).2⟩
  | stage => entryAt (nextStage stage)

theorem generatedNextEntry_eq (stage : LAlanineStage) :
    generatedNextEntry stage = entryAt (nextStage stage) := entryAt_unique _

inductive LAlanineRootEventAt : LAlanineStage → LAlanineStage → Type where
  | exact (stage : LAlanineStage) : LAlanineRootEventAt stage stage

def vocabulary : ConstructiveRoot.Vocabulary where
  Current := LAlanineStage
  Anchor := LAlanine40KSourceKey
  Incidence := LAlanineStage
  Lineage := LAlanine40KSourceKey
  anchorAt := fun _stage => key
  incidenceAt := id
  lineageAt := fun _stage => key
  NativeWriteAt := fun _current => PUnit
  RelationWriteAt := fun _current => PEmpty
  ContinuedTransportAt := fun _current => PEmpty
  BorromeanRedirectAt := fun _current => PEmpty
  FaithfulTerminalAt := fun _current => PEmpty
  nativeTarget := fun {current} _write => nextStage current
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

abbrev V := vocabulary

def eventLaw : SourceNativeEventAlgebra N V where
  EventAt := LAlanineRootEventAt
  compile := fun _event => .nativeWrite PUnit.unit
  AffectedInventoryAt := fun _event => Unit
  affectedInventoryPresentation := fun {_current} {_support} event => by
    cases event
    exact
      { forward := fun _ => entryAt _
        backward := fun _ => ()
        backward_forward := fun _ => rfl
        forward_backward := fun candidate => (entryAt_unique candidate).symm }
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun event => by cases event; rfl
  incidence_commutes := fun event => by cases event; rfl
  lineage_commutes := fun event => by cases event; rfl

def nativeSource : SourceNativeSource N V where
  initial := .targetErasedDensityBCPCensusFrozen
  law := eventLaw

def emitted (current : V.Current) :
    nativeSource.toRootSource.actual.OccurrenceAt current :=
  ⟨current, .exact current⟩

abbrev ExactTransitionAt
    {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt N
      (nativeSource.toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt N targetSupport) :=
  LedgerEntryEvolutionAt N sourceEntry targetEntry

abbrev IncidenceOccurrenceAt
    {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current)
    {targetSupport : N.Support}
    (sourceEntry : OpenResponsibilityAt N
      (nativeSource.toRootSource.account.supportOf occurrence))
    (targetEntry : OpenResponsibilityAt N targetSupport) :=
  LedgerEntryEvolutionAt N sourceEntry targetEntry

def writeRowSource : LedgerWriteRowSourceAt nativeSource ExactTransitionAt where
  IncidenceOccurrenceAt := IncidenceOccurrenceAt
  compileEvolution := fun evolution => evolution
  compileExact := fun evolution => evolution

def evolutionAt (stage : LAlanineStage) :
    LedgerEntryEvolutionAt N (entryAt stage) (generatedNextEntry stage) :=
  match stage with
  | .targetErasedDensityBCPCensusFrozen =>
      .transferred PUnit.unit rfl rfl (by decide)
  | .physicalChemicalBondIncidenceCertified =>
      .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  | .molecularEnergyLedgerCertified =>
      .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  | .forceDrivenMaterialNextCertified =>
      .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  | .electronicPropagationCertified =>
      .transferred PUnit.unit rfl rfl (Nat.le_refl 0)
  | .nativeElectronicCurrent _time =>
      .transferred PUnit.unit rfl rfl (Nat.le_refl 0)

def generatedPatch {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      ⟨nextStage current⟩ := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact .complete
    { size := 1
      sourceEntryAt := fun _ => entryAt current
      targetEntryAt := fun _ => generatedNextEntry current
      rowAt := fun _ => writeRowSource.generate (evolutionAt current) }
    { destinationIndex := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
      originIndex := fun _ => ⟨0, Nat.zero_lt_succ 0⟩
      destination_sound := fun candidate => (entryAt_unique candidate).symm
      origin_sound := fun candidate =>
        (generatedNextEntry_eq current).trans (entryAt_unique candidate).symm }

def ledgerCompiler : SourceNativeLedgerCompiler nativeSource where
  IncidenceTransitionAt := fun _occurrence _source _target => PUnit
  ExactTransitionAt := ExactTransitionAt
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := LedgerTerminalRowSourceAt.empty nativeSource
  compile := by
    intro current occurrence
    exact .nativeWrite PUnit.unit rfl (emitted (nextStage current))
      (generatedPatch occurrence).toLedgerWriteEvolution
  compilePatch := by
    intro _current occurrence
    exact ⟨generatedPatch occurrence, rfl⟩

def ledgerSource : SourceNativeLedgerSource N V where
  source := nativeSource
  ledgerCompiler := ledgerCompiler

def restructuringLaw : SourceNativeLedgerRestructuringLaw nativeSource :=
  identityOnlyWorldLedgerRestructuringLaw nativeSource key
    (fun support responsibility => openAtSubsingleton support responsibility)

def restructuringCertification {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) :=
  ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)
    (fun left right _ => (entryAt_unique left).trans (entryAt_unique right).symm)

def restructuringCompiler :
    SourceNativeRestructuringLedgerCompiler nativeSource where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

def restructuringSource : SourceNativeRestructuringLedgerSource N V where
  source := nativeSource
  compiler := restructuringCompiler

inductive LAlanineSiblingProjection where
  | physicalDensity
  | chemicalIncidence
  | molecularDensityField
  | molecularEnergyLedger
  | forceSourceEnergyLedger
  | forceTargetEnergyLedger
  | forceDrivenMaterialUpdate
  | electronicPropagationSource
  | electronicHamiltonian
  | electronicDensityLaw
  | electronicCurrentDensity
  | electronicNativeTarget
  | nativeElectronicEvolution
  | thermalCollision
  | timedPairEvolution
  deriving DecidableEq, Repr

def projectionActiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PUnit
  | .physicalChemicalBondIncidenceCertified => PEmpty
  | .molecularEnergyLedgerCertified => PEmpty
  | .forceDrivenMaterialNextCertified => PEmpty
  | .electronicPropagationCertified => PEmpty
  | .nativeElectronicCurrent _time => PEmpty

def projectionInactiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PEmpty
  | .physicalChemicalBondIncidenceCertified => PUnit
  | .molecularEnergyLedgerCertified => PUnit
  | .forceDrivenMaterialNextCertified => PUnit
  | .electronicPropagationCertified => PUnit
  | .nativeElectronicCurrent _time => PUnit

def energyProjectionActiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PEmpty
  | .physicalChemicalBondIncidenceCertified => PUnit
  | .molecularEnergyLedgerCertified => PEmpty
  | .forceDrivenMaterialNextCertified => PEmpty
  | .electronicPropagationCertified => PEmpty
  | .nativeElectronicCurrent _time => PEmpty

def energyProjectionInactiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PUnit
  | .physicalChemicalBondIncidenceCertified => PEmpty
  | .molecularEnergyLedgerCertified => PUnit
  | .forceDrivenMaterialNextCertified => PUnit
  | .electronicPropagationCertified => PUnit
  | .nativeElectronicCurrent _time => PUnit

def forceProjectionActiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PEmpty
  | .physicalChemicalBondIncidenceCertified => PEmpty
  | .molecularEnergyLedgerCertified => PUnit
  | .forceDrivenMaterialNextCertified => PEmpty
  | .electronicPropagationCertified => PEmpty
  | .nativeElectronicCurrent _time => PEmpty

def forceProjectionInactiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PUnit
  | .physicalChemicalBondIncidenceCertified => PUnit
  | .molecularEnergyLedgerCertified => PEmpty
  | .forceDrivenMaterialNextCertified => PUnit
  | .electronicPropagationCertified => PUnit
  | .nativeElectronicCurrent _time => PUnit

def electronicProjectionActiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PEmpty
  | .physicalChemicalBondIncidenceCertified => PEmpty
  | .molecularEnergyLedgerCertified => PEmpty
  | .forceDrivenMaterialNextCertified => PUnit
  | .electronicPropagationCertified => PEmpty
  | .nativeElectronicCurrent _time => PEmpty

def electronicProjectionInactiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PUnit
  | .physicalChemicalBondIncidenceCertified => PUnit
  | .molecularEnergyLedgerCertified => PUnit
  | .forceDrivenMaterialNextCertified => PEmpty
  | .electronicPropagationCertified => PUnit
  | .nativeElectronicCurrent _time => PUnit

def nativeElectronicProjectionActiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PEmpty
  | .physicalChemicalBondIncidenceCertified => PEmpty
  | .molecularEnergyLedgerCertified => PEmpty
  | .forceDrivenMaterialNextCertified => PEmpty
  | .electronicPropagationCertified => PUnit
  | .nativeElectronicCurrent _time => PUnit

def nativeElectronicProjectionInactiveAt : LAlanineStage → Type
  | .targetErasedDensityBCPCensusFrozen => PUnit
  | .physicalChemicalBondIncidenceCertified => PUnit
  | .molecularEnergyLedgerCertified => PUnit
  | .forceDrivenMaterialNextCertified => PUnit
  | .electronicPropagationCertified => PEmpty
  | .nativeElectronicCurrent _time => PEmpty

def nativeElectronicTime : LAlanineStage → ℚ
  | .electronicPropagationCertified => 1
  | .nativeElectronicCurrent time => time
  | _ => 0

def thermalProjectionActiveAt : LAlanineStage → Type
  | .nativeElectronicCurrent time => PLift (time = Thermal.Preparation.collisionCurrentTime)
  | _ => PEmpty

def thermalProjectionInactiveAt : LAlanineStage → Type
  | .nativeElectronicCurrent time => PLift (time ≠ Thermal.Preparation.collisionCurrentTime)
  | _ => PUnit

def timedPairProjectionActiveAt : LAlanineStage → Type
  | .nativeElectronicCurrent time => PLift (Thermal.Runtime.HoldsCollision time)
  | _ => PEmpty

def timedPairProjectionInactiveAt : LAlanineStage → Type
  | .nativeElectronicCurrent time => PLift (¬ Thermal.Runtime.HoldsCollision time)
  | _ => PUnit

/-- The pair face receives the complete joint already held by this exact source row. -/
def timedPairEffectAt : (stage : LAlanineStage) → timedPairProjectionActiveAt stage →
    Thermal.Runtime.TimedPairStepAt (nativeElectronicTime stage)
  | .targetErasedDensityBCPCensusFrozen, impossible => nomatch impossible
  | .physicalChemicalBondIncidenceCertified, impossible => nomatch impossible
  | .molecularEnergyLedgerCertified, impossible => nomatch impossible
  | .forceDrivenMaterialNextCertified, impossible => nomatch impossible
  | .electronicPropagationCertified, impossible => nomatch impossible
  | .nativeElectronicCurrent time, active =>
      Thermal.Runtime.timedPairStep time
        ((entryAt (.nativeElectronicCurrent time)).2.heldPair active.down)
        ((entryAt (.nativeElectronicCurrent time)).2.heldPair_exact active.down)

/-- The thermal compiler receives this exact row's operator, before its next is written. -/
def thermalCollisionEffectAt : (stage : LAlanineStage) →
    thermalProjectionActiveAt stage → Thermal.Runtime.ThermalCollisionMaterial
  | .targetErasedDensityBCPCensusFrozen, impossible => nomatch impossible
  | .physicalChemicalBondIncidenceCertified, impossible => nomatch impossible
  | .molecularEnergyLedgerCertified, impossible => nomatch impossible
  | .forceDrivenMaterialNextCertified, impossible => nomatch impossible
  | .electronicPropagationCertified, impossible => nomatch impossible
  | .nativeElectronicCurrent time, _active =>
      Thermal.Runtime.collideCurrent (entryAt (.nativeElectronicCurrent time)).2.density

/-- The installed effect consumes the density held by this exact source row. -/
def nativeElectronicEffectAt : (stage : LAlanineStage) →
    nativeElectronicProjectionActiveAt stage →
      Propagation.Runtime.NativeElectronicStepAt (nativeElectronicTime stage)
  | .targetErasedDensityBCPCensusFrozen, impossible => nomatch impossible
  | .physicalChemicalBondIncidenceCertified, impossible => nomatch impossible
  | .molecularEnergyLedgerCertified, impossible => nomatch impossible
  | .forceDrivenMaterialNextCertified, impossible => nomatch impossible
  | .electronicPropagationCertified, _active =>
      Propagation.Runtime.nativeElectronicStep 1
        (entryAt .electronicPropagationCertified).2.nativeTarget
        (by
          have sourceExact := (entryAt .electronicPropagationCertified).2.nativeTargetExact
          rw [(entryAt .electronicPropagationCertified).2.sourceMatricesExact] at sourceExact
          simpa only [Rat.cast_one] using sourceExact)
  | .nativeElectronicCurrent time, _active =>
      Propagation.Runtime.nativeElectronicStep time
        (entryAt (.nativeElectronicCurrent time)).2.density
        ((entryAt (.nativeElectronicCurrent time)).2.density_eq_source)

def baseProjectionLaw :
    SourceNativeProjectionLaw restructuringSource.toLedgerSource where
  Projection := LAlanineSiblingProjection
  ActiveAt := fun projection {current} _occurrence =>
    match projection with
    | .physicalDensity | .chemicalIncidence => projectionActiveAt current
    | .molecularDensityField | .molecularEnergyLedger => energyProjectionActiveAt current
    | .forceSourceEnergyLedger | .forceTargetEnergyLedger | .forceDrivenMaterialUpdate =>
        forceProjectionActiveAt current
    | .electronicPropagationSource | .electronicHamiltonian | .electronicDensityLaw |
        .electronicCurrentDensity | .electronicNativeTarget => electronicProjectionActiveAt current
    | .nativeElectronicEvolution => nativeElectronicProjectionActiveAt current
    | .thermalCollision => thermalProjectionActiveAt current
    | .timedPairEvolution => timedPairProjectionActiveAt current
  InactiveAt := fun projection {current} _occurrence =>
    match projection with
    | .physicalDensity | .chemicalIncidence => projectionInactiveAt current
    | .molecularDensityField | .molecularEnergyLedger => energyProjectionInactiveAt current
    | .forceSourceEnergyLedger | .forceTargetEnergyLedger | .forceDrivenMaterialUpdate =>
        forceProjectionInactiveAt current
    | .electronicPropagationSource | .electronicHamiltonian | .electronicDensityLaw |
        .electronicCurrentDensity | .electronicNativeTarget => electronicProjectionInactiveAt current
    | .nativeElectronicEvolution => nativeElectronicProjectionInactiveAt current
    | .thermalCollision => thermalProjectionInactiveAt current
    | .timedPairEvolution => timedPairProjectionInactiveAt current
  classify := by
    intro projection current _occurrence
    cases projection <;> cases current
    all_goals first
      | exact .inl PUnit.unit
      | exact .inr PUnit.unit
      | rename_i time
        -- The mathematical classifier must not re-evaluate the 9604-entry source clock.
        letI : Decidable (time = Thermal.Preparation.collisionCurrentTime) := Classical.propDecidable _
        exact if active : time = Thermal.Preparation.collisionCurrentTime then
          .inl ⟨active⟩ else .inr ⟨active⟩
      | rename_i time
        letI : Decidable (Thermal.Runtime.HoldsCollision time) := Classical.propDecidable _
        exact if active : Thermal.Runtime.HoldsCollision time then
          .inl ⟨active⟩ else .inr ⟨active⟩
  PayloadAt := fun projection {current} _occurrence _active =>
    match projection with
    | .physicalDensity =>
        PLift SourceGeneratedTargetErasedLAlanine40KBondDensityCrown
    | .chemicalIncidence =>
        PLift SourceGeneratedLAlanine40KPhysicalChemicalBondIncidenceCrown
    | .molecularDensityField => SourceRecordedTargetErasedDensityAt
    | .molecularEnergyLedger => Energy.Interface.MolecularEnergyLedger
    | .forceSourceEnergyLedger => Energy.Interface.MolecularEnergyLedger
    | .forceTargetEnergyLedger => Energy.Interface.MolecularEnergyLedger
    | .forceDrivenMaterialUpdate => Force.Interface.NuclearUpdateReadout
    | .electronicPropagationSource => Propagation.Interface.ElectronicPropagationSource
    | .electronicHamiltonian | .electronicCurrentDensity | .electronicNativeTarget =>
        Propagation.Dynamics.ElectronicOperator
    | .electronicDensityLaw => ℝ → Propagation.Dynamics.ElectronicOperator
    | .nativeElectronicEvolution =>
        Propagation.Runtime.NativeElectronicStepAt (nativeElectronicTime current)
    | .thermalCollision => Thermal.Runtime.ThermalCollisionMaterial
    | .timedPairEvolution => Thermal.Runtime.TimedPairStepAt (nativeElectronicTime current)
  project := by
    intro projection current _occurrence active
    cases projection with
    | physicalDensity =>
        exact ⟨sourceGeneratedTargetErasedLAlanine40KBondDensity_crown⟩
    | chemicalIncidence =>
        exact ⟨sourceGeneratedLAlanine40KPhysicalChemicalBondIncidence_crown⟩
    | molecularDensityField => exact sourceRecorded
    | molecularEnergyLedger => exact Energy.Source.energyLedger
    | forceSourceEnergyLedger => exact Energy.Source.energyLedger
    | forceTargetEnergyLedger => exact Force.Source.updateReadout.targetEnergyLedger
    | forceDrivenMaterialUpdate => exact Force.Source.updateReadout
    | electronicPropagationSource => exact Propagation.Source.electronicSource
    | electronicHamiltonian =>
        exact Propagation.Dynamics.hamiltonian Propagation.Source.electronicSource
    | electronicDensityLaw =>
        exact Propagation.Dynamics.densityEvolution Propagation.Source.electronicSource
    | electronicCurrentDensity =>
        exact Propagation.Dynamics.initialDensity Propagation.Source.electronicSource
    | electronicNativeTarget => exact Propagation.Producer.nativeElectronicNext
    | nativeElectronicEvolution => exact nativeElectronicEffectAt current active
    | thermalCollision => exact thermalCollisionEffectAt current active
    | timedPairEvolution => exact timedPairEffectAt current active

def baseAuthoritySource : SourceNativeAuthoritySource N V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource
      (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic N
  projectionLaw := baseProjectionLaw

def sourceEntryAt {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt N
      (nativeSource.toRootSource.account.supportOf occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact entryAt current

def sourceRow {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeFiniteLedgerPatchGeneratedEntryAt nativeSource
      ledgerCompiler.ExactTransitionAt ledgerCompiler.writeRowSource
      ledgerCompiler.terminalRowSource (ledgerCompiler.compile occurrence)
      (ledgerCompiler.compilePatch occurrence) (sourceEntryAt occurrence) :=
  (sourceNativeFiniteLedgerPatchGeneratedEntry? nativeSource
      ledgerCompiler.ExactTransitionAt ledgerCompiler.writeRowSource
      ledgerCompiler.terminalRowSource (ledgerCompiler.compile occurrence)
      (ledgerCompiler.compilePatch occurrence) (sourceEntryAt occurrence)).get (by
        rcases occurrence with ⟨support, event⟩
        cases event
        rfl)

def successor {current : V.Current}
    (occurrence : nativeSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerGeneratedSuccessorAt occurrence
      (ledgerCompiler.compile occurrence) :=
  (SourceNativeLedgerGeneratedSuccessorAt.ofGenerated?
    (ledgerCompiler.compile occurrence)).get (by
      rcases occurrence with ⟨support, event⟩
      cases event
      rfl)

theorem occurrence_unique {current : V.Current}
    (left right : nativeSource.toRootSource.actual.OccurrenceAt current) :
    left = right := by
  rcases left with ⟨leftSupport, leftEvent⟩
  rcases right with ⟨rightSupport, rightEvent⟩
  cases leftEvent
  cases rightEvent
  rfl

def renewalRootShell : SourceNativeRenewalRootShellAt ledgerSource where
  ActiveAt := fun {current} _occurrence => projectionActiveAt current
  InactiveAt := fun {current} _occurrence => projectionInactiveAt current
  classify := by
    intro current _occurrence
    cases current with
    | targetErasedDensityBCPCensusFrozen => exact .inl PUnit.unit
    | physicalChemicalBondIncidenceCertified => exact .inr PUnit.unit
    | molecularEnergyLedgerCertified => exact .inr PUnit.unit
    | forceDrivenMaterialNextCertified => exact .inr PUnit.unit
    | electronicPropagationCertified => exact .inr PUnit.unit
    | nativeElectronicCurrent _time => exact .inr PUnit.unit
  sourceEntry := fun occurrence _active => sourceEntryAt occurrence
  selectedRow := fun occurrence _active => sourceRow occurrence
  successor := fun occurrence _active => successor occurrence
  activeOccurrences_eq := by
    intro leftCurrent rightCurrent leftOccurrence rightOccurrence leftActive rightActive
    cases leftCurrent with
    | targetErasedDensityBCPCensusFrozen =>
        cases rightCurrent with
        | targetErasedDensityBCPCensusFrozen =>
            cases occurrence_unique leftOccurrence rightOccurrence
            rfl
        | physicalChemicalBondIncidenceCertified => exact nomatch rightActive
        | molecularEnergyLedgerCertified => exact nomatch rightActive
        | forceDrivenMaterialNextCertified => exact nomatch rightActive
        | electronicPropagationCertified => exact nomatch rightActive
        | nativeElectronicCurrent _time => exact nomatch rightActive
    | physicalChemicalBondIncidenceCertified => exact nomatch leftActive
    | molecularEnergyLedgerCertified => exact nomatch leftActive
    | forceDrivenMaterialNextCertified => exact nomatch leftActive
    | electronicPropagationCertified => exact nomatch leftActive
    | nativeElectronicCurrent _time => exact nomatch leftActive

end

end LAlanine40K2025.Root
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
