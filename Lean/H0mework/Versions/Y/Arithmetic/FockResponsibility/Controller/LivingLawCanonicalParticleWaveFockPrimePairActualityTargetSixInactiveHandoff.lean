import H0mework.Foundation.Responsibility.DebtPositiveRoot
import H0mework.Versions.Y.Arithmetic.FockResponsibility.TargetSixActionDebt

/-!
# Target-six direct controller and inactive arithmetic handoff

The actual `3 + 3 = 6` source branch specializes the generic direct positive
root.  Its strict payment reaches the paid current; only the resulting
support terminal hands control to the canonical arithmetic next current on
the debt-inactive face.  The generic residual diagnostic is deliberately kept
outside this positive controller, so no sibling source can select its branch.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairActualityTargetSixInactiveHandoff

open CanonicalUnitArithmeticRoot
open DebtActivationLedger
open DebtActivationWorld
open ParticleWaveFockPrimePairActualityTargetSixActionDebt
open RootGeneratedDebtActivationDirect
open RootGeneratedDebtActivationDirectPositive
open RootGeneratedProofRelevantRestructuring

noncomputable section

abbrev BaseN := CanonicalUnitArithmeticRoot.N
abbrev Activation := ParticleWaveFockPrimePairActualityTargetSixActionDebt.Activation
abbrev Law := ParticleWaveFockPrimePairActualityTargetSixActionDebt.Law
abbrev World := Activation.World

abbrev targetState : Law.DebtState :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.targetState
abbrev payment : Law.StepAt
    ParticleWaveFockPrimePairActualityTargetSixActionDebt.State.open
    targetState :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.payment
abbrev terminal : Law.SupportTerminalAt targetState :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.terminal

theorem sourceDisposition_is_step :
    Activation.generatedDisposition = .step payment :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.sourceDisposition_is_step

def positive : GeneratedPositiveAt Activation :=
  ParticleWaveFockPrimePairActualityTargetSixActionDebt.positive

abbrev ControllerV := RootGeneratedDebtActivationDirectPositive.V positive
abbrev controllerAuthoritySource :=
  RootGeneratedDebtActivationDirectPositive.authoritySource positive
abbrev controllerAuthoritativeRoot :=
  RootGeneratedDebtActivationDirectPositive.authoritativeRoot positive
abbrev controllerPaidVisit :=
  RootGeneratedDebtActivationDirectPositive.paidVisit positive
abbrev controllerPaidTerminalAuthority :=
  RootGeneratedDebtActivationDirectPositive.paidTerminalAuthority positive

namespace InactiveContinuation

abbrev V := CanonicalUnitArithmeticRoot.V

def initialCurrent : V.Current :=
  CanonicalUnitArithmeticRoot.next Activation.lowerSupport

def supportAt (current : V.Current) : World.Support :=
  ⟨current, none⟩

structure EventAt (current : V.Current) (support : World.Support) : Type where
  support_eq : support = supportAt current

def eventAlgebra : SourceNativeEventAlgebra World V where
  EventAt := EventAt
  compile := fun {current} {_support} _event =>
    .nativeWrite (CanonicalUnitArithmeticRoot.nativeWriteAt current)
  AffectedInventoryAt := fun _ => PUnit
  affectedInventoryPresentation := by
    intro current support event
    cases event.support_eq
    exact inactiveInventoryPresentation
      (law := Law)
      (CanonicalUnitArithmeticRoot.rootLedgerInventoryPresentation current)
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := by
    intro current support event
    cases event.support_eq
    rfl
  incidence_commutes := by
    intro current support event
    cases event.support_eq
    rfl
  lineage_commutes := by
    intro current support event
    cases event.support_eq
    rfl

def rootSource : SourceNativeSource World V where
  initial := initialCurrent
  law := eventAlgebra

def emitted (current : V.Current) :
    rootSource.toRootSource.actual.OccurrenceAt current :=
  ⟨supportAt current, ⟨rfl⟩⟩

structure ExactTransitionAt
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current)
    {targetSupport : World.Support}
    (_sourceEntry : OpenResponsibilityAt World occurrence.1)
    (_targetEntry : OpenResponsibilityAt World targetSupport) : Type where
  targetSupport_eq : targetSupport =
    supportAt (CanonicalUnitArithmeticRoot.next current)

def sourceEntry (current : V.Current) :
    OpenResponsibilityAt World (supportAt current) :=
  oldEntry (law := Law) (state? := none)
    (CanonicalUnitArithmeticRoot.rootLedgerEntry current)

def transferReceipt (current : V.Current) :
    World.DispositionAt (supportAt current) .transfer :=
  .inl (.transfer (CanonicalUnitArithmeticRoot.nativeWriteAt current))

def rowEvolution (current : V.Current) :
    LedgerEntryEvolutionAt World (sourceEntry current)
      (sourceEntry (CanonicalUnitArithmeticRoot.next current)) :=
  .transferred (transferReceipt current) rfl rfl (Nat.le_refl _)

def writeRowSource : LedgerWriteRowSourceAt rootSource ExactTransitionAt where
  IncidenceOccurrenceAt := by
    intro current occurrence targetSupport sourceEntry targetEntry
    exact ExactTransitionAt occurrence sourceEntry targetEntry
  compileEvolution := by
    intro current occurrence targetSupport sourceEntry targetEntry event
    rcases occurrence with ⟨support, sourceEvent⟩
    cases sourceEvent.support_eq
    cases event.targetSupport_eq
    have source_eq : sourceEntry = InactiveContinuation.sourceEntry current :=
      (inactiveInventoryPresentation
        (law := Law)
        (CanonicalUnitArithmeticRoot.rootLedgerInventoryPresentation current)
        ).forward_backward sourceEntry |>.symm
    have target_eq : targetEntry = InactiveContinuation.sourceEntry
        (CanonicalUnitArithmeticRoot.next current) :=
      (inactiveInventoryPresentation
        (law := Law)
        (CanonicalUnitArithmeticRoot.rootLedgerInventoryPresentation
          (CanonicalUnitArithmeticRoot.next current))
        ).forward_backward targetEntry |>.symm
    cases source_eq
    cases target_eq
    exact rowEvolution current
  compileExact := fun event => event

def terminalRowSource : LedgerTerminalRowSourceAt rootSource :=
  LedgerTerminalRowSourceAt.empty rootSource

def occurrenceEntry
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    OpenResponsibilityAt World occurrence.1 :=
  (rootSource.law.affectedInventoryPresentation occurrence.2).forward
    PUnit.unit

def generatedRows
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWriteRowsAt writeRowSource occurrence
      ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩ where
  size := 1
  sourceEntryAt := fun _ => occurrenceEntry occurrence
  targetEntryAt := fun _ => sourceEntry (CanonicalUnitArithmeticRoot.next current)
  rowAt := fun _ => writeRowSource.generate ⟨rfl⟩

def generatedCoverage
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    LedgerCompleteFiniteCoverageAt (generatedRows occurrence) where
  destinationIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  originIndex := fun _ => ⟨0, Nat.zero_lt_one⟩
  destination_sound := by
    intro entry
    change occurrenceEntry occurrence = entry
    exact (rootSource.law.affectedInventoryPresentation occurrence.2
      ).forward_backward entry
  origin_sound := by
    intro entry
    change sourceEntry (CanonicalUnitArithmeticRoot.next current) = entry
    exact (inactiveInventoryPresentation
      (law := Law)
      (CanonicalUnitArithmeticRoot.rootLedgerInventoryPresentation
        (CanonicalUnitArithmeticRoot.next current))
      ).forward_backward entry

def generatedPatch
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt writeRowSource occurrence
      ⟨supportAt (CanonicalUnitArithmeticRoot.next current)⟩ :=
  .complete (generatedRows occurrence) (generatedCoverage occurrence)

def generatedLedger
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerEvolutionAt rootSource occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event.support_eq
  exact .nativeWrite (CanonicalUnitArithmeticRoot.nativeWriteAt current) rfl
    (emitted (CanonicalUnitArithmeticRoot.next current))
    (generatedPatch ⟨supportAt current, ⟨rfl⟩⟩).toLedgerWriteEvolution

def ledgerCompiler : SourceNativeLedgerCompiler rootSource where
  IncidenceTransitionAt := fun _ _ _ => PUnit
  ExactTransitionAt := ExactTransitionAt
  exact_incidence := fun _ => PUnit.unit
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource
  terminalRowSource := terminalRowSource
  compile := generatedLedger
  compilePatch := by
    intro current occurrence
    rcases occurrence with ⟨support, event⟩
    cases event.support_eq
    exact ⟨generatedPatch ⟨supportAt current, ⟨rfl⟩⟩, rfl⟩

def ledgerSource : SourceNativeLedgerSource World V where
  source := rootSource
  ledgerCompiler := ledgerCompiler

def ledgerRoot : SourceNativeLedgerRootClosure World V where
  source := ledgerSource
  emitted := emitted
  compiler_commutes := fun _ => rfl

theorem inactiveEntrySubsingleton (current : V.Current) :
    Subsingleton (OpenResponsibilityAt World (supportAt current)) :=
  (inactiveInventoryPresentation
    (law := Law)
    (CanonicalUnitArithmeticRoot.rootLedgerInventoryPresentation current)
    ).subsingleton_target

def restructuringLaw : SourceNativeLedgerRestructuringLaw rootSource :=
  RootGeneratedProofRelevantRestructuring.law World (supportAt initialCurrent)
    rootSource

def restructuringCertification
    {current : V.Current}
    (occurrence : rootSource.toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt restructuringLaw
      (ledgerCompiler.compile occurrence) := by
  rcases occurrence with ⟨support, event⟩
  cases event.support_eq
  exact ExactLedgerRestructuringCertificationAt.ofInjective
    (fun left right _ => (inactiveEntrySubsingleton _).elim left right)
    (fun left right _ => (inactiveEntrySubsingleton _).elim left right)

def restructuringCompiler : SourceNativeRestructuringLedgerCompiler rootSource where
  ledgerCompiler := ledgerCompiler
  restructuringLaw := restructuringLaw
  certifyRestructuring := restructuringCertification

def restructuringSource : SourceNativeRestructuringLedgerSource World V where
  source := rootSource
  compiler := restructuringCompiler

def projectionLaw : SourceNativeProjectionLaw ledgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _occurrence => PUnit
  InactiveAt := fun _ {_current} _occurrence => PEmpty
  classify := fun _ {_current} _occurrence => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => PUnit
  project := fun _ {_current} _ _ => PUnit.unit

def authoritySource : SourceNativeAuthoritySource World V where
  restructuringSource := restructuringSource
  eventInventoryAdmission :=
    .reflOfNoFaithfulTerminal restructuringSource <| fun _current =>
      ⟨fun terminal => nomatch terminal⟩
  lawSurface := .rootSemantic World
  projectionLaw := projectionLaw

def authoritativeRoot : SourceNativeAuthoritativeRootClosure World V where
  source := authoritySource
  emitted := emitted
  compiler_commutes := fun _ => rfl

end InactiveContinuation

def handoffOccurrencePresentation : ConstructivePresentation
    (InactiveContinuation.authoritativeRoot.toRoot.actual.OccurrenceAt
      InactiveContinuation.initialCurrent)
    PUnit where
  forward := fun _ => PUnit.unit
  backward := fun _ => InactiveContinuation.authoritativeRoot.emitted
    InactiveContinuation.initialCurrent
  backward_forward := by
    rintro ⟨support, event⟩
    cases event.support_eq
    rfl
  forward_backward := fun value => by cases value; rfl

def terminalHandoffLaw : SourceNativeTerminalHandoffLaw
    controllerAuthoritySource :=
  SourceNativeTerminalHandoffLaw.create
    (fun {_current} _history {_occurrence} _terminal => PUnit)
    (fun {_current} _history {_occurrence} _terminal => PUnit.unit)
    (fun _event => InactiveContinuation.V)
    (fun _event => InactiveContinuation.authoritativeRoot)
    (fun _event => handoffOccurrencePresentation)
    (by intros; rfl)
    (by intros; rfl)
    (by
      intro current history occurrence terminalEvent event targetEntry
      cases current with
      | live => exact nomatch terminalEvent.terminal
      | paid =>
          rcases occurrence with ⟨support, sourceEvent⟩
          cases sourceEvent with
          | terminal =>
              rcases targetEntry with ⟨responsibility, opened⟩
              cases responsibility with
              | inl oldResponsibility =>
                  exact .inl ⟨oldEntry
                    (law := Law) (state? := some targetState)
                    (CanonicalUnitArithmeticRoot.rootLedgerEntry
                      Activation.lowerSupport), ⟨rfl, rfl⟩⟩
              | inr debtId => exact nomatch opened)
    (by
      intro current history occurrence terminalEvent event sourceEntry
        targetEntry sameDebt
      rcases targetEntry with ⟨responsibility, opened⟩
      cases responsibility with
      | inl oldResponsibility => exact Nat.zero_le _
      | inr debtId => exact nomatch opened)
    (by
      intro current history occurrence terminalEvent event sourceEntry left right
        leftIdentity rightIdentity
      exact (InactiveContinuation.inactiveEntrySubsingleton _).elim left right)

def livingRoot : SourceNativeLivingRootClosure World ControllerV where
  source := {
    base := controllerAuthoritySource
    terminalHandoff := terminalHandoffLaw }
  emitted := controllerAuthoritativeRoot.emitted
  compiler_commutes := controllerAuthoritativeRoot.compiler_commutes

def generatedTerminalHandoff : SourceNativeAuthoritativeRootCurrentAt World :=
  livingRoot.generatedTerminalHandoffAt (.finite controllerPaidVisit)
    controllerPaidTerminalAuthority

theorem generatedTerminalHandoff_is_inactive_next :
    generatedTerminalHandoff.V = InactiveContinuation.V ∧
      generatedTerminalHandoff.root = InactiveContinuation.authoritativeRoot ∧
      generatedTerminalHandoff.visit.current =
        CanonicalUnitArithmeticRoot.next Activation.lowerSupport :=
  ⟨rfl, rfl, rfl⟩

end


end ParticleWaveFockPrimePairActualityTargetSixInactiveHandoff
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
