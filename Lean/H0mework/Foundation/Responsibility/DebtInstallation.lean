import H0mework.Foundation.Responsibility.DebtCompiler

/-!
# Source-ledger installation boundary for direct debt activation

The direct compiler's positive branches are exactly the payloads needed by
the existing source-native ledger ABI.  A native structural step can install
the strict whole-ledger evolution, and a structural faithful terminal can
install the source terminal evolution.

An obstruction has no such installation.  The source-native ledger ABI is
exhaustive between a generated successor and a faithful terminal, whereas the
obstruction compiler image is a same-row U7 theory audit with neither.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace RootGeneratedDebtActivationDirect

open DebtActivationLedger
open DebtActivationWorld

universe u

/-- Existing structural data sufficient to install one source-generated
strict debt step as a native-write ledger compiler image.  Both support
equalities are indexed by the exact source occurrences. -/
structure NativeStepInstallationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    (activation : OccurrenceIndexedSourceAt lower current)
    {target : activation.law.DebtState}
    (step : activation.law.StepAt activation.state target)
    {RootV : Vocabulary.{u}}
    (rootSource : SourceNativeSource activation.World RootV)
    (rootCurrent : RootV.Current)
    (event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩) :
    Type u where
  write : RootV.NativeWriteAt rootCurrent
  structural_eq :
    rootSource.toRootSource.actual.compile
      ⟨⟨activation.lowerSupport, some activation.state⟩, event⟩ =
        .nativeWrite write
  targetEvent : rootSource.law.EventAt (RootV.nativeTarget write)
    ⟨activation.lowerSupport, some target⟩

namespace NativeStepInstallationAt

/-- Install the exact strict whole-ledger evolution in the existing
source-native ledger output type. -/
def generated
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {activation : OccurrenceIndexedSourceAt lower current}
    {target : activation.law.DebtState}
    {step : activation.law.StepAt activation.state target}
    {RootV : Vocabulary.{u}}
    {rootSource : SourceNativeSource activation.World RootV}
    {rootCurrent : RootV.Current}
    {event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩}
    (installation :
      NativeStepInstallationAt activation step rootSource rootCurrent event) :
    SourceNativeLedgerEvolutionAt rootSource
      ⟨⟨activation.lowerSupport, some activation.state⟩, event⟩ := by
  rcases installation with ⟨write, structural_eq, targetEvent⟩
  exact .nativeWrite write structural_eq
    ⟨⟨activation.lowerSupport, some target⟩, targetEvent⟩
    (stepLedgerEvolution activation.lowerSupport step)

end NativeStepInstallationAt

/-- Existing structural data sufficient to install one source-generated
support terminal as a faithful-terminal ledger compiler image. -/
structure SupportTerminalInstallationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    (activation : OccurrenceIndexedSourceAt lower current)
    (terminal : activation.law.SupportTerminalAt activation.state)
    {RootV : Vocabulary.{u}}
    (rootSource : SourceNativeSource activation.World RootV)
    (rootCurrent : RootV.Current)
    (event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩) :
    Type u where
  terminalPayload : RootV.FaithfulTerminalAt rootCurrent
  structural_eq :
    rootSource.toRootSource.actual.compile
      ⟨⟨activation.lowerSupport, some activation.state⟩, event⟩ =
      .faithfulTerminal terminalPayload

namespace SupportTerminalInstallationAt

/-- Install the exact whole-ledger terminal in the existing source-native
ledger output type. -/
def generated
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {activation : OccurrenceIndexedSourceAt lower current}
    {terminal : activation.law.SupportTerminalAt activation.state}
    {RootV : Vocabulary.{u}}
    {rootSource : SourceNativeSource activation.World RootV}
    {rootCurrent : RootV.Current}
    {event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩}
    (installation :
      SupportTerminalInstallationAt activation terminal rootSource rootCurrent
        event) :
    SourceNativeLedgerEvolutionAt rootSource
      ⟨⟨activation.lowerSupport, some activation.state⟩, event⟩ := by
  rcases installation with ⟨terminalPayload, structural_eq⟩
  exact .faithfulTerminal terminalPayload structural_eq
    (supportTerminalLedgerEvolution activation.lowerSupport terminal)

end SupportTerminalInstallationAt

/-- Branch-exact source-ledger installation mouth.

The source-generated obstruction branch reduces definitionally to `PEmpty`;
it cannot be renamed into a native write or faithful terminal. -/
def SourceNativeLedgerInstallationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    (activation : OccurrenceIndexedSourceAt lower current)
    {RootV : Vocabulary.{u}}
    (rootSource : SourceNativeSource activation.World RootV)
    (rootCurrent : RootV.Current)
    (event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩) :
    GeneratedDispositionAt activation.law activation.state → Type u
  | .step step =>
      NativeStepInstallationAt activation step rootSource rootCurrent event
  | .supportTerminal terminal =>
      SupportTerminalInstallationAt activation terminal rootSource rootCurrent
        event
  | .obstruction _obstruction => PEmpty

/-- Installation mouth selected only by the domain source's generated
disposition. -/
abbrev GeneratedSourceNativeLedgerInstallationAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    (activation : OccurrenceIndexedSourceAt lower current)
    {RootV : Vocabulary.{u}}
    (rootSource : SourceNativeSource activation.World RootV)
    (rootCurrent : RootV.Current)
    (event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩) :=
  SourceNativeLedgerInstallationAt activation rootSource rootCurrent event
    activation.generatedDisposition

/-- Every inhabited positive installation produces the existing canonical
source-ledger output object. -/
def SourceNativeLedgerInstallationAt.generated
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {activation : OccurrenceIndexedSourceAt lower current}
    {RootV : Vocabulary.{u}}
    {rootSource : SourceNativeSource activation.World RootV}
    {rootCurrent : RootV.Current}
    {event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩}
    {disposition : GeneratedDispositionAt activation.law activation.state}
    (installation : SourceNativeLedgerInstallationAt activation rootSource
      rootCurrent event disposition) :
    SourceNativeLedgerEvolutionAt rootSource
      ⟨⟨activation.lowerSupport, some activation.state⟩, event⟩ := by
  cases disposition with
  | step step => exact NativeStepInstallationAt.generated installation
  | supportTerminal terminal =>
      exact SupportTerminalInstallationAt.generated installation
  | obstruction obstruction => exact nomatch installation

/-- A generated strict-step equality exposes the corresponding positive
source-ledger installation mouth. -/
def generatedStepInstallation
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {activation : OccurrenceIndexedSourceAt lower current}
    {target : activation.law.DebtState}
    {step : activation.law.StepAt activation.state target}
    {RootV : Vocabulary.{u}}
    {rootSource : SourceNativeSource activation.World RootV}
    {rootCurrent : RootV.Current}
    {event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩}
    (generated_eq : activation.generatedDisposition = .step step)
    (installation : NativeStepInstallationAt activation step rootSource
      rootCurrent event) :
    GeneratedSourceNativeLedgerInstallationAt activation rootSource rootCurrent
      event := by
  unfold GeneratedSourceNativeLedgerInstallationAt
  rw [generated_eq]
  exact installation

/-- A generated support-terminal equality exposes the corresponding positive
source-ledger installation mouth. -/
def generatedTerminalInstallation
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {activation : OccurrenceIndexedSourceAt lower current}
    {terminal : activation.law.SupportTerminalAt activation.state}
    {RootV : Vocabulary.{u}}
    {rootSource : SourceNativeSource activation.World RootV}
    {rootCurrent : RootV.Current}
    {event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩}
    (generated_eq : activation.generatedDisposition =
      .supportTerminal terminal)
    (installation :
      SupportTerminalInstallationAt activation terminal rootSource rootCurrent
        event) :
    GeneratedSourceNativeLedgerInstallationAt activation rootSource rootCurrent
      event := by
  unfold GeneratedSourceNativeLedgerInstallationAt
  rw [generated_eq]
  exact installation

/-- An obstruction generated by the domain source has no source-ledger
installation inhabitant.  Its canonical output is the U7 object from the
direct compiler, not a normal root evolution. -/
theorem generatedObstructionInstallation_isEmpty
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    {activation : OccurrenceIndexedSourceAt lower current}
    {obstruction : activation.law.ObstructionAt activation.state}
    {RootV : Vocabulary.{u}}
    {rootSource : SourceNativeSource activation.World RootV}
    {rootCurrent : RootV.Current}
    {event : rootSource.law.EventAt rootCurrent
      ⟨activation.lowerSupport, some activation.state⟩}
    (generated_eq : activation.generatedDisposition =
      .obstruction obstruction) :
    IsEmpty
      (GeneratedSourceNativeLedgerInstallationAt activation rootSource
        rootCurrent event) := by
  constructor
  intro installation
  unfold GeneratedSourceNativeLedgerInstallationAt at installation
  rw [generated_eq] at installation
  exact nomatch installation

/-! ## Exact current-ABI boundary -/

/-- Faithful-terminal witness carried by an existing source-ledger compiler
image. -/
def SourceNativeLedgerFaithfulTerminalAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) : Type u :=
  match generated with
  | .faithfulTerminal .. => PUnit
  | .nativeWrite ..
  | .relationWrite ..
  | .continuedTransport ..
  | .borromeanRedirect .. => PEmpty

/-- The present source-ledger ABI is exhaustive: every image produces either
an ordinary successor or a faithful terminal. -/
def sourceNativeLedgerSuccessorOrTerminal
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) :
    SourceNativeLedgerGeneratedSuccessorAt occurrence generated ⊕
      SourceNativeLedgerFaithfulTerminalAt generated := by
  cases generated with
  | nativeWrite => exact .inl PUnit.unit
  | relationWrite => exact .inl PUnit.unit
  | continuedTransport => exact .inl PUnit.unit
  | borromeanRedirect => exact .inl PUnit.unit
  | faithfulTerminal => exact .inr PUnit.unit

/-- A hypothetical source-ledger image with neither successor nor terminal. -/
structure SourceNativeLedgerCutOnlyAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) : Type u where
  noSuccessor :
    SourceNativeLedgerGeneratedSuccessorAt occurrence generated → PEmpty
  noTerminal : SourceNativeLedgerFaithfulTerminalAt generated → PEmpty

/-- Exact no-go: the existing source-ledger output type cannot encode a
nonterminal, no-successor U7 cut. -/
theorem sourceNativeLedgerCutOnly_isEmpty
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {source : SourceNativeSource N V} {current : V.Current}
    {occurrence : source.toRootSource.actual.OccurrenceAt current}
    (generated : SourceNativeLedgerEvolutionAt source occurrence) :
    IsEmpty (SourceNativeLedgerCutOnlyAt generated) := by
  constructor
  intro cutOnly
  cases sourceNativeLedgerSuccessorOrTerminal generated with
  | inl successor => exact PEmpty.elim (cutOnly.noSuccessor successor)
  | inr terminal => exact PEmpty.elim (cutOnly.noTerminal terminal)

end RootGeneratedDebtActivationDirect
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
