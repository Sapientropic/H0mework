import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Receipts.OriginalRoot

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
universe u
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

/-- The complete original admission depends on the actual lower ledger
source. Restructuring receipts do not change any of its dependent fields. -/
structure AdmissionBody {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
    (lower : SourceNativeLedgerSource N V) : Type (u + 1) where

  ActualV : ConstructiveRoot.Vocabulary.{u}
  actualSource : SourceNativeLedgerSource N ActualV

  currentPresentation : ConstructivePresentation ActualV.Current V.Current
  initial_eq :
    currentPresentation.forward actualSource.source.initial =
      lower.source.initial

  occurrencePresentation : (current : V.Current) ->
    ConstructivePresentation
      (actualSource.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current))
      (lower.source.toRootSource.actual.OccurrenceAt current)

  evolutionPresentation : (current : V.Current) ->
    ConstructivePresentation
      (EvolutionAt ActualV (currentPresentation.backward current))
      (EvolutionAt V current)
  structural_commutes : (current : V.Current) ->
    (occurrence :
      actualSource.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    (evolutionPresentation current).forward
        (actualSource.source.toRootSource.actual.compile occurrence) =
      lower.source.toRootSource.actual.compile
        ((occurrencePresentation current).forward occurrence)

  kind_commutes : (current : V.Current) ->
    (evolution : EvolutionAt ActualV
      (currentPresentation.backward current)) ->
    ((evolutionPresentation current).forward evolution).kind = evolution.kind

  nextCurrent_commutes : (current : V.Current) ->
    (evolution : EvolutionAt ActualV
      (currentPresentation.backward current)) ->
    Option.map currentPresentation.forward evolution.nextCurrent? =
      ((evolutionPresentation current).forward evolution).nextCurrent?
  support_commutes : (current : V.Current) ->
    (occurrence :
      actualSource.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    lower.source.toRootSource.account.supportOf
        ((occurrencePresentation current).forward occurrence) =
      actualSource.source.toRootSource.account.supportOf occurrence
  wholeLedgerWriteBack_commutes : (current : V.Current) ->
    (occurrence :
      actualSource.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    HEq
      (lower.ledgerCompiler.compile
        ((occurrencePresentation current).forward occurrence))
      (actualSource.ledgerCompiler.compile occurrence)
  finitePatch_commutes : (current : V.Current) ->
    (occurrence :
      actualSource.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    HEq
      (lower.ledgerCompiler.compilePatch
        ((occurrencePresentation current).forward occurrence))
      (actualSource.ledgerCompiler.compilePatch occurrence)

  cofinalEventPresentation :
    ConstructivePresentation ActualV.cofinal.Event V.cofinal.Event

  cofinalEmit_commutes :
    Option.map cofinalEventPresentation.forward ActualV.cofinal.emit? =
      V.cofinal.emit?

  cofinalPath_commutes : (event : ActualV.cofinal.Event) -> (index : Nat) ->
    currentPresentation.forward (ActualV.cofinal.pathAt event index) =
      V.cofinal.pathAt (cofinalEventPresentation.forward event) index

  cofinalTarget_commutes : (event : ActualV.cofinal.Event) ->
    currentPresentation.forward (ActualV.cofinal.target event) =
      V.cofinal.target (cofinalEventPresentation.forward event)
  terminal_exhausts_actual_inventory :
    {current : V.Current} ->
    (occurrence :
      actualSource.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    (terminal : V.FaithfulTerminalAt current) ->
    (evolutionPresentation current).forward
        (actualSource.source.toRootSource.actual.compile occurrence) =
      .faithfulTerminal terminal ->
    IsEmpty (SourceNativeActualOutgoingEventAt actualSource
      (currentPresentation.backward current))

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}

def admissionBodyEquiv (represented : SourceNativeRestructuringLedgerSource N V) :
    SourceNativeCompleteEventInventoryAdmission represented ≃ AdmissionBody represented.toLedgerSource where
  toFun := fun value => {
    ActualV := value.ActualV
    actualSource := value.actualSource
    currentPresentation := value.currentPresentation
    initial_eq := value.initial_eq
    occurrencePresentation := value.occurrencePresentation
    evolutionPresentation := value.evolutionPresentation
    structural_commutes := value.structural_commutes
    kind_commutes := value.kind_commutes
    nextCurrent_commutes := value.nextCurrent_commutes
    support_commutes := value.support_commutes
    wholeLedgerWriteBack_commutes := value.wholeLedgerWriteBack_commutes
    finitePatch_commutes := value.finitePatch_commutes
    cofinalEventPresentation := value.cofinalEventPresentation
    cofinalEmit_commutes := value.cofinalEmit_commutes
    cofinalPath_commutes := value.cofinalPath_commutes
    cofinalTarget_commutes := value.cofinalTarget_commutes
    terminal_exhausts_actual_inventory := value.terminal_exhausts_actual_inventory
  }
  invFun := fun value => {
    ActualV := value.ActualV
    actualSource := value.actualSource
    currentPresentation := value.currentPresentation
    initial_eq := value.initial_eq
    occurrencePresentation := value.occurrencePresentation
    evolutionPresentation := value.evolutionPresentation
    structural_commutes := value.structural_commutes
    kind_commutes := value.kind_commutes
    nextCurrent_commutes := value.nextCurrent_commutes
    support_commutes := value.support_commutes
    wholeLedgerWriteBack_commutes := value.wholeLedgerWriteBack_commutes
    finitePatch_commutes := value.finitePatch_commutes
    cofinalEventPresentation := value.cofinalEventPresentation
    cofinalEmit_commutes := value.cofinalEmit_commutes
    cofinalPath_commutes := value.cofinalPath_commutes
    cofinalTarget_commutes := value.cofinalTarget_commutes
    terminal_exhausts_actual_inventory := value.terminal_exhausts_actual_inventory
  }
  left_inv := fun value => by cases value; rfl
  right_inv := fun value => by cases value; rfl

/-- Transport uses literal lower-source equality, retaining the entire
original admission rather than replacing it by a reflective admission. -/
def reindexAdmission {left right : SourceNativeRestructuringLedgerSource N V}
    (same : left.toLedgerSource = right.toLedgerSource) :
    SourceNativeCompleteEventInventoryAdmission left ≃ SourceNativeCompleteEventInventoryAdmission right :=
  (admissionBodyEquiv left).trans
    ((Equiv.cast (congrArg AdmissionBody same)).trans (admissionBodyEquiv right).symm)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
