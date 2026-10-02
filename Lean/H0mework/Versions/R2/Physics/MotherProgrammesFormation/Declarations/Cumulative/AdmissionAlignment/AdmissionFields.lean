import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.VocabularyRestriction

/-! Exact native admission fields indexed by the complete actual header.
The decomposition changes no original field or law; it enables the header
and the four whole programs to be recovered from their generated values. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionRestriction
open MotherAdmissionAlignment MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

abbrev Header (N : WorldRelationNetwork.{0}) :=
  Σ vocab : ConstructiveRoot.Vocabulary.{0}, SourceNativeLedgerSource N vocab

structure Fields {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (lower : SourceNativeLedgerSource N V) (header : Header N) : Type 1 where
  currentPresentation : ConstructivePresentation header.1.Current V.Current
  initial_eq :
    currentPresentation.forward header.2.source.initial =
      lower.source.initial

  occurrencePresentation : (current : V.Current) ->
    ConstructivePresentation
      (header.2.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current))
      (lower.source.toRootSource.actual.OccurrenceAt current)

  evolutionPresentation : (current : V.Current) ->
    ConstructivePresentation
      (EvolutionAt header.1 (currentPresentation.backward current))
      (EvolutionAt V current)
  structural_commutes : (current : V.Current) ->
    (occurrence :
      header.2.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    (evolutionPresentation current).forward
        (header.2.source.toRootSource.actual.compile occurrence) =
      lower.source.toRootSource.actual.compile
        ((occurrencePresentation current).forward occurrence)

  kind_commutes : (current : V.Current) ->
    (evolution : EvolutionAt header.1
      (currentPresentation.backward current)) ->
    ((evolutionPresentation current).forward evolution).kind = evolution.kind

  nextCurrent_commutes : (current : V.Current) ->
    (evolution : EvolutionAt header.1
      (currentPresentation.backward current)) ->
    Option.map currentPresentation.forward evolution.nextCurrent? =
      ((evolutionPresentation current).forward evolution).nextCurrent?
  support_commutes : (current : V.Current) ->
    (occurrence :
      header.2.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    lower.source.toRootSource.account.supportOf
        ((occurrencePresentation current).forward occurrence) =
      header.2.source.toRootSource.account.supportOf occurrence
  wholeLedgerWriteBack_commutes : (current : V.Current) ->
    (occurrence :
      header.2.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    HEq
      (lower.ledgerCompiler.compile
        ((occurrencePresentation current).forward occurrence))
      (header.2.ledgerCompiler.compile occurrence)
  finitePatch_commutes : (current : V.Current) ->
    (occurrence :
      header.2.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    HEq
      (lower.ledgerCompiler.compilePatch
        ((occurrencePresentation current).forward occurrence))
      (header.2.ledgerCompiler.compilePatch occurrence)

  cofinalEventPresentation :
    ConstructivePresentation header.1.cofinal.Event V.cofinal.Event

  cofinalEmit_commutes :
    Option.map cofinalEventPresentation.forward header.1.cofinal.emit? =
      V.cofinal.emit?

  cofinalPath_commutes : (event : header.1.cofinal.Event) -> (index : Nat) ->
    currentPresentation.forward (header.1.cofinal.pathAt event index) =
      V.cofinal.pathAt (cofinalEventPresentation.forward event) index

  cofinalTarget_commutes : (event : header.1.cofinal.Event) ->
    currentPresentation.forward (header.1.cofinal.target event) =
      V.cofinal.target (cofinalEventPresentation.forward event)
  terminal_exhausts_actual_inventory :
    {current : V.Current} ->
    (occurrence :
      header.2.source.toRootSource.actual.OccurrenceAt
        (currentPresentation.backward current)) ->
    (terminal : V.FaithfulTerminalAt current) ->
    (evolutionPresentation current).forward
        (header.2.source.toRootSource.actual.compile occurrence) =
      .faithfulTerminal terminal ->
    IsEmpty (SourceNativeActualOutgoingEventAt header.2
      (currentPresentation.backward current))

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (represented : SourceNativeRestructuringLedgerSource N V)

def assemble (header : Header N) (fields : Fields represented.toLedgerSource header) :
    SourceNativeCompleteEventInventoryAdmission represented where
  ActualV := header.1
  actualSource := header.2
  currentPresentation := fields.currentPresentation
  initial_eq := fields.initial_eq
  occurrencePresentation := fields.occurrencePresentation
  evolutionPresentation := fields.evolutionPresentation
  structural_commutes := fields.structural_commutes
  kind_commutes := fields.kind_commutes
  nextCurrent_commutes := fields.nextCurrent_commutes
  support_commutes := fields.support_commutes
  wholeLedgerWriteBack_commutes := fields.wholeLedgerWriteBack_commutes
  finitePatch_commutes := fields.finitePatch_commutes
  cofinalEventPresentation := fields.cofinalEventPresentation
  cofinalEmit_commutes := fields.cofinalEmit_commutes
  cofinalPath_commutes := fields.cofinalPath_commutes
  cofinalTarget_commutes := fields.cofinalTarget_commutes
  terminal_exhausts_actual_inventory := fields.terminal_exhausts_actual_inventory

def fieldsOf (admission : SourceNativeCompleteEventInventoryAdmission represented) :
    Fields represented.toLedgerSource ⟨admission.ActualV, admission.actualSource⟩ where
  currentPresentation := admission.currentPresentation
  initial_eq := admission.initial_eq
  occurrencePresentation := admission.occurrencePresentation
  evolutionPresentation := admission.evolutionPresentation
  structural_commutes := admission.structural_commutes
  kind_commutes := admission.kind_commutes
  nextCurrent_commutes := admission.nextCurrent_commutes
  support_commutes := admission.support_commutes
  wholeLedgerWriteBack_commutes := admission.wholeLedgerWriteBack_commutes
  finitePatch_commutes := admission.finitePatch_commutes
  cofinalEventPresentation := admission.cofinalEventPresentation
  cofinalEmit_commutes := admission.cofinalEmit_commutes
  cofinalPath_commutes := admission.cofinalPath_commutes
  cofinalTarget_commutes := admission.cofinalTarget_commutes
  terminal_exhausts_actual_inventory := admission.terminal_exhausts_actual_inventory

theorem assemble_fieldsOf (admission : SourceNativeCompleteEventInventoryAdmission represented) :
    assemble represented ⟨admission.ActualV, admission.actualSource⟩ (fieldsOf represented admission) = admission := by
  cases admission
  rfl

theorem fieldsOf_assemble (header : Header N) (fields : Fields represented.toLedgerSource header) :
    fieldsOf represented (assemble represented header fields) = fields := by
  cases fields
  rfl

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionRestriction
