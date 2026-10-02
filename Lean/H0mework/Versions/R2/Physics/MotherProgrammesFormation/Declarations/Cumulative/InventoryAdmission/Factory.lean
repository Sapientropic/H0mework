import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InventoryAdmission.PresentationData

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
open MotherNetworkFactory
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

structure AdmissionCheck (value : SourcePair) (data : PresentationData value) : Prop where
  initial_eq :
    data.current.forward value.2.2.source.initial =
      (Represented value).toLedgerSource.source.initial
  structural_commutes : (current : (RepresentedV value).Current) ->
    (occurrence :
      value.2.2.source.toRootSource.actual.OccurrenceAt
        (data.current.backward current)) ->
    (data.evolution current).forward
        (value.2.2.source.toRootSource.actual.compile occurrence) =
      (Represented value).toLedgerSource.source.toRootSource.actual.compile
        ((data.occurrence current).forward occurrence)
  kind_commutes : (current : (RepresentedV value).Current) ->
    (evolution : EvolutionAt value.2.1
      (data.current.backward current)) ->
    ((data.evolution current).forward evolution).kind = evolution.kind
  nextCurrent_commutes : (current : (RepresentedV value).Current) ->
    (evolution : EvolutionAt value.2.1
      (data.current.backward current)) ->
    Option.map data.current.forward evolution.nextCurrent? =
      ((data.evolution current).forward evolution).nextCurrent?
  support_commutes : (current : (RepresentedV value).Current) ->
    (occurrence :
      value.2.2.source.toRootSource.actual.OccurrenceAt
        (data.current.backward current)) ->
    (Represented value).toLedgerSource.source.toRootSource.account.supportOf
        ((data.occurrence current).forward occurrence) =
      value.2.2.source.toRootSource.account.supportOf occurrence
  wholeLedgerWriteBack_commutes : (current : (RepresentedV value).Current) ->
    (occurrence :
      value.2.2.source.toRootSource.actual.OccurrenceAt
        (data.current.backward current)) ->
    HEq
      ((Represented value).toLedgerSource.ledgerCompiler.compile
        ((data.occurrence current).forward occurrence))
      (value.2.2.ledgerCompiler.compile occurrence)
  finitePatch_commutes : (current : (RepresentedV value).Current) ->
    (occurrence :
      value.2.2.source.toRootSource.actual.OccurrenceAt
        (data.current.backward current)) ->
    HEq
      ((Represented value).toLedgerSource.ledgerCompiler.compilePatch
        ((data.occurrence current).forward occurrence))
      (value.2.2.ledgerCompiler.compilePatch occurrence)
  cofinalEmit_commutes :
    Option.map data.cofinal.forward value.2.1.cofinal.emit? =
      (RepresentedV value).cofinal.emit?
  cofinalPath_commutes : (event : value.2.1.cofinal.Event) -> (index : Nat) ->
    data.current.forward (value.2.1.cofinal.pathAt event index) =
      (RepresentedV value).cofinal.pathAt (data.cofinal.forward event) index
  cofinalTarget_commutes : (event : value.2.1.cofinal.Event) ->
    data.current.forward (value.2.1.cofinal.target event) =
      (RepresentedV value).cofinal.target (data.cofinal.forward event)
  terminal_exhausts_actual_inventory :
    {current : (RepresentedV value).Current} ->
    (occurrence :
      value.2.2.source.toRootSource.actual.OccurrenceAt
        (data.current.backward current)) ->
    (terminal : (RepresentedV value).FaithfulTerminalAt current) ->
    (data.evolution current).forward
        (value.2.2.source.toRootSource.actual.compile occurrence) =
      .faithfulTerminal terminal ->
    IsEmpty (SourceNativeActualOutgoingEventAt value.2.2
      (data.current.backward current))

def admissionOfData (value : SourcePair) (data : PresentationData value) (checked : AdmissionCheck value data) :
    SourceNativeCompleteEventInventoryAdmission (Represented value) where
  ActualV := value.2.1
  actualSource := value.2.2
  currentPresentation := data.current
  occurrencePresentation := data.occurrence
  evolutionPresentation := data.evolution
  cofinalEventPresentation := data.cofinal
  initial_eq := checked.initial_eq
  structural_commutes := checked.structural_commutes
  kind_commutes := checked.kind_commutes
  nextCurrent_commutes := checked.nextCurrent_commutes
  support_commutes := checked.support_commutes
  wholeLedgerWriteBack_commutes := checked.wholeLedgerWriteBack_commutes
  finitePatch_commutes := checked.finitePatch_commutes
  cofinalEmit_commutes := checked.cofinalEmit_commutes
  cofinalPath_commutes := checked.cofinalPath_commutes
  cofinalTarget_commutes := checked.cofinalTarget_commutes
  terminal_exhausts_actual_inventory := checked.terminal_exhausts_actual_inventory

abbrev AdmissionValue := Σ value : SourcePair, SourceNativeCompleteEventInventoryAdmission (Represented value)

def formAdmissionParts (parent material : M) : Option AdmissionValue :=
  (formSources parent).pbind (fun value formed =>
    (formPresentationData value (coordinatesOfPair parent value formed) material).bind (fun data =>
      if checked : AdmissionCheck value data then some ⟨value, admissionOfData value data checked⟩ else none))

/-- Both source declarations and all complete presentation programs are
formed before the original admission constructor checks its own equations. -/
def formAdmission (material : M) : Option AdmissionValue :=
  let parts := MotherHigherLawValue.split material
  formAdmissionParts parts.1 parts.2

theorem every_admission_on_sources (parent : M) (value : SourcePair) (formed : formSources parent = some value)
    (data : PresentationData value) (checked : AdmissionCheck value data) :
    ∃ material : M, formAdmission material = some ⟨value, admissionOfData value data checked⟩ := by
  obtain ⟨material, dataFormed⟩ := every_presentation_data value (coordinatesOfPair parent value formed) data
  refine ⟨MotherHigherLawValue.pack (parent, material), ?_⟩
  simp only [formAdmission, MotherHigherLawValue.split_pack, formAdmissionParts, formed, Option.pbind_some]
  change (formPresentationData value (coordinatesOfPair parent value formed) material).bind
    (fun data => if checked : AdmissionCheck value data then some (⟨value, admissionOfData value data checked⟩ : AdmissionValue) else none) = _
  rw [dataFormed]
  simp only [Option.bind_some, dif_pos checked]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherInventoryAdmission
