import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.AdmissionFields

/-! Complete native admission recovery from the actual generated header and
the four whole presentation programs. Image membership is paid by the
source factory's literal transportedData output; it is not a new public
coverage or node-formation assumption. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionRestriction
open MotherAdmissionAlignment MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (represented : SourceNativeRestructuringLedgerSource N V) (header : Header N)
    (value : SourcePair)
    (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
    (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
    (w : MotherVocabularyOrigin.Presentation header.1 value.2.1)
    (p : MotherNativeSourceOrigin.Presentation n v represented.source (Represented value).source)
    (a : MotherNativeSourceOrigin.Presentation n w header.2.source value.2.2.source)

def transportFields (fields : Fields represented.toLedgerSource header) : PresentationData value :=
  AdmissionTransport.transportedData (assemble represented header fields) value n v w p a

theorem transportFields_injective :
    Function.Injective (transportFields represented header value n v w p a) := by
  intro first last same
  rcases first with ⟨currentFirst, initialFirst, occurrenceFirst, evolutionFirst, structuralFirst,
    kindFirst, nextFirst, supportFirst, wholeFirst, patchFirst, cofinalFirst, emitFirst,
    pathFirst, targetFirst, terminalFirst⟩
  rcases last with ⟨currentLast, initialLast, occurrenceLast, evolutionLast, structuralLast,
    kindLast, nextLast, supportLast, wholeLast, patchLast, cofinalLast, emitLast,
    pathLast, targetLast, terminalLast⟩
  let first : Fields represented.toLedgerSource header :=
    ⟨currentFirst, initialFirst, occurrenceFirst, evolutionFirst, structuralFirst,
      kindFirst, nextFirst, supportFirst, wholeFirst, patchFirst, cofinalFirst, emitFirst,
      pathFirst, targetFirst, terminalFirst⟩
  let last : Fields represented.toLedgerSource header :=
    ⟨currentLast, initialLast, occurrenceLast, evolutionLast, structuralLast,
      kindLast, nextLast, supportLast, wholeLast, patchLast, cofinalLast, emitLast,
      pathLast, targetLast, terminalLast⟩
  have currentSame : currentFirst = currentLast :=
    (AdmissionTransport.current_recovers (assemble represented header first) value n v w p a).symm.trans
      ((congrArg (fun data : PresentationData value => presentationFromEquiv (w.current.trans
        ((presentationEquiv data.current).trans v.current.symm))) same).trans
          (AdmissionTransport.current_recovers (assemble represented header last) value n v w p a))
  cases currentSame
  have sameOccurrence :
      (transportFields represented header value n v w p a first).occurrence =
        (transportFields represented header value n v w p a last).occurrence :=
    eq_of_heq (PresentationData.mk.inj same).2.1
  have sameEvolution :
      (transportFields represented header value n v w p a first).evolution =
        (transportFields represented header value n v w p a last).evolution :=
    eq_of_heq (PresentationData.mk.inj same).2.2.1
  have occurrenceSame : occurrenceFirst = occurrenceLast := by
    funext oldCurrent
    obtain ⟨current, rfl⟩ := v.current.symm.surjective oldCurrent
    exact (AdmissionTransport.occurrence_recovers (assemble represented header first) value n v w p a current).symm.trans
      ((congrArg (fun occurrence => presentationFromEquiv
        ((a.event (currentFirst.backward (v.current.symm current))).trans
          ((presentationEquiv occurrence).trans (AdmissionTransport.eventAt p current).symm)))
            (congrFun sameOccurrence current)).trans
        (AdmissionTransport.occurrence_recovers (assemble represented header last) value n v w p a current))
  have evolutionSame : evolutionFirst = evolutionLast := by
    funext oldCurrent
    obtain ⟨current, rfl⟩ := v.current.symm.surjective oldCurrent
    exact (AdmissionTransport.evolution_recovers (assemble represented header first) value n v w p a current).symm.trans
      ((congrArg (fun evolution => presentationFromEquiv
        ((w.evolution (currentFirst.backward (v.current.symm current))).trans
          ((presentationEquiv evolution).trans (AdmissionTransport.evolutionAt v current).symm)))
            (congrFun sameEvolution current)).trans
        (AdmissionTransport.evolution_recovers (assemble represented header last) value n v w p a current))
  have cofinalSame : cofinalFirst = cofinalLast :=
    (AdmissionTransport.cofinal_recovers (assemble represented header first) value n v w p a).symm.trans
      ((congrArg (fun data : PresentationData value => presentationFromEquiv (w.cofinal.trans
        ((presentationEquiv data.cofinal).trans v.cofinal.symm))) same).trans
          (AdmissionTransport.cofinal_recovers (assemble represented header last) value n v w p a))
  cases occurrenceSame
  cases evolutionSame
  cases cofinalSame
  rfl

def fieldsImageEquiv : Fields represented.toLedgerSource header ≃
    Set.range (transportFields represented header value n v w p a) :=
  Equiv.ofInjective (transportFields represented header value n v w p a)
    (transportFields_injective represented header value n v w p a)

private theorem assemble_cast {first last : Header N} (same : first = last)
    (fields : Fields represented.toLedgerSource last) :
    assemble represented first
      (Equiv.cast (congrArg (Fields represented.toLedgerSource) same.symm) fields) =
        assemble represented last fields := by
  cases same
  rfl

variable (actualCompiler : CompilerPresentation a header.2.ledgerCompiler value.2.2.ledgerCompiler)

/-- Full faithful restriction: every value is read from the generated header
or from the four generated presentation programs. The old header supplies
the target indices of the inverse representation. -/
def restrictAdmission
    (data : Set.range (transportFields represented header value n v w p a)) :
    SourceNativeCompleteEventInventoryAdmission represented :=
  let fields := (fieldsImageEquiv represented header value n v w p a).symm data
  let headerSame : actualCompiler.restrictHeader = header := actualCompiler.restrictHeader_eq
  assemble represented actualCompiler.restrictHeader
    (Equiv.cast (congrArg (Fields represented.toLedgerSource) headerSame.symm) fields)

theorem restrictAdmission_recovers (fields : Fields represented.toLedgerSource header) :
    restrictAdmission represented header value n v w p a actualCompiler
      ⟨transportFields represented header value n v w p a fields, fields, rfl⟩ =
        assemble represented header fields := by
  unfold restrictAdmission
  exact (assemble_cast represented actualCompiler.restrictHeader_eq _).trans
    (congrArg (assemble represented header)
      ((fieldsImageEquiv represented header value n v w p a).symm_apply_apply fields))

/-- The image witness is produced from the factory's literal output equality;
it is not an additional entry condition on an admitted process. -/
def generatedDataInImage (fields : Fields represented.toLedgerSource header)
    (data : PresentationData value)
    (dataSame : data = transportFields represented header value n v w p a fields) :
    Set.range (transportFields represented header value n v w p a) :=
  ⟨data, fields, dataSame.symm⟩

theorem generatedData_recovers (fields : Fields represented.toLedgerSource header)
    (data : PresentationData value)
    (dataSame : data = transportFields represented header value n v w p a fields) :
    restrictAdmission represented header value n v w p a actualCompiler
      (generatedDataInImage represented header value n v w p a fields data dataSame) =
        assemble represented header fields := by
  cases dataSame
  exact restrictAdmission_recovers represented header value n v w p a actualCompiler fields

end

section OriginalAdmission

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {represented : SourceNativeRestructuringLedgerSource N V}
    (admission : SourceNativeCompleteEventInventoryAdmission represented)
    (value : SourcePair)
    (n : MotherNetworkOrigin.Presentation N value.1.1.1.1.1)
    (v : MotherVocabularyOrigin.Presentation V (RepresentedV value))
    (w : MotherVocabularyOrigin.Presentation admission.ActualV value.2.1)
    (p : MotherNativeSourceOrigin.Presentation n v represented.source (Represented value).source)
    (a : MotherNativeSourceOrigin.Presentation n w admission.actualSource.source value.2.2.source)
    (actualCompiler : CompilerPresentation a admission.actualSource.ledgerCompiler value.2.2.ledgerCompiler)

private theorem transportFields_fieldsOf :
    transportFields represented ⟨admission.ActualV, admission.actualSource⟩ value n v w p a
        (fieldsOf represented admission) =
      AdmissionTransport.transportedData admission value n v w p a := by
  cases admission
  rfl

def originalDataInImage (data : PresentationData value)
    (dataSame : data = AdmissionTransport.transportedData admission value n v w p a) :
    Set.range (transportFields represented ⟨admission.ActualV, admission.actualSource⟩ value n v w p a) := by
  refine generatedDataInImage represented ⟨admission.ActualV, admission.actualSource⟩ value n v w p a
    (fieldsOf represented admission) data ?_
  exact dataSame.trans (transportFields_fieldsOf admission value n v w p a).symm

/-- All fields of the original native admission are recovered from the actual
generated compiler/source and the complete generated presentation data. -/
theorem original_admission_restricted (data : PresentationData value)
    (dataSame : data = AdmissionTransport.transportedData admission value n v w p a) :
    restrictAdmission represented ⟨admission.ActualV, admission.actualSource⟩ value n v w p a actualCompiler
      (originalDataInImage admission value n v w p a data dataSame) = admission := by
  exact (generatedData_recovers represented ⟨admission.ActualV, admission.actualSource⟩
    value n v w p a actualCompiler (fieldsOf represented admission) data
      (dataSame.trans (transportFields_fieldsOf admission value n v w p a).symm)).trans
        (assemble_fieldsOf represented admission)

end OriginalAdmission
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionRestriction
