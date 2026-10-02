import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.AdmissionAlignment.SourceRestriction

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

private theorem actual_cast_heq {A B : Type 1} (same : A = B) (value : A) :
    HEq (Equiv.cast same value) value := by
  cases same
  rfl

variable {V W : ConstructiveRoot.Vocabulary.{0}} (v : MotherVocabularyOrigin.Presentation V W)

def restrictCofinal : SourceNativeCofinalTransitionLaw V.Current where
  Event := V.cofinal.Event
  emit? := Option.map v.cofinal.symm W.cofinal.emit?
  pathAt := fun event index => v.current.symm (W.cofinal.pathAt (v.cofinal event) index)
  target := fun event => v.current.symm (W.cofinal.target (v.cofinal event))

theorem restrictCofinal_eq : restrictCofinal v = V.cofinal := by
  have emitted : Option.map v.cofinal.symm W.cofinal.emit? = V.cofinal.emit? :=
    (congrArg (Equiv.optionCongr v.cofinal).symm v.cofinal_emit.symm).trans
      ((Equiv.optionCongr v.cofinal).symm_apply_apply _)
  have path : (fun event index => v.current.symm (W.cofinal.pathAt (v.cofinal event) index)) = V.cofinal.pathAt := by
    funext event index
    exact (congrArg v.current.symm (v.cofinal_path event index)).trans (v.current.symm_apply_apply _)
  have target : (fun event => v.current.symm (W.cofinal.target (v.cofinal event))) = V.cofinal.target := by
    funext event
    exact (congrArg v.current.symm (v.cofinal_target event)).trans (v.current.symm_apply_apply _)
  unfold restrictCofinal
  rw [emitted, path, target]

def restrictVocabulary : ConstructiveRoot.Vocabulary.{0} where
  Current := V.Current
  Anchor := V.Anchor
  Incidence := V.Incidence
  Lineage := V.Lineage
  anchorAt := fun current => v.anchor.symm (W.anchorAt (v.current current))
  incidenceAt := fun current => v.incidence.symm (W.incidenceAt (v.current current))
  lineageAt := fun current => v.lineage.symm (W.lineageAt (v.current current))
  NativeWriteAt := V.NativeWriteAt
  RelationWriteAt := V.RelationWriteAt
  ContinuedTransportAt := V.ContinuedTransportAt
  BorromeanRedirectAt := V.BorromeanRedirectAt
  FaithfulTerminalAt := V.FaithfulTerminalAt
  nativeTarget := fun {current} event => v.current.symm (W.nativeTarget (v.native current event))
  relationTarget := fun {current} event => v.current.symm (W.relationTarget (v.relation current event))
  continuedTarget := fun {current} event => v.current.symm (W.continuedTarget (v.continued current event))
  redirectTarget := fun {current} event => v.current.symm (W.redirectTarget (v.redirect current event))
  cofinal := restrictCofinal v

theorem restrictVocabulary_eq : restrictVocabulary v = V := by
  have anchor : (fun current => v.anchor.symm (W.anchorAt (v.current current))) = V.anchorAt := by
    funext current
    exact (congrArg v.anchor.symm (v.anchor_eq current)).trans (v.anchor.symm_apply_apply _)
  have incidence : (fun current => v.incidence.symm (W.incidenceAt (v.current current))) = V.incidenceAt := by
    funext current
    exact (congrArg v.incidence.symm (v.incidence_eq current)).trans (v.incidence.symm_apply_apply _)
  have lineage : (fun current => v.lineage.symm (W.lineageAt (v.current current))) = V.lineageAt := by
    funext current
    exact (congrArg v.lineage.symm (v.lineage_eq current)).trans (v.lineage.symm_apply_apply _)
  have native : (fun {current} event => v.current.symm (W.nativeTarget (v.native current event))) = @V.nativeTarget := by
    funext current event
    exact (congrArg v.current.symm (v.native_eq current event)).trans (v.current.symm_apply_apply _)
  have relation : (fun {current} event => v.current.symm (W.relationTarget (v.relation current event))) = @V.relationTarget := by
    funext current event
    exact (congrArg v.current.symm (v.relation_eq current event)).trans (v.current.symm_apply_apply _)
  have continued : (fun {current} event => v.current.symm (W.continuedTarget (v.continued current event))) = @V.continuedTarget := by
    funext current event
    exact (congrArg v.current.symm (v.continued_eq current event)).trans (v.current.symm_apply_apply _)
  have redirect : (fun {current} event => v.current.symm (W.redirectTarget (v.redirect current event))) = @V.redirectTarget := by
    funext current event
    exact (congrArg v.current.symm (v.redirect_eq current event)).trans (v.current.symm_apply_apply _)
  unfold restrictVocabulary
  rw [anchor, incidence, lineage, native, relation, continued, redirect, restrictCofinal_eq]

namespace CompilerPresentation

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {p : MotherNativeSourceOrigin.Presentation n v original generated}
    {originalCompiler : SourceNativeLedgerCompiler original}
    {generatedCompiler : SourceNativeLedgerCompiler generated}
    (presentation : CompilerPresentation p originalCompiler generatedCompiler)

def restrictLedgerSource : SourceNativeLedgerSource N V :=
  ⟨restrictSource p, Equiv.cast (congrArg SourceNativeLedgerCompiler (restrictSource_eq p).symm)
    presentation.restrictLedgerCompiler⟩

private theorem ledgerSource_eq {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {first last : SourceNativeSource N V} (same : first = last)
    (compiler : SourceNativeLedgerCompiler last) (recovered : SourceNativeLedgerCompiler last)
    (compiler_eq : recovered = compiler) :
    (⟨first, Equiv.cast (congrArg SourceNativeLedgerCompiler same.symm) recovered⟩ : SourceNativeLedgerSource N V) =
      ⟨last, compiler⟩ := by
  cases same
  cases compiler_eq
  rfl

theorem restrictLedgerSource_eq : presentation.restrictLedgerSource = ⟨original, originalCompiler⟩ :=
  ledgerSource_eq (restrictSource_eq p) originalCompiler presentation.restrictLedgerCompiler presentation.restrictLedgerCompiler_eq

def restrictHeader : Σ vocab : ConstructiveRoot.Vocabulary.{0}, SourceNativeLedgerSource N vocab :=
  ⟨restrictVocabulary v,
    Equiv.cast (congrArg (SourceNativeLedgerSource N) (restrictVocabulary_eq v).symm)
      presentation.restrictLedgerSource⟩

theorem restrictHeader_eq : presentation.restrictHeader = ⟨V, ⟨original, originalCompiler⟩⟩ := by
  have same : (⟨restrictVocabulary v,
      Equiv.cast (congrArg (SourceNativeLedgerSource N) (restrictVocabulary_eq v).symm)
        presentation.restrictLedgerSource⟩ : Σ vocab : ConstructiveRoot.Vocabulary.{0}, SourceNativeLedgerSource N vocab) =
      ⟨V, presentation.restrictLedgerSource⟩ := by
    exact Sigma.ext (restrictVocabulary_eq v) (by
      exact (actual_cast_heq (congrArg (SourceNativeLedgerSource N) (restrictVocabulary_eq v).symm)
        presentation.restrictLedgerSource))
  exact same.trans (congrArg (Sigma.mk V) presentation.restrictLedgerSource_eq)

end CompilerPresentation
end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAdmissionAlignment
