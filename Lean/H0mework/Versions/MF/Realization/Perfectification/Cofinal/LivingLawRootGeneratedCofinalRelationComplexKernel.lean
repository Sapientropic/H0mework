import H0mework.Realization.Completion.HistorySettlement
import H0mework.Versions.R2.Realization.Completion.HistoryInstallation
import H0mework.Versions.R2.Realization.Completion.CommonCochainOccurrence
import H0mework.Foundation.Relations.CochainPresentation
import H0mework.Realization.Arithmetic.DerivedAdicCofiber
import Mathlib.Algebra.Homology.Embedding.Extend

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace CofinalRelationGeneratedComplex

open CategoryTheory
open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CochainRelationPresentation
open DerivedAdicCofiber

noncomputable section

universe u
section NativeUniverse

variable {Root Generator : Type u}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}

def relationInclusion
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    face.relationClosure →ₗ[ℤ] face.generatorClosure :=
  Submodule.inclusion face.relationClosure_le_generatorClosure

def object
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) : ℕ → ModuleCat.{u} ℤ
  | 0 => ModuleCat.of ℤ face.relationClosure
  | 1 => ModuleCat.of ℤ face.generatorClosure
  | _ + 2 => ModuleCat.of ℤ (ULift.{u} (Fin 0 → ℤ))

def differential
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    ∀ i : ℕ, object face i ⟶ object face (i + 1)
  | 0 => ModuleCat.ofHom (relationInclusion face)
  | _ + 1 => 0

theorem differential_sq
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) (i : ℕ) :
    differential face i ≫ differential face (i + 1) = 0 := by
  cases i with
  | zero => rfl
  | succ i => rfl

def natComplex
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  CochainComplex.of (object face) (differential face) (differential_sq face)

@[simp] theorem natComplex_d_zero_one
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    (natComplex face).d 0 1 = ModuleCat.ofHom (relationInclusion face) := by
  simpa [natComplex, differential] using
    (CochainComplex.of_d (object face) (differential face) 0)

/-- A generated differential value is precisely an actual relation, hence
the original completion quotient kills it. -/
theorem completion_kills_generated_differential
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (relation : face.relationClosure) :
    face.completionProjection
      (((natComplex face).d 0 1).hom relation) = 0 := by
  rw [natComplex_d_zero_one]
  apply (Submodule.Quotient.mk_eq_zero
    face.relationInGeneratorClosure).2
  exact relation.property

/-- Conversely every original completion-zero value is an actual generated
relation differential; no extra relation is silently imposed. -/
theorem completion_zero_iff_generated_boundary
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (value : face.generatorClosure) :
    face.completionProjection value = 0 ↔
      ∃ relation : face.relationClosure,
        ((natComplex face).d 0 1).hom relation = value := by
  constructor
  · intro zero
    have mem : value ∈ face.relationInGeneratorClosure :=
      (Submodule.Quotient.mk_eq_zero
        face.relationInGeneratorClosure).1 zero
    exact ⟨⟨value.1, mem⟩, by
      rw [natComplex_d_zero_one]
      apply Subtype.ext
      rfl⟩
  · rintro ⟨relation, rfl⟩
    exact completion_kills_generated_differential face relation

end NativeUniverse

variable {Root Generator : Type}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}

def intComplex
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    IntegralCochainComplex ℤ :=
  (natComplex face).extend ComplexShape.embeddingUpNat

def degreeZeroGeneratorComplex
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    IntegralCochainComplex ℤ :=
  (intComplex face)⟦(1 : ℤ)⟧

def shiftedGeneratorIso
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    (degreeZeroGeneratorComplex face).X 0 ≅
      ModuleCat.of ℤ face.generatorClosure :=
  ((intComplex face).shiftFunctorObjXIso 1 0 1 rfl) ≪≫
    ((natComplex face).extendXIso ComplexShape.embeddingUpNat rfl)

def sourceGeneratorVector
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) (generator : Generator) :
    face.generatorClosure := by
  classical
  exact if present : Finsupp.single generator 1 ∈ face.generatorClosure then
    ⟨Finsupp.single generator 1, present⟩ else 0

/-- The common-face evaluator is computed from the actual generator closure.
An unseen generator has zero image; no independently selected evaluator enters. -/
def sourceEvaluator
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    Generator → (degreeZeroGeneratorComplex face).X 0 :=
  fun generator => (shiftedGeneratorIso face).inv.hom
    (sourceGeneratorVector face generator)

theorem actual_generator_single_mem_closure
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (stage : Nat) (generator : Generator)
    (present : generator ∈ face.generatorSupport stage) :
    Finsupp.single generator (1 : ℤ) ∈ face.generatorClosure :=
  face.generatorStage_le_closure stage
    (Finsupp.single_mem_supported ℤ 1 present)

theorem sourceEvaluator_reads_actual_generator
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (stage : Nat) (generator : Generator)
    (present : generator ∈ face.generatorSupport stage) :
    (shiftedGeneratorIso face).hom.hom (sourceEvaluator face generator) =
      (⟨Finsupp.single generator 1,
        actual_generator_single_mem_closure face stage generator present⟩ :
        face.generatorClosure) := by
  have mem := actual_generator_single_mem_closure face stage generator present
  simp [sourceEvaluator, sourceGeneratorVector, mem]

/-- The integer-indexed differential consumed by the old relation
presentation is the same actual closure inclusion transported through the
canonical Nat-to-Int extension, rather than a separately supplied complex. -/
theorem intComplex_d_zero_one
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    (intComplex face).d 0 1 =
      ((natComplex face).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫
        ModuleCat.ofHom (relationInclusion face) ≫
      ((natComplex face).extendXIso ComplexShape.embeddingUpNat rfl).inv := by
  change ((natComplex face).extend ComplexShape.embeddingUpNat).d
      (ComplexShape.embeddingUpNat.f 0) (ComplexShape.embeddingUpNat.f 1) = _
  rw [(natComplex face).extend_d_eq ComplexShape.embeddingUpNat rfl rfl,
    natComplex_d_zero_one]
  rfl

def complexOccurrence
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    RootedAccountedUnfolding (IntegralCochainComplex ℤ) :=
  RootedAccountedUnfolding.zero (intComplex face)

def relationConsumer
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    RootGeneratedCochainRelationPresentationAt
      face.root (complexOccurrence face) :=
  RootGeneratedCochainRelationPresentationAt.generate

theorem generatedDifferential_relation_naturality
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence) :
    ((relationConsumer face).differentialGeneratorMap 0 1).comp
        (FiniteAdditiveRelationPresentation.additionRelationMap
          ((relationConsumer face).complex.X 0)) =
      (FiniteAdditiveRelationPresentation.additionRelationMap
        ((relationConsumer face).complex.X 1)).comp
        ((relationConsumer face).differentialRelationMap 0 1) :=
  (relationConsumer face).differential_relation_naturality 0 1

theorem generatedDifferential_presented_commutes
    (face : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (value : ((relationConsumer face).termPresentation 0).cokernel) :
    FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
        ((relationConsumer face).termPresentation 1)
        ((relationConsumer face).differentialPresentedMap 0 1 value) =
      (relationConsumer face).differentialAddHom 0 1
        (FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
          ((relationConsumer face).termPresentation 0) value) :=
  (relationConsumer face).differential_presentedMap_commutes 0 1 value

section InstalledRaw

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
variable {source : SourceNativeLedgerSource N V}
variable (law : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw source)
variable {current : V.Current}
variable (occurrence : source.source.toRootSource.actual.OccurrenceAt current)

/-- No cochain complex, evaluator, or target quotient is an input: the
original installed raw source projection alone determines this complex. -/
def ofHistory : IntegralCochainComplex ℤ :=
  degreeZeroGeneratorComplex (law.historyAt occurrence)

theorem ofHistory_reads_original_projection :
    ofHistory law occurrence =
      degreeZeroGeneratorComplex (RootGeneratedCofinalHistoryAt.generate
        (rootOccurrence := (law.toProjectionLaw.project
          PUnit.unit occurrence PUnit.unit).rootExposure)
        (seedOccurrence := (law.toProjectionLaw.project
          PUnit.unit occurrence PUnit.unit).seed)
        (continuationOccurrence := (law.toProjectionLaw.project
          PUnit.unit occurrence PUnit.unit).continuation)) :=
  rfl

end InstalledRaw

section DerivedCommon

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
variable {source : SourceNativeLedgerSource N V}

/-- The old common material law can be built with no caller-supplied complex
or evaluator. Both are calculated from the already installed raw history. -/
def ofHistoryCommonLaw
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw source) :
    CofinalHistoryCochainCommonOccurrence.SourceNativeCofinalHistoryCochainMaterialLaw source :=
  CofinalHistoryCochainCommonOccurrence.SourceNativeCofinalHistoryCochainMaterialLaw.create
    historyLaw
    (fun occurrence => RootedAccountedUnfolding.zero
      (ofHistory historyLaw occurrence))
    (fun occurrence => RootedAccountedUnfolding.zero
      (sourceEvaluator (historyLaw.historyAt occurrence)))

theorem ofHistoryCommonLaw_projection_eq
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw source) :
    (ofHistoryCommonLaw historyLaw).toProjectionLaw =
      historyLaw.toProjectionLaw :=
  rfl

theorem ofHistoryCommonLaw_d_squared_zero
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw source)
    {current : V.Current}
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current)
    (value : (((ofHistoryCommonLaw historyLaw).cochainAt occurrence).termPresentation (-1)).cokernel) :
    FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
        (((ofHistoryCommonLaw historyLaw).cochainAt occurrence).termPresentation 1)
        (((ofHistoryCommonLaw historyLaw).cochainAt occurrence).differentialPresentedMap 0 1
          (((ofHistoryCommonLaw historyLaw).cochainAt occurrence).differentialPresentedMap
            (-1) 0 value)) = 0 :=
  ((ofHistoryCommonLaw historyLaw).cochainAt occurrence).differential_presentedMap_comp_zero
    (-1) 0 1 value

def ofHistoryRecognition
    {root : SourceNativeLivingRootClosure N V}
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      historyLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw) :
    CofinalHistoryCochainCommonOccurrence.SourceNativeCofinalHistoryCochainRecognitionAt root :=
  CofinalHistoryCochainCommonOccurrence.SourceNativeCofinalHistoryCochainRecognitionAt.create
    (ofHistoryCommonLaw historyLaw) installation

def ofHistoryStep
    {root : SourceNativeLivingRootClosure N V}
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      historyLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :
    CofinalHistoryCochainCommonOccurrence.RootGeneratedCofinalHistoryCochainCommonStepAt
      (ofHistoryRecognition historyLaw installation) visit :=
  (ofHistoryRecognition historyLaw installation).generateStepAt visit

theorem ofHistoryStep_source_root_ledger_next
    {root : SourceNativeLivingRootClosure N V}
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      historyLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :
    let step := ofHistoryStep historyLaw installation visit
    step.history.seed =
        (historyLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).seed ∧
      step.history.actualContinuation =
        (historyLaw.toProjectionLaw.project PUnit.unit
          step.sourceOccurrence PUnit.unit).continuation.root ∧
      HEq
        (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
          (installation.embed PUnit.unit) step.sourceOccurrence)
        (historyLaw.toProjectionLaw.outcomeAt
          PUnit.unit step.sourceOccurrence) ∧
      HEq step.wholeLedgerWriteBack
        (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
      step.nextCurrent = root.generatedNextCurrentAt visit := by
  exact (ofHistoryStep historyLaw installation visit).sourceHistoryAction_root_ledger_next

theorem ofHistoryStep_consumes_generated_d_squared
    {root : SourceNativeLivingRootClosure N V}
    (historyLaw : CofinalHistorySettlementFace.SourceNativeCofinalHistoryMaterialLaw
      root.toAuthoritativeRoot.toLedgerRoot.source)
    (installation : SourceNativeProjectionLaw.InstallationAt
      historyLaw.toProjectionLaw root.toAuthoritativeRoot.source.projectionLaw)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (value : ((ofHistoryStep historyLaw installation visit).cochainFace.termPresentation
      (-1)).cokernel) :
    let step := ofHistoryStep historyLaw installation visit
    FiniteAdditiveRelationPresentation.finiteAdditiveRelationPresentation_cokernelEquiv _
        (step.cochainFace.termPresentation 1)
        (step.cochainFace.differentialPresentedMap 0 1
          (step.cochainFace.differentialPresentedMap (-1) 0 value)) = 0 :=
  (ofHistoryStep historyLaw installation visit).cochain_d_squared (-1) 0 1 value

end DerivedCommon

end
end CofinalRelationGeneratedComplex
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
