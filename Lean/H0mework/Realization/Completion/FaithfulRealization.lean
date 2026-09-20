import Mathlib.LinearAlgebra.Isomorphisms
import H0mework.Realization.Completion.HistorySettlement

/-!
# Root-generated faithful realization of a cofinal presentation

The cofinal history kernel produces a formal Finsupp quotient.  This file is
the missing faithful-realization mouth: an actual root-owned evaluator of
generator atoms is extended linearly, relation soundness is calculated, and
the presented completion maps to the actual domain carrier.

The engine generates both defects of that map:

* the kernel residual (missing relations / failure of faithfulness);
* the cokernel residual (missing generators / failure of coverage).

Only simultaneous vanishing generates the canonical quotient equivalence.
The caller supplies neither relation soundness, injectivity, surjectivity,
coverage, nor an equivalence.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalFaithfulRealization

open CofinalHistorySettlement
open CofinalPerfectCompressionAxiomFreeCore

noncomputable section

universe e u v w

/-- Root-owned faithful-realization face.  Its only new actual input is the
generator evaluator occurrence; the history already owns seed and
continuation. -/
structure RootGeneratedCofinalFaithfulRealizationAt
    {Root : Type w} {Generator : Type u} {Carrier : Type v}
    [AddCommGroup Carrier]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {seedOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator)}
    {continuationOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (evaluatorOccurrence : RootedAccountedUnfolding (Generator → Carrier)) :
    Type (max u v w) where
  private mk ::
  core : RootGeneratedCofinalCompressionIncidenceAt history.root
    (fun generator : Generator => RootedAccountedUnfolding.zero generator)
    evaluatorOccurrence

namespace RootGeneratedCofinalFaithfulRealizationAt

variable {Root : Type w} {Generator : Type u} {Carrier : Type v}
variable [AddCommGroup Carrier]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history : RootGeneratedCofinalHistoryAt rootOccurrence
  seedOccurrence continuationOccurrence}
variable {evaluatorOccurrence : RootedAccountedUnfolding
  (Generator → Carrier)}

def generate : RootGeneratedCofinalFaithfulRealizationAt
    history evaluatorOccurrence :=
  ⟨RootGeneratedCofinalCompressionIncidenceAt.generate (fun _ => rfl)⟩

def root
    (_face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :=
  history.root

def actualGeneratorEvaluator
    (_face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :=
  evaluatorOccurrence.root

/-- Linear extension of the actual atom evaluator. -/
def freeEvaluation
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    (Generator →₀ ℤ) →ₗ[ℤ] Carrier :=
  (Finsupp.liftAddHom fun generator =>
    AddMonoidHom.flip (smulAddHom ℤ Carrier)
      (face.actualGeneratorEvaluator generator)).toIntLinearMap

@[simp] theorem freeEvaluation_single
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (generator : Generator) (coefficient : ℤ) :
    face.freeEvaluation (Finsupp.single generator coefficient) =
      coefficient • face.actualGeneratorEvaluator generator := by
  simp [freeEvaluation]

def closureEvaluation
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    history.generatorClosure →ₗ[ℤ] Carrier :=
  face.freeEvaluation.comp history.generatorClosure.subtype

/-- Relation soundness is calculated from the actual evaluator. -/
def RelationsSound
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Prop :=
  history.relationClosure ≤ LinearMap.ker face.freeEvaluation

structure GeneratedRelationSoundnessAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Prop where
  private mk ::
  sound : face.RelationsSound

structure GeneratedUnsoundRelationObstructionAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Prop where
  private mk ::
  notSound : ¬ face.RelationsSound

/-- Relation soundness is settled before coverage.  This smaller outcome is
the entry used by derived-compression producers: they need the canonical map
from the formal completion to an actual carrier, but they must not demand a
degreewise equivalence. -/
inductive RelationSettlementOutcome
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Type (max u v) where
  | sound (soundness : GeneratedRelationSoundnessAt face)
  | unsound (obstruction : GeneratedUnsoundRelationObstructionAt face)

/-- Caller-free classification of relation soundness alone. -/
noncomputable def settleRelations
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : RelationSettlementOutcome face := by
  classical
  by_cases relationsSound : face.RelationsSound
  · exact .sound ⟨relationsSound⟩
  · exact .unsound ⟨relationsSound⟩

theorem unsoundRelationWitness
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (obstruction : GeneratedUnsoundRelationObstructionAt face) :
    ∃ relation, relation ∈ history.relationClosure ∧
      face.freeEvaluation relation ≠ 0 := by
  have notSound := obstruction.notSound
  unfold RelationsSound at notSound
  rw [SetLike.not_le_iff_exists] at notSound
  obtain ⟨relation, relation_mem, relation_not_kernel⟩ :=
    notSound
  exact ⟨relation, relation_mem, by
    simpa [LinearMap.mem_ker] using relation_not_kernel⟩

theorem relationInGeneratorClosure_le_kernel
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) :
    history.relationInGeneratorClosure ≤
      LinearMap.ker face.closureEvaluation := by
  intro relation relation_mem
  rw [LinearMap.mem_ker]
  exact soundness.sound relation_mem

/-- The presentation-to-actual map exists only on the generated sound
branch. -/
def completionEvaluation
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) :
    history.CompletionCarrier →ₗ[ℤ] Carrier :=
  history.relationInGeneratorClosure.liftQ face.closureEvaluation
    (face.relationInGeneratorClosure_le_kernel soundness)

@[simp] theorem completionEvaluation_mk
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (value : history.generatorClosure) :
    face.completionEvaluation soundness (Submodule.Quotient.mk value) =
      face.closureEvaluation value :=
  rfl

/-- Missing-relation residual. -/
def KernelResidual
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) :=
  LinearMap.ker (face.completionEvaluation soundness)

/-- Missing-generator residual. -/
abbrev CokernelResidual
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) :=
  Carrier ⧸ LinearMap.range (face.completionEvaluation soundness)

/-- Mapping-residual zero means both faithful relations and full coverage.
Surjectivity alone would not justify a quotient equivalence. -/
def CoverageResidualVanishes
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) : Prop :=
  face.KernelResidual soundness = ⊥ ∧
    Subsingleton (face.CokernelResidual soundness)

structure GeneratedCoverageResidualZeroAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) : Prop where
  private mk ::
  vanishes : face.CoverageResidualVanishes soundness

structure GeneratedCoverageResidualObstructionAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face) : Prop where
  private mk ::
  persists : ¬ face.CoverageResidualVanishes soundness

/-- Faithful realization token generated only after both residuals vanish. -/
structure GeneratedFaithfulRealizationAt
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence)
    (soundness : GeneratedRelationSoundnessAt face)
    (coverage : GeneratedCoverageResidualZeroAt face soundness) : Type where
  private mk ::

namespace GeneratedFaithfulRealizationAt

variable {face : RootGeneratedCofinalFaithfulRealizationAt
  history evaluatorOccurrence}
variable {soundness : GeneratedRelationSoundnessAt face}
variable {coverage : GeneratedCoverageResidualZeroAt face soundness}

theorem evaluation_injective
    (_faithful : GeneratedFaithfulRealizationAt face soundness coverage) :
    Function.Injective (face.completionEvaluation soundness) :=
  LinearMap.ker_eq_bot.mp coverage.vanishes.1

theorem evaluation_surjective
    (_faithful : GeneratedFaithfulRealizationAt face soundness coverage) :
    Function.Surjective (face.completionEvaluation soundness) := by
  apply LinearMap.range_eq_top.mp
  exact Submodule.Quotient.subsingleton_iff.mp coverage.vanishes.2

/-- Canonical quotient equivalence generated from the actual evaluation map.
No inverse or equivalence is supplied by the caller. -/
noncomputable def canonicalQuotientEquiv
    (faithful : GeneratedFaithfulRealizationAt face soundness coverage) :
    history.CompletionCarrier ≃ₗ[ℤ] Carrier :=
  LinearEquiv.ofBijective (face.completionEvaluation soundness)
    ⟨faithful.evaluation_injective, faithful.evaluation_surjective⟩

/-- Instance-independent additive shadow used to assemble an actual complex
when the domain stores a non-definitional `ℤ`-module instance. -/
noncomputable def canonicalQuotientAddEquiv
    (faithful : GeneratedFaithfulRealizationAt face soundness coverage) :
    history.CompletionCarrier ≃+ Carrier :=
  faithful.canonicalQuotientEquiv.toAddEquiv

@[simp] theorem canonicalQuotientEquiv_apply
    (faithful : GeneratedFaithfulRealizationAt face soundness coverage)
    (value : history.CompletionCarrier) :
    faithful.canonicalQuotientEquiv value =
      face.completionEvaluation soundness value :=
  rfl

end GeneratedFaithfulRealizationAt

/-- Total generated outcome. -/
inductive SettlementOutcome
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : Type (max u v) where
  | faithful
      (soundness : GeneratedRelationSoundnessAt face)
      (coverage : GeneratedCoverageResidualZeroAt face soundness)
      (realization : GeneratedFaithfulRealizationAt face soundness coverage)
  | unsound (obstruction : GeneratedUnsoundRelationObstructionAt face)
  | uncovered
      (soundness : GeneratedRelationSoundnessAt face)
      (obstruction : GeneratedCoverageResidualObstructionAt face soundness)

/-- Caller-free classification of the actual evaluator. -/
noncomputable def settle
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) : SettlementOutcome face := by
  classical
  by_cases relationsSound : face.RelationsSound
  · let soundness : GeneratedRelationSoundnessAt face := ⟨relationsSound⟩
    by_cases coverageZero : face.CoverageResidualVanishes soundness
    · let coverage : GeneratedCoverageResidualZeroAt face soundness :=
        ⟨coverageZero⟩
      exact .faithful soundness coverage ⟨⟩
    · exact .uncovered soundness ⟨coverageZero⟩
  · exact .unsound ⟨relationsSound⟩

theorem settlementMouth
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    Nonempty (SettlementOutcome face) :=
  ⟨face.settle⟩

theorem preserves_actual_history_and_evaluator
    (face : RootGeneratedCofinalFaithfulRealizationAt
      history evaluatorOccurrence) :
    face.root = history.root ∧
      face.actualGeneratorEvaluator = evaluatorOccurrence.root :=
  ⟨rfl, rfl⟩

end RootGeneratedCofinalFaithfulRealizationAt

/-! ## Universal-fold adapter -/

/-- Strong public mouth when the domain already owns event occurrences and
a fold algebra.  The generator evaluator is then a derived universal-fold
readout rather than a submitted function table. -/
structure RootGeneratedCofinalEventFoldEvaluatorAt
    {Root : Type w} {Generator : Type u} {Event : Type e}
    {Carrier : Type v} [AddCommGroup Carrier]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {seedOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator)}
    {continuationOccurrence : RootedAccountedUnfolding
      (PresentedRelationEventAt Generator →
        RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
    (history : RootGeneratedCofinalHistoryAt rootOccurrence
      seedOccurrence continuationOccurrence)
    (eventOccurrences : Generator → RootedAccountedUnfolding Event)
    (algebraOccurrence : RootedAccountedUnfolding
      (Event → List Carrier → Carrier)) : Type (max e u v w) where
  private mk ::

namespace RootGeneratedCofinalEventFoldEvaluatorAt

variable {Root : Type w} {Generator : Type u} {Event : Type e}
variable {Carrier : Type v} [AddCommGroup Carrier]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {seedOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator)}
variable {continuationOccurrence : RootedAccountedUnfolding
  (PresentedRelationEventAt Generator →
    RootedAccountedUnfolding (PresentedRelationEventAt Generator))}
variable {history : RootGeneratedCofinalHistoryAt rootOccurrence
  seedOccurrence continuationOccurrence}
variable {eventOccurrences : Generator → RootedAccountedUnfolding Event}
variable {algebraOccurrence : RootedAccountedUnfolding
  (Event → List Carrier → Carrier)}

def generate : RootGeneratedCofinalEventFoldEvaluatorAt history
    eventOccurrences algebraOccurrence :=
  ⟨⟩

/-- Source-generated atom evaluator. -/
def evaluator
    (_face : RootGeneratedCofinalEventFoldEvaluatorAt history
      eventOccurrences algebraOccurrence)
    (generator : Generator) : Carrier :=
  (eventOccurrences generator).fold algebraOccurrence.root

def evaluatorOccurrence
    (face : RootGeneratedCofinalEventFoldEvaluatorAt history
      eventOccurrences algebraOccurrence) :
    RootedAccountedUnfolding (Generator → Carrier) :=
  RootedAccountedUnfolding.zero face.evaluator

/-- The faithful-realization face generated from the fold evaluator. -/
def faithfulRealization
    (face : RootGeneratedCofinalEventFoldEvaluatorAt history
      eventOccurrences algebraOccurrence) :
    RootGeneratedCofinalFaithfulRealizationAt
      history face.evaluatorOccurrence :=
  RootGeneratedCofinalFaithfulRealizationAt.generate

theorem evaluator_is_universal_fold
    (face : RootGeneratedCofinalEventFoldEvaluatorAt history
      eventOccurrences algebraOccurrence)
    (generator : Generator) :
    face.evaluator generator =
      (eventOccurrences generator).fold algebraOccurrence.root :=
  rfl

theorem preserves_actual_fold_inputs
    (face : RootGeneratedCofinalEventFoldEvaluatorAt history
      eventOccurrences algebraOccurrence) :
    face.faithfulRealization.root = history.root ∧
      face.faithfulRealization.actualGeneratorEvaluator = face.evaluator :=
  ⟨rfl, rfl⟩

end RootGeneratedCofinalEventFoldEvaluatorAt

end


end CofinalFaithfulRealization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
