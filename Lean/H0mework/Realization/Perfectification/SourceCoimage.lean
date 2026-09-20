import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dual.Defs
import H0mework.Realization.Perfectification.FiniteCompressionNoGo
import H0mework.Foundation.Relations.AdditivePresentation
import H0mework.Realization.Perfectification.DualDisposition

/-!
# Source-generated perfectification

For one source occurrence, let `e : C → Dual D` be the generated dual
evaluation.  The perfectification candidate is the coimage
`P := C / ker e`, with its canonical quotient map and its canonical
injective map into `Dual D`.  The construction is a disposition, not a free
perfectness theorem: surjectivity of the embedding is generated as evidence
or replaced by an exact duality residual.  A faithful source map is likewise
factored through `P` only when its kernel contains `ker e`; otherwise the
kernel element is retained as a representation residual.

The root-controlled adapter in the sibling cofinal face kernel binds this
coimage to the existing history, cochain, and faithful-realization faces.  No finite, projective,
nondegenerate, determinant, inverse, or coverage premise is accepted.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedPerfectification

open SourceGeneratedDualEvaluation
open FiniteAdditiveRelationPresentation

noncomputable section

universe c d a u v w

/-! ## Universal coimage mouth -/

variable {C : Type c} {D : Type d}
variable [AddCommGroup C] [AddCommGroup D]
variable (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)

abbrev PerfectificationCarrier := C ⧸ LinearMap.ker evaluation

def canonicalMap : C →ₗ[ℤ] PerfectificationCarrier evaluation :=
  Submodule.mkQ _

def dualEmbedding : PerfectificationCarrier evaluation →ₗ[ℤ]
    Module.Dual ℤ D :=
  (LinearMap.ker evaluation).liftQ evaluation le_rfl

@[simp] theorem dualEmbedding_comp_canonicalMap :
    (dualEmbedding evaluation).comp (canonicalMap evaluation) = evaluation := by
  apply LinearMap.ext
  intro value
  rfl

theorem dualEmbedding_injective :
    Function.Injective (dualEmbedding evaluation) := by
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

/-! Every map annihilating the generated invisible kernel factors uniquely
through the canonical quotient. -/

def canonicalFactor
    {Q : Type a} [AddCommGroup Q]
    (map : C →ₗ[ℤ] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    PerfectificationCarrier evaluation →ₗ[ℤ] Q :=
  (LinearMap.ker evaluation).liftQ map kernel_compatibility

@[simp] theorem canonicalFactor_comp
    {Q : Type a} [AddCommGroup Q]
    (map : C →ₗ[ℤ] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    (canonicalFactor evaluation map kernel_compatibility).comp
        (canonicalMap evaluation) = map := by
  unfold canonicalFactor canonicalMap
  apply Submodule.liftQ_mkQ

theorem canonicalFactor_unique
    {Q : Type a} [AddCommGroup Q]
    (map : C →ₗ[ℤ] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map)
    (other : PerfectificationCarrier evaluation →ₗ[ℤ] Q)
    (other_commutes : other.comp (canonicalMap evaluation) = map) :
    other = canonicalFactor evaluation map kernel_compatibility := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) quotientValue
  have equality := LinearMap.congr_fun other_commutes value
  exact equality.trans (by rfl)

theorem canonicalMap_universal
    {Q : Type a} [AddCommGroup Q]
    (map : C →ₗ[ℤ] Q)
    (kernel_compatibility : LinearMap.ker evaluation ≤ LinearMap.ker map) :
    ∃! factor : PerfectificationCarrier evaluation →ₗ[ℤ] Q,
      factor.comp (canonicalMap evaluation) = map := by
  refine ⟨canonicalFactor evaluation map kernel_compatibility,
    canonicalFactor_comp evaluation map kernel_compatibility, ?_⟩
  intro other other_eq
  exact canonicalFactor_unique evaluation map kernel_compatibility other other_eq

theorem dualEmbedding_universal :
    ∃! factor : PerfectificationCarrier evaluation →ₗ[ℤ]
        Module.Dual ℤ D,
      factor.comp (canonicalMap evaluation) = evaluation :=
  canonicalMap_universal evaluation evaluation le_rfl

/-! ## Generated duality evidence or residual -/

inductive PerfectificationDisposition : Type (max c d + 2) where
  | dualizable
      (equivalence : PerfectificationCarrier evaluation ≃ₗ[ℤ]
        Module.Dual ℤ D)
  | residual
      (outcome : EvaluationDispositionOutcome evaluation)

noncomputable def settlePerfectification :
    PerfectificationDisposition evaluation := by
  classical
  by_cases injective : Function.Injective evaluation
  · by_cases surjective : Function.Surjective evaluation
    · let candidateEquivalence : PerfectificationCarrier evaluation ≃ₗ[ℤ]
          Module.Dual ℤ D :=
        LinearEquiv.ofBijective (dualEmbedding evaluation) (by
          constructor
          · exact dualEmbedding_injective evaluation
          · intro target
            obtain ⟨value, equality⟩ := surjective target
            refine ⟨canonicalMap evaluation value, ?_⟩
            calc
              dualEmbedding evaluation (canonicalMap evaluation value) =
                  evaluation value := by rfl
              _ = target := equality)
      exact .dualizable candidateEquivalence
    · have existsCoordinate :
          ∃ coordinate : GeneratedEvaluationCokernelCoordinate evaluation,
            settleEvaluation evaluation = .coverageResidual coordinate := by
        simp [settleEvaluation, injective, surjective]
      exact .residual (.coverageResidual (Classical.choose existsCoordinate))
  · let existsCoordinate :=
      settleEvaluation_eq_kernelResidual_of_not_injective evaluation injective
    exact .residual (.kernelResidual (Classical.choose existsCoordinate))

theorem perfectificationDisposition_total :
    Nonempty (PerfectificationDisposition evaluation) :=
  ⟨settlePerfectification evaluation⟩

/-! ## Two-sided pairing disposition -/

variable {Dually : Type d} [AddCommGroup Dually]

inductive PairedPerfectificationDisposition
    (pairing : C →ₗ[ℤ] Dually →ₗ[ℤ] ℤ) : Type (max c d + 2) where
  | dualizable
      (leftEquivalence : PerfectificationCarrier pairing ≃ₗ[ℤ]
        Module.Dual ℤ Dually)
      (rightEquivalence : PerfectificationCarrier pairing.flip ≃ₗ[ℤ]
        Module.Dual ℤ C)
  | leftResidual
      (outcome : EvaluationDispositionOutcome pairing)
  | rightResidual
      (outcome : EvaluationDispositionOutcome pairing.flip)

noncomputable def settlePairedPerfectification
    (pairing : C →ₗ[ℤ] Dually →ₗ[ℤ] ℤ) :
    PairedPerfectificationDisposition pairing := by
  cases settlePerfectification pairing with
  | dualizable leftEquivalence =>
      cases settlePerfectification pairing.flip with
      | dualizable rightEquivalence =>
          exact .dualizable leftEquivalence rightEquivalence
      | residual outcome => exact .rightResidual outcome
  | residual outcome => exact .leftResidual outcome

theorem pairedPerfectificationDisposition_total
    (pairing : C →ₗ[ℤ] Dually →ₗ[ℤ] ℤ) :
    Nonempty (PairedPerfectificationDisposition pairing) :=
  ⟨settlePairedPerfectification pairing⟩

/-! ## Faithful map factorization and its exact residual -/

variable {A : Type a} [AddCommGroup A]
variable (faithful : C →ₗ[ℤ] A)

structure FaithfulFactorizationResidual where
  coordinate : C
  invisible_to_dual : coordinate ∈ LinearMap.ker evaluation
  visible_to_actual : faithful coordinate ≠ 0

inductive FaithfulFactorizationDisposition : Type (max c a + 2) where
  | factors
      (factor : PerfectificationCarrier evaluation →ₗ[ℤ] A)
      (factorization : factor.comp (canonicalMap evaluation) = faithful)
  | residual (coordinate : FaithfulFactorizationResidual evaluation faithful)

noncomputable def settleFaithfulFactorization :
    FaithfulFactorizationDisposition evaluation faithful := by
  classical
  by_cases compatible : LinearMap.ker evaluation ≤ LinearMap.ker faithful
  · exact .factors
      ((LinearMap.ker evaluation).liftQ faithful compatible)
      (by apply LinearMap.ext; intro value; rfl)
  · rw [SetLike.not_le_iff_exists] at compatible
    let value := Classical.choose compatible
    have value_spec := Classical.choose_spec compatible
    exact .residual
      ⟨value, value_spec.1, by
        simpa [value, LinearMap.mem_ker] using value_spec.2⟩

theorem faithfulFactorizationDisposition_total :
    Nonempty (FaithfulFactorizationDisposition evaluation faithful) :=
  ⟨settleFaithfulFactorization evaluation faithful⟩

theorem faithful_factorization_exists_iff :
    (∃ factor : PerfectificationCarrier evaluation →ₗ[ℤ] A,
      factor.comp (canonicalMap evaluation) = faithful) ↔
      LinearMap.ker evaluation ≤ LinearMap.ker faithful := by
  constructor
  · rintro ⟨factor, factorization⟩ value value_mem
    rw [LinearMap.mem_ker] at value_mem ⊢
    have equality := LinearMap.congr_fun factorization value
    have canonical_zero : canonicalMap evaluation value = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 value_mem
    rw [LinearMap.comp_apply, canonical_zero, map_zero] at equality
    exact equality.symm
  · intro compatibility
    exact ⟨canonicalFactor evaluation faithful compatibility,
      canonicalFactor_comp evaluation faithful compatibility⟩

/-! ## Actual-carrier lift disposition -/

/-- A source-generated lift from an actual carrier into the canonical
perfectification. -/
structure SourceGeneratedAmbientLift where
  lift : A →ₗ[ℤ] PerfectificationCarrier evaluation
  commutes : lift.comp faithful = canonicalMap evaluation

/-- If an actual carrier kills a source direction that the perfectification
retains, that direction is an explicit residual coordinate. -/
structure SourceGeneratedAmbientLiftKernelResidual where
  coordinate : C
  actual_zero : faithful coordinate = 0
  perfectification_nonzero : canonicalMap evaluation coordinate ≠ 0

inductive SourceGeneratedAmbientLiftDisposition : Type (max c a + 2) where
  | lifted (lift : SourceGeneratedAmbientLift evaluation faithful)
  | kernelResidual (residual :
      SourceGeneratedAmbientLiftKernelResidual evaluation faithful)
  | extensionResidual (obstruction :
      ¬ Nonempty (SourceGeneratedAmbientLift evaluation faithful))

noncomputable def settleSourceGeneratedAmbientLift :
    SourceGeneratedAmbientLiftDisposition evaluation faithful := by
  classical
  by_cases existsLift : Nonempty (SourceGeneratedAmbientLift evaluation faithful)
  · exact .lifted existsLift.some
  · by_cases compatible :
        LinearMap.ker faithful ≤ LinearMap.ker (canonicalMap evaluation)
    · exact .extensionResidual existsLift
    · rw [SetLike.not_le_iff_exists] at compatible
      let value := Classical.choose compatible
      have value_spec := Classical.choose_spec compatible
      exact .kernelResidual
        ⟨value, by
          simpa [value, LinearMap.mem_ker] using value_spec.1, by
          simpa [value, LinearMap.mem_ker] using value_spec.2⟩

theorem sourceGeneratedAmbientLiftDisposition_total :
    Nonempty (SourceGeneratedAmbientLiftDisposition evaluation faithful) :=
  ⟨settleSourceGeneratedAmbientLift evaluation faithful⟩

/-! ## Canonical free relation envelope of the perfectification carrier -/

/-- Every coimage carrier has a canonical source-generated free presentation:
actual points are generators and actual addition laws are relations.  This
exists without any finite or projective hypothesis. -/
abbrev PerfectificationPresentationCarrier :=
  PresentedAdditiveCarrier (PerfectificationCarrier evaluation)

def perfectificationPresentationEvaluation :
    PerfectificationPresentationCarrier evaluation →ₗ[ℤ]
      PerfectificationCarrier evaluation :=
  presentedEvaluation (PerfectificationCarrier evaluation)

def perfectificationPresentationGenerator :
    PerfectificationCarrier evaluation →+
      PerfectificationPresentationCarrier evaluation :=
  presentedGeneratorHom (PerfectificationCarrier evaluation)

def perfectificationPresentationEquiv :
    PerfectificationPresentationCarrier evaluation ≃+
      PerfectificationCarrier evaluation :=
  presentedAdditiveEquiv (PerfectificationCarrier evaluation)

@[simp] theorem perfectificationPresentation_evaluation_generator
    (value : PerfectificationCarrier evaluation) :
    perfectificationPresentationEvaluation evaluation
        (perfectificationPresentationGenerator evaluation value) = value :=
  presentedEvaluation_generator (PerfectificationCarrier evaluation) value

@[simp] theorem perfectificationPresentation_generator_evaluation
    (value : PerfectificationPresentationCarrier evaluation) :
    perfectificationPresentationGenerator evaluation
        (perfectificationPresentationEvaluation evaluation value) = value :=
  presentedGenerator_evaluation (PerfectificationCarrier evaluation) value

/-- The canonical presentation is always generated.  Its current integral
language is then classified as finite-free, finite but nonfree, or genuinely
non-finite.  The latter two are representation/perfection residuals, not
failures of the source carrier. -/
inductive PerfectificationPresentationDisposition : Type (max c d + 2) where
  | eligible
      (free : Module.Free ℤ (PerfectificationCarrier evaluation))
      (finite : Module.Finite ℤ (PerfectificationCarrier evaluation))
  | finiteNonfree
      (finite : Module.Finite ℤ (PerfectificationCarrier evaluation))
      (notFree : ¬ Module.Free ℤ (PerfectificationCarrier evaluation))
  | representationResidual
      (notFinite : ¬ Module.Finite ℤ (PerfectificationCarrier evaluation))

noncomputable def settlePerfectificationPresentation :
    PerfectificationPresentationDisposition evaluation := by
  classical
  by_cases finite : Module.Finite ℤ (PerfectificationCarrier evaluation)
  · by_cases free : Module.Free ℤ (PerfectificationCarrier evaluation)
    · exact .eligible free finite
    · exact .finiteNonfree finite free
  · exact .representationResidual finite

theorem perfectificationPresentationDisposition_total :
    Nonempty (PerfectificationPresentationDisposition evaluation) :=
  ⟨settlePerfectificationPresentation evaluation⟩

theorem settlePerfectificationPresentation_eq_eligible
    (free : Module.Free ℤ (PerfectificationCarrier evaluation))
    (finite : Module.Finite ℤ (PerfectificationCarrier evaluation)) :
    settlePerfectificationPresentation evaluation =
      .eligible free finite := by
  simp [settlePerfectificationPresentation, free, finite]

/-! ## Any finite observation language gets a bounded face or a residual -/

inductive FiniteObservationDisposition
    {P : Type c} {O : Type d}
    [AddCommGroup P] [AddCommGroup O]
    (observation : P →ₗ[ℤ] O) : Type (max c d + 2) where
  | bounded (equivalence : P ≃ₗ[ℤ] O)
  | residual (outcome : EvaluationDispositionOutcome observation)

noncomputable def settleFiniteObservation
    {P : Type c} {O : Type d}
    [AddCommGroup P] [AddCommGroup O]
    (observation : P →ₗ[ℤ] O) :
    FiniteObservationDisposition observation :=
  match settleEvaluation observation with
  | .equivalence equivalence => .bounded equivalence
  | .kernelResidual coordinate => .residual (.kernelResidual coordinate)
  | .coverageResidual coordinate => .residual (.coverageResidual coordinate)

theorem settleFiniteObservation_eq_bounded_of_bijective
    {P : Type c} {O : Type d}
    [AddCommGroup P] [AddCommGroup O]
    (observation : P →ₗ[ℤ] O)
    (injective : Function.Injective observation)
    (surjective : Function.Surjective observation) :
    settleFiniteObservation observation =
      .bounded (LinearEquiv.ofBijective observation ⟨injective, surjective⟩) := by
  rw [settleFiniteObservation,
    SourceGeneratedDualEvaluation.settleEvaluation_eq_equivalence_of_bijective
      observation injective surjective]

theorem finiteObservation_bounded_generates_finite
    {P : Type c} {O : Type d}
    [AddCommGroup P] [AddCommGroup O]
    [Module.Finite ℤ O]
    (equivalence : P ≃ₗ[ℤ] O) :
    Module.Finite ℤ P := by
  exact Module.Finite.of_surjective equivalence.symm.toLinearMap
    equivalence.symm.surjective

theorem finiteObservation_bounded_generates_free
    {P : Type c} {O : Type d}
    [AddCommGroup P] [AddCommGroup O]
    [Module.Free ℤ O]
    (equivalence : P ≃ₗ[ℤ] O) :
    Module.Free ℤ P := by
  exact Module.Free.of_equiv equivalence.symm

/-! ## Natural transport of the canonical perfectification -/

variable {C' : Type c} {D' : Type d}
variable [AddCommGroup C'] [AddCommGroup D']
variable (evaluation' : C' →ₗ[ℤ] Module.Dual ℤ D')

/-- Contravariant transport of dual functionals along a source map. -/
def inducedDualTarget (dualMap : D' →ₗ[ℤ] D) :
    Module.Dual ℤ D →ₗ[ℤ] Module.Dual ℤ D' :=
  dualMap.dualMap

@[simp] theorem inducedDualTarget_apply (dualMap : D' →ₗ[ℤ] D)
    (functional : Module.Dual ℤ D) (value : D') :
    inducedDualTarget dualMap functional value = functional (dualMap value) :=
  LinearMap.dualMap_apply dualMap functional value

/-- A source morphism satisfying the dual-evaluation square induces a unique
map between the two canonical coimage perfectifications.  Kernel compatibility
is generated from the square, not accepted as an extra premise. -/
def inducedPerfectificationMap
    (carrierMap : C →ₗ[ℤ] C')
    (dualMap : D' →ₗ[ℤ] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    PerfectificationCarrier evaluation →ₗ[ℤ]
      PerfectificationCarrier evaluation' :=
  (LinearMap.ker evaluation).liftQ
    ((canonicalMap evaluation').comp carrierMap)
    (by
      intro value value_mem
      rw [LinearMap.mem_ker] at value_mem ⊢
      apply (Submodule.Quotient.mk_eq_zero _).2
      have equality := LinearMap.congr_fun naturality value
      have left_zero : inducedDualTarget dualMap (evaluation value) = 0 := by
        rw [value_mem]
        rfl
      exact LinearMap.mem_ker.mpr (equality.symm.trans left_zero))

theorem inducedPerfectificationMap_comp
    (carrierMap : C →ₗ[ℤ] C')
    (dualMap : D' →ₗ[ℤ] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (inducedPerfectificationMap evaluation evaluation' carrierMap dualMap
      naturality).comp (canonicalMap evaluation) =
      (canonicalMap evaluation').comp carrierMap := by
  unfold inducedPerfectificationMap canonicalMap
  apply Submodule.liftQ_mkQ

theorem dualEmbedding_naturality
    (carrierMap : C →ₗ[ℤ] C')
    (dualMap : D' →ₗ[ℤ] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap) :
    (dualEmbedding evaluation').comp
        (inducedPerfectificationMap evaluation evaluation' carrierMap dualMap
          naturality) =
      (inducedDualTarget dualMap).comp (dualEmbedding evaluation) := by
  apply LinearMap.ext
  intro quotientValue
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (LinearMap.ker evaluation) quotientValue
  have equality := LinearMap.congr_fun naturality value
  exact equality.symm

theorem inducedPerfectificationMap_unique
    (carrierMap : C →ₗ[ℤ] C')
    (dualMap : D' →ₗ[ℤ] D)
    (naturality : (inducedDualTarget dualMap).comp evaluation =
      evaluation'.comp carrierMap)
    (other : PerfectificationCarrier evaluation →ₗ[ℤ]
      PerfectificationCarrier evaluation')
    (other_commutes : other.comp (canonicalMap evaluation) =
      (canonicalMap evaluation').comp carrierMap) :
    other = inducedPerfectificationMap evaluation evaluation' carrierMap dualMap
      naturality := by
  let compatibility : LinearMap.ker evaluation ≤
      LinearMap.ker (canonicalMap evaluation' |>.comp carrierMap) := by
    intro value value_mem
    rw [LinearMap.mem_ker] at value_mem ⊢
    apply (Submodule.Quotient.mk_eq_zero _).2
    have equality := LinearMap.congr_fun naturality value
    have left_zero : inducedDualTarget dualMap (evaluation value) = 0 := by
      rw [value_mem]
      rfl
    exact LinearMap.mem_ker.mpr (equality.symm.trans left_zero)
  calc
    other = (LinearMap.ker evaluation).liftQ
        ((canonicalMap evaluation').comp carrierMap)
        compatibility :=
      (canonicalMap_universal evaluation
        ((canonicalMap evaluation').comp carrierMap)
        compatibility).unique other_commutes
        (Submodule.liftQ_mkQ _ _ _)
    _ = inducedPerfectificationMap evaluation evaluation' carrierMap dualMap
        naturality := by
      rfl

/-! ## Explicit finite-language disposition

This is deliberately only a language classifier.  A finite free compression
is returned only when the source-generated proposition is inhabited; otherwise
the exact nonexistence obstruction is retained.  No finite/free witness enters
the producer's input, and the infinite-rank consumer below prevents this
branch from being silently universalized.
-/

inductive FiniteLanguageDisposition (module : Type a) [AddCommGroup module] :
    Type (a + 2) where
  | eligible (compression : CofinalPerfectCompressionNoGo.FiniteFreeSurjectiveCompressionAt module)
  | residual (obstruction :
      ¬ Nonempty (CofinalPerfectCompressionNoGo.FiniteFreeSurjectiveCompressionAt module))

noncomputable def settleFiniteLanguage
    {module : Type a} [AddCommGroup module] :
    FiniteLanguageDisposition module := by
  classical
  by_cases eligible : Nonempty
      (CofinalPerfectCompressionNoGo.FiniteFreeSurjectiveCompressionAt module)
  · exact .eligible eligible.some
  · exact .residual eligible

theorem infiniteRank_no_finiteLanguageCompression :
    ¬ Nonempty
      (CofinalPerfectCompressionNoGo.FiniteFreeSurjectiveCompressionAt
        (ℕ →₀ ℤ)) :=
  CofinalPerfectCompressionNoGo.natFinsupp_no_finiteFreeSurjectiveCompression

/-! ## Bounded observation face and determinant eligibility -/

inductive BoundedDualizableObservationDisposition
    (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)
    {O : Type a} [AddCommGroup O]
    (observation : PerfectificationCarrier evaluation →ₗ[ℤ] O) :
    Type (max c d a + 2) where
  | eligible
      (perfectificationEquivalence : PerfectificationCarrier evaluation ≃ₗ[ℤ]
        Module.Dual ℤ D)
      (observationEquivalence : PerfectificationCarrier evaluation ≃ₗ[ℤ] O)
  | perfectificationResidual
      (outcome : PerfectificationDisposition evaluation)
  | observationResidual
      (outcome : EvaluationDispositionOutcome observation)

noncomputable def settleBoundedDualizableObservation
    (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)
    {O : Type a} [AddCommGroup O]
    (observation : PerfectificationCarrier evaluation →ₗ[ℤ] O) :
    BoundedDualizableObservationDisposition evaluation observation := by
  cases settlePerfectification evaluation with
  | dualizable perfectificationEquivalence =>
      cases settleFiniteObservation observation with
      | bounded observationEquivalence =>
          exact .eligible perfectificationEquivalence observationEquivalence
      | residual outcome => exact .observationResidual outcome
  | residual outcome => exact .perfectificationResidual (.residual outcome)

theorem boundedDualizableObservation_total
    (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)
    {O : Type a} [AddCommGroup O]
    (observation : PerfectificationCarrier evaluation →ₗ[ℤ] O) :
    Nonempty (BoundedDualizableObservationDisposition evaluation observation) :=
  ⟨settleBoundedDualizableObservation evaluation observation⟩

/-- A bounded observer equivalence and its finite/free observer language
generate the finite-free compression used by determinant readouts. -/
def finiteFreeCompression_of_observationEquivalence
    {O : Type} [AddCommGroup O]
    [Module.Free ℤ O] [Module.Finite ℤ O]
    (equivalence : PerfectificationCarrier evaluation ≃ₗ[ℤ] O) :
    CofinalPerfectCompressionNoGo.FiniteFreeSurjectiveCompressionAt
      (PerfectificationCarrier evaluation) where
  Carrier := O
  readout := equivalence.symm.toLinearMap
  readout_surjective := equivalence.symm.surjective

/-! The root-controlled source adapter is kept in
LivingLawRootGeneratedCofinalSourcePerfectificationKernel.lean so this
coimage kernel remains source-neutral and reusable. -/

end
end SourceGeneratedPerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
