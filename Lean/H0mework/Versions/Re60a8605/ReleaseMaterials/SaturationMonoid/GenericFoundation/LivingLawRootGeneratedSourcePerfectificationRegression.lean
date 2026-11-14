import H0mework.Realization.Perfectification.SourceCoimage

/-!
# Direct regression for source-generated perfectification

The positive integer evaluation exercises the dualizable branch and the
coimage universal property.  The zero evaluation exercises the generated
kernel residual.  A separate infinite-rank check keeps finite-language
compression from being read as a universal premise.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedPerfectificationRegression

open SourceGeneratedDualEvaluation
open SourceGeneratedPerfectification
open CofinalPerfectCompressionNoGo

noncomputable section

/-! ## Positive and residual coimage branches -/

def integerEvaluation : ℤ →ₗ[ℤ] Module.Dual ℤ ℤ :=
  LinearMap.lsmul ℤ ℤ

theorem integerEvaluation_injective :
    Function.Injective integerEvaluation := by
  intro left right equality
  have evaluated := LinearMap.congr_fun equality (1 : ℤ)
  simpa [integerEvaluation, LinearMap.lsmul_apply] using evaluated

theorem integerEvaluation_surjective :
    Function.Surjective integerEvaluation := by
  intro functional
  refine ⟨functional 1, ?_⟩
  apply LinearMap.ext
  intro value
  rw [integerEvaluation, LinearMap.lsmul_apply]
  calc
    functional 1 • value = value • functional 1 := by simp [mul_comm]
    _ = functional (value • (1 : ℤ)) := (functional.map_smul value 1).symm
    _ = functional value := by simp

def integerEquivalence :
    PerfectificationCarrier integerEvaluation ≃ₗ[ℤ]
      Module.Dual ℤ ℤ :=
  LinearEquiv.ofBijective (dualEmbedding integerEvaluation)
    ⟨dualEmbedding_injective integerEvaluation, by
      intro target
      obtain ⟨value, equality⟩ := integerEvaluation_surjective target
      refine ⟨canonicalMap integerEvaluation value, ?_⟩
      calc
        dualEmbedding integerEvaluation
            (canonicalMap integerEvaluation value) = integerEvaluation value := rfl
        _ = target := equality⟩

theorem integer_positive_branch :
    settlePerfectification integerEvaluation =
      .dualizable integerEquivalence := by
  apply congrArg (fun outcome => outcome)
  exact (by
    simp [settlePerfectification, integerEvaluation_injective,
      integerEvaluation_surjective, integerEquivalence])

def integerPairing : ℤ →ₗ[ℤ] ℤ →ₗ[ℤ] ℤ :=
  LinearMap.lsmul ℤ ℤ

theorem integer_paired_perfectification_total :
    Nonempty (PairedPerfectificationDisposition integerPairing) :=
  pairedPerfectificationDisposition_total integerPairing

def integerFiniteObservation :
    PerfectificationCarrier integerEvaluation →ₗ[ℤ]
      Module.Dual ℤ ℤ :=
  dualEmbedding integerEvaluation

theorem integer_bounded_observation_total :
    Nonempty (SourceGeneratedPerfectification.BoundedDualizableObservationDisposition
      integerEvaluation
      integerFiniteObservation) :=
  SourceGeneratedPerfectification.boundedDualizableObservation_total
    integerEvaluation integerFiniteObservation

def integer_finite_observation_bounded :
    FiniteObservationDisposition integerFiniteObservation :=
  .bounded integerEquivalence

theorem integer_finite_observation_generates_finite :
    Module.Finite ℤ (PerfectificationCarrier integerEvaluation) :=
  finiteObservation_bounded_generates_finite integerEquivalence

theorem integer_finite_observation_generates_free :
    Module.Free ℤ (PerfectificationCarrier integerEvaluation) := by
  letI : Module.Free ℤ (Module.Dual ℤ ℤ) := by
    exact Module.Free.of_equiv
      (LinearEquiv.ofBijective integerEvaluation
        ⟨integerEvaluation_injective, integerEvaluation_surjective⟩)
  exact finiteObservation_bounded_generates_free integerEquivalence

noncomputable def integerFiniteCompression :
    FiniteFreeSurjectiveCompressionAt
      (PerfectificationCarrier integerEvaluation) := by
  let dualEquivalence : ℤ ≃ₗ[ℤ] Module.Dual ℤ ℤ :=
    LinearEquiv.ofBijective integerEvaluation
      ⟨integerEvaluation_injective, integerEvaluation_surjective⟩
  letI : Module.Free ℤ (Module.Dual ℤ ℤ) :=
    Module.Free.of_equiv dualEquivalence
  letI : Module.Finite ℤ (Module.Dual ℤ ℤ) := by
    exact Module.Finite.of_surjective dualEquivalence.toLinearMap
      dualEquivalence.surjective
  exact finiteFreeCompression_of_observationEquivalence
    integerEvaluation integerEquivalence

theorem integer_finite_compression_surjective :
    Function.Surjective integerFiniteCompression.readout :=
  integerFiniteCompression.readout_surjective

theorem integer_universal_factorization :
    ∃! factor : PerfectificationCarrier integerEvaluation →ₗ[ℤ] ℤ,
      factor.comp (canonicalMap integerEvaluation) = LinearMap.id := by
  apply canonicalMap_universal integerEvaluation
  intro value value_mem
  change value = 0
  change integerEvaluation value = 0 at value_mem
  have evaluated := congrArg (fun functional => functional (1 : ℤ)) value_mem
  simpa [integerEvaluation, LinearMap.lsmul_apply] using evaluated

def zeroEvaluation : ℤ →ₗ[ℤ] Module.Dual ℤ ℤ := 0

abbrev InfiniteCarrier := ℕ →₀ ℤ

def infiniteZeroEvaluation : InfiniteCarrier →ₗ[ℤ]
    Module.Dual ℤ InfiniteCarrier := 0

theorem infinite_rank_source_direction_is_dual_invisible :
    ∃ coordinate : InfiniteCarrier,
      coordinate ≠ 0 ∧ infiniteZeroEvaluation coordinate = 0 := by
  refine ⟨Finsupp.single 0 1, ?_, ?_⟩
  · simp
  · simp [infiniteZeroEvaluation]

theorem infinite_zero_evaluation_not_injective :
    ¬ Function.Injective infiniteZeroEvaluation := by
  intro injective
  have equality : infiniteZeroEvaluation (Finsupp.single 0 1) =
      infiniteZeroEvaluation 0 := by
    simp [infiniteZeroEvaluation]
  have coordinate_zero := injective equality
  simp at coordinate_zero

theorem infinite_perfectification_kernel_residual :
    ∃ coordinate : GeneratedEvaluationKernelCoordinate infiniteZeroEvaluation,
      settlePerfectification infiniteZeroEvaluation =
        .residual (.kernelResidual coordinate) := by
  let existsCoordinate :=
    settleEvaluation_eq_kernelResidual_of_not_injective
      infiniteZeroEvaluation infinite_zero_evaluation_not_injective
  let coordinate := Classical.choose existsCoordinate
  refine ⟨coordinate, ?_⟩
  have equality := congrArg (fun outcome =>
      PerfectificationDisposition.residual outcome)
    (Classical.choose_spec existsCoordinate)
  simp [settlePerfectification, infinite_zero_evaluation_not_injective,
    coordinate] at equality ⊢

theorem infinite_rank_keeps_explicit_representation_residual :
    ¬ Module.Finite ℤ InfiniteCarrier ∧
      ¬ Nonempty (FiniteFreeSurjectiveCompressionAt InfiniteCarrier) :=
  ⟨CofinalPerfectCompressionNoGo.natFinsupp_not_moduleFinite,
    CofinalPerfectCompressionNoGo.natFinsupp_no_finiteFreeSurjectiveCompression⟩

theorem zero_kernel_residual :
    ∃ coordinate : GeneratedEvaluationKernelCoordinate zeroEvaluation,
      settlePerfectification zeroEvaluation =
        .residual (.kernelResidual coordinate) := by
  have not_injective : ¬ Function.Injective zeroEvaluation := by
    intro injective
    have equality : zeroEvaluation (1 : ℤ) = zeroEvaluation 0 := by
      simp [zeroEvaluation]
    exact one_ne_zero (injective equality)
  let existsCoordinate :=
    settleEvaluation_eq_kernelResidual_of_not_injective zeroEvaluation not_injective
  let coordinate := Classical.choose existsCoordinate
  refine ⟨coordinate, ?_⟩
  have equality := congrArg
    (fun outcome =>
      PerfectificationDisposition.residual
        (.kernelResidual (Classical.choose existsCoordinate)))
    (Classical.choose_spec existsCoordinate)
  simp [settlePerfectification, not_injective, coordinate] at equality ⊢

/-! ## Faithful factorization branches -/

def integerFaithful : ℤ →ₗ[ℤ] ℤ := LinearMap.id

theorem integer_faithful_factors :
    ∃ factor : PerfectificationCarrier integerEvaluation →ₗ[ℤ] ℤ,
      factor.comp (canonicalMap integerEvaluation) = integerFaithful := by
  cases settleFaithfulFactorization integerEvaluation integerFaithful with
  | factors factor factorization => exact ⟨factor, factorization⟩
  | residual coordinate =>
      exfalso
      apply coordinate.visible_to_actual
      have equality : integerEvaluation coordinate.coordinate =
          integerEvaluation 0 := by
        simpa [integerEvaluation, LinearMap.lsmul_apply] using
          coordinate.invisible_to_dual
      have coordinate_zero : coordinate.coordinate = 0 :=
        integerEvaluation_injective equality
      simp [integerFaithful, coordinate_zero]

def integerAmbientLift :
    SourceGeneratedPerfectification.SourceGeneratedAmbientLift
      integerEvaluation integerFaithful where
  lift := canonicalMap integerEvaluation
  commutes := by
    apply LinearMap.ext
    intro value
    rfl

theorem integer_ambient_lift_commutes :
    integerAmbientLift.lift.comp integerFaithful =
      canonicalMap integerEvaluation :=
  integerAmbientLift.commutes

def zeroFaithful : ℤ →ₗ[ℤ] ℤ := 0

theorem canonicalMap_one_ne_zero :
    canonicalMap integerEvaluation (1 : ℤ) ≠ 0 := by
  intro equality
  have mapped := congrArg (dualEmbedding integerEvaluation) equality
  change integerEvaluation (1 : ℤ) = integerEvaluation 0 at mapped
  exact one_ne_zero (integerEvaluation_injective mapped)

def zeroFaithfulResidual :
    SourceGeneratedPerfectification.SourceGeneratedAmbientLiftKernelResidual
      integerEvaluation zeroFaithful where
  coordinate := 1
  actual_zero := by simp [zeroFaithful]
  perfectification_nonzero := canonicalMap_one_ne_zero

theorem zero_faithful_has_no_ambient_lift :
    ¬ Nonempty
      (SourceGeneratedPerfectification.SourceGeneratedAmbientLift
        integerEvaluation zeroFaithful) := by
  rintro ⟨lift⟩
  have atOne := LinearMap.congr_fun lift.commutes (1 : ℤ)
  apply canonicalMap_one_ne_zero
  simpa [zeroFaithful] using atOne.symm

/-! ## Finite observation and source-morphism naturality -/

def zeroObservation : PerfectificationCarrier integerEvaluation →ₗ[ℤ] ℤ := 0

theorem zeroObservation_not_injective : ¬ Function.Injective zeroObservation := by
  intro injective
  have equality : zeroObservation (canonicalMap integerEvaluation 1) =
      zeroObservation 0 := by simp [zeroObservation]
  exact canonicalMap_one_ne_zero (injective equality)

theorem zeroObservation_disposition_total :
    Nonempty (FiniteObservationDisposition zeroObservation) :=
  ⟨settleFiniteObservation zeroObservation⟩

noncomputable def zeroObservationKernelCoordinate :
    GeneratedEvaluationKernelCoordinate zeroObservation :=
  Classical.choose
    (settleEvaluation_eq_kernelResidual_of_not_injective
      zeroObservation zeroObservation_not_injective)

theorem zeroObservationKernelCoordinate_nonzero :
    zeroObservationKernelCoordinate.coordinate ≠ 0 :=
  zeroObservationKernelCoordinate.coordinate_ne_zero

theorem integer_identity_perfectification_natural :
    (inducedPerfectificationMap integerEvaluation integerEvaluation
      LinearMap.id LinearMap.id rfl).comp (canonicalMap integerEvaluation) =
      (canonicalMap integerEvaluation).comp LinearMap.id :=
  inducedPerfectificationMap_comp integerEvaluation integerEvaluation
    LinearMap.id LinearMap.id rfl

theorem integer_identity_dual_embedding_natural :
    (dualEmbedding integerEvaluation).comp
        (inducedPerfectificationMap integerEvaluation integerEvaluation
          LinearMap.id LinearMap.id rfl) =
      (inducedDualTarget (LinearMap.id : ℤ →ₗ[ℤ] ℤ)).comp
        (dualEmbedding integerEvaluation) :=
  dualEmbedding_naturality integerEvaluation integerEvaluation
    LinearMap.id LinearMap.id rfl

theorem infinite_rank_representation_residual :
    ¬ Nonempty
      (FiniteFreeSurjectiveCompressionAt (ℕ →₀ ℤ)) :=
  infiniteRank_no_finiteLanguageCompression

/-! Root-scoped consumption is covered by the sibling
CofinalHistoryCochainSourcePerfectificationRegression file. -/

#print axioms integer_positive_branch
#print axioms integer_paired_perfectification_total
#print axioms integer_bounded_observation_total
#print axioms integer_finite_observation_generates_finite
#print axioms integer_finite_compression_surjective
#print axioms integer_identity_perfectification_natural
#print axioms integer_identity_dual_embedding_natural
#print axioms zero_faithful_has_no_ambient_lift
#print axioms zero_kernel_residual
#print axioms infinite_rank_source_direction_is_dual_invisible
#print axioms infinite_perfectification_kernel_residual
#print axioms infinite_rank_keeps_explicit_representation_residual
end
end SourceGeneratedPerfectificationRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
