import H0mework.Versions.Y.Arithmetic.PoleOrbit.ClozelAllPlaceOriginOrbitDilationAction
import H0mework.Versions.Y.Arithmetic.PoleOrbit.OrbitSource

/-!
# Positive energy of the complete all-place origin orbit

The complete co-Poisson orbit is recharted at the source-owned half
coordinate and subtracted from the quarter-Mellin energy.  The actual source
relation is therefore in the kernel.  Dilation becomes the existing unitary
logarithmic translation, including on the source-generated energy range.

The selected and reversal modified-WeakFE pole sources have nonzero energy in
this realization.  No boundedness, unitarity, or energy-support premise is
used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace AllPlaceOriginDefect
namespace Orbit

open ClozelGeneralizedDual
open MeasureTheory
open scoped ENNReal SchwartzMap

noncomputable section

/-- The complete co-Poisson orbit recharted into quarter-Mellin energy. -/
theorem allPlaceOrbitCoPoissonCarrierQuarter_memLp
    (orbit : CoPoissonLogTranslationCarrier) :
    MemLp (fun x : ℝ => orbit.1 (x / 2)) (2 : ℝ≥0∞)
      (volume : Measure ℝ) := by
  rcases orbit.2 with ⟨test, orbit_eq⟩
  rw [← orbit_eq]
  have source := coPoissonQuarterMellinMap_mem_quarterL2 test
  change MemLp
    (positiveMellinLogQuarterTransform
      (coPoissonQuarterMellinMap test))
      (2 : ℝ≥0∞) (volume : Measure ℝ) at source
  apply (memLp_congr_ae ?_).mp source
  exact ae_of_all _ fun x =>
    positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap test x

def allPlaceOrbitCoPoissonQuarterEnergyMap :
    CoPoissonLogTranslationCarrier →ₗ[ℂ]
      PositiveMellinQuarterEnergy where
  toFun orbit := (allPlaceOrbitCoPoissonCarrierQuarter_memLp orbit).toLp
  map_add' left right := by
    change MemLp.toLp
        ((fun x : ℝ => left.1 (x / 2)) +
          fun x : ℝ => right.1 (x / 2)) _ = _
    exact MemLp.toLp_add
      (allPlaceOrbitCoPoissonCarrierQuarter_memLp left)
      (allPlaceOrbitCoPoissonCarrierQuarter_memLp right)
  map_smul' coefficient orbit := by
    change MemLp.toLp
        (coefficient • fun x : ℝ => orbit.1 (x / 2)) _ = _
    exact MemLp.toLp_const_smul coefficient
      (allPlaceOrbitCoPoissonCarrierQuarter_memLp orbit)

theorem allPlaceOrbitCoPoissonQuarterEnergyMap_source
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOrbitCoPoissonQuarterEnergyMap
        (coPoissonLogOrbitSourceMap test) =
      quarterMellinL2Feature z
        (coPoissonQuarterMellinConvergentMap
          z positive belowHalf test) := by
  change (allPlaceOrbitCoPoissonCarrierQuarter_memLp
      (coPoissonLogOrbitSourceMap test)).toLp
        (fun x : ℝ => (coPoissonLogOrbitSourceMap test).1 (x / 2)) =
    (coPoissonQuarterMellinConvergentMap
      z positive belowHalf test).2.1.toLp
        (positiveMellinLogQuarterTransform
          (coPoissonQuarterMellinConvergentMap
            z positive belowHalf test).1)
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => by
    rw [coPoissonQuarterMellinConvergentMap_value]
    exact (positiveMellinLogQuarterTransform_coPoissonQuarterMellinMap
      test x).symm

/-- Positive complete-orbit defect: quarter energy minus the recharted
co-Poisson orbit energy. -/
def allPlaceOrbitPositiveEnergyMap (z : ℂ) :
    AllPlaceOriginOrbitJointCarrier z →ₗ[ℂ]
      PositiveMellinQuarterEnergy where
  toFun value := quarterMellinL2Feature z value.1 -
    allPlaceOrbitCoPoissonQuarterEnergyMap value.2
  map_add' left right := by
    change quarterMellinL2Feature z (left.1 + right.1) -
        allPlaceOrbitCoPoissonQuarterEnergyMap (left.2 + right.2) = _
    rw [map_add, map_add]
    abel
  map_smul' coefficient value := by
    change quarterMellinL2Feature z (coefficient • value.1) -
        allPlaceOrbitCoPoissonQuarterEnergyMap
          (coefficient • value.2) = _
    rw [map_smul, map_smul]
    exact (smul_sub coefficient _ _).symm

/-- Mellin coordinate on the same complete-orbit presentation. -/
def allPlaceOrbitMellinFunctional (z : ℂ) :
    SourceGeneratedTestHilbertGeneralizedDual.TestDual
      (AllPlaceOriginOrbitJointCarrier z) where
  toFun value := quarterMellinL2Functional z value.1
  map_add' left right :=
    map_add (quarterMellinL2Functional z) left.1 right.1
  map_smul' coefficient value :=
    map_smul (quarterMellinL2Functional z) coefficient value.1

theorem allPlaceOrbitPositiveEnergyMap_relation
    (z : ℂ) (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (test : SchwartzMap ℝ ℂ) :
    allPlaceOrbitPositiveEnergyMap z
        (allPlaceOriginOrbitRelationMap z positive belowHalf test) = 0 := by
  change quarterMellinL2Feature z
      (coPoissonQuarterMellinConvergentMap
        z positive belowHalf test) -
      allPlaceOrbitCoPoissonQuarterEnergyMap
        (coPoissonLogOrbitSourceMap test) = 0
  rw [allPlaceOrbitCoPoissonQuarterEnergyMap_source
    z positive belowHalf test, sub_self]

theorem allPlaceOrbitCoPoissonQuarterEnergyMap_dilation
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale)
    (orbit : CoPoissonLogTranslationCarrier) :
    allPlaceOrbitCoPoissonQuarterEnergyMap
        (quarterMuntzOrbitDilationAction scale positive orbit) =
      positiveMellinQuarterEnergyTranslationIsometry (Real.log scale)
        (allPlaceOrbitCoPoissonQuarterEnergyMap orbit) := by
  rcases orbit.2 with ⟨test, orbit_eq⟩
  have orbit_source : coPoissonLogOrbitSourceMap test = orbit := by
    apply Subtype.ext
    exact orbit_eq
  rw [← orbit_source, quarterMuntzOrbitDilationAction_source,
    allPlaceOrbitCoPoissonQuarterEnergyMap_source
      z positiveZ belowHalf,
    allPlaceOrbitCoPoissonQuarterEnergyMap_source
      z positiveZ belowHalf]
  have relationSquare := LinearMap.congr_fun
    (quarterDilation_muntzRelation_square
      z positiveZ belowHalf scale positive) test
  change quarterDilationTestAction z scale positive
      (coPoissonQuarterMellinConvergentMap
        z positiveZ belowHalf test) =
    coPoissonQuarterMellinConvergentMap z positiveZ belowHalf
      (quarterMuntzSchwartzDilationAction scale positive test)
    at relationSquare
  rw [← relationSquare]
  exact (LinearMap.congr_fun
    (quarterDilationFeature_covariance z scale positive)
    (coPoissonQuarterMellinConvergentMap
      z positiveZ belowHalf test)).symm

/-- The complete source action intertwines with the genuine unitary energy
translation. -/
theorem allPlaceOrbitPositiveEnergyMap_dilation
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (scale : ℝ) (positive : 0 < scale)
    (value : AllPlaceOriginOrbitJointCarrier z) :
    allPlaceOrbitPositiveEnergyMap z
        (allPlaceOriginOrbitDilationAction z scale positive value) =
      positiveMellinQuarterEnergyTranslationIsometry (Real.log scale)
        (allPlaceOrbitPositiveEnergyMap z value) := by
  change quarterMellinL2Feature z
        (quarterDilationTestAction z scale positive value.1) -
      allPlaceOrbitCoPoissonQuarterEnergyMap
        (quarterMuntzOrbitDilationAction scale positive value.2) =
    positiveMellinQuarterEnergyTranslationIsometry (Real.log scale)
      (quarterMellinL2Feature z value.1 -
        allPlaceOrbitCoPoissonQuarterEnergyMap value.2)
  rw [allPlaceOrbitCoPoissonQuarterEnergyMap_dilation
      z positiveZ belowHalf scale positive value.2]
  have featureCovariance := LinearMap.congr_fun
    (quarterDilationFeature_covariance z scale positive) value.1
  change positiveMellinQuarterEnergyTranslationIsometry (Real.log scale)
      (quarterMellinL2Feature z value.1) =
    quarterMellinL2Feature z
      (quarterDilationTestAction z scale positive value.1)
    at featureCovariance
  rw [← featureCovariance]
  exact (map_sub
    (positiveMellinQuarterEnergyTranslationIsometry (Real.log scale))
    (quarterMellinL2Feature z value.1)
    (allPlaceOrbitCoPoissonQuarterEnergyMap value.2)).symm

/-- Minimal positive pre-Hilbert realization: the source-generated range in
the existing quarter-energy Hilbert carrier. -/
abbrev AllPlaceOrbitPositiveEnergyRange (z : ℂ) :=
  LinearMap.range (allPlaceOrbitPositiveEnergyMap z)

theorem allPlaceOrbitPositiveEnergyRange_translation_mem
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) (value : AllPlaceOrbitPositiveEnergyRange z) :
    positiveMellinQuarterEnergyTranslationIsometry shift value.1 ∈
      LinearMap.range (allPlaceOrbitPositiveEnergyMap z) := by
  rcases value.2 with ⟨source, source_eq⟩
  refine ⟨allPlaceOriginOrbitDilationAction z (Real.exp shift)
      (Real.exp_pos shift) source, ?_⟩
  rw [allPlaceOrbitPositiveEnergyMap_dilation
      z positiveZ belowHalf (Real.exp shift) (Real.exp_pos shift),
    Real.log_exp, source_eq]

def allPlaceOrbitPositiveEnergyRangeTranslationEquiv
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) :
    AllPlaceOrbitPositiveEnergyRange z ≃ₗ[ℂ]
      AllPlaceOrbitPositiveEnergyRange z where
  toFun value := ⟨
    positiveMellinQuarterEnergyTranslationIsometry shift value.1,
    allPlaceOrbitPositiveEnergyRange_translation_mem
      z positiveZ belowHalf shift value⟩
  invFun value := ⟨
    positiveMellinQuarterEnergyTranslationIsometry (-shift) value.1,
    allPlaceOrbitPositiveEnergyRange_translation_mem
      z positiveZ belowHalf (-shift) value⟩
  map_add' left right := by
    apply Subtype.ext
    exact map_add
      (positiveMellinQuarterEnergyTranslationIsometry shift)
      left.1 right.1
  map_smul' coefficient value := by
    apply Subtype.ext
    exact map_smul
      (positiveMellinQuarterEnergyTranslationIsometry shift)
      coefficient value.1
  left_inv value := by
    apply Subtype.ext
    exact (positiveMellinQuarterEnergyTranslationEquiv shift).left_inv value.1
  right_inv value := by
    apply Subtype.ext
    exact (positiveMellinQuarterEnergyTranslationEquiv shift).right_inv value.1

/-- Unitary logarithmic translation on the source-generated range. -/
def allPlaceOrbitPositiveEnergyRangeTranslationIsometry
    (z : ℂ) (positiveZ : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ))
    (shift : ℝ) :
    AllPlaceOrbitPositiveEnergyRange z ≃ₗᵢ[ℂ]
      AllPlaceOrbitPositiveEnergyRange z :=
  ⟨allPlaceOrbitPositiveEnergyRangeTranslationEquiv
      z positiveZ belowHalf shift,
    fun value => positiveMellinQuarterEnergyTranslation_norm shift value.1⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

theorem selectedAllPlacePole_positiveEnergy_readback :
    allPlaceOrbitPositiveEnergyMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial) =
      quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation)
        (selectedSourceModifiedUnitQuarterTest observation nontrivial) := by
  unfold selectedAllPlacePoleOrbitJointValue
  rw [map_sub, map_smul,
    allPlaceOrbitPositiveEnergyMap_relation, smul_zero, sub_zero]
  change quarterMellinL2Feature
      (selectedCoPoissonMuntzParameter observation)
      (selectedSourceModifiedUnitQuarterTest observation nontrivial) -
      allPlaceOrbitCoPoissonQuarterEnergyMap 0 = _
  rw [map_zero, sub_zero]

theorem reversalAllPlacePole_positiveEnergy_readback :
    allPlaceOrbitPositiveEnergyMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial) =
      quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation)
        (reversalSourceModifiedUnitQuarterTest observation nontrivial) := by
  unfold reversalAllPlacePoleOrbitJointValue
  rw [map_sub, map_smul,
    allPlaceOrbitPositiveEnergyMap_relation, smul_zero, sub_zero]
  change quarterMellinL2Feature
      (reversalCoPoissonMuntzParameter observation)
      (reversalSourceModifiedUnitQuarterTest observation nontrivial) -
      allPlaceOrbitCoPoissonQuarterEnergyMap 0 = _
  rw [map_zero, sub_zero]

theorem selectedAllPlacePole_positiveEnergy_ne_zero :
    allPlaceOrbitPositiveEnergyMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial) ≠ 0 := by
  rw [selectedAllPlacePole_positiveEnergy_readback]
  intro energyZero
  have functionalZero :=
    ClozelGeneralizedDual.CenteredGram.quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
      (selectedCoPoissonMuntzParameter observation)
      (selectedSourceModifiedUnitQuarterTest observation nontrivial)
      energyZero
  rw [selectedSourceModifiedUnitQuarterTest_functional_one] at functionalZero
  norm_num at functionalZero

theorem reversalAllPlacePole_positiveEnergy_ne_zero :
    allPlaceOrbitPositiveEnergyMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial) ≠ 0 := by
  rw [reversalAllPlacePole_positiveEnergy_readback]
  intro energyZero
  have functionalZero :=
    ClozelGeneralizedDual.CenteredGram.quarterMellinL2Feature_eq_zero_imp_functional_eq_zero
      (reversalCoPoissonMuntzParameter observation)
      (reversalSourceModifiedUnitQuarterTest observation nontrivial)
      energyZero
  rw [reversalSourceModifiedUnitQuarterTest_functional_one] at functionalZero
  norm_num at functionalZero

end

end Orbit
end AllPlaceOriginDefect
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
