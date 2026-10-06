import H0mework.Arithmetic.PoleOrbit.OriginOrbitCarrier
import H0mework.Arithmetic.MuntzAction.GaussianCoPoissonRelation
import H0mework.Arithmetic.SonineCoupling.ModifiedWeakFEPoleSourceEnergy

/-!
# Source-owned complete all-place pole orbit

The modified WeakFE pole is lifted before every boundary or runtime read.  Its
quarter test, complete co-Poisson log orbit, zero-origin defect, and nonzero
quarter energy are sibling projections of one source value.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

namespace ClozelGeneralizedDual

noncomputable section

theorem reversalGaussianQuarterTest_eq_coPoissonRelation
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    reversalGaussianQuarterTest observation nontrivial =
      coPoissonQuarterMellinConvergentMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        clozelGaussianSchwartz := by
  apply Subtype.ext
  change positiveGeneratedClozelGaussianRemainder owner =
    coPoissonQuarterMellinMap clozelGaussianSchwartz
  exact (coPoissonQuarterMellinMap_clozelGaussian
    owner).symm

end
end ClozelGeneralizedDual

namespace AllPlaceOriginDefect

open ClozelGeneralizedDual

noncomputable section

theorem positiveSourceModifiedUnitDetector_logQuarter_origin
    (owner : GlobalGermOwner) (z : ℂ) :
    positiveMellinLogQuarterTransform
        (positiveSourceModifiedUnitDetector owner z) 0 = 0 := by
  unfold positiveMellinLogQuarterTransform positiveSourceModifiedUnitDetector
    sourceModifiedUnitDetector
  rw [GeneratedRiemannWeakFEPairAt.generate_pair]
  unfold WeakFEPair.f_modif
  simp

namespace Orbit

open ClozelGeneralizedDual.CenteredGram
open scoped SchwartzMap

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial :
  ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))

def selectedAllPlacePoleOrbitJointValue :
    AllPlaceOriginOrbitJointCarrier
      (selectedCoPoissonMuntzParameter observation) :=
  (selectedSourceModifiedUnitQuarterTest observation nontrivial, 0) -
    sourceModifiedUnitCoefficient
        (selectedCoPoissonMuntzParameter observation) •
      allPlaceOriginOrbitRelationMap
        (selectedCoPoissonMuntzParameter observation)
        (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
        (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        clozelGaussianSchwartz

def reversalAllPlacePoleOrbitJointValue :
    AllPlaceOriginOrbitJointCarrier
      (reversalCoPoissonMuntzParameter observation) :=
  (reversalSourceModifiedUnitQuarterTest observation nontrivial, 0) -
    sourceModifiedUnitCoefficient
        (reversalCoPoissonMuntzParameter observation) •
      allPlaceOriginOrbitRelationMap
        (reversalCoPoissonMuntzParameter observation)
        (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
        (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
        clozelGaussianSchwartz

theorem selectedAllPlacePoleOrbit_fst :
    (selectedAllPlacePoleOrbitJointValue observation nontrivial).1 =
      selectedModifiedWeakFEPoleTraceTest observation nontrivial := by
  unfold selectedAllPlacePoleOrbitJointValue
    allPlaceOriginOrbitRelationMap
  change selectedSourceModifiedUnitQuarterTest observation nontrivial -
      sourceModifiedUnitCoefficient
          (selectedCoPoissonMuntzParameter observation) •
        coPoissonQuarterMellinConvergentMap
          (selectedCoPoissonMuntzParameter observation)
          (selectedCoPoissonMuntzParameter_re_pos observation nontrivial)
          (selectedCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          clozelGaussianSchwartz = _
  rw [← selectedGaussianQuarterTest_eq_coPoissonRelation
    observation nontrivial]
  rfl

theorem reversalAllPlacePoleOrbit_fst :
    (reversalAllPlacePoleOrbitJointValue observation nontrivial).1 =
      reversalModifiedWeakFEPoleTraceTest observation nontrivial := by
  unfold reversalAllPlacePoleOrbitJointValue
    allPlaceOriginOrbitRelationMap
  change reversalSourceModifiedUnitQuarterTest observation nontrivial -
      sourceModifiedUnitCoefficient
          (reversalCoPoissonMuntzParameter observation) •
        coPoissonQuarterMellinConvergentMap
          (reversalCoPoissonMuntzParameter observation)
          (reversalCoPoissonMuntzParameter_re_pos observation nontrivial)
          (reversalCoPoissonMuntzParameter_re_lt_half observation nontrivial)
          clozelGaussianSchwartz = _
  rw [← reversalGaussianQuarterTest_eq_coPoissonRelation
    observation nontrivial]
  rfl

theorem selectedAllPlacePoleOrbit_sourceEnergy_ne_zero :
    quarterMellinL2Feature
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial).1 ≠ 0 := by
  rw [selectedAllPlacePoleOrbit_fst]
  exact selectedModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
    observation nontrivial

theorem reversalAllPlacePoleOrbit_sourceEnergy_ne_zero :
    quarterMellinL2Feature
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial).1 ≠ 0 := by
  rw [reversalAllPlacePoleOrbit_fst]
  exact reversalModifiedWeakFEPoleTraceTest_sourceEnergy_ne_zero
    observation nontrivial

theorem selectedAllPlacePoleOrbitDefect_zero_at_origin :
    allPlaceOriginOrbitDefect
        (selectedCoPoissonMuntzParameter observation)
        (selectedAllPlacePoleOrbitJointValue observation nontrivial) 0 = 0 := by
  unfold selectedAllPlacePoleOrbitJointValue
  rw [map_sub, map_smul,
    allPlaceOriginOrbitDefect_relation_eq_zero, smul_zero, sub_zero]
  change positiveMellinLogQuarterTransform
      (positiveSourceModifiedUnitDetector globalGermOccurrence.root
        (selectedCoPoissonMuntzParameter observation)) 0 - 0 = 0
  rw [positiveSourceModifiedUnitDetector_logQuarter_origin]
  exact sub_self 0

theorem reversalAllPlacePoleOrbitDefect_zero_at_origin :
    allPlaceOriginOrbitDefect
        (reversalCoPoissonMuntzParameter observation)
        (reversalAllPlacePoleOrbitJointValue observation nontrivial) 0 = 0 := by
  unfold reversalAllPlacePoleOrbitJointValue
  rw [map_sub, map_smul,
    allPlaceOriginOrbitDefect_relation_eq_zero, smul_zero, sub_zero]
  change positiveMellinLogQuarterTransform
      (positiveSourceModifiedUnitDetector globalGermOccurrence.root
        (reversalCoPoissonMuntzParameter observation)) 0 - 0 = 0
  rw [positiveSourceModifiedUnitDetector_logQuarter_origin]
  exact sub_self 0

end Orbit
end
end AllPlaceOriginDefect
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
