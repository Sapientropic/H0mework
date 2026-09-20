import H0mework.Realization.Integral.PrimeResidual
import H0mework.Arithmetic.CoPoisson.PrimePowerFace
import H0mework.Arithmetic.Tempered.RemainderReality

/-!
# First cofinal compression residual for the theta integral face

The canonical scale pull transports the whole distribution from the `4`
stage to the `2` stage.  It sends the quotient generator to one half of the
previous generator, which lies outside the previous cyclic integral face.
Thus each finite stage is faithful and prime-power eligible, while the first
candidate cofinal restriction has an explicit representation residual.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open ClozelEndpointSourceEffect
open SourceGeneratedFaithfulIntegralFace
open scoped SchwartzMap

noncomputable section

abbrev ThetaDistributionPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

theorem remainderWitnessThetaDistributionHalf_apply_eq_one :
    coPoissonMuntzThetaDistribution (1 / 2 : ℝ) (by norm_num)
        remainderWitnessSchwartz = 1 := by
  rw [coPoissonMuntzThetaDistribution_apply,
    coPoissonMuntzTheta_eq_integer_tsum remainderWitnessSchwartz
      (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [tsum_eq_single 0]
  · simp
  · intro n nonzero
    rw [remainderWitnessSchwartz_apply]
    have bumpZero :
        remainderWitnessBump ((1 / 2 : ℝ) * (n : ℝ)) = 0 := by
      apply remainderWitnessBump.zero_of_le_dist
      have oneLe : (1 : ℝ) ≤ |(n : ℝ)| := by
        exact_mod_cast Int.one_le_abs nonzero
      simpa [remainderWitnessBump, Real.dist_eq, abs_mul] using
        (show (1 / 2 : ℝ) ≤ (1 / 2) * |(n : ℝ)| by linarith)
    rw [bumpZero]
    exact Complex.ofReal_zero

theorem thetaDistributionPrimeTwoQuotient_ne_zero :
    thetaDistributionQuotient ThetaDistributionPrimeTwo 1 ≠ 0 := by
  intro quotientZero
  have landing := thetaDistributionWhole_eq_primePower_nsmul_quotient
    ThetaDistributionPrimeTwo 1
  rw [quotientZero, nsmul_zero] at landing
  have evaluated := congrArg
    (fun distribution : ComplexTempered ↦
      distribution remainderWitnessSchwartz) landing
  change coPoissonMuntzThetaDistribution (1 / 2 : ℝ) (by norm_num)
      remainderWitnessSchwartz = 0 at evaluated
  rw [remainderWitnessThetaDistributionHalf_apply_eq_one] at evaluated
  exact one_ne_zero evaluated

theorem thetaDistributionPrimeTwoIntegralFace_nontrivial :
    Nontrivial
      (ThetaDistributionPrimePowerIntegralFace
        ThetaDistributionPrimeTwo 1) := by
  exact nontrivial_iff.mpr ⟨thetaDistributionQuotientElement
    ThetaDistributionPrimeTwo 1, 0, by
      intro equality
      apply thetaDistributionPrimeTwoQuotient_ne_zero
      exact congrArg Subtype.val equality⟩

theorem thetaDistributionPrimeTwoQuotientElement_not_divisible :
    ¬ ∃ divided : ThetaDistributionPrimePowerIntegralFace
        ThetaDistributionPrimeTwo 1,
      2 • divided = thetaDistributionQuotientElement
        ThetaDistributionPrimeTwo 1 := by
  rintro ⟨divided, division⟩
  obtain ⟨multiplicity, dividedValue⟩ :=
    AddSubgroup.mem_zmultiples_iff.mp divided.2
  have ambient := congrArg Subtype.val division
  change 2 • (divided : ComplexTempered) =
    thetaDistributionQuotient ThetaDistributionPrimeTwo 1 at ambient
  rw [← dividedValue] at ambient
  have ambientC :
      (2 : ℂ) • ((multiplicity : ℂ) •
        thetaDistributionQuotient ThetaDistributionPrimeTwo 1) =
          thetaDistributionQuotient ThetaDistributionPrimeTwo 1 := by
    calc
      _ = (2 : ℂ) • (multiplicity •
          thetaDistributionQuotient ThetaDistributionPrimeTwo 1) := by
        congr 1
        exact Int.cast_smul_eq_zsmul ℂ multiplicity
          (thetaDistributionQuotient ThetaDistributionPrimeTwo 1)
      _ = (2 : Nat) • (multiplicity •
          thetaDistributionQuotient ThetaDistributionPrimeTwo 1) :=
        Nat.cast_smul_eq_nsmul ℂ 2
          (multiplicity •
            thetaDistributionQuotient ThetaDistributionPrimeTwo 1)
      _ = _ := ambient
  have scalarEquality : (((2 : ℤ) * multiplicity : ℤ) : ℂ) = 1 := by
    apply smul_left_injective ℂ thetaDistributionPrimeTwoQuotient_ne_zero
    simpa only [Int.cast_mul, Int.cast_ofNat, smul_smul, one_smul] using ambientC
  have integerEquality : (2 : ℤ) * multiplicity = 1 := by
    exact_mod_cast scalarEquality
  omega

def thetaDistributionPrimeTwoResidualCoordinate :
    PrimeResidualCoordinate
      (L := ThetaDistributionPrimePowerIntegralFace
        ThetaDistributionPrimeTwo 1)
      ThetaDistributionPrimeTwo where
  representative := thetaDistributionQuotientElement
    ThetaDistributionPrimeTwo 1
  not_divisible := thetaDistributionPrimeTwoQuotientElement_not_divisible

/-- Precomposition by source scaling on actual tempered distributions. -/
def thetaDistributionScalePull
    (scale : ℝ) (nonzero : scale ≠ 0) :
    ComplexTempered →L[ℂ] ComplexTempered :=
  PointwiseConvergenceCLM.precomp ℂ
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (realScaleEquiv scale nonzero))

@[simp] theorem thetaDistributionScalePull_apply
    (scale : ℝ) (nonzero : scale ≠ 0)
    (distribution : ComplexTempered) (test : SchwartzMap ℝ ℂ) :
    thetaDistributionScalePull scale nonzero distribution test =
      distribution (scaledSchwartzTest scale nonzero test) :=
  rfl

theorem thetaDistributionScalePull_thetaDistribution
    (outer inner : ℝ) (outerNe : outer ≠ 0) (innerNe : inner ≠ 0) :
    thetaDistributionScalePull outer outerNe
        (coPoissonMuntzThetaDistribution inner innerNe) =
      coPoissonMuntzThetaDistribution (outer * inner)
        (mul_ne_zero outerNe innerNe) := by
  ext test
  rw [thetaDistributionScalePull_apply,
    coPoissonMuntzThetaDistribution_apply,
    coPoissonMuntzThetaDistribution_apply,
    coPoissonMuntzTheta_eq_integer_tsum
      (scaledSchwartzTest outer outerNe test) innerNe,
    coPoissonMuntzTheta_eq_integer_tsum test (mul_ne_zero outerNe innerNe)]
  apply tsum_congr
  intro n
  rw [scaledSchwartzTest_apply]
  congr 1
  ring

theorem thetaDistributionScalePull_two_whole_four_eq_whole_two :
    thetaDistributionScalePull 2 (by norm_num)
        (thetaDistributionWhole ThetaDistributionPrimeTwo 2) =
      thetaDistributionWhole ThetaDistributionPrimeTwo 1 := by
  unfold thetaDistributionWhole thetaDistributionPrimePower
  convert thetaDistributionScalePull_thetaDistribution
      2 (1 / 4) (by norm_num) (by norm_num) using 1 <;> norm_num

theorem thetaDistributionScalePull_two_quotient_four_eq_half_quotient_two :
    thetaDistributionScalePull 2 (by norm_num)
        (thetaDistributionQuotient ThetaDistributionPrimeTwo 2) =
      (1 / 2 : ℂ) •
        thetaDistributionQuotient ThetaDistributionPrimeTwo 1 := by
  have landingFour := congrArg
    (thetaDistributionScalePull 2 (by norm_num))
    (thetaDistributionWhole_eq_primePower_nsmul_quotient
      ThetaDistributionPrimeTwo 2)
  rw [map_nsmul,
    thetaDistributionScalePull_two_whole_four_eq_whole_two] at landingFour
  rw [thetaDistributionWhole_eq_primePower_nsmul_quotient
    ThetaDistributionPrimeTwo 1] at landingFour
  have landingFour' := landingFour.symm
  change 4 • thetaDistributionScalePull 2 (by norm_num)
      (thetaDistributionQuotient ThetaDistributionPrimeTwo 2) =
    2 • thetaDistributionQuotient ThetaDistributionPrimeTwo 1 at landingFour'
  rw [← Nat.cast_smul_eq_nsmul ℂ,
    ← Nat.cast_smul_eq_nsmul ℂ] at landingFour'
  have scaled := congrArg
    (fun value : ComplexTempered => (1 / 4 : ℂ) • value) landingFour'
  simp only [smul_smul] at scaled
  calc
    _ = ((1 / 4 : ℂ) * 2) •
        thetaDistributionQuotient ThetaDistributionPrimeTwo 1 := by
      simpa using scaled
    _ = _ := by norm_num

private theorem half_smul_not_mem_zmultiples
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    {point : E} (pointNe : point ≠ 0) :
    (1 / 2 : ℂ) • point ∉ AddSubgroup.zmultiples point := by
  rw [AddSubgroup.mem_zmultiples_iff]
  rintro ⟨multiplicity, equality⟩
  have scalarEquality : (multiplicity : ℂ) = 1 / 2 := by
    apply smul_left_injective ℂ pointNe
    simpa only [Int.cast_smul_eq_zsmul] using equality
  have integerEquation : (2 : ℤ) * multiplicity = 1 := by
    exact_mod_cast
      (show (2 : ℂ) * (multiplicity : ℂ) = 1 by
        rw [scalarEquality]
        norm_num)
  omega

theorem thetaDistributionScalePull_two_quotient_four_not_mem_face_two :
    thetaDistributionScalePull 2 (by norm_num)
        (thetaDistributionQuotient ThetaDistributionPrimeTwo 2) ∉
      ThetaDistributionPrimePowerIntegralFace
        ThetaDistributionPrimeTwo 1 := by
  rw [thetaDistributionScalePull_two_quotient_four_eq_half_quotient_two]
  exact half_smul_not_mem_zmultiples
    thetaDistributionPrimeTwoQuotient_ne_zero

/-- Exact action-escape coordinate for the first candidate cofinal
restriction. -/
theorem thetaDistributionScalePull_two_not_mapsTo_integralFaces :
    ¬ Set.MapsTo
      (thetaDistributionScalePull 2 (by norm_num))
      (ThetaDistributionPrimePowerIntegralFace
        ThetaDistributionPrimeTwo 2 : Set ComplexTempered)
      (ThetaDistributionPrimePowerIntegralFace
        ThetaDistributionPrimeTwo 1 : Set ComplexTempered) := by
  intro mapsTo
  exact thetaDistributionScalePull_two_quotient_four_not_mem_face_two
    (mapsTo (AddSubgroup.mem_zmultiples _))

end
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
