import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.L1
import H0mework.Arithmetic.Mellin.PositiveMellinCarrier
import H0mework.Arithmetic.Mellin.GaussianRemainderMellin
import H0mework.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinRadialDefect

/-!
# Source-owned proper Mellin representation

The full quarter `L²` carrier is deliberately not given a Mellin functional.
For a fixed convergent parameter, the literal Mellin integrand is instead
realized in the proper weighted `L¹` space on `Ioi 0`.  Its Bochner integral is
an honest continuous linear functional.  The generated Gaussian remainder,
the normalized low correction, and both q-rich character readbacks are
specialized from this same source-owned construction.

This is a representation/coface producer.  It does not assert a map to the
quarter `L²` carrier and does not settle the radial defect.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Set
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

abbrev PositiveMellinL1 := ℝ →₁[volume.restrict (Ioi (0 : ℝ))] ℂ

def positiveMellinWeightedFunction (z : ℂ)
    (f : positiveMellinConvergentSubmodule z) : ℝ → ℂ :=
  fun t => (t : ℂ) ^ (z - 1) • positiveMellinExtension f.1 t

theorem positiveMellinWeightedFunction_integrable (z : ℂ)
    (f : positiveMellinConvergentSubmodule z) :
    Integrable (positiveMellinWeightedFunction z f)
      (volume.restrict (Ioi (0 : ℝ))) := by
  exact f.2

def positiveMellinWeightedL1 (z : ℂ)
    (f : positiveMellinConvergentSubmodule z) : PositiveMellinL1 :=
  (positiveMellinWeightedFunction_integrable z f).toL1

theorem positiveMellinWeightedL1_coeFn
    (z : ℂ) (f : positiveMellinConvergentSubmodule z) :
    (positiveMellinWeightedL1 z f : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      positiveMellinWeightedFunction z f := by
  exact (positiveMellinWeightedFunction_integrable z f).coeFn_toL1

def positiveMellinWeightedL1Map (z : ℂ) :
    positiveMellinConvergentSubmodule z →ₗ[ℂ] PositiveMellinL1 where
  toFun := positiveMellinWeightedL1 z
  map_add' f g := by
    apply Lp.ext
    filter_upwards
      [positiveMellinWeightedL1_coeFn z (f + g),
        positiveMellinWeightedL1_coeFn z f,
        positiveMellinWeightedL1_coeFn z g,
        Lp.coeFn_add (positiveMellinWeightedL1 z f)
          (positiveMellinWeightedL1 z g)]
      with t hleft hf hg hright
    change ((positiveMellinWeightedL1 z (f + g) : PositiveMellinL1) :
      ℝ → ℂ) t =
      ((positiveMellinWeightedL1 z f + positiveMellinWeightedL1 z g :
        PositiveMellinL1) : ℝ → ℂ) t
    rw [hleft]
    have hright' :
        ((positiveMellinWeightedL1 z f + positiveMellinWeightedL1 z g :
          PositiveMellinL1) : ℝ → ℂ) t =
          (positiveMellinWeightedL1 z f : ℝ → ℂ) t +
            (positiveMellinWeightedL1 z g : ℝ → ℂ) t := by
      simpa only [Pi.add_apply] using hright
    rw [hright', hf, hg]
    by_cases ht : 0 < t
    · simp [positiveMellinWeightedFunction, positiveMellinExtension,
        ht, smul_eq_mul]
      ring
    · simp [positiveMellinWeightedFunction, positiveMellinExtension,
        ht, smul_eq_mul]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards
      [positiveMellinWeightedL1_coeFn z (c • f),
        positiveMellinWeightedL1_coeFn z f,
        Lp.coeFn_smul c (positiveMellinWeightedL1 z f)]
      with t hleft hf hright
    change ((positiveMellinWeightedL1 z (c • f) : PositiveMellinL1) :
      ℝ → ℂ) t =
      (((RingHom.id ℂ) c • positiveMellinWeightedL1 z f :
        PositiveMellinL1) : ℝ → ℂ) t
    rw [hleft]
    have hright' :
        (((RingHom.id ℂ) c • positiveMellinWeightedL1 z f :
          PositiveMellinL1) : ℝ → ℂ) t =
          (RingHom.id ℂ) c •
            (positiveMellinWeightedL1 z f : ℝ → ℂ) t := by
      simpa only [RingHom.id_apply, Pi.smul_apply] using hright
    rw [hright', hf]
    simp only [RingHom.id_apply]
    by_cases ht : 0 < t
    · simp [positiveMellinWeightedFunction, positiveMellinExtension,
        ht, smul_eq_mul]
      ring
    · simp [positiveMellinWeightedFunction, positiveMellinExtension,
        ht, smul_eq_mul]

def positiveMellinL1Integral : PositiveMellinL1 →L[ℂ] ℂ :=
  L1.integralCLM' ℂ

theorem positiveMellinL1Integral_norm_le (value : PositiveMellinL1) :
    ‖positiveMellinL1Integral value‖ ≤ ‖value‖ := by
  calc
    ‖positiveMellinL1Integral value‖ = ‖L1.integral value‖ := by
      congr 1
      unfold positiveMellinL1Integral
      exact (L1.integral_eq' ℂ value).symm
    _ ≤ ‖value‖ := L1.norm_integral_le value

theorem positiveMellinL1Integral_weighted_eq_mellin
    (z : ℂ) (f : positiveMellinConvergentSubmodule z) :
    positiveMellinL1Integral (positiveMellinWeightedL1 z f) =
      positiveMellinFunctional z f := by
  unfold positiveMellinL1Integral
  rw [← L1.integral_eq' ℂ]
  change L1.integral
      (positiveMellinWeightedFunction_integrable z f).toL1 = _
  rw [← MeasureTheory.integral_eq
    (positiveMellinWeightedFunction z f)
    (positiveMellinWeightedFunction_integrable z f)]
  change (∫ t : ℝ,
      positiveMellinWeightedFunction z f t
        ∂(volume.restrict (Ioi (0 : ℝ)))) =
    ∫ t : ℝ in Ioi (0 : ℝ),
      (t : ℂ) ^ (z - 1) • positiveMellinExtension f.1 t
  rfl

theorem positiveMellinL1Integral_weighted_zero_of_hasMellin_zero
    (z : ℂ) (f : positiveMellinConvergentSubmodule z)
    (zero : positiveMellinFunctional z f = 0) :
    positiveMellinL1Integral (positiveMellinWeightedL1 z f) = 0 := by
  rw [positiveMellinL1Integral_weighted_eq_mellin, zero]

theorem positiveMellinL1Integral_weighted_dilation
    (z : ℂ) (a : ℝ) (positive : 0 < a)
    (f : positiveMellinConvergentSubmodule z) :
    positiveMellinL1Integral
        (positiveMellinWeightedL1 z
          (positiveMellinDilation z a positive f)) =
      (a : ℂ) ^ (-z) •
        positiveMellinL1Integral (positiveMellinWeightedL1 z f) := by
  rw [positiveMellinL1Integral_weighted_eq_mellin,
    positiveMellinL1Integral_weighted_eq_mellin,
    positiveMellinFunctional_dilation]

theorem positiveMellinL1Integral_weighted_tate
    (z : ℂ)
    (f : positiveMellinConvergentSubmodule ((1 / 2 : ℂ) - z)) :
    positiveMellinL1Integral
        (positiveMellinWeightedL1 z
          (positiveMellinTateMap z f)) =
      positiveMellinL1Integral
        (positiveMellinWeightedL1 ((1 / 2 : ℂ) - z) f) := by
  rw [positiveMellinL1Integral_weighted_eq_mellin,
    positiveMellinL1Integral_weighted_eq_mellin,
    positiveMellinFunctional_tateMap]

open QRich

def generatedZeroSelectedMellinL1Element
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PositiveMellinL1 :=
  positiveMellinWeightedL1 (observation.coordinate / 2)
    (selectedPositiveMellinRelation observation nontrivial)

theorem generatedZeroSelectedMellinL1Element_integral_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1Integral
        (generatedZeroSelectedMellinL1Element observation nontrivial) = 0 := by
  unfold generatedZeroSelectedMellinL1Element
  exact positiveMellinL1Integral_weighted_zero_of_hasMellin_zero
    (observation.coordinate / 2)
    (selectedPositiveMellinRelation observation nontrivial)
    (selectedPositiveMellinRelation_annihilated observation nontrivial)

def generatedZeroSelectedNormalizedLowMellinL1Element
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    PositiveMellinL1 :=
  positiveMellinWeightedL1 (observation.coordinate / 2)
    (positiveClozelLowCorrectionElement
      (observation.coordinate / 2)
      (selectedPositiveParameter_re_pos observation nontrivial))

theorem generatedZeroSelectedNormalizedLowMellinL1Element_integral
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1Integral
        (generatedZeroSelectedNormalizedLowMellinL1Element observation nontrivial) =
      1 / (observation.coordinate / 2) := by
  unfold generatedZeroSelectedNormalizedLowMellinL1Element
  rw [positiveMellinL1Integral_weighted_eq_mellin]
  exact positiveMellinFunctional_positiveClozelLowCorrectionElement
    (observation.coordinate / 2)
    (selectedPositiveParameter_re_pos observation nontrivial)

theorem generatedZeroSelectedNormalizedLowMellinL1Element_scaled_integral_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinL1Integral
        ((observation.coordinate / 2 : ℂ) •
          generatedZeroSelectedNormalizedLowMellinL1Element observation nontrivial) = 1 := by
  rw [map_smul,
    generatedZeroSelectedNormalizedLowMellinL1Element_integral]
  have zNe : observation.coordinate / 2 ≠ 0 := by
    exact div_ne_zero
      (GeneratedRiemannZeroObservationAt.coordinate_ne_zero observation)
      (by norm_num)
  simp only [smul_eq_mul]
  field_simp [zNe]
  exact div_self
    (GeneratedRiemannZeroObservationAt.coordinate_ne_zero observation)

theorem generatedZeroSelectedNormalizedLowMellinL1Element_nonzero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedZeroSelectedNormalizedLowMellinL1Element observation nontrivial ≠ 0 := by
  intro zero
  have integralZero := congrArg positiveMellinL1Integral zero
  rw [generatedZeroSelectedNormalizedLowMellinL1Element_integral] at integralZero
  have zNe : observation.coordinate / 2 ≠ 0 := by
    exact div_ne_zero
      (GeneratedRiemannZeroObservationAt.coordinate_ne_zero observation)
      (by norm_num)
  rw [map_zero] at integralZero
  exact (one_div_ne_zero zNe) integralZero

theorem generatedZeroSelectedProperMellinCharacter
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    positiveMellinL1Integral
        (positiveMellinWeightedL1 (observation.coordinate / 2)
          (positiveMellinDilation (observation.coordinate / 2)
            (blockQRichSuccessorScale stage : ℝ) (by
              rw [blockQRichSuccessorScale_eq_stage_add_three]
              positivity)
            ((observation.coordinate / 2 : ℂ) •
              positiveClozelLowCorrectionElement
                (observation.coordinate / 2)
                (selectedPositiveParameter_re_pos observation nontrivial)))) =
      (blockQRichSuccessorScale stage : ℂ) ^
        (-(observation.coordinate / 2)) := by
  let z : ℂ := observation.coordinate / 2
  let q : ℝ := blockQRichSuccessorScale stage
  let positiveQ : 0 < q := by
    dsimp [q]
    rw [blockQRichSuccessorScale_eq_stage_add_three]
    positivity
  let low := positiveClozelLowCorrectionElement z
    (selectedPositiveParameter_re_pos observation nontrivial)
  have hlow : positiveMellinFunctional z low = 1 / z := by
    exact positiveMellinFunctional_positiveClozelLowCorrectionElement z _
  have zNe : z ≠ 0 := by
    dsimp [z]
    exact div_ne_zero
      (GeneratedRiemannZeroObservationAt.coordinate_ne_zero observation)
      (by norm_num)
  calc
    positiveMellinL1Integral
        (positiveMellinWeightedL1 z
          (positiveMellinDilation z q positiveQ (z • low))) =
        positiveMellinFunctional z
          (positiveMellinDilation z q positiveQ (z • low)) :=
      positiveMellinL1Integral_weighted_eq_mellin _ _
    _ = (q : ℂ) ^ (-z) • positiveMellinFunctional z (z • low) :=
      positiveMellinFunctional_dilation z q positiveQ (z • low)
    _ = (q : ℂ) ^ (-z) := by
      rw [map_smul, hlow]
      simp only [smul_eq_mul]
      field_simp [zNe]
    _ = (blockQRichSuccessorScale stage : ℂ) ^
        (-(observation.coordinate / 2)) := by
      rfl

def generatedZeroSelectedProperMellinReadback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℂ :=
  positiveMellinL1Integral
    (positiveMellinWeightedL1 (observation.coordinate / 2)
      (positiveMellinDilation (observation.coordinate / 2)
        (blockQRichSuccessorScale stage : ℝ) (by
          rw [blockQRichSuccessorScale_eq_stage_add_three]
          positivity)
        ((observation.coordinate / 2 : ℂ) •
          positiveClozelLowCorrectionElement
            (observation.coordinate / 2)
            (selectedPositiveParameter_re_pos observation nontrivial))))

theorem generatedZeroSelectedProperMellinReadback_eq_character
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    generatedZeroSelectedProperMellinReadback observation nontrivial stage =
      (blockQRichSuccessorScale stage : ℂ) ^
        (-(observation.coordinate / 2)) := by
  exact generatedZeroSelectedProperMellinCharacter observation nontrivial stage

theorem generatedZeroReversalProperMellinCharacter
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    positiveMellinL1Integral
        (positiveMellinWeightedL1
          (coordinateReversal observation.coordinate / 2)
          (positiveMellinDilation
            (coordinateReversal observation.coordinate / 2)
            (blockQRichSuccessorScale stage : ℝ) (by
              rw [blockQRichSuccessorScale_eq_stage_add_three]
              positivity)
            ((coordinateReversal observation.coordinate / 2 : ℂ) •
              positiveClozelLowCorrectionElement
                (coordinateReversal observation.coordinate / 2)
                (reversalPositiveParameter_re_pos observation nontrivial)))) =
      (blockQRichSuccessorScale stage : ℂ) ^
        (-(coordinateReversal observation.coordinate / 2)) := by
  let z : ℂ := coordinateReversal observation.coordinate / 2
  let q : ℝ := blockQRichSuccessorScale stage
  let positiveQ : 0 < q := by
    dsimp [q]
    rw [blockQRichSuccessorScale_eq_stage_add_three]
    positivity
  have hz : 0 < z.re := by
    dsimp [z]
    exact reversalPositiveParameter_re_pos observation nontrivial
  let low := positiveClozelLowCorrectionElement z hz
  have hlow : positiveMellinFunctional z low = 1 / z := by
    exact positiveMellinFunctional_positiveClozelLowCorrectionElement z _
  have zNe : z ≠ 0 := by
    dsimp [z]
    have hcoord : coordinateReversal observation.coordinate ≠ 0 := by
      intro hzero
      have hreal := congrArg Complex.re hzero
      simp [coordinateReversal] at hreal
      have strip := observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
      linarith
    exact div_ne_zero hcoord (by norm_num)
  calc
    positiveMellinL1Integral
        (positiveMellinWeightedL1 z
          (positiveMellinDilation z q positiveQ (z • low))) =
        positiveMellinFunctional z
          (positiveMellinDilation z q positiveQ (z • low)) :=
      positiveMellinL1Integral_weighted_eq_mellin _ _
    _ = (q : ℂ) ^ (-z) • positiveMellinFunctional z (z • low) :=
      positiveMellinFunctional_dilation z q positiveQ (z • low)
    _ = (q : ℂ) ^ (-z) := by
      rw [map_smul, hlow]
      simp only [smul_eq_mul]
      field_simp [zNe]
    _ = (blockQRichSuccessorScale stage : ℂ) ^
        (-(coordinateReversal observation.coordinate / 2)) := by
      rfl

def generatedZeroReversalProperMellinReadback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℂ :=
  positiveMellinL1Integral
    (positiveMellinWeightedL1
      (coordinateReversal observation.coordinate / 2)
      (positiveMellinDilation
        (coordinateReversal observation.coordinate / 2)
        (blockQRichSuccessorScale stage : ℝ) (by
          rw [blockQRichSuccessorScale_eq_stage_add_three]
          positivity)
        ((coordinateReversal observation.coordinate / 2 : ℂ) •
          positiveClozelLowCorrectionElement
            (coordinateReversal observation.coordinate / 2)
            (reversalPositiveParameter_re_pos observation nontrivial))))

theorem generatedZeroReversalProperMellinReadback_eq_character
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    generatedZeroReversalProperMellinReadback observation nontrivial stage =
      (blockQRichSuccessorScale stage : ℂ) ^
        (-(coordinateReversal observation.coordinate / 2)) := by
  exact generatedZeroReversalProperMellinCharacter observation nontrivial stage

def generatedZeroProperMellinRadialDefect
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) : ℝ :=
  ‖generatedZeroSelectedProperMellinReadback observation nontrivial stage‖ -
    ‖generatedZeroReversalProperMellinReadback observation nontrivial stage‖

theorem generatedZeroProperMellinRadialDefect_eq_existing
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    generatedZeroProperMellinRadialDefect observation nontrivial stage =
      zeroOwnedPositiveMellinRadialDefect observation nontrivial stage := by
  rw [generatedZeroProperMellinRadialDefect,
    generatedZeroSelectedProperMellinReadback_eq_character,
    generatedZeroReversalProperMellinReadback_eq_character,
    zeroOwnedPositiveMellinRadialDefect,
    selectedPositiveMellinDilationReadback_eq_character,
    reversalPositiveMellinDilationReadback_eq_character]

theorem generatedZeroProperMellinRadialDefect_eq_zero_iff
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : Nat) :
    generatedZeroProperMellinRadialDefect observation nontrivial stage = 0 ↔
      observation.coordinate.re = 1 / 2 := by
  rw [generatedZeroProperMellinRadialDefect_eq_existing,
    zeroOwnedPositiveMellinRadialDefect_eq_zero_iff]

end
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
