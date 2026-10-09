import H0mework.Versions.R2.Arithmetic.Mellin.GaussianRemainderMellin
import H0mework.Versions.R2.Arithmetic.SonineCoupling.ConjugateTateMuntzRelationNaturality

/-!
# Source-generated modified WeakFE unit detector

At a nontrivial generated zero `z`, the actual theta/WeakFE modified kernel
has Mellin value equal to its two canonical pole terms.  Multiplication by
`2*z*(1/2-z)` therefore generates a Mellin-unit detector directly from the
source kernel.  Reality, self-duality and the conjugated normalization make
its selected and reversal faces exactly conjugate--Tate partners.

No normalized low probe, criticality, endpoint equality or radial statement
is an input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann

open Complex
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelGeneralizedDual

noncomputable section

def sourceModifiedUnitCoefficient (z : ℂ) : ℂ :=
  2 * z * ((1 / 2 : ℂ) - z)

def sourceModifiedUnitDetector (owner : GlobalGermOwner) (z : ℂ) :
    ℝ → ℂ :=
  fun t => sourceModifiedUnitCoefficient z *
    (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t

theorem sourceModifiedUnitDetector_hasMellin_one_of_lambda_zero
    (owner : GlobalGermOwner) (z : ℂ)
    (zNe : z ≠ 0) (halfSubNe : (1 / 2 : ℂ) - z ≠ 0)
    (lambdaZero :
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ z = 0) :
    HasMellin (sourceModifiedUnitDetector owner z) z 1 := by
  let P := GeneratedRiemannWeakFEPairAt.generate owner
  have lambdaZeroCorrected : P.pair.Λ₀ z =
      1 / z + 1 / ((1 / 2 : ℂ) - z) := by
    rw [WeakFEPair.Λ₀_eq, lambdaZero]
    simp [P, GeneratedRiemannWeakFEPairAt.generate,
      HurwitzZeta.hurwitzEvenFEPair]
  have convergent : MellinConvergent P.pair.f_modif z :=
    (P.pair.isStrongFEPair_toStrongFEPair.hasMellin z).1
  change HasMellin
      (fun t => sourceModifiedUnitCoefficient z * P.pair.f_modif t)
      z 1
  constructor
  · change MellinConvergent
      (fun t => sourceModifiedUnitCoefficient z • P.pair.f_modif t) z
    exact convergent.const_smul (sourceModifiedUnitCoefficient z)
  · have scaled := (hasMellin_const_smul convergent
      (sourceModifiedUnitCoefficient z)).2
    change mellin
      (fun t => sourceModifiedUnitCoefficient z • P.pair.f_modif t) z = 1
    rw [scaled]
    change sourceModifiedUnitCoefficient z * P.pair.Λ₀ z = 1
    rw [lambdaZeroCorrected]
    unfold sourceModifiedUnitCoefficient
    have scaledHalfNe : 1 - 2 * z ≠ 0 := by
      intro equality
      apply halfSubNe
      have productZero :
          (2 : ℂ) * ((1 / 2 : ℂ) - z) = 0 := by
        calc
          (2 : ℂ) * ((1 / 2 : ℂ) - z) = 1 - 2 * z := by ring
          _ = 0 := equality
      exact (mul_eq_zero.mp productZero).resolve_left (by norm_num)
    field_simp [zNe, halfSubNe, scaledHalfNe]
    ring

theorem generatedZero_sourceModifiedUnitDetector_hasMellin_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HasMellin (sourceModifiedUnitDetector owner (observation.coordinate / 2))
      (observation.coordinate / 2) 1 := by
  have strip := observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  apply sourceModifiedUnitDetector_hasMellin_one_of_lambda_zero
  · intro equality
    have realZero := congrArg Complex.re equality
    rw [div_ofNat_re] at realZero
    norm_num at realZero
    linarith
  · intro equality
    have realZero := congrArg Complex.re equality
    norm_num [Complex.div_re] at realZero
    linarith
  · rw [generatedThetaMellin_eq_two_mul_completed,
      observation.completed_eq_zero_of_nontrivial nontrivial, mul_zero]

theorem generatedZero_reversalSourceModifiedUnitDetector_hasMellin_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    let reversal := coordinateReversal observation.coordinate / 2
    HasMellin (sourceModifiedUnitDetector owner reversal) reversal 1 := by
  dsimp only
  have strip := observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  apply sourceModifiedUnitDetector_hasMellin_one_of_lambda_zero
  · intro equality
    have realZero := congrArg Complex.re equality
    rw [div_ofNat_re] at realZero
    simp [coordinateReversal] at realZero
    linarith
  · intro equality
    have realZero := congrArg Complex.re equality
    norm_num [Complex.div_re] at realZero
    simp [coordinateReversal] at realZero
    linarith
  · rw [generatedThetaMellin_eq_two_mul_completed,
      observation.completed_reversal_eq_zero_of_nontrivial nontrivial,
      mul_zero]

theorem sourceModifiedUnitCoefficient_conjugateTate (z : ℂ) :
    star (sourceModifiedUnitCoefficient z) =
      sourceModifiedUnitCoefficient ((1 / 2 : ℂ) - star z) := by
  simp [sourceModifiedUnitCoefficient]
  ring

theorem generatedRiemannModifiedKernel_star
    (owner : GlobalGermOwner) (t : ℝ) :
    star ((GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t) =
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t := by
  rw [GeneratedRiemannWeakFEPairAt.generate_pair]
  unfold WeakFEPair.f_modif
  simp only [Pi.add_apply]
  by_cases high : t ∈ Set.Ioi (1 : ℝ)
  · have lowNot : t ∉ Set.Ioo (0 : ℝ) 1 := by
      intro low
      exact (not_lt_of_ge high.le) low.2
    rw [Set.indicator_of_mem high, Set.indicator_of_notMem lowNot]
    simp [HurwitzZeta.hurwitzEvenFEPair]
  · rw [Set.indicator_of_notMem high]
    by_cases low : t ∈ Set.Ioo (0 : ℝ) 1
    · rw [Set.indicator_of_mem low]
      simp [HurwitzZeta.hurwitzEvenFEPair]
    · rw [Set.indicator_of_notMem low]
      simp

theorem generatedRiemannModifiedKernel_tate
    (owner : GlobalGermOwner) (t : PositiveMellinReal) :
    (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
        (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1⁻¹ =
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1 := by
  let P := GeneratedRiemannWeakFEPairAt.generate owner
  change (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) * P.pair.f_modif t.1⁻¹ =
    P.pair.f_modif t.1
  have functional := P.pair.hf_modif_FE t.1 t.2
  rw [one_div] at functional
  have modifiedSymm : P.pair.g_modif t.1 = P.pair.f_modif t.1 := by
    change P.pair.symm.f_modif t.1 = P.pair.f_modif t.1
    rw [show P.pair.symm = P.pair by
      exact GeneratedRiemannWeakFEPairAt.generate_selfDual owner]
  rw [modifiedSymm] at functional
  have functional' :
      P.pair.f_modif t.1⁻¹ =
        ((t.1 : ℂ) ^ (1 / 2 : ℂ)) * P.pair.f_modif t.1 := by
    have castPower :
        ((t.1 ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
          (t.1 : ℂ) ^ (1 / 2 : ℂ) := by
      convert Complex.ofReal_cpow t.2.le (1 / 2 : ℝ) using 1
      all_goals norm_num
    rw [show P.pair.ε = 1 by rfl, show P.pair.k = (1 / 2 : ℝ) by rfl]
      at functional
    simp only [one_mul, smul_eq_mul] at functional
    change P.pair.f_modif t.1⁻¹ =
      ((t.1 ^ (1 / 2 : ℝ) : ℝ) : ℂ) * P.pair.f_modif t.1
      at functional
    rw [castPower] at functional
    exact functional
  rw [functional', ← mul_assoc, Complex.cpow_neg]
  rw [inv_mul_cancel₀]
  · simp
  · exact Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr t.2.ne'))

def positiveSourceModifiedUnitDetector
    (owner : GlobalGermOwner) (z : ℂ) : ClozelPositiveMellinFunction :=
  fun t => sourceModifiedUnitDetector owner z t.1

theorem positiveSourceModifiedUnitDetector_conjugateTate
    (owner : GlobalGermOwner) (z : ℂ) :
    positiveTateInvolution
        (positiveMellinPointwiseConjugation
          (positiveSourceModifiedUnitDetector owner z)) =
      positiveSourceModifiedUnitDetector owner
        ((1 / 2 : ℂ) - star z) := by
  funext t
  change (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      star (sourceModifiedUnitCoefficient z *
        (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1⁻¹) =
    sourceModifiedUnitCoefficient ((1 / 2 : ℂ) - star z) *
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1
  rw [star_mul, generatedRiemannModifiedKernel_star,
    sourceModifiedUnitCoefficient_conjugateTate]
  let coefficient := sourceModifiedUnitCoefficient ((1 / 2 : ℂ) - star z)
  change (t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
      ((GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1⁻¹ *
        coefficient) =
    coefficient *
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1
  calc
    _ = coefficient * ((t.1 : ℂ) ^ (-(1 / 2 : ℂ)) *
        (GeneratedRiemannWeakFEPairAt.generate owner).pair.f_modif t.1⁻¹) := by
      ring
    _ = _ := by rw [generatedRiemannModifiedKernel_tate]

def selectedSourceModifiedUnitElement
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule (observation.coordinate / 2) :=
  restrictPositiveMellin (observation.coordinate / 2)
    ⟨sourceModifiedUnitDetector owner (observation.coordinate / 2),
      (generatedZero_sourceModifiedUnitDetector_hasMellin_one
        observation nontrivial).1⟩

def reversalSourceModifiedUnitElement
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinConvergentSubmodule
      (coordinateReversal observation.coordinate / 2) :=
  restrictPositiveMellin (coordinateReversal observation.coordinate / 2)
    ⟨sourceModifiedUnitDetector owner
        (coordinateReversal observation.coordinate / 2),
      (generatedZero_reversalSourceModifiedUnitDetector_hasMellin_one
        observation nontrivial).1⟩

theorem selectedSourceModifiedUnitElement_functional_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinFunctional (observation.coordinate / 2)
      (selectedSourceModifiedUnitElement observation nontrivial) = 1 := by
  rw [selectedSourceModifiedUnitElement,
    positiveMellinFunctional_restrictPositive]
  exact (generatedZero_sourceModifiedUnitDetector_hasMellin_one
    observation nontrivial).2

theorem reversalSourceModifiedUnitElement_functional_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    positiveMellinFunctional
        (coordinateReversal observation.coordinate / 2)
        (reversalSourceModifiedUnitElement observation nontrivial) = 1 := by
  rw [reversalSourceModifiedUnitElement,
    positiveMellinFunctional_restrictPositive]
  exact (generatedZero_reversalSourceModifiedUnitDetector_hasMellin_one
    observation nontrivial).2

end
end NoIslandNoMagic.CanonicalRiemann
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
