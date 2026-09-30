import H0mework.Versions.Y.Arithmetic.Mellin.GaussianRemainderKernel
import H0mework.Versions.Y.Arithmetic.RiemannSource.NontrivialCompletedZero

/-!
# Complementary-strip Mellin incidence for the Clozel remainder kernel

The two canonical pole corrections turn Mathlib's entire modified FE kernel
back into the meromorphic weak-FE value.  Hence on `0 < re z < 1/2` the
source-generated Gaussian remainder has Mellin transform exactly `Λ z`.
An owner-indexed nontrivial generated zero then kills this transform on the
selected and reversal branches separately.

No centered parameter, odd coefficient, q-rich point, or separator conclusion
is stored in this module.
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
open CanonicalUnitArithmeticFactorizationGlobalDeterminantCoordinateRealization

noncomputable section

theorem generatedClozelGaussianRemainderKernel_hasMellin
    (owner : GlobalGermOwner) {z : ℂ}
    (positive : 0 < z.re) (belowHalf : z.re < (1 / 2 : ℝ)) :
    HasMellin (generatedClozelGaussianRemainderKernel owner) z
      ((GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ z) := by
  let P := (GeneratedRiemannWeakFEPairAt.generate owner).pair
  have modifiedConvergent : MellinConvergent P.f_modif z := by
    exact (P.isStrongFEPair_toStrongFEPair.hasMellin z).1
  have modifiedMellin : mellin P.f_modif z = P.Λ₀ z := rfl
  have low := hasMellin_clozelLowCorrection positive
  have high := hasMellin_clozelHighCorrection belowHalf
  have first := hasMellin_sub modifiedConvergent low.1
  have combined := hasMellin_sub first.1 high.1
  have modifiedTarget :
      HasMellin (generatedClozelModifiedMinusCorrections owner) z
        (P.Λ z) := by
    constructor
    · exact combined.1
    · change mellin
        (fun t => P.f_modif t - clozelLowCorrection t -
          clozelHighCorrection t) z = P.Λ z
      calc
        _ = mellin
              (fun t => P.f_modif t - clozelLowCorrection t) z -
            mellin clozelHighCorrection z := combined.2
        _ = mellin P.f_modif z - mellin clozelLowCorrection z -
              mellin clozelHighCorrection z := by rw [first.2]
        _ = P.Λ₀ z - 1 / z - 1 / ((1 / 2 : ℂ) - z) := by
          rw [modifiedMellin, low.2, high.2]
        _ = P.Λ z := by
          unfold WeakFEPair.Λ
          simp [P, HurwitzZeta.hurwitzEvenFEPair, smul_eq_mul]
  have aeEquality :=
    generatedClozelGaussianRemainderKernel_ae_eq_modified owner
  constructor
  · unfold MellinConvergent at modifiedTarget ⊢
    exact modifiedTarget.1.congr <|
      aeEquality.symm.mono fun t equality => by
        simpa only using congrArg
          (fun value : ℂ => (t : ℂ) ^ (z - 1) • value) equality
  · unfold mellin
    rw [integral_congr_ae <|
      aeEquality.mono fun t equality => by rw [equality]]
    exact modifiedTarget.2

theorem generatedZero_clozelGaussianRemainderKernel_hasMellin_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HasMellin (generatedClozelGaussianRemainderKernel owner)
      (observation.coordinate / 2) 0 := by
  have strip :=
    observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  have positiveHalf : 0 < (observation.coordinate / 2).re := by
    rw [div_ofNat_re]
    linarith
  have belowHalf :
      (observation.coordinate / 2).re < (1 / 2 : ℝ) := by
    rw [div_ofNat_re]
    linarith
  have incidence := generatedClozelGaussianRemainderKernel_hasMellin
    owner positiveHalf belowHalf
  have valueZero :
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ
          (observation.coordinate / 2) = 0 := by
    rw [generatedThetaMellin_eq_two_mul_completed,
      observation.completed_eq_zero_of_nontrivial nontrivial, mul_zero]
  rw [valueZero] at incidence
  exact incidence

theorem generatedZero_reversalClozelGaussianRemainderKernel_hasMellin_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    HasMellin (generatedClozelGaussianRemainderKernel owner)
      (coordinateReversal observation.coordinate / 2) 0 := by
  have strip :=
    observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial
  have reversedReal :
      (coordinateReversal observation.coordinate).re =
        1 - observation.coordinate.re := by
    simp [coordinateReversal]
  have positiveHalf :
      0 < (coordinateReversal observation.coordinate / 2).re := by
    rw [div_ofNat_re, reversedReal]
    linarith
  have belowHalf :
      (coordinateReversal observation.coordinate / 2).re <
        (1 / 2 : ℝ) := by
    rw [div_ofNat_re, reversedReal]
    linarith
  have incidence := generatedClozelGaussianRemainderKernel_hasMellin
    owner positiveHalf belowHalf
  have valueZero :
      (GeneratedRiemannWeakFEPairAt.generate owner).pair.Λ
          (coordinateReversal observation.coordinate / 2) = 0 := by
    rw [generatedThetaMellin_eq_two_mul_completed,
      observation.completed_reversal_eq_zero_of_nontrivial nontrivial,
      mul_zero]
  rw [valueZero] at incidence
  exact incidence

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
