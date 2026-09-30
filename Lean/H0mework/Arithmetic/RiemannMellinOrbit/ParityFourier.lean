import Mathlib.Analysis.Fourier.ZMod
import H0mework.Arithmetic.RiemannMellinOrbit.ParitySeparator

/-!
# Clozel parity as the two-point Fourier transform

The existing integral Hadamard analysis is Mathlib's unnormalised DFT on
`ZMod 2`; its odd frequency is the existing Clozel cross coefficient.
No inverse DFT or scalar `1 / 2` is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open scoped ZMod

noncomputable section

abbrev ZModTwoIndex := ZMod 2
abbrev ZModTwoCarrier := ZModTwoIndex → ℂ

/-- Reindex the two J coordinates by the canonical `Fin 2 ≃ ZMod 2`. -/
noncomputable def clozelJPairToZModTwo :
    ClozelJPair ≃ₗ[ℂ] ZModTwoCarrier :=
  (LinearEquiv.finTwoArrow ℂ ℂ).symm ≪≫ₗ
    LinearEquiv.piCongrLeft ℂ (fun _ : ZModTwoIndex => ℂ)
      (ZMod.finEquiv 2).toEquiv

@[simp] theorem clozelJPairToZModTwo_zero (value : ClozelJPair) :
    clozelJPairToZModTwo value 0 = value.1 :=
  rfl

@[simp] theorem clozelJPairToZModTwo_one (value : ClozelJPair) :
    clozelJPairToZModTwo value 1 = value.2 :=
  rfl

theorem sum_zmodTwo (family : ZModTwoCarrier) :
    (∑ index : ZModTwoIndex, family index) = family 0 + family 1 := by
  calc
    (∑ index : ZModTwoIndex, family index) =
        ∑ index : Fin 2, family (ZMod.finEquiv 2 index) := by
      exact Fintype.sum_equiv
        (ZMod.finEquiv 2).toEquiv.symm _ _ (fun index => by simp)
    _ = family 0 + family 1 := by
      rw [Fin.sum_univ_two]
      rfl

theorem stdAddChar_zmodTwo_one :
    ZMod.stdAddChar (1 : ZModTwoIndex) = -1 := by
  change ZMod.stdAddChar ((1 : ℤ) : ZMod 2) = -1
  rw [ZMod.stdAddChar_coe]
  norm_num
  have argument :
      2 * (Real.pi : ℂ) * Complex.I / 2 =
        (Real.pi : ℂ) * Complex.I := by
    ring
  rw [argument, Complex.exp_pi_mul_I]

/-- The production parity map is exactly the unnormalised two-point DFT. -/
theorem clozelJParityAnalysis_eq_zmodTwo_dft (value : ClozelJPair) :
    clozelJPairToZModTwo (clozelJParityAnalysis value) =
      ZMod.dft (clozelJPairToZModTwo value) := by
  funext index
  obtain ⟨finIndex, rfl⟩ := (ZMod.finEquiv 2).surjective index
  fin_cases finIndex
  · change clozelJPairToZModTwo
        (clozelJParityAnalysis value) (0 : ZModTwoIndex) =
      ZMod.dft (clozelJPairToZModTwo value) 0
    rw [ZMod.dft_apply_zero, sum_zmodTwo]
    rfl
  · change clozelJPairToZModTwo
        (clozelJParityAnalysis value) (1 : ZModTwoIndex) =
      ZMod.dft (clozelJPairToZModTwo value) 1
    rw [ZMod.dft_apply, sum_zmodTwo]
    change value.1 - value.2 =
      ZMod.stdAddChar (0 : ZModTwoIndex) * value.1 +
        ZMod.stdAddChar (-(1 : ZModTwoIndex)) * value.2
    rw [AddChar.map_zero_eq_one,
      show (-(1 : ZModTwoIndex)) = 1 by decide,
      stdAddChar_zmodTwo_one]
    ring

/-- The centered selected/reversal pair has odd frequency equal to the
source-owned cross coefficient. -/
theorem clozelCenteredPair_dft_odd (s : ℂ) :
    ZMod.dft
        (clozelJPairToZModTwo
          (clozelCenteredParameter s,
            clozelReversedCenteredParameter s)) 1 =
      clozelJCrossCoefficient s := by
  rw [← clozelJParityAnalysis_eq_zmodTwo_dft]
  rfl

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
