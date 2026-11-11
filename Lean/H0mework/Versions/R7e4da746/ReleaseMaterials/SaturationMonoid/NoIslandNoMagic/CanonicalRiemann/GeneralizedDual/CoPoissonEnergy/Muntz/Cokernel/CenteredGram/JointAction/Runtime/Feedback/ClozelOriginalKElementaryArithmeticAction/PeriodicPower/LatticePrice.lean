import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Lattice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Sampling

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.LatticePrice
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszFinitePairing
open OriginalKElementaryArithmeticAction.PeriodicPower.Sampling OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
open scoped Topology InnerProductSpace
open private shifted_quarter_supported from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Sampling
local notation "Hq" => BurnolQuarterIntervalL2
local notation "b" => burnolRieszSingleFourierSource
local notation "E" => burnolQuarterZeroExtension
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2

def shiftedBSample (c : BurnolCompletedMellinCoordinate) (h : ℝ) (n : ℕ) : ℂ :=
  (Real.exp (h/2):ℂ)*bSample c (Real.exp h*(n+1))

private theorem positive_index_injective : Function.Injective (fun n:ℕ=>(n+1:ℤ)) := by
  intro a b same
  exact_mod_cast (add_right_cancel same)

private theorem actual_B_square (c : BurnolCompletedMellinCoordinate) :
    Summable (fun n:ℕ=>star (bSample c (n+1))*bSample c (n+1)) := by
  simpa only [Function.comp_def,bSample,originalFourierSample,Int.cast_add,Int.cast_natCast,Int.cast_one] using
    (actual_original_lattice_self c).summable.comp_injective positive_index_injective

private theorem actual_shifted_B_square (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (bounded : h≤Real.log 2) :
    Summable (fun n:ℕ=>star (shiftedBSample c h n)*shiftedBSample c h n) := by
  have supported := shifted_quarter_supported (b c:Hq) h bounded
  have whole := (actual_supported_sampling (D (-h) (E (b c:Hq)))
    (D (-h) (E (b c:Hq))) supported supported).summable
  have source := whole.comp_injective positive_index_injective
  simpa only [Function.comp_def,fourierSample,actual_dilation_fourier_point,actual_extension_fourier_point,
    shiftedBSample,bSample,originalFourierSample,Int.cast_add,Int.cast_natCast,Int.cast_one] using source

private theorem cross_summable (f g : ℕ→ℂ)
    (left : Summable (fun n=>star (f n)*f n))
    (right : Summable (fun n=>star (g n)*g n)) : Summable (fun n=>star (f n)*g n) := by
  apply Summable.of_norm_bounded ((left.norm.add right.norm).div_const 2)
  intro n
  simp only [norm_mul,norm_star]
  nlinarith [sq_nonneg (‖f n‖-‖g n‖)]

def powerBPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∑' n:ℕ,star (powerSample c n)*shiftedBSample c h n

def bPowerPrice (c : BurnolCompletedMellinCoordinate) : ℂ :=
  ∑' n:ℕ,star (bSample c (n+1))*powerSample c n

theorem actual_B_positive_lattice_pair (c : BurnolCompletedMellinCoordinate)
    (h : ℝ) (bounded : h≤Real.log 2) :
    HasSum (fun n:ℕ=>star (bSample c (n+1))*shiftedBSample c h n)
      ((1/2:ℂ)*inner ℂ (F (E (b c:Hq))) (D h (F (E (b c:Hq))))) := by
  let pair : ℤ→ℂ := fun n=>star (originalFourierSample c n)*
    ((Real.exp (h/2):ℂ)*originalFourierSample c (Real.exp h*n))
  have whole := actual_original_lattice_pair c c h bounded
  change HasSum pair _ at whole
  have even : pair.Even := by
    intro n
    dsimp only [pair,originalFourierSample]
    rw [Int.cast_neg,source_fourier_even,show Real.exp h * -(n:ℝ)= -(Real.exp h*n) by ring,
      source_fourier_even]
  have zero : pair 0=0 := by simp only [pair,Int.cast_zero,actual_original_origin,star_zero,zero_mul]
  have price := tsum_int_eq_zero_add_two_mul_tsum_pnat even whole.summable
  rw [zero,zero_add,whole.tsum_eq] at price
  have reindex : (∑' n:ℕ+,pair (n:ℤ))=(∑' n:ℕ,pair (n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ (f:=fun n:ℕ=>pair (n:ℤ)))
  rw [reindex,two_nsmul] at price
  have series := whole.summable.comp_injective positive_index_injective
  have paid : (∑' n:ℕ,pair (n+1))=
      (1/2:ℂ)*inner ℂ (F (E (b c:Hq))) (D h (F (E (b c:Hq)))) := by
    rw [price]
    ring
  have sum := series.hasSum
  change HasSum (fun n:ℕ=>pair (n+1)) (∑' n:ℕ,pair (n+1)) at sum
  rw [paid] at sum
  simpa only [pair,originalFourierSample,bSample,shiftedBSample,
    Int.cast_add,Int.cast_natCast,Int.cast_one] using sum

/-- The actual sampled K current retains both power/B cross prices and consumes the complete B sampling law. -/
theorem actual_original_K_lattice_price (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (lower : -Real.log 2≤h) (upper : h≤Real.log 2) :
    HasSum (fun n:ℕ=>star (burnolRieszStateRaw c (n+1))*burnolRieszDilationRaw c h (n+1))
      (fullMellinTranslationCharacter (star c.value) h*((1/4:ℂ)*riemannZeta (c.value+star c.value))-
        powerBPrice c h-fullMellinTranslationCharacter (star c.value) h*bPowerPrice c+
        (1/2:ℂ)*inner ℂ (F (E (b c:Hq))) (D h (F (E (b c:Hq))))) := by
  have power := actual_power_lattice_price c
  have pb := cross_summable (powerSample c) (shiftedBSample c h) power.summable
    (actual_shifted_B_square c h upper)
  have bp := cross_summable (fun n:ℕ=>bSample c (n+1)) (powerSample c)
    (actual_B_square c) power.summable
  have paired := actual_B_positive_lattice_pair c h upper
  have sum := (((power.mul_left (fullMellinTranslationCharacter (star c.value) h)).sub pb.hasSum).sub
    (bp.hasSum.mul_left (fullMellinTranslationCharacter (star c.value) h))).add paired
  apply sum.congr_fun
  intro n
  rw [actual_original_lattice_value,actual_original_shifted_lattice_value c h lower]
  simp only [star_sub]
  unfold shiftedBSample
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.LatticePrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
