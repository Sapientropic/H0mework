import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.LatticePrice

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Source
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszFinitePairing OriginalPaPhysicalGreen
open OriginalKElementaryArithmeticAction.PeriodicPower.Sampling OriginalKElementaryArithmeticAction.PeriodicPower.Lattice
open OriginalKElementaryArithmeticAction.PeriodicPower.LatticePrice
open scoped Topology ENNReal InnerProductSpace
open private circleRaw circle_mem circleValue circle_coefficient interval_fourier_sample
  quarter_supported shifted_quarter_supported from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Sampling
local notation "Hq" => BurnolQuarterIntervalL2
local notation "b" => burnolRieszSingleFourierSource
local notation "E" => burnolQuarterZeroExtension
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local instance periodPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩

def powerCoefficient (c : BurnolCompletedMellinCoordinate) (n : ℤ) : ℂ :=
  if n=0 then 0 else powerSample c (n.natAbs-1)

theorem powerCoefficient_zero (c : BurnolCompletedMellinCoordinate) :
    powerCoefficient c 0=0 := by simp [powerCoefficient]

theorem powerCoefficient_even (c : BurnolCompletedMellinCoordinate) :
    (powerCoefficient c).Even := by
  intro n
  simp only [powerCoefficient,neg_eq_zero,Int.natAbs_neg]

theorem powerCoefficient_positive (c : BurnolCompletedMellinCoordinate) (n : ℕ) :
    powerCoefficient c (n+1)=powerSample c n := by
  have nonzero : (n:ℤ)+1≠0 := by omega
  have absolute : ((n:ℤ)+1).natAbs=n+1 := by omega
  rw [powerCoefficient,if_neg nonzero,absolute,Nat.add_sub_cancel]

private theorem power_mem (c : BurnolCompletedMellinCoordinate) :
    Memℓp (powerCoefficient c) 2 := by
  have squares : Summable (fun n:ℕ=>‖powerSample c n‖^2) := by
    simpa only [norm_mul,norm_star,pow_two] using (actual_power_lattice_price c).summable.norm
  have positive : Summable (fun n:ℕ=>‖powerCoefficient c n‖^2) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [Nat.cast_add,Nat.cast_one,powerCoefficient_positive] using squares
  have whole : Summable (fun n:ℤ=>‖powerCoefficient c n‖^2) := by
    rw [summable_int_iff_summable_nat_and_neg]
    exact ⟨positive,by simpa only [powerCoefficient,neg_eq_zero,Int.natAbs_neg] using positive⟩
  apply memℓp_gen
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using whole

def powerSequence (c : BurnolCompletedMellinCoordinate) : lp (fun _ : ℤ=>ℂ) 2 :=
  ⟨powerCoefficient c,power_mem c⟩

/-- The same original power samples generate a period-one Hilbert source in the actual strip. -/
def periodicPower (c : BurnolCompletedMellinCoordinate) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T:=(1:ℝ))) :=
  _root_.fourierBasis.repr.symm (powerSequence c)

theorem actual_periodic_coefficient (c : BurnolCompletedMellinCoordinate) (n : ℤ) :
    _root_.fourierBasis.repr (periodicPower c) n=powerCoefficient c n := by
  simp only [periodicPower,LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem actual_periodic_pair (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (support : originalPhysicalCutoff (1/2) value=value) :
    HasSum (fun n:ℤ=>star (powerCoefficient c n)*fourierSample value n)
      (inner ℂ (periodicPower c) (circleValue value)) := by
  have source:=lp.hasSum_inner (𝕜:=ℂ) (_root_.fourierBasis.repr (periodicPower c))
    (_root_.fourierBasis.repr (circleValue value))
  rw [_root_.fourierBasis.repr.inner_map_map] at source
  apply source.congr_fun
  intro n
  rw [actual_periodic_coefficient,circle_coefficient,interval_fourier_sample value support]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

theorem actual_periodic_reverse_pair (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (support : originalPhysicalCutoff (1/2) value=value) :
    HasSum (fun n:ℤ=>star (fourierSample value n)*powerCoefficient c n)
      (inner ℂ (circleValue value) (periodicPower c)) := by
  have source:=lp.hasSum_inner (𝕜:=ℂ) (_root_.fourierBasis.repr (circleValue value))
    (_root_.fourierBasis.repr (periodicPower c))
  rw [_root_.fourierBasis.repr.inner_map_map] at source
  apply source.congr_fun
  intro n
  rw [actual_periodic_coefficient,circle_coefficient,interval_fourier_sample value support]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

private theorem even_positive_price (pair : ℤ→ℂ) (even : pair.Even) (zero : pair 0=0)
    (summable : Summable pair) :
    (∑' n:ℕ,pair (n+1))=(1/2:ℂ)*(∑' n:ℤ,pair n) := by
  have price:=tsum_int_eq_zero_add_two_mul_tsum_pnat even summable
  rw [zero,zero_add] at price
  have reindex : (∑' n:ℕ+,pair (n:ℤ))=(∑' n:ℕ,pair (n+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ (f:=fun n:ℕ=>pair (n:ℤ)))
  rw [reindex,two_nsmul] at price
  rw [price]
  ring

/-- The V77 power/B cross reads the actual compact source after the opposite dilation clock. -/
theorem actual_power_B_contact (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (bounded : h≤Real.log 2) :
    powerBPrice c h=(1/2:ℂ)*inner ℂ (periodicPower c) (circleValue (D (-h) (E (b c:Hq)))) := by
  let pair : ℤ→ℂ := fun n=>star (powerCoefficient c n)*fourierSample (D (-h) (E (b c:Hq))) n
  have whole:=actual_periodic_pair c (D (-h) (E (b c:Hq)))
    (shifted_quarter_supported _ h bounded)
  change HasSum pair _ at whole
  have even : pair.Even := by
    intro n
    dsimp only [pair]
    rw [powerCoefficient_even]
    simp only [fourierSample,actual_dilation_fourier_point,actual_extension_fourier_point,
      originalFourierSample,Int.cast_neg]
    rw [show Real.exp h * -(n:ℝ)= -(Real.exp h*n) by ring,source_fourier_even]
  have zero : pair 0=0 := by simp only [pair,powerCoefficient_zero,star_zero,zero_mul]
  have price:=even_positive_price pair even zero whole.summable
  rw [whole.tsum_eq] at price
  simpa only [pair,powerBPrice,powerCoefficient_positive,fourierSample,
    actual_dilation_fourier_point,actual_extension_fourier_point,originalFourierSample,
    bSample,shiftedBSample,Int.cast_add,Int.cast_natCast,Int.cast_one] using price

theorem actual_B_power_contact (c : BurnolCompletedMellinCoordinate) :
    bPowerPrice c=(1/2:ℂ)*inner ℂ (circleValue (E (b c:Hq))) (periodicPower c) := by
  let pair : ℤ→ℂ := fun n=>star (fourierSample (E (b c:Hq)) n)*powerCoefficient c n
  have whole:=actual_periodic_reverse_pair c (E (b c:Hq)) (quarter_supported _)
  change HasSum pair _ at whole
  have even : pair.Even := by
    intro n
    dsimp only [pair]
    rw [powerCoefficient_even]
    simp only [fourierSample,actual_extension_fourier_point,originalFourierSample,
      Int.cast_neg,source_fourier_even]
  have zero : pair 0=0 := by simp only [pair,powerCoefficient_zero,mul_zero]
  have price:=even_positive_price pair even zero whole.summable
  rw [whole.tsum_eq] at price
  simpa only [pair,bPowerPrice,powerCoefficient_positive,fourierSample,
    actual_extension_fourier_point,originalFourierSample,bSample,
    Int.cast_add,Int.cast_natCast,Int.cast_one] using price

theorem actual_power_B_integral (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (bounded : h≤Real.log 2) :
    powerBPrice c h=(1/2:ℂ)*∫x:AddCircle (1:ℝ),
      star (periodicPower c x)*circleRaw (D (-h) (E (b c:Hq))) x ∂AddCircle.haarAddCircle := by
  rw [actual_power_B_contact c h bounded,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [(circle_mem (D (-h) (E (b c:Hq)))).coeFn_toLp] with x source
  rw [RCLike.inner_apply,starRingEnd_apply]
  change circleValue (D (-h) (E (b c:Hq))) x*star (periodicPower c x)=_
  rw [show circleValue (D (-h) (E (b c:Hq))) x=circleRaw (D (-h) (E (b c:Hq))) x from source]
  ring

theorem actual_B_power_integral (c : BurnolCompletedMellinCoordinate) :
    bPowerPrice c=(1/2:ℂ)*∫x:AddCircle (1:ℝ),
      star (circleRaw (E (b c:Hq)) x)*periodicPower c x ∂AddCircle.haarAddCircle := by
  rw [actual_B_power_contact,L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [(circle_mem (E (b c:Hq))).coeFn_toLp] with x source
  rw [RCLike.inner_apply,starRingEnd_apply]
  change periodicPower c x*star (circleValue (E (b c:Hq)) x)=_
  rw [show circleValue (E (b c:Hq)) x=circleRaw (E (b c:Hq)) x from source]
  ring

/-- Both crosses enter the original K lattice law through this same generated periodic power. -/
theorem actual_original_K_periodic_price (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (lower : -Real.log 2≤h) (upper : h≤Real.log 2) :
    HasSum (fun n:ℕ=>star (burnolRieszStateRaw c (n+1))*burnolRieszDilationRaw c h (n+1))
      (fullMellinTranslationCharacter (star c.value) h*((1/4:ℂ)*riemannZeta (c.value+star c.value))-
        (1/2:ℂ)*inner ℂ (periodicPower c) (circleValue (D (-h) (E (b c:Hq))))-
        fullMellinTranslationCharacter (star c.value) h*((1/2:ℂ)*inner ℂ (circleValue (E (b c:Hq))) (periodicPower c))+
        (1/2:ℂ)*inner ℂ (F (E (b c:Hq))) (D h (F (E (b c:Hq))))) := by
  simpa only [actual_power_B_contact c h upper,actual_B_power_contact] using
    actual_original_K_lattice_price c h lower upper

end OriginalKElementaryArithmeticAction.PeriodicPower.Source
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
