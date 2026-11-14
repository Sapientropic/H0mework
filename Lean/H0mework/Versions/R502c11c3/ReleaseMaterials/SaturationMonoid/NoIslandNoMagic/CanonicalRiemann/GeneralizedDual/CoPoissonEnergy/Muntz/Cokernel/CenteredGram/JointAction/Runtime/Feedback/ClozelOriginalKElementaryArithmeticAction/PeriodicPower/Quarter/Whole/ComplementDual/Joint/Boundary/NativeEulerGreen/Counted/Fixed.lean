import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.FixedPrice

open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKSourceResolventReconstruction
open OriginalKElementaryArithmeticAction
open OriginalKElementaryArithmeticAction.FreeParameter.Riesz
open OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer
open OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Consumer
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Cotest
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.PositionDual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped InnerProductSpace

open private mean_raw_linear from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Green
open private native_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open private mean_power from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P₀" => Constructor.zeroMean
local notation "Q" => burnolQuarterRestriction
local notation "g" => nativeSmooth
local notation "Z" => elementaryReverseSource
local notation "leading" => ForcingPrimitive.leadingCoefficient
local notation "h₀" => Real.log stageZeroSonineQ

private theorem first_channel (x : ℝ) (lower : q/2 < |x|) (upper : |x| ≤ q) :
    DualSourceRaw.channels x = Finset.Icc 1 1 := by
  have positive : 0 < |x| := lt_trans (by norm_num) lower
  have index : ⌊q/|x|⌋₊ = 1 := by
    apply (Nat.floor_eq_iff (show 0 ≤ q/|x| from div_nonneg (by norm_num) positive.le)).mpr
    constructor
    · rw [Nat.cast_one,le_div_iff₀ positive]
      simpa only [one_mul] using upper
    · norm_num
      rw [div_lt_iff₀ positive]
      linarith
  rw [DualSourceRaw.channels,index]

private theorem correction_raw (c : BurnolCompletedMellinCoordinate) {x : ℝ}
    (inside : |x| ≤ q) :
    correctionRaw c.value c.belowOne x = burnolMeanZeroFourierRaw (g c) x := by
  rw [actual_dual_correction_point c x (abs_le.mp inside)]
  exact (mean_raw_linear (leading c) (logBFirst c 0) (burnolRieszSingleFourierSource c) x).symm

/-- The original first cell combines the full floor and full Unit with the actual return. -/
private theorem first_cell_raw (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (lower : q/2 < |x|) (upper : |x| ≤ q) :
    fullFloorRaw c x + elementaryReverseRaw c x = burnolMeanZeroFourierRaw (g c) x := by
  rw [fullFloorRaw,floorRaw,elementaryReverseRaw,first_channel x lower upper,
    Finset.Icc_self,Finset.sum_singleton,Finset.sum_singleton,Nat.cast_one,one_mul,one_mul]
  rw [dualRaw,seedRaw,powerRaw,correction_raw c upper]
  linear_combination -(mean_power c)

private theorem unit_outer_zero (c : BurnolCompletedMellinCoordinate) (x : ℝ)
    (outside : q < |x|) : elementaryReverseRaw c x = 0 := by
  have positive := (show (0 : ℝ) < q by norm_num).trans outside
  have index : ⌊q/|x|⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one positive).mpr outside)
  simp only [elementaryReverseRaw,DualSourceRaw.channels,index,
    Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1), Finset.sum_empty, neg_zero]

private theorem actual_floor_unit_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    inner ℂ (movedTest c h) (fullFloorValue c zero + Z c zero) =
      inner ℂ (movedTest c h) (E (S (g c) : Hq)) := by
  have half : q/2 ≤ q*Real.exp (-h) := by
    have bound : (1/2 : ℝ) ≤ Real.exp (-h) := by
      calc
        _ = Real.exp (-Real.log 2) := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
        _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg bounded)
    nlinarith
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (fullFloorValue c zero) (Z c zero),actual_full_floor_raw c zero,
    elementary_reverse_raw c zero, burnolZeroExtensionMeanZeroFourier_ae_raw (g c),
    actual_moved_gap c h nonnegative] with x sum floor unit returned gap
  rw [RCLike.inner_apply,RCLike.inner_apply,sum,Pi.add_apply,floor,unit,returned]
  by_cases inside : |x| ≤ q
  · have member : x ∈ symmetricInterval q := abs_le.mp inside
    rw [indicator_of_mem member]
    by_cases first : q*Real.exp (-h) < |x|
    · rw [first_cell_raw c x (half.trans_lt first) inside]
    · rw [gap (le_of_not_gt first)]
      simp
  · have outside : x ∉ symmetricInterval q := fun member => inside (abs_le.mpr member)
    rw [indicator_of_notMem outside, fullFloorRaw,
      actual_floor_outer_zero c.value c.belowOne x (lt_of_not_ge inside),
      unit_outer_zero c x (lt_of_not_ge inside),zero_add]

private theorem cotest_faces (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    inner ℂ (jointCotest c h) (g c) =
      inner ℂ (fourierTest c h) (E (g c : Hq)) -
        inner ℂ (movedTest c h) (E (S (g c) : Hq)) := by
  rw [jointCotest,inner_sub_left,
    OriginalRieszSourceGreen.meanZero_fourier_pairing_of_reflection _ _ (native_even c)]
  change inner ℂ (P₀ (Q (fourierTest c h)) : Hq) (g c : Hq) -
    inner ℂ (P₀ (Q (movedTest c h)) : Hq) (S (g c) : Hq) =
    inner ℂ (fourierTest c h) (burnolQuarterRestriction.adjoint (g c : Hq)) -
      inner ℂ (movedTest c h) (burnolQuarterRestriction.adjoint (S (g c) : Hq))
  rw [ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  exact congrArg₂ (fun left right : ℂ => left-right)
    (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (g c) (Q (fourierTest c h)))
    (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right (S (g c)) (Q (movedTest c h)))

/-- The actual counted floor and complete Unit jointly enter the original cotest. -/
theorem actual_fixed_counted_coupling (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    inner ℂ (movedTest c h₀) (freeUnit (star c.value) ConstantDual.value) +
      inner ℂ (jointCotest c h₀) (g c) =
        inner ℂ (fourierTest c h₀) (E (g c : Hq)) -
          inner ℂ (movedTest c h₀) (floorFromResponses c) := by
  have nn : 0 ≤ h₀ := Real.log_nonneg (by
    change 1 ≤ Real.sqrt 3
    exact Real.one_le_sqrt.mpr (by norm_num))
  have bounded : h₀ ≤ Real.log 2 := Real.log_le_log stageZeroSonineQ_pos (by
    change Real.sqrt 3 ≤ 2
    exact Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  have price := actual_floor_unit_price c zero h₀ nn bounded
  rw [inner_add_right, actual_counted_floor_response c zero,
    elementary_reverse_unit_resolvent c zero, actual_free_unit] at price
  rw [cotest_faces]
  linear_combination price

/-- The original net reads the counted floor and the two complete Fourier seed prices. -/
theorem actual_fixed_counted_net (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    let test := fourierTest c h₀
    let acted := sourceResolvent (OriginalPrimitiveRankBalance.conjugateCoordinate c) test
    OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed.nativeFixedNet c =
      (pairedMellinTranslationCharacter c.value h₀ -
        pairedMellinTranslationCharacter (star c.value) h₀)*kernelSelfSource c +
      (1/2 : ℂ)*(inner ℂ (movedTest c h₀) (floorFromResponses c) +
        leading c*inner ℂ (twoClockCorrection c h₀) (centeredLogColumn c 0) -
        (1/2 : ℂ)*((nativeGamma c-originCoefficient c)*inner ℂ acted Response.wholeU -
          nativeBeta c*inner ℂ acted Response.wholeV +
          2*nativeBeta c*inner ℂ test ConstantDual.seed +
          star c.value*nativeBeta c*inner ℂ acted ConstantDual.seed)) := by
  dsimp only
  have price := actual_fixed_counted_coupling c zero
  have green := native_resonant_green c (fourierTest c h₀)
  unfold OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fixed.nativeFixedNet
  linear_combination -(1/2 : ℂ)*price - (1/4 : ℂ)*green

end OriginalCanonicalNativeEulerGreen.Counted.FixedPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
