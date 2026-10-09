import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialJoinedHessian
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialHessianBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeHessian
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialNativeBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaRadialMixedClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaRadialBoundaryBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialCoefficient SourceLocalizedInverseFormPayment
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail SourceClockYukawaTail
open SourceClockYukawaNormalizedCurrent SourceCutoffDilationWard SourcePhysicalKineticSquare SourceClockReflectedForm
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] state fullAction inverseRadius normalizedAction finiteResolvent
  GaussGradedCompression.compression actualIncrement correctedCutoffCore sourceB constantBounded

private theorem cubic_geometric_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1:ℝ)*(n+2:ℝ)*s^3*(1-s)^n ≤ 6/(n+3:ℝ) := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have hterm := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+3-j)*((n+3).choose j:ℝ))
    (fun j _ => by positivity) (show 3∈Finset.range (n+3+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at hterm
  rw [show n+3-3=n by omega] at hterm
  have hc := congrArg (fun j : ℕ => (j:ℝ)) (Nat.add_one_mul_choose_eq (n+2) 2)
  push_cast at hc
  rw [Nat.cast_choose_two] at hc
  push_cast at hc
  have hc' : ((n+3).choose 3:ℝ)=(n+3:ℝ)*(n+2:ℝ)*(n+1:ℝ)/6 := by
    convert (show (((n+2)+1).choose (2+1):ℝ)=(n+3:ℝ)*(n+2:ℝ)*(n+1:ℝ)/6 from ?_) using 1
    nlinarith only [hc]
  rw [hc'] at hterm
  apply (le_div_iff₀ (by positivity : 0<(n+3:ℝ))).mpr
  nlinarith only [hterm]

private theorem second_peak_bound (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n:ℝ)*(n+1:ℝ)*s^3*(1-s)^(n-1) ≤ 6/(n+2:ℝ) := by
  cases n with
  | zero => norm_num
  | succ n =>
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    convert cubic_geometric_peak s hs hs1 n using 1 <;> ring

private def firstCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((ell+1:ℝ)*(1-reciprocal z)^ell-(m+1:ℝ)*(1-reciprocal z)^m)*reciprocal z^2
private def secondCoefficient (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  ((m:ℝ)*(m+1:ℝ)*(1-reciprocal z)^(m-1)-
    (ell:ℝ)*(ell+1:ℝ)*(1-reciprocal z)^(ell-1))*reciprocal z^3

private theorem first_smooth (m ell : ℕ) : ContDiff ℝ ∞ (firstCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow ell)).sub
    (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow m))).mul (reciprocal_smooth.pow 2))
private theorem second_smooth (m ell : ℕ) : ContDiff ℝ ∞ (secondCoefficient m ell) :=
  (((contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow (m-1))).sub
    (contDiff_const.mul ((contDiff_const.sub reciprocal_smooth).pow (ell-1)))).mul (reciprocal_smooth.pow 3))

private theorem first_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |firstCoefficient m ell z| ≤ 4/(m+2:ℝ) := by
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have h₁ := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 ell
  have h₂ := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 m
  have hd : 2/(ell+2:ℝ) ≤ 2/(m+2:ℝ) := by gcongr
  have he : firstCoefficient m ell z=
      (ell+1:ℝ)*reciprocal z^2*(1-reciprocal z)^ell-
      (m+1:ℝ)*reciprocal z^2*(1-reciprocal z)^m := by unfold firstCoefficient;ring
  rw [he]
  calc
    _ ≤ |(ell+1:ℝ)*reciprocal z^2*(1-reciprocal z)^ell|+
        |(m+1:ℝ)*reciprocal z^2*(1-reciprocal z)^m| := abs_sub _ _
    _ ≤ 2/(ell+2:ℝ)+2/(m+2:ℝ) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      exact add_le_add h₁ h₂
    _ ≤ 4/(m+2:ℝ) := (add_le_add hd (le_refl _)).trans_eq (by ring)

private theorem second_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    |secondCoefficient m ell z| ≤ 12/(m+2:ℝ) := by
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have h₁ := second_peak_bound (reciprocal z) hs hs1 m
  have h₂ := second_peak_bound (reciprocal z) hs hs1 ell
  have hd : 6/(ell+2:ℝ) ≤ 6/(m+2:ℝ) := by gcongr
  have he : secondCoefficient m ell z=
      (m:ℝ)*(m+1:ℝ)*reciprocal z^3*(1-reciprocal z)^(m-1)-
      (ell:ℝ)*(ell+1:ℝ)*reciprocal z^3*(1-reciprocal z)^(ell-1) := by unfold secondCoefficient;ring
  rw [he]
  calc
    _ ≤ |(m:ℝ)*(m+1:ℝ)*reciprocal z^3*(1-reciprocal z)^(m-1)|+
        |(ell:ℝ)*(ell+1:ℝ)*reciprocal z^3*(1-reciprocal z)^(ell-1)| := abs_sub _ _
    _ ≤ 6/(m+2:ℝ)+6/(ell+2:ℝ) := by
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
      exact add_le_add h₁ h₂
    _ ≤ 12/(m+2:ℝ) := (add_le_add (le_refl _) hd).trans_eq (by ring)

private def realFiber (c : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (c z:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem real_fiber_smooth (c : SourceCoordinateSlice → ℝ) (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (realFiber c) := (Complex.ofRealCLM.contDiff.comp hc).smul contDiff_const
private theorem real_fiber_weight (c : SourceCoordinateSlice → ℝ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (realFiber c z) := (Commute.one_right (GaussFockWeights.weight w)).smul_right _
private theorem real_fiber_bound (c : SourceCoordinateSlice → ℝ) (C : ℝ) (hb : ∀ z,|c z| ≤ C)
    (z : SourceCoordinateSlice) (f : FockFiber) : ‖realFiber c z f‖ ≤ C*‖f‖ := by
  change ‖(c z:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb z) (norm_nonneg _)

private def firstOp (m ell : ℕ) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (realFiber (firstCoefficient m ell))
    (fun _ => (real_fiber_smooth _ (first_smooth m ell)).contDiffAt)
    (fun z => real_fiber_weight _ z) (4/(m+2:ℝ)) (by positivity)
    (fun z => real_fiber_bound _ _ (first_bound m ell hml) z)
private def secondOp (m ell : ℕ) (hml : m ≤ ell) : Op :=
  GaussBoundedMultiplier.extension (realFiber (secondCoefficient m ell))
    (fun _ => (real_fiber_smooth _ (second_smooth m ell)).contDiffAt)
    (fun z => real_fiber_weight _ z) (12/(m+2:ℝ)) (by positivity)
    (fun z => real_fiber_bound _ _ (second_bound m ell hml) z)
private theorem first_norm (m ell : ℕ) (hml : m ≤ ell) : ‖firstOp m ell hml‖ ≤ 4/(m+2:ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem second_norm (m ell : ℕ) (hml : m ≤ ell) : ‖secondOp m ell hml‖ ≤ 12/(m+2:ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private def radialBounded (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) : Op :=
  (-1/2:ℂ) • (firstOp m ell hml*(sourceB sharp-inverseRadius*constantBounded sharp vacuum))+
    (1/4:ℂ) • ((secondOp m ell hml*(1-inverseRadius^2)-
      firstOp m ell hml*((58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2))*sourceB sharp)

private def radialCost (sharp : Bool) : ℝ :=
  2*‖sourceB sharp-inverseRadius*constantBounded sharp vacuum‖+67*‖sourceB sharp‖
attribute [local irreducible] radialBounded radialCost

private theorem inverse_norm : ‖inverseRadius‖ ≤ 1 := by
  unfold inverseRadius
  exact GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private theorem radial_norm (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) :
    ‖radialBounded sharp m ell hml‖ ≤ radialCost sharp/(m+2:ℝ) := by
  have hS : ‖inverseRadius^2‖ ≤ 1 := by
    rw [pow_two]
    exact (norm_mul_le _ _).trans ((mul_le_mul inverse_norm inverse_norm (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
  have hD : ‖(1:Op)-inverseRadius^2‖ ≤ 2 := by
    have h := norm_sub_le (1:Op) (inverseRadius^2)
    have h1 : ‖(1:Op)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    linarith only [h,h1,hS]
  have hP : ‖(58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2‖ ≤ 61 := by
    have h := norm_add_le ((58:ℂ) • (1:Op)) ((3:ℂ) • inverseRadius^2)
    rw [norm_smul,norm_smul] at h
    norm_num at h
    have h1 : ‖(1:Op)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith only [h,h1,hS]
  have ha := (norm_mul_le (firstOp m ell hml)
    (sourceB sharp-inverseRadius*constantBounded sharp vacuum)).trans
      (mul_le_mul_of_nonneg_right (first_norm m ell hml) (norm_nonneg _))
  have hb := (norm_sub_le (secondOp m ell hml*(1-inverseRadius^2))
      (firstOp m ell hml*((58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2))).trans
    (add_le_add ((norm_mul_le _ _).trans (mul_le_mul (second_norm m ell hml) hD
      (norm_nonneg _) (by positivity)))
      ((norm_mul_le _ _).trans (mul_le_mul (first_norm m ell hml) hP (norm_nonneg _) (by positivity))))
  have hc := (norm_mul_le (secondOp m ell hml*(1-inverseRadius^2)-
      firstOp m ell hml*((58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2)) (sourceB sharp)).trans
    (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  unfold radialBounded radialCost
  calc
    _ ≤ ‖(-1/2:ℂ) • (firstOp m ell hml*(sourceB sharp-inverseRadius*constantBounded sharp vacuum))‖+
        ‖(1/4:ℂ) • ((secondOp m ell hml*(1-inverseRadius^2)-
          firstOp m ell hml*((58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2))*sourceB sharp)‖ := norm_add_le _ _
    _ ≤ (1/2:ℝ)*((4/(m+2:ℝ))*‖sourceB sharp-inverseRadius*constantBounded sharp vacuum‖)+
        (1/4:ℝ)*(((12/(m+2:ℝ))*2+(4/(m+2:ℝ))*61)*‖sourceB sharp‖) := by
      rw [norm_smul,norm_smul]
      norm_num
      exact add_le_add (mul_le_mul_of_nonneg_left ha (by positivity))
        (mul_le_mul_of_nonneg_left hc (by positivity))
    _=_ := by ring

private theorem two_square (x y : H) : ‖x-y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]

private def responsePrice (μ : ℝ) (g : H) : ℝ :=
  2*(Real.pi/μ)*(‖g‖^2+‖inverseRadius g‖^2)
attribute [local irreducible] responsePrice

private theorem response_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖SourceRadiusResponseDecay.response F (line μ w) g‖^2)) ≤
      ENNReal.ofReal (responsePrice μ g) := by
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hm : Measurable (fun w : ℝ => ENNReal.ofReal (2:ℝ)*
      ENNReal.ofReal (‖finiteResolvent F (line μ w) (inverseRadius g)‖^2)) :=
    (((hr.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  have henergy (x : H) : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) x‖^2))=
      ENNReal.ofReal (Real.pi/μ*‖x‖^2) := by
    simpa only [line,mul_comm] using SourceActualResolventEnergy.actual_square_lintegral F μ hμ x
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2)+
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖finiteResolvent F (line μ w) (inverseRadius g)‖^2) := by
      apply lintegral_mono
      intro w
      change ENNReal.ofReal (‖SourceRadiusResponseDecay.response F (line μ w) g‖^2) ≤
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2)+
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (‖finiteResolvent F (line μ w) (inverseRadius g)‖^2)
      rw [SourceRadiusResponseDecay.actual_response_difference F (line μ w) (by simpa only [line_im] using hμ.ne')]
      have h := two_square (inverseRadius (finiteResolvent F (line μ w) g))
        (finiteResolvent F (line μ w) (inverseRadius g))
      have hi := (inverseRadius.le_opNorm (finiteResolvent F (line μ w) g)).trans
        ((mul_le_mul_of_nonneg_right inverse_norm (norm_nonneg _)).trans_eq (one_mul _))
      have hi2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
      have hb : ‖inverseRadius (finiteResolvent F (line μ w) g)-finiteResolvent F (line μ w) (inverseRadius g)‖^2 ≤
          2*‖finiteResolvent F (line μ w) g‖^2+2*‖finiteResolvent F (line μ w) (inverseRadius g)‖^2 := by
        nlinarith only [h,hi2]
      apply (ENNReal.ofReal_le_ofReal hb).trans
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      exact ENNReal.ofReal_add_le
    _=ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (Real.pi/μ*‖g‖^2)+
        ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (Real.pi/μ*‖inverseRadius g‖^2) := by
      rw [lintegral_add_right _ hm,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,henergy,henergy]
    _=_ := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      unfold responsePrice
      ring

private theorem bounded_response_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,(hml : m ≤ ell) → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖radialBounded sharp m ell hml
        (SourceRadiusResponseDecay.response F (line μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (radialCost sharp)^2*responsePrice μ g
  have hP : 0 ≤ responsePrice μ g := by unfold responsePrice;positivity
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hP
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F => ?_⟩
  have hrad : 0 ≤ radialCost sharp := by unfold radialCost;positivity
  have hden : 0<(m+2:ℝ) := by positivity
  have hN' : C/ε<(m:ℝ)+2 := by
    have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hN,hm']
  have htail : (radialCost sharp/(m+2:ℝ))^2*responsePrice μ g ≤ ε := by
    have hlin : C<ε*((m:ℝ)+2) := by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hN'
    have hd2 : (m+2:ℝ) ≤ (m+2:ℝ)^2 := by
      have hm0 : (0:ℝ) ≤ m := by positivity
      nlinarith only [hm0]
    have hsq := mul_le_mul_of_nonneg_left hd2 hε.le
    rw [div_pow,div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    change C ≤ _
    linarith only [hlin,hsq]
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal ((radialCost sharp/(m+2:ℝ))^2)*
        ENNReal.ofReal (‖SourceRadiusResponseDecay.response F (line μ w) g‖^2) := by
      apply lintegral_mono
      intro w
      have h := ((radialBounded sharp m ell hml).le_opNorm
        (SourceRadiusResponseDecay.response F (line μ w) g)).trans
        (mul_le_mul_of_nonneg_right (radial_norm sharp m ell hml) (norm_nonneg _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [mul_pow] at hs
      change ENNReal.ofReal (‖radialBounded sharp m ell hml (SourceRadiusResponseDecay.response F (line μ w) g)‖^2) ≤
        ENNReal.ofReal ((radialCost sharp/(m+2:ℝ))^2)*ENNReal.ofReal (‖SourceRadiusResponseDecay.response F (line μ w) g‖^2)
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hs
    _ ≤ ENNReal.ofReal ((radialCost sharp/(m+2:ℝ))^2)*ENNReal.ofReal (responsePrice μ g) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul (le_refl _) (response_energy F μ hμ g) zero_le zero_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal htail

open SourceClockYukawaRadialJoinedHessian
open SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialNativeBudget
open SourceClockYukawaRadialNativeAbsorption (inputSource mixedNormEnergy)
open SourceClockYukawaRadialMixedClock

private theorem inverse_power_apply (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((inverseAction^n) f) z=(reciprocal z:ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (reciprocal z:ℂ) • (((inverseAction^n) f) z)=_
    rw [ih,pow_succ',mul_smul]

private theorem geometric_point (n : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (((1-inverseAction)^n) f) z=((1-reciprocal z:ℝ):ℂ)^n • f z := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change (((1-inverseAction)^n) f) z-(reciprocal z:ℂ) • ((((1-inverseAction)^n) f) z)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module

private theorem first_core (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    firstOp m ell hml (embed f)=embed ((firstPeak m ell*inverseAction^2) f) := by
  rw [firstOp,GaussBoundedMultiplier.extension_core]
  congr 1
  apply DFunLike.ext
  intro z
  change (firstCoefficient m ell z:ℂ) • f z=
    ((firstPeak m ell) ((inverseAction^2) f)) z
  simp only [firstPeak,LinearMap.sub_apply,LinearMap.smul_apply]
  change _=(ell+1:ℂ) • ((((1-inverseAction)^ell) ((inverseAction^2) f)) z)-
    (m+1:ℂ) • ((((1-inverseAction)^m) ((inverseAction^2) f)) z)
  rw [geometric_point,geometric_point,inverse_power_apply]
  unfold firstCoefficient
  push_cast
  module

private theorem second_core (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    secondOp m ell hml (embed f)=embed ((secondPeak m ell*inverseAction^3) f) := by
  rw [secondOp,GaussBoundedMultiplier.extension_core]
  congr 1
  apply DFunLike.ext
  intro z
  change (secondCoefficient m ell z:ℂ) • f z=
    ((secondPeak m ell) ((inverseAction^3) f)) z
  simp only [secondPeak,LinearMap.sub_apply,LinearMap.smul_apply]
  change _=((m:ℂ)*(m+1:ℂ)) • ((((1-inverseAction)^(m-1)) ((inverseAction^3) f)) z)-
    ((ell:ℂ)*(ell+1:ℂ)) • ((((1-inverseAction)^(ell-1)) ((inverseAction^3) f)) z)
  rw [geometric_point,geometric_point,inverse_power_apply]
  unfold secondCoefficient
  push_cast
  module

private theorem inverse_power_core (n : ℕ) (f : QuantumTest) :
    (inverseRadius^n) (embed f)=embed ((inverseAction^n) f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change inverseRadius ((inverseRadius^n) (embed f))=_
    rw [ih,inverse_core]
    rfl

private theorem radial_factor (sharp : Bool) (m ell : ℕ) :
    radialHessianCore sharp m ell=
      (-1/2:ℂ) • ((firstPeak m ell*inverseAction^2)*(normalizedAction sharp-inverseAction*constantAction sharp vacuum))+
        (1/4:ℂ) • (((secondPeak m ell*inverseAction^3)*(1-inverseAction^2)-
          (firstPeak m ell*inverseAction^2)*((58:ℂ) • (1:End)+(3:ℂ) • inverseAction^2))*normalizedAction sharp) := by
  have h3 : (secondPeak m ell*inverseAction^3)*(1-inverseAction^2)=
      secondPeak m ell*(inverseAction^3-inverseAction^5) := by
    simp only [mul_sub,mul_one,mul_assoc,←pow_add]
  have h2 : (firstPeak m ell*inverseAction^2)*((58:ℂ) • (1:End)+(3:ℂ) • inverseAction^2)=
      firstPeak m ell*((58:ℂ) • inverseAction^2+(3:ℂ) • inverseAction^4) := by
    simp only [mul_add,mul_smul_comm,mul_one,mul_assoc,←pow_add]
  simp only [radialHessianCore,h3,h2,neg_div]

private theorem radial_core (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    radialBounded sharp m ell hml (embed f)=embed (radialHessianCore sharp m ell f) := by
  have hB (q : QuantumTest) :
      (sourceB sharp-inverseRadius*constantBounded sharp vacuum) (embed q)=
        embed ((normalizedAction sharp-inverseAction*constantAction sharp vacuum) q) := by
    simp only [sub_apply,mul_apply_eq_comp,original_normalized_core,constant_bounded_core,inverse_core,
      LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  have hS (q : QuantumTest) : ((1:Op)-inverseRadius^2) (embed q)=embed (((1:End)-inverseAction^2) q) := by
    simp only [sub_apply,one_apply_eq_self,LinearMap.sub_apply,Module.End.one_apply,map_sub,inverse_power_core]
  have hH (q : QuantumTest) : ((58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2) (embed q)=
      embed (((58:ℂ) • (1:End)+(3:ℂ) • inverseAction^2) q) := by
    simp only [add_apply,smul_apply,one_apply_eq_self,LinearMap.add_apply,LinearMap.smul_apply,
      Module.End.one_apply,map_add,map_smul,inverse_power_core]
  rw [radial_factor]
  simp only [radialBounded,add_apply,smul_apply,mul_apply_eq_comp,sub_apply,hB,
    original_normalized_core,hS,hH,first_core,second_core,←map_sub,←map_add,←map_smul]
  congr 1
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sub_apply,Module.End.mul_apply,map_smul]

private theorem state_embed (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (state F z hz g)=finiteResolvent F z (g:H) := by
  unfold state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem compression_embed (F : Index) (f : QuantumTest) :
    embed (compressionCore F f)=GaussGradedCompression.compression F (embed f) := by
  unfold compressionCore
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem radial_response_core (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (radialCore F z hz g)=SourceRadiusResponseDecay.response F z (g:H) := by
  rw [radialCore,state_embed]
  change finiteResolvent F z (embed (SourceRadiusResponseDecay.radialCurrent F (state F z hz g)))=_
  rw [SourceRadiusResponseDecay.original_radial_current]
  simp only [LinearMap.sub_apply,Module.End.mul_apply,map_sub,compression_embed,←inverse_core,state_embed]
  simp only [SourceRadiusResponseDecay.response,mul_apply_eq_comp,sub_apply,map_sub]

private theorem radial_response_measurable (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (radialHessianCore sharp m ell
      (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
  simp_rw [←radial_core sharp m ell hml,radial_response_core]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hs : Continuous (fun w : ℝ => SourceRadiusResponseDecay.response F (line μ w) (g:H)) := by
    have he (w : ℝ) : SourceRadiusResponseDecay.response F (line μ w) (g:H)=
        inverseRadius (finiteResolvent F (line μ w) (g:H))-finiteResolvent F (line μ w) (inverseRadius (g:H)) :=
      SourceRadiusResponseDecay.actual_response_difference F (line μ w) (by simpa only [line_im] using hμ.ne') (g:H)
    simp_rw [he]
    exact (inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub (hr.clm_apply continuous_const)
  exact (((radialBounded sharp m ell hml).continuous.comp hs).norm.pow 2).measurable.ennreal_ofReal

private theorem radial_response_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (radialHessianCore sharp m ell
        (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := bounded_response_tail sharp μ hμ (g:H) ε hε
  refine ⟨N,fun m hm ell hml F => ?_⟩
  simpa only [←radial_core sharp m ell hml,radial_response_core] using hN m hm ell hml F

attribute [local irreducible] mixedState mixedPrice

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

def radialForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  (-(sourceTime 0:ℂ)/2) • inverseVolumeAction (radialHessianCore sharp m ell
    (radialCore F z hz (inputSource g)))

/-- All remaining physical fields stay in their single signed source word. -/
def fieldForce (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : QuantumTest :=
  let q := state F z hz (inputSource g)
  let rS := radialCore F z hz (inputSource g)
  let rA := cutoffResponseCore sharp m ell F z hz (inputSource g)
  ((bracket GaussMatterCore.matterAction (fullAction sharp)+SourceInverseNeutralSpinCurrent.reducedSpinCurrent sharp)*thetaAction m ell) rS+
    ((sourceTime 0:ℂ)/2) • inverseVolumeAction ((thetaAction m ell*gammaAction sharp) rS)-
    bracket (defectAction F) (SourceCutoffDilationWard.literalIncrementAction sharp m ell) rS-
    bracket (defectAction F) inverseAction rA+
    bracket (bracket (defectAction F) inverseAction) (SourceCutoffDilationWard.literalIncrementAction sharp m ell) q

/-- The original entire joined Hessian is split using its actual scalar boundary and broken-density source. -/
theorem actual_boundary_forcing_split (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) :
    SourceClockYukawaRadialHessianBudget.reducedForce sharp m ell F z hz g=
      radialForce sharp m ell F z hz g+fieldForce sharp m ell F z hz g := by
  have h := LinearMap.congr_fun (original_joined_hessian_source sharp m ell)
    (radialCore F z hz (inputSource g))
  simp only [LinearMap.sum_apply] at h
  simp only [SourceClockYukawaRadialHessianBudget.reducedForce,radialForce,fieldForce,h,joinedHessianCore,
    Module.End.mul_apply,LinearMap.smul_apply,LinearMap.sub_apply,weight_inverse,map_sub,
    smul_sub,smul_smul]
  have hi : (-Complex.I/2)*Complex.I=1/2 := by
    calc _= -(Complex.I*Complex.I)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  simp only [←mul_assoc,hi]
  module

private theorem young (a b η : ℝ) (hη : 0<η) : a*b ≤ η*a^2+b^2/(4*η) := by
  have he : (4*η)*(b^2/(4*η))=b^2 := by field_simp
  nlinarith [sq_nonneg (2*η*a-b)]

/-- The source coframe floor pays the entire actual radial boundary response. -/
theorem actual_boundary_force_price (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ‖sourcePair (mixedState sharp m ell F z hz g) (radialForce sharp m ell F z hz g)‖ ≤
      η*mixedPrice sharp m ell F z hz g+
        ‖embed (radialHessianCore sharp m ell (radialCore F z hz (inputSource g)))‖^2/(100*η) := by
  let p := mixedState sharp m ell F z hz g
  let v := radialHessianCore sharp m ell (radialCore F z hz (inputSource g))
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp : sourcePair p (inverseVolumeAction v)=sourcePair (inverseVolumeAction p) v := multiply_pair _ _ _ _
  have hc : ‖(-(sourceTime 0:ℂ)/2)‖=sourceTime 0/2 := by
    rw [norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
    norm_num
  change ‖sourcePair p ((-(sourceTime 0:ℂ)/2) • inverseVolumeAction v)‖ ≤ _
  rw [show sourcePair p ((-(sourceTime 0:ℂ)/2) • inverseVolumeAction v)=
    (-(sourceTime 0:ℂ)/2)*sourcePair p (inverseVolumeAction v) by simp only [sourcePair,map_smul,inner_smul_right]]
  rw [hp,norm_mul,hc]
  have hi := mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) (embed (inverseVolumeAction p)) (embed v))
    (show 0 ≤ sourceTime 0/2 by positivity)
  have hf := mul_le_mul_of_nonneg_left (SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction p))
    (show 0 ≤ (sourceTime 0)^2/4 by positivity)
  have hpos := (actual_mixed_positive_payment sharp m ell F z hz g).1
  have hy := young (5*sourceTime 0/2*‖embed (inverseVolumeAction p)‖) (1/5*‖embed v‖) η hη
  have he : (1/5*‖embed v‖)^2/(4*η)=‖embed v‖^2/(100*η) := by field_simp;ring
  rw [he] at hy
  change (sourceTime 0)^2/4*coframeGram (inverseVolumeAction p) ≤ _ at hpos
  have hb := mul_le_mul_of_nonneg_left (hf.trans hpos) hη.le
  change sourceTime 0/2*‖sourcePair (inverseVolumeAction p) v‖ ≤
    sourceTime 0/2*(‖embed (inverseVolumeAction p)‖*‖embed v‖) at hi
  change sourceTime 0/2*‖sourcePair (inverseVolumeAction p) v‖ ≤
    η*mixedPrice sharp m ell F z hz g+‖embed v‖^2/(100*η)
  nlinarith only [hi,hy,hb]

def fieldPrice (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) : ℝ :=
  η*mixedPrice sharp m ell F z hz g-(sourcePair (mixedState sharp m ell F z hz g)
    (fieldForce sharp m ell F z hz g)).im

def fieldBudget (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (fieldPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)

private theorem field_remaining_point (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    SourceClockYukawaRadialHessianBudget.reducedPrice sharp m ell F z hz g (η/2) ≤
      fieldPrice sharp m ell F z hz g η+
        ‖embed (radialHessianCore sharp m ell (radialCore F z hz (inputSource g)))‖^2/(100*(η/2)) := by
  have h := congrArg (fun f => (sourcePair (mixedState sharp m ell F z hz g) f).im)
    (actual_boundary_forcing_split sharp m ell F z hz g)
  simp only [sourcePair,map_add,inner_add_right,Complex.add_im] at h
  have hp := actual_boundary_force_price sharp m ell F z hz g (η/2) (by positivity)
  have hi := (neg_le_abs (sourcePair (mixedState sharp m ell F z hz g)
    (radialForce sharp m ell F z hz g)).im).trans (Complex.abs_im_le_norm _)
  unfold SourceClockYukawaRadialHessianBudget.reducedPrice fieldPrice
  change (sourcePair (mixedState sharp m ell F z hz g)
    (SourceClockYukawaRadialHessianBudget.reducedForce sharp m ell F z hz g)).im=
    (sourcePair (mixedState sharp m ell F z hz g) (radialForce sharp m ell F z hz g)).im+
    (sourcePair (mixedState sharp m ell F z hz g) (fieldForce sharp m ell F z hz g)).im at h
  linarith only [h,hp,hi]

private theorem field_remaining_integral (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    SourceClockYukawaRadialHessianBudget.reducedBudget sharp m ell F μ hμ g (η/2) ≤
      fieldBudget sharp m ell F μ hμ g η+ENNReal.ofReal (1/(100*(η/2)))*
        (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (radialHessianCore sharp m ell
          (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') (inputSource g)))‖^2)) := by
  let E (w : ℝ) := ENNReal.ofReal (‖embed (radialHessianCore sharp m ell
    (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') (inputSource g)))‖^2)
  let Q (w : ℝ) := ENNReal.ofReal (fieldPrice sharp m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η)
  have hE : Measurable (fun w => ENNReal.ofReal (1/(100*(η/2)))*E w) :=
    (radial_response_measurable sharp m ell hml F μ hμ (inputSource g)).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,Q w+ENNReal.ofReal (1/(100*(η/2)))*E w := by
      apply lintegral_mono
      intro w
      have h := field_remaining_point sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g η hη
      apply (ENNReal.ofReal_le_ofReal h).trans
      have ha := ENNReal.ofReal_add_le (p := fieldPrice sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g η)
        (q := ‖embed (radialHessianCore sharp m ell
          (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') (inputSource g)))‖^2/(100*(η/2)))
      have he (a : ℝ) : ENNReal.ofReal (a/(100*(η/2)))=ENNReal.ofReal (1/(100*(η/2)))*ENNReal.ofReal a := by
        rw [show a/(100*(η/2))=(1/(100*(η/2)))*a by ring,ENNReal.ofReal_mul (by positivity)]
      rw [he (‖embed (radialHessianCore sharp m ell
        (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') (inputSource g)))‖^2)] at ha
      simpa only [Q,E] using ha
    _=_ := by rw [lintegral_add_right _ hE,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top];rfl

/-- One source cutoff now pays every native radial boundary term.
The actual broken-density, matter, signed spin and complete compression word remain together. -/
theorem actual_field_mu_remaining_budget (μ : ℝ) (hμ : 0<μ)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        mixedNormEnergy sharp m ell F μ hμ g ≤ ENNReal.ofReal ε+fieldBudget sharp m ell F μ hμ g η := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := SourceClockYukawaRadialHessianBudget.actual_reduced_mu_remaining_budget μ hμ g (η/2)
    (by positivity) (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := radial_response_tail false μ hμ (inputSource g) (100*η*ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := radial_response_tail true μ hμ (inputSource g) (100*η*ε/4) (by positivity)
  refine ⟨max N₀ (max N₁ N₂),fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m ((le_max_left _ _).trans hm) ell hml] with F hM sharp
  have hE : (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (radialHessianCore sharp m ell
      (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') (inputSource g)))‖^2)) ≤
      ENNReal.ofReal (100*η*ε/4) := by
    cases sharp
    · exact h₁ m ((le_max_left _ _).trans ((le_max_right _ _).trans hm)) ell hml F
    · exact h₂ m ((le_max_right _ _).trans ((le_max_right _ _).trans hm)) ell hml F
  have hconst : ENNReal.ofReal (1/(100*(η/2)))*ENNReal.ofReal (100*η*ε/4)=ENNReal.ofReal (ε/2) := by
    rw [←ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
    ring
  have hb := field_remaining_integral sharp m ell hml F μ hμ g η hη
  have hpay := (mul_le_mul (le_refl (ENNReal.ofReal (1/(100*(η/2))))) hE zero_le zero_le).trans_eq hconst
  calc
    _ ≤ ENNReal.ofReal (ε/2)+SourceClockYukawaRadialHessianBudget.reducedBudget sharp m ell F μ hμ g (η/2) := hM sharp
    _ ≤ ENNReal.ofReal (ε/2)+(fieldBudget sharp m ell F μ hμ g η+ENNReal.ofReal (ε/2)) :=
      add_le_add (le_refl _) (hb.trans (add_le_add (le_refl _) hpay))
    _=ENNReal.ofReal ε+fieldBudget sharp m ell F μ hμ g η := by
      have hs : ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2)=ENNReal.ofReal ε := by
        rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      calc
        _=(ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2))+fieldBudget sharp m ell F μ hμ g η := by ac_rfl
        _=_ := by rw [hs]

end LowEnergy.SourceClockYukawaRadialBoundaryBudget
