import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaJointRadialCrossBound
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaJointRadialZero
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
namespace LowEnergy.SourceClockYukawaJointRadialZeroBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourceClockYukawaRadialMixedCore SourceClockYukawaRadialCoefficient SourceLocalizedInverseFormPayment
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail SourceClockYukawaTail
open SourceClockYukawaNormalizedCurrent SourceCutoffDilationWard SourcePhysicalKineticSquare SourceClockReflectedForm
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
open SourceInverseNeutralSpinCurrent SourceClockYukawaSpinClosure
open SourceClockYukawaSpinNativeBudget SourceClockYukawaSpinJointForce
open SourceClockYukawaJointRadialZero
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


open SourceClockYukawaRadialJoinedHessian
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


open GaussQuantumMultiplier GaussFockWeights
private theorem spin_bounded_core (j : Fin 4) (f : QuantumTest) :
    spinBounded j (embed f)=embed (activeSpin j f) :=
  GaussBoundedMultiplier.extension_core (fun _ => quantized (GaussCoframeSpin.full (activeIndex j)))
    (fun _ => contDiffAt_const) (fun _ w => weight_commute w _)
      ‖quantized (GaussCoframeSpin.full (activeIndex j))‖ (norm_nonneg _)
        (fun _ v => ContinuousLinearMap.le_opNorm _ v) f

private theorem bracket_core (A B : Op) (a b : End)
    (ha : ∀ f, A (embed f)=embed (a f)) (hb : ∀ f,B (embed f)=embed (b f)) (f : QuantumTest) :
    bracket A B (embed f)=embed (bracket a b f) := by
  simp only [bracket,mul_apply_eq_comp,sub_apply,Module.End.mul_apply,LinearMap.sub_apply,ha,hb,map_sub]

/-- The eight native coefficients are the same actual spin-closure images of the paid joined Z. -/
private def ad (J : End) : End →ₗ[ℂ] End where
  toFun A := bracket J A
  map_add' A B := by unfold bracket;noncomm_ring
  map_smul' c A := by simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private def recipe (mu : Fin 8) : End →ₗ[ℂ] End :=
  if h0 : mu.val=0 then LinearMap.id else
  if h1 : mu.val<5 then ad (activeSpin ⟨mu.val-1,by omega⟩) else
    (ad (activeSpin ⟨mu.val-5,by omega⟩)).comp (ad (activeSpin 3))

private def boundedRecipe (mu : Fin 8) (A : Op) : Op :=
  if h0 : mu.val=0 then A else
  if h1 : mu.val<5 then bracket (spinBounded ⟨mu.val-1,by omega⟩) A else
    bracket (spinBounded ⟨mu.val-5,by omega⟩) (bracket (spinBounded 3) A)
private def recipePrice (mu : Fin 8) : ℝ :=
  if h0 : mu.val=0 then 1 else
  if h1 : mu.val<5 then 2*‖spinBounded ⟨mu.val-1,by omega⟩‖ else
    4*‖spinBounded ⟨mu.val-5,by omega⟩‖*‖spinBounded 3‖
private theorem recipe_price_nonnegative (mu : Fin 8) : 0 ≤ recipePrice mu := by
  unfold recipePrice
  split_ifs <;> positivity
private theorem bracket_norm (A B : Op) : ‖bracket A B‖ ≤ 2*‖A‖*‖B‖ := by
  exact ((norm_sub_le _ _).trans (add_le_add (norm_mul_le A B) (norm_mul_le B A))).trans_eq (by ring)
private theorem recipe_norm (mu : Fin 8) (A : Op) : ‖boundedRecipe mu A‖ ≤ recipePrice mu*‖A‖ := by
  unfold boundedRecipe recipePrice
  split_ifs
  · simp only [one_mul,le_refl]
  · exact bracket_norm _ _
  · exact ((bracket_norm _ _).trans (mul_le_mul_of_nonneg_left (bracket_norm _ _) (by positivity))).trans_eq (by ring)
private def radialEight (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (hml : m ≤ ell) : Op :=
  boundedRecipe mu (radialBounded sharp m ell hml)
private def radialEightPrice (sharp : Bool) (mu : Fin 8) : ℝ := recipePrice mu*radialCost sharp
private theorem radial_eight_nonnegative (sharp : Bool) (mu : Fin 8) : 0 ≤ radialEightPrice sharp mu :=
  mul_nonneg (recipe_price_nonnegative mu) (by unfold radialCost;positivity)
private theorem radial_eight_norm (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (hml : m ≤ ell) :
    ‖radialEight sharp mu m ell hml‖ ≤ radialEightPrice sharp mu/(m+2:ℝ) := by
  exact ((recipe_norm mu _).trans (mul_le_mul_of_nonneg_left (radial_norm sharp m ell hml)
    (recipe_price_nonnegative mu))).trans_eq (by unfold radialEightPrice;ring)
private theorem radial_eight_core (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (hml : m ≤ ell)
    (f : QuantumTest) : radialEight sharp mu m ell hml (embed f)=embed (radialHessian sharp mu m ell f) := by
  have hJ (j : Fin 4) := bracket_core (spinBounded j) (radialBounded sharp m ell hml)
    (activeSpin j) (radialHessianCore sharp m ell) (spin_bounded_core j) (radial_core sharp m ell hml)
  have hJJ (j : Fin 4) := bracket_core (spinBounded j)
    (bracket (spinBounded 3) (radialBounded sharp m ell hml)) (activeSpin j)
    (bracket (activeSpin 3) (radialHessianCore sharp m ell)) (spin_bounded_core j) (hJ 3)
  have hs : radialHessian sharp mu m ell=
      if h0 : mu.val=0 then radialHessianCore sharp m ell else
      if h1 : mu.val<5 then bracket (activeSpin ⟨mu.val-1,by omega⟩) (radialHessianCore sharp m ell) else
        bracket (activeSpin ⟨mu.val-5,by omega⟩) (bracket (activeSpin 3) (radialHessianCore sharp m ell)) := by
    change recipe mu (radialHessianCore sharp m ell)=_
    unfold recipe
    split_ifs <;> rfl
  rw [hs]
  unfold radialEight boundedRecipe
  split_ifs
  · exact radial_core sharp m ell hml f
  · exact hJ _ f
  · exact hJJ _ f
private theorem bounded_response_tail (sharp : Bool) (mu : Fin 8) (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,(hml : m ≤ ell) → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖radialEight sharp mu m ell hml
        (SourceRadiusResponseDecay.response F (line μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := (radialEightPrice sharp mu)^2*responsePrice μ g
  have hP : 0 ≤ responsePrice μ g := by unfold responsePrice;positivity
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hP
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F => ?_⟩
  have hrad : 0 ≤ radialEightPrice sharp mu := radial_eight_nonnegative sharp mu
  have hden : 0<(m+2:ℝ) := by positivity
  have hN' : C/ε<(m:ℝ)+2 := by
    have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
    linarith only [hN,hm']
  have htail : (radialEightPrice sharp mu/(m+2:ℝ))^2*responsePrice μ g ≤ ε := by
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
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal ((radialEightPrice sharp mu/(m+2:ℝ))^2)*
        ENNReal.ofReal (‖SourceRadiusResponseDecay.response F (line μ w) g‖^2) := by
      apply lintegral_mono
      intro w
      have h := ((radialEight sharp mu m ell hml).le_opNorm
        (SourceRadiusResponseDecay.response F (line μ w) g)).trans
        (mul_le_mul_of_nonneg_right (radial_eight_norm sharp mu m ell hml) (norm_nonneg _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [mul_pow] at hs
      change ENNReal.ofReal (‖radialEight sharp mu m ell hml (SourceRadiusResponseDecay.response F (line μ w) g)‖^2) ≤
        ENNReal.ofReal ((radialEightPrice sharp mu/(m+2:ℝ))^2)*ENNReal.ofReal (‖SourceRadiusResponseDecay.response F (line μ w) g‖^2)
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hs
    _ ≤ ENNReal.ofReal ((radialEightPrice sharp mu/(m+2:ℝ))^2)*ENNReal.ofReal (responsePrice μ g) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul (le_refl _) (response_energy F μ hμ g) zero_le zero_le
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal htail


open SourceClockYukawaCubicCurrent SourceClockYukawaRadialHessianBudget
private theorem inverse_spin (j : Fin 4) : Commute inverseAction (activeSpin j) := by
  unfold activeSpin
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (reciprocal z:ℂ) • quantized (GaussCoframeSpin.full (activeIndex j)) (f z)=
    quantized (GaussCoframeSpin.full (activeIndex j)) ((reciprocal z:ℂ) • f z)
  exact (map_smul _ _ _).symm

private theorem inverse_coefficient (sharp : Bool) (mu : Fin 8) :
    Commute inverseAction (spinClosureCoefficient sharp mu) := by
  have hY : Commute inverseAction (fullAction sharp) := by
    unfold fullAction
    cases sharp
    · exact GaussRadialHamiltonian.original_commutes.symm
    · exact GaussRadialHamiltonian.adjoint_commutes.symm
  have hb (A B : End) (hA : Commute inverseAction A) (hB : Commute inverseAction B) :
      Commute inverseAction (bracket A B) := (hA.mul_right hB).sub_right (hB.mul_right hA)
  unfold spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  split
  · exact hY
  · split
    · exact hb _ _ (inverse_spin _) hY
    · exact hb _ _ (inverse_spin _) (hb _ _ (inverse_spin 3) hY)

private theorem normalized_joint_core (sharp : Bool) (mu : Fin 8) (f : QuantumTest) :
    normalizedJoint sharp mu (embed f)=embed (inverseAction (spinClosureCoefficient sharp mu f)) := by
  have hs (j : Fin 4) (A : End) : bracket (activeSpin j) (inverseAction*A)=
      inverseAction*bracket (activeSpin j) A := by
    have h := (inverse_spin j).eq
    unfold bracket
    linear_combination (norm := noncomm_ring) -h*A
  have hY : ∀ f,sourceB sharp (embed f)=embed ((inverseAction*fullAction sharp) f) :=
    by intro f;simpa only [normalizedAction,Module.End.mul_apply] using original_normalized_core sharp f
  have hJ (j : Fin 4) (f : QuantumTest) :
      bracket (spinBounded j) (sourceB sharp) (embed f)=
        embed ((inverseAction*bracket (activeSpin j) (fullAction sharp)) f) := by
    rw [bracket_core _ _ _ _ (spin_bounded_core j) hY,hs]
  have hJJ (j : Fin 4) (f : QuantumTest) :
      bracket (spinBounded j) (bracket (spinBounded 3) (sourceB sharp)) (embed f)=
        embed ((inverseAction*bracket (activeSpin j) (bracket (activeSpin 3) (fullAction sharp))) f) := by
    rw [bracket_core _ _ _ _ (spin_bounded_core j) (hJ 3),hs]
  unfold normalizedJoint spinClosureCoefficient SourceClockYukawaSpinRelativeForm.spinCoefficient
  split
  · exact hY f
  · split
    · exact hJ _ f
    · exact hJJ _ f

attribute [local irreducible] normalizedJoint inverseAction
  SourceClockYukawaSpinJointForce.currentCore SourceClockYukawaSpinJointForce.cutoffCore
  resolventCore compressionCore defectAction diagonalAction
private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore
  exact state_embed F z hz (coreEquiv f)

private theorem core_inverses (F : Index) (z : ℂ) (hz : z.im≠0) :
    (compressionCore F-z • (1:End))*resolventCore F z hz=1 ∧
      resolventCore F z hz*(compressionCore F-z • (1:End))=1 := by
  constructor
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      map_sub,map_smul,compression_embed,resolvent_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_right (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self] using h
  · apply LinearMap.ext
    intro f
    apply embed_injective
    simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply,
      resolvent_embed,map_sub,map_smul,compression_embed]
    have h := congrArg (fun A : H →L[ℂ] H => A (embed f))
      (resolvent_left (GaussGradedCompression.compression F) (GaussGradedCompression.compression_selfAdjoint F) z hz)
    simpa only [finiteResolvent,mul_apply_eq_comp,sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul] using h

private theorem response_difference (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    cutoffResponseCore sharp mu m ell F z hz g=
      spinClosureCoefficient sharp mu (SourceMixedNativeReturn.thetaAction m ell (resolventCore F z hz (coreEquiv.symm g)))-
        resolventCore F z hz (SourceMixedNativeReturn.thetaAction m ell (spinClosureCoefficient sharp mu (coreEquiv.symm g))) := by
  let L : End := compressionCore F-z • 1
  let R : End := resolventCore F z hz
  let A : End := SourceClockYukawaSpinJointForce.cutoffCore sharp m ell mu
  have hi := core_inverses F z hz
  have hm (L R A : End) (hL : L*R=1) (hR : R*L=1) : R*bracket L A*R=A*R-R*A := by
    unfold bracket
    rw [mul_sub,sub_mul,←mul_assoc,←mul_assoc,hR,one_mul,mul_assoc,mul_assoc,hL,mul_one]
  have hJ : bracket L A=SourceClockYukawaSpinJointForce.currentCore sharp m ell F mu := by
    unfold SourceClockYukawaSpinJointForce.currentCore defectAction
    dsimp only [L,A]
    simp only [bracket,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
    module
  have h := LinearMap.congr_fun (hm L R A hi.1 hi.2) (coreEquiv.symm g)
  rw [hJ] at h
  have ht : Commute (SourceMixedNativeReturn.thetaAction m ell) (spinClosureCoefficient sharp mu) := by
    exact ((((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _).sub_left
      (((Commute.one_left _).sub_left (inverse_coefficient sharp mu)).pow_left _))
  have ht' := LinearMap.congr_fun ht.eq (coreEquiv.symm g)
  simp only [Module.End.mul_apply] at ht'
  simpa only [cutoffResponseCore,Module.End.mul_apply,LinearMap.sub_apply,A,SourceClockYukawaSpinJointForce.cutoffCore,ht',R]
    using h

private def coefficientSource (sharp : Bool) (mu : Fin 8) (g : diagonal.domain) : diagonal.domain :=
  coreEquiv (spinClosureCoefficient sharp mu (coreEquiv.symm g))


private def weightHead (sharp : Bool) (mu : Fin 8) : Op :=
  ((58:ℂ) • (1:Op)+(3:ℂ) • inverseRadius^2)*normalizedJoint sharp mu

private theorem weight_core (f : QuantumTest) : weightOp (embed f)=embed (weightCore f) := by
  simp only [weightOp,weightCore,add_apply,smul_apply,LinearMap.add_apply,LinearMap.smul_apply,
    inverse_power_core,map_add,map_smul]

private theorem weight_factor (sharp : Bool) (mu : Fin 8) :
    weightCore*spinClosureCoefficient sharp mu=
      (((58:ℂ) • (1:End)+(3:ℂ) • inverseAction^2)*(inverseAction*spinClosureCoefficient sharp mu))*inverseAction^2 := by
  have hc : spinClosureCoefficient sharp mu*inverseAction^2=inverseAction^2*spinClosureCoefficient sharp mu :=
    ((inverse_coefficient sharp mu).pow_left 2).eq.symm
  simp only [weightCore,add_mul,smul_mul_assoc,one_mul,mul_assoc,hc]
  noncomm_ring

private theorem weight_head_core (sharp : Bool) (mu : Fin 8) (f : QuantumTest) :
    weightHead sharp mu (embed f)=
      embed ((((58:ℂ) • (1:End)+(3:ℂ) • inverseAction^2)*(inverseAction*spinClosureCoefficient sharp mu)) f) := by
  simp only [weightHead,mul_apply_eq_comp,add_apply,smul_apply,one_apply_eq_self,normalized_joint_core,
    inverse_power_core,Module.End.mul_apply,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,map_add,map_smul]

attribute [local irreducible] weightCore weightOp weightHead cutoffResponseCore coefficientSource

private theorem weighted_response_return (sharp : Bool) (mu : Fin 8)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (weightCore (cutoffResponseCore sharp mu m ell F z hz g))=
      weightHead sharp mu ((inverseRadius^2*relativeTail m ell) (finiteResolvent F z (g:H)))-
        weightOp (finiteResolvent F z (relativeTail m ell (coefficientSource sharp mu g:H))) := by
  rw [response_difference]
  simp only [map_sub]
  have hg : embed (coreEquiv.symm g)=(g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply g)
  have hY : embed (spinClosureCoefficient sharp mu (coreEquiv.symm g))=(coefficientSource sharp mu g:H) := by unfold coefficientSource;rfl
  congr 1
  · rw [←hg,←resolvent_embed F z hz]
    change embed ((weightCore*spinClosureCoefficient sharp mu) (SourceMixedNativeReturn.thetaAction m ell
        (resolventCore F z hz (coreEquiv.symm g))))=_
    rw [weight_factor]
    simp only [Module.End.mul_apply,mul_apply_eq_comp,SourceMixedNativeReturn.theta_core,inverse_power_core,weight_head_core]
  · exact (weight_core (resolventCore F z hz (SourceMixedNativeReturn.thetaAction m ell
        (spinClosureCoefficient sharp mu (coreEquiv.symm g))))).symm.trans
      ((congrArg weightOp (resolvent_embed F z hz _)).trans
        (congrArg (fun v : H => weightOp (finiteResolvent F z v))
          ((SourceMixedNativeReturn.theta_core m ell _).symm.trans (congrArg (relativeTail m ell) hY))))

private theorem weighted_energy_measurable (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (weightCore (cutoffResponseCore sharp mu m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
  simp_rw [weighted_response_return]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact (((((weightHead sharp mu).continuous.comp (((inverseRadius^2*relativeTail m ell):Op).continuous.comp
    (hr.clm_apply continuous_const))).sub (weightOp.continuous.comp (hr.clm_apply continuous_const))).norm.pow 2).measurable.ennreal_ofReal)

private theorem radial_eight_measurable (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (radialHessian sharp mu m ell
      (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
  simp_rw [←radial_eight_core sharp mu m ell hml,radial_response_core]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hs : Continuous (fun w : ℝ => SourceRadiusResponseDecay.response F (line μ w) (g:H)) := by
    have he (w : ℝ) := SourceRadiusResponseDecay.actual_response_difference F (line μ w)
      (by simpa only [line_im] using hμ.ne') (g:H)
    simp_rw [he]
    exact (inverseRadius.continuous.comp (hr.clm_apply continuous_const)).sub (hr.clm_apply continuous_const)
  exact (((radialEight sharp mu m ell hml).continuous.comp hs).norm.pow 2).measurable.ennreal_ofReal


private theorem small_resolvent_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,(hml : m ≤ ell) → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖(inverseRadius^2*relativeTail m ell)
        (finiteResolvent F (line μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C := Real.pi/μ*‖g‖^2
  have hC : 0 ≤ C := by dsimp [C];positivity
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hml F => ?_⟩
  have hden : 0 < (m+2:ℝ) := by positivity
  have hm' : (N:ℝ) ≤ m := by exact_mod_cast hm
  have hsmall : C/ε < (m+2:ℝ) := by linarith only [hN,hm']
  have hlin : C < ε*(m+2:ℝ) := by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hsmall
  have htail : (1/(m+2:ℝ))^2*C ≤ ε := by
    have hd2 : (m+2:ℝ) ≤ (m+2:ℝ)^2 := by nlinarith only [Nat.cast_nonneg (α := ℝ) m]
    have hsq := mul_le_mul_of_nonneg_left hd2 hε.le
    rw [div_pow,one_pow,div_mul_eq_mul_div,one_mul]
    exact (div_le_iff₀ (sq_pos_of_pos hden)).mpr (hlin.le.trans hsq)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal ((1/(m+2:ℝ))^2)*
        ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2) := by
      apply lintegral_mono
      intro w
      have hb := ((inverseRadius^2*relativeTail m ell).le_opNorm (finiteResolvent F (line μ w) g)).trans
        (mul_le_mul_of_nonneg_right (SourceClockYukawaJointRadialCrossBound.original_inverse_square_theta_norm m ell hml) (norm_nonneg _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
      rw [mul_pow] at hs
      change ENNReal.ofReal (‖(inverseRadius^2*relativeTail m ell) (finiteResolvent F (line μ w) g)‖^2) ≤
        ENNReal.ofReal ((1/(m+2:ℝ))^2)*ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2)
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hs
    _ = ENNReal.ofReal ((1/(m+2:ℝ))^2)*ENNReal.ofReal C := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      congr 1
      simpa only [C,line,mul_comm] using SourceActualResolventEnergy.actual_square_lintegral F μ hμ g
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal htail

private theorem scalar_budget (P Q ε : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hε : 0 ≤ ε) :
    (P+Q)*(ε/(P+Q+1)) ≤ ε := by
  rw [←mul_div_assoc]
  exact (div_le_iff₀ (by positivity : 0<P+Q+1)).mpr (by nlinarith only [hε])

private theorem weighted_response_tail (sharp : Bool) (mu : Fin 8)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (weightCore (cutoffResponseCore sharp mu m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let P := 2*‖weightHead sharp mu‖^2
  let Q := 2*‖weightOp‖^2
  have hP : 0 ≤ P := by dsimp [P];positivity
  have hQ : 0 ≤ Q := by dsimp [Q];positivity
  let δ := ε/(P+Q+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  obtain ⟨N₁,h₁⟩ := small_resolvent_tail μ hμ (g:H) δ hδ
  obtain ⟨N₂,h₂⟩ := fixed_forcing_uniform_energy_tail μ hμ (1:Op) (coefficientSource sharp mu g:H) δ hδ
  refine ⟨max N₁ N₂,fun m hm ell hml F => ?_⟩
  have hx := h₁ m ((le_max_left _ _).trans hm) ell hml F
  have hy := h₂ m ((le_max_right _ _).trans hm) ell hml F
  simp only [one_apply_eq_self] at hy
  let X (w : ℝ) := ENNReal.ofReal (‖(inverseRadius^2*relativeTail m ell) (finiteResolvent F (line μ w) (g:H))‖^2)
  let Y (w : ℝ) := ENNReal.ofReal (‖finiteResolvent F (line μ w) (relativeTail m ell (coefficientSource sharp mu g:H))‖^2)
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hmY : Measurable (fun w => ENNReal.ofReal Q*Y w) :=
    (((hr.clm_apply continuous_const).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal P*X w+ENNReal.ofReal Q*Y w := by
      apply lintegral_mono
      intro w
      change ENNReal.ofReal (‖embed (weightCore (cutoffResponseCore sharp mu m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g))‖^2) ≤ _
      rw [weighted_response_return sharp mu m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g]
      let x := (inverseRadius^2*relativeTail m ell) (finiteResolvent F (line μ w) (g:H))
      let y := finiteResolvent F (line μ w) (relativeTail m ell (coefficientSource sharp mu g:H))
      have hx2 := pow_le_pow_left₀ (norm_nonneg _) ((weightHead sharp mu).le_opNorm x) 2
      have hy2 := pow_le_pow_left₀ (norm_nonneg _) (weightOp.le_opNorm y) 2
      rw [mul_pow] at hx2 hy2
      have hs := two_square (weightHead sharp mu x) (weightOp y)
      have hb : ‖weightHead sharp mu x-weightOp y‖^2 ≤ P*‖x‖^2+Q*‖y‖^2 := by
        dsimp only [P,Q]
        nlinarith only [hx2,hy2,hs]
      apply (ENNReal.ofReal_le_ofReal hb).trans
      change ENNReal.ofReal (P*‖x‖^2+Q*‖y‖^2) ≤
        ENNReal.ofReal P*ENNReal.ofReal (‖x‖^2)+ENNReal.ofReal Q*ENNReal.ofReal (‖y‖^2)
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ]
      exact ENNReal.ofReal_add_le
    _ = ENNReal.ofReal P*(∫⁻ w : ℝ,X w)+ENNReal.ofReal Q*(∫⁻ w : ℝ,Y w) := by
      rw [lintegral_add_right _ hmY,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal P*ENNReal.ofReal δ+ENNReal.ofReal Q*ENNReal.ofReal δ := by gcongr
    _ ≤ ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul hP,←ENNReal.ofReal_mul hQ,←ENNReal.ofReal_add (by positivity) (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have he : P*δ+Q*δ=(P+Q)*(ε/(P+Q+1)) := by dsimp [δ];ring
      rw [he]
      exact scalar_budget P Q ε hP hQ hε.le

open SourceClockYukawaJointRadialCrossBound SourceClockYukawaRadialNativeBudget
private theorem cross_core_apply (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (q : QuantumTest) :
    crossCore sharp mu m ell q=∑ a : ScalarIndex,inverseDerivativeCore a (jointCoefficient sharp mu a m ell q) := by
  simp only [crossCore,LinearMap.sum_apply,Module.End.mul_apply]

private theorem cross_energy_measurable (sharp : Bool) (mu : Fin 8) (m ell : ℕ) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (‖embed (crossCore sharp mu m ell
      (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2)) := by
  simp_rw [←original_cross_bounded_core,state_embed]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact (((crossBounded sharp mu m ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal

private def responseVector (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : Column := fun mu =>
  paidVector sharp mu m ell (radialCore F z hz g) (cutoffResponseCore sharp mu m ell F z hz g) (state F z hz g)

private theorem real_three_square (a b c x : ℝ) (hx : x^2 ≤ (a+b+c)^2) :
    x^2 ≤ 3*(a^2+b^2+c^2) := by
  nlinarith only [hx,sq_nonneg (a-b),sq_nonneg (a-c),sq_nonneg (b-c)]
private theorem three_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b c : E) :
    ‖(-1/2:ℂ) • a+(1/8:ℂ) • b-c‖^2 ≤ 3*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have ha : ‖(-1/2:ℂ) • a‖ ≤ ‖a‖ := (norm_smul _ _).le.trans
    (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(-1/2:ℂ)‖ ≤ 1))
  have hb : ‖(1/8:ℂ) • b‖ ≤ ‖b‖ := (norm_smul _ _).le.trans
    (mul_le_of_le_one_left (norm_nonneg _) (by norm_num : ‖(1/8:ℂ)‖ ≤ 1))
  have hh : ‖(-1/2:ℂ) • a+(1/8:ℂ) • b-c‖ ≤ ‖a‖+‖b‖+‖c‖ :=
    (norm_sub_le _ c).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ha hb)) (le_refl ‖c‖))
  exact real_three_square _ _ _ _ (pow_le_pow_left₀ (norm_nonneg _) hh 2)

private theorem vector_bound (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : columnNorm (responseVector sharp m ell F z hz g) ≤
      3*(∑ mu : Fin 8,‖embed (radialHessian sharp mu m ell (radialCore F z hz g))‖^2)+
      3*(∑ mu : Fin 8,‖embed (weightCore (cutoffResponseCore sharp mu m ell F z hz g))‖^2)+
      3*(∑ mu : Fin 8,‖embed (crossCore sharp mu m ell (state F z hz g))‖^2) := by
  unfold columnNorm responseVector
  calc
    _ ≤ ∑ mu : Fin 8,3*(‖embed (radialHessian sharp mu m ell (radialCore F z hz g))‖^2+
        ‖embed (weightCore (cutoffResponseCore sharp mu m ell F z hz g))‖^2+
        ‖embed (crossCore sharp mu m ell (state F z hz g))‖^2) := by
      apply Finset.sum_le_sum
      intro mu _
      rw [paidVector,←cross_core_apply]
      simp only [map_sub,map_add,map_smul]
      exact three_square _ _ _
    _ = _ := by simp only [Finset.mul_sum,mul_add,Finset.sum_add_distrib]

private theorem vector_energy_measurable (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (columnNorm
      (responseVector sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g))) := by
  have hc : Continuous (fun w : ℝ => columnNorm
      (responseVector sharp m ell F (line μ w) (by simpa only [line_im] using hμ.ne') g)) := by
    unfold columnNorm responseVector
    apply continuous_finsetSum
    intro mu _
    simp_rw [paidVector,←cross_core_apply,map_sub,map_add,map_smul,
      ←radial_eight_core sharp mu m ell hml,radial_response_core,weighted_response_return,
      ←original_cross_bounded_core,state_embed]
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    have hd (w : ℝ) := SourceRadiusResponseDecay.actual_response_difference F (line μ w)
      (by simpa only [line_im] using hμ.ne') (g:H)
    simp_rw [hd]
    fun_prop
  exact hc.measurable.ennreal_ofReal

private theorem vector_energy_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (columnNorm (responseVector sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g))) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hδ : 0<ε/72 := div_pos hε (by norm_num)
  have hR (i : Bool×Fin 8) := bounded_response_tail i.1 i.2 μ hμ (g:H) (ε/72) hδ
  have hW (i : Bool×Fin 8) := weighted_response_tail i.1 i.2 μ hμ g (ε/72) hδ
  choose NR hR using hR
  choose NW hW using hW
  obtain ⟨NX,hX⟩ := actual_joint_cross_common_tail μ hμ g (ε/9) (div_pos hε (by norm_num))
  refine ⟨max (Finset.univ.sup NR) (max (Finset.univ.sup NW) NX),fun m hm ell hml F sharp => ?_⟩
  have hnr (i : Bool×Fin 8) : NR i ≤ m :=
    (Finset.le_sup (f := NR) (Finset.mem_univ i)).trans ((le_max_left _ _).trans hm)
  have hnw (i : Bool×Fin 8) : NW i ≤ m :=
    (Finset.le_sup (f := NW) (Finset.mem_univ i)).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hm))
  let R (w : ℝ) := ∑ mu : Fin 8,‖embed (radialHessian sharp mu m ell
    (radialCore F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2
  let W (w : ℝ) := ∑ mu : Fin 8,‖embed (weightCore (cutoffResponseCore sharp mu m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g))‖^2
  let X (w : ℝ) := ∑ mu : Fin 8,‖embed (crossCore sharp mu m ell
    (state F (line μ w) (by simpa only [line_im] using hμ.ne') g))‖^2
  have hsum {f : Fin 8 → ℝ → ℝ} (hf : ∀ i w,0 ≤ f i w)
      (hfmeas : ∀ i,Measurable (fun w => ENNReal.ofReal (f i w)))
      (ht : ∀ i,(∫⁻ w : ℝ,ENNReal.ofReal (f i w)) ≤ ENNReal.ofReal (ε/72)) :
      (∫⁻ w : ℝ,ENNReal.ofReal (∑ i,f i w)) ≤ ENNReal.ofReal (ε/9) := by
    simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hf i _)]
    rw [lintegral_finsetSum Finset.univ (fun i _ => hfmeas i)]
    calc _ ≤ ∑ _ : Fin 8,ENNReal.ofReal (ε/72) := Finset.sum_le_sum (fun i _ => ht i)
         _ = _ := by rw [←ENNReal.ofReal_sum_of_nonneg (fun _ _ => hδ.le)];congr 1;simp;ring
  have hr : (∫⁻ w : ℝ,ENNReal.ofReal (R w)) ≤ ENNReal.ofReal (ε/9) := by
    apply hsum (fun _ _ => sq_nonneg _) (fun i => radial_eight_measurable sharp i m ell hml F μ hμ g)
    intro i
    simpa only [←radial_eight_core sharp i m ell hml,radial_response_core] using hR (sharp,i) m (hnr _) ell hml F
  have hw : (∫⁻ w : ℝ,ENNReal.ofReal (W w)) ≤ ENNReal.ofReal (ε/9) :=
    hsum (fun _ _ => sq_nonneg _) (fun i => weighted_energy_measurable sharp i m ell F μ hμ g)
      (fun i => hW (sharp,i) m (hnw _) ell hml F)
  have hx : (∫⁻ w : ℝ,ENNReal.ofReal (X w)) ≤ ENNReal.ofReal (ε/9) :=
    hX m ((le_max_right _ _).trans ((le_max_right _ _).trans hm)) ell hml F sharp
  have hmW : Measurable (fun w : ℝ => ENNReal.ofReal (W w)) := by
    simp_rw [W,ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    exact Finset.measurable_sum _ (fun i _ => weighted_energy_measurable sharp i m ell F μ hμ g)
  have hmX : Measurable (fun w : ℝ => ENNReal.ofReal (X w)) := by
    simp_rw [X,ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    exact Finset.measurable_sum _ (fun i _ => cross_energy_measurable sharp i m ell F μ hμ g)
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (R w)+
        ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (W w)+ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (X w) := by
      apply lintegral_mono
      intro w
      apply (ENNReal.ofReal_le_ofReal (vector_bound sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)).trans
      change ENNReal.ofReal (3*R w+3*W w+3*X w) ≤ _
      rw [ENNReal.ofReal_add (by dsimp [R,W];positivity) (by dsimp [X];positivity),
        ENNReal.ofReal_add (by dsimp [R];positivity) (by dsimp [W];positivity),
        ENNReal.ofReal_mul (q := R w) (by norm_num : (0:ℝ) ≤ 3),
        ENNReal.ofReal_mul (q := W w) (by norm_num : (0:ℝ) ≤ 3),
        ENNReal.ofReal_mul (q := X w) (by norm_num : (0:ℝ) ≤ 3)]
    _ = ENNReal.ofReal (3:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (R w))+
        ENNReal.ofReal (3:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (W w))+
        ENNReal.ofReal (3:ℝ)*(∫⁻ w : ℝ,ENNReal.ofReal (X w)) := by
      rw [lintegral_add_right _ (hmX.const_mul _),lintegral_add_right _ (hmW.const_mul _)]
      simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/9)+ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/9)+
        ENNReal.ofReal (3:ℝ)*ENNReal.ofReal (ε/9) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3),←ENNReal.ofReal_add (by positivity) (by positivity),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

private theorem gram_bound {ι : Type*} [Fintype ι] (p q : ι → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤ (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (𝕜 := ℂ) (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem pair_square (q v : Column) :
    ‖∑ mu : Fin 8,sourcePair (q mu) ((sourceTime 0:ℂ) • inverseVolumeAction (v mu))‖^2 ≤
      ((sourceTime 0)^2*jointCoframe q)*(columnNorm v/25) := by
  have hp (p f : QuantumTest) : sourcePair p ((sourceTime 0:ℂ) • inverseVolumeAction f)=
      (sourceTime 0:ℂ)*sourcePair (inverseVolumeAction p) f := by
    rw [show sourcePair p ((sourceTime 0:ℂ) • inverseVolumeAction f)=
        (sourceTime 0:ℂ)*sourcePair p (inverseVolumeAction f) by simp only [sourcePair,map_smul,inner_smul_right]]
    congr 1
    exact multiply_pair _ _ _ _
  rw [show (∑ mu : Fin 8,sourcePair (q mu) ((sourceTime 0:ℂ) • inverseVolumeAction (v mu)))=
      (sourceTime 0:ℂ)*(∑ mu : Fin 8,sourcePair (inverseVolumeAction (q mu)) (v mu)) by simp only [hp,Finset.mul_sum]]
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hf : 25*(∑ mu : Fin 8,‖embed (inverseVolumeAction (q mu))‖^2) ≤ jointCoframe q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun mu _ => SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction (q mu)))
  have he : 0 ≤ columnNorm v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have h := gram_bound (fun mu => inverseVolumeAction (q mu)) v
  have h0 := mul_le_mul_of_nonneg_left h (sq_nonneg (sourceTime 0))
  have hf0 := mul_le_mul_of_nonneg_left hf (mul_nonneg (sq_nonneg (sourceTime 0)) he)
  change _ ≤ ((sourceTime 0)^2*jointCoframe q)*(columnNorm v/25)
  change _ ≤ (sourceTime 0)^2*((∑ mu : Fin 8,‖embed (inverseVolumeAction (q mu))‖^2)*columnNorm v) at h0
  nlinarith only [h0,hf0]

private theorem young_square (a p e η : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) (hη : 0<η)
    (hs : a^2 ≤ p*e) : a ≤ η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0 ≤ η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]

private theorem coframe_nonnegative (q : Column) : 0 ≤ jointCoframe q :=
  Finset.sum_nonneg (fun mu _ => (SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction (q mu))).trans'
    (mul_nonneg (by norm_num) (sq_nonneg _)))

def radialEnergy (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ := columnNorm
  (responseVector sharp m ell F z hz (SourceClockYukawaRadialMixedBudget.radiusSource g))

/-- The original positive coframe slot pays the full eight-component radial zero-order word. -/
theorem actual_joint_radial_zero_pair_price (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    ‖∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu) (paidRadialWord sharp m ell F z hz g mu)‖ ≤
      η*((sourceTime 0)^2*jointCoframe (jointState sharp m ell F z hz g))+radialEnergy sharp m ell F z hz g/(100*η) := by
  let q := jointState sharp m ell F z hz g
  let v := responseVector sharp m ell F z hz (SourceClockYukawaRadialMixedBudget.radiusSource g)
  have hp : 0 ≤ (sourceTime 0)^2*jointCoframe q := mul_nonneg (sq_nonneg _) (coframe_nonnegative q)
  have he : 0 ≤ columnNorm v/25 := div_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by norm_num)
  have h := young_square _ _ _ η hp he hη (pair_square q v)
  exact h.trans_eq (by dsimp only [q,v,radialEnergy];ring)

/-- The measurable radial response is generated by the same three actual source operators. -/
theorem actual_joint_radial_energy_measurable (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal (radialEnergy sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') g)) :=
  vector_energy_measurable sharp m ell hml F μ hμ (SourceClockYukawaRadialMixedBudget.radiusSource g)

/-- All three radial zero-order responses have one full-frequency cutoff before every F and both sharp branches. -/
theorem actual_joint_radial_energy_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell → ∀ F : Index,∀ sharp : Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (radialEnergy sharp m ell F (line μ w)
        (by simpa only [line_im] using hμ.ne') g)) ≤ ENNReal.ofReal ε :=
  vector_energy_tail μ hμ (SourceClockYukawaRadialMixedBudget.radiusSource g)

end LowEnergy.SourceClockYukawaJointRadialZeroBudget
