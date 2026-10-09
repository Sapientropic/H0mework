import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockRadiusAffineCutoff
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockRadiusResponseNativeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiRadiusResponseNativeBudget
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourceScalarPositiveBulkWard
open SourcePhysicalKineticSquare SourceClockReflectedForm SourceHamiltonianVolume SourceCoframeVolume GaussFockWeights
open SourceClockYukawaCubicCurrent SourceClockRadiusResponseAffine SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceLocalizedInverseFormPayment PositiveScalarCoefficientDecay SourceRelativePowerTail SourceRetardedForcingTail
open FullYSourceResolventGraphSplice SourceResolventBandLimit FullYSourceTimeFamilyGraph FullYSourceCutoffTimeGraph
open SourceFamilyHilbert SourceFamilyOperator FullYSourceFiniteTimeIntegral MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
attribute [local irreducible] resolventCore finiteResolvent
private theorem center_nonnegative : 0 ≤ centerPrice := by unfold centerPrice;positivity
private theorem scale_one : 1 ≤ scalePrice := by unfold scalePrice;linarith only [center_nonnegative]
private theorem scale_two : 2 ≤ scalePrice := by unfold scalePrice;linarith only [center_nonnegative]
private theorem scale_positive : 0   <   scalePrice := lt_of_lt_of_le zero_lt_one scale_one

private theorem radius_lower (x : SourceCoordinateSlice) : 1 ≤ affineRadius x := by
  have h : affineRadius x^2=1+‖scalarField x‖^2/4 := Real.sq_sqrt (by positivity)
  have hp : 0 ≤ affineRadius x := Real.sqrt_nonneg _
  nlinarith only [h,hp,sq_nonneg ‖scalarField x‖]
private theorem affine_positive (x : SourceCoordinateSlice) : 0   <   affineRadius x := lt_of_lt_of_le zero_lt_one (radius_lower x)

private def scaledProfile (x : SourceCoordinateSlice) : ℝ := 1-reciprocal x/scalePrice
private def errorProfile (n : ℕ) (x : SourceCoordinateSlice) : ℝ :=
  affineRadius x*((1-reciprocal x)^(n+1)-(1-(affineRadius x)⁻¹)^(n+1))
private def boundaryProfile (n : ℕ) (x : SourceCoordinateSlice) : ℝ :=
  (n+1:ℝ)*(reciprocal x/scalePrice)*scaledProfile x^n

private theorem profile_nonnegative (x : SourceCoordinateSlice) : 0 ≤ scaledProfile x := by
  have hs : reciprocal x ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius x)
  have hi : reciprocal x/scalePrice ≤ 1 := (div_le_one scale_positive).mpr (hs.trans scale_one)
  exact sub_nonneg.mpr hi
private theorem profile_le_one (x : SourceCoordinateSlice) : scaledProfile x ≤ 1 := by
  have hs : 0 ≤ reciprocal x := inv_nonneg.mpr (radius_pos x).le
  exact sub_le_self _ (div_nonneg hs scale_positive.le)
private theorem boundary_nonnegative (n : ℕ) (x : SourceCoordinateSlice) : 0 ≤ boundaryProfile n x := by
  unfold boundaryProfile
  exact mul_nonneg (mul_nonneg (by positivity) (div_nonneg (inv_nonneg.mpr (radius_pos x).le) scale_positive.le))
    (pow_nonneg (profile_nonnegative x) n)

private theorem error_profile_bound (n : ℕ) (x : SourceCoordinateSlice) :
    |errorProfile n x| ≤ (centerPrice*scalePrice)*boundaryProfile n x := by
  have hr := radius_pos x
  have hp := affine_positive x
  have hs : 0 ≤ reciprocal x := inv_nonneg.mpr hr.le
  have hs1 : reciprocal x ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius x)
  have ht : 0 ≤ (affineRadius x)⁻¹ := inv_nonneg.mpr hp.le
  have ht1 : (affineRadius x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (radius_lower x)
  have hd := original_radius_center_bound x
  have hle : affineRadius x ≤ scalePrice*radius x := by
    have hh := (abs_le.mp hd).1
    unfold centerDifference at hh
    have hm := mul_le_mul_of_nonneg_left (one_le_radius x) center_nonnegative
    unfold scalePrice
    nlinarith only [hh,hm,hr]
  have hsK : reciprocal x/scalePrice ≤ (affineRadius x)⁻¹ := by
    calc
      _=1/(scalePrice*radius x) := by unfold reciprocal;field_simp
      _ ≤ (affineRadius x)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hp hle
  have hq0 : 0 ≤ 1-reciprocal x := sub_nonneg.mpr hs1
  have hq1 : 0 ≤ 1-(affineRadius x)⁻¹ := sub_nonneg.mpr ht1
  have hqm : max |1-reciprocal x| |1-(affineRadius x)⁻¹| ≤ scaledProfile x := by
    rw [abs_of_nonneg hq0,abs_of_nonneg hq1]
    apply max_le
    · have hh : reciprocal x/scalePrice ≤ reciprocal x := div_le_self hs scale_one
      exact sub_le_sub_left hh 1
    · exact sub_le_sub_left hsK 1
  have hpow := abs_pow_sub_pow_le (a:=1-reciprocal x) (b:=1-(affineRadius x)⁻¹) (n:=n+1)
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] at hpow
  have hcoef : affineRadius x*|(1-reciprocal x)-(1-(affineRadius x)⁻¹)| ≤ centerPrice*reciprocal x := by
    have he : affineRadius x*((1-reciprocal x)-(1-(affineRadius x)⁻¹))=(radius x-affineRadius x)*reciprocal x := by
      unfold reciprocal
      field_simp [hr.ne',hp.ne']
      ring
    calc
      _=|affineRadius x*((1-reciprocal x)-(1-(affineRadius x)⁻¹))| := by rw [abs_mul,abs_of_pos hp]
      _=|radius x-affineRadius x| *reciprocal x := by rw [he,abs_mul,abs_of_nonneg hs]
      _ ≤ _ := mul_le_mul_of_nonneg_right hd hs
  unfold errorProfile boundaryProfile
  rw [abs_mul,abs_of_pos hp]
  calc
    _ ≤ affineRadius x*(|(1-reciprocal x)-(1-(affineRadius x)⁻¹)| *(n+1:ℝ)*
      max |1-reciprocal x| |1-(affineRadius x)⁻¹|^n) := mul_le_mul_of_nonneg_left hpow hp.le
    _ = (affineRadius x*|(1-reciprocal x)-(1-(affineRadius x)⁻¹)|)*(n+1:ℝ)*
        max |1-reciprocal x| |1-(affineRadius x)⁻¹|^n := by ring
    _ ≤ (centerPrice*reciprocal x)*(n+1:ℝ)*scaledProfile x^n :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (by positivity))
        (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hqm n)
        (pow_nonneg (le_max_of_le_left (abs_nonneg _)) n)
        (mul_nonneg (mul_nonneg center_nonnegative hs) (by positivity))
    _ = _ := by field_simp [scale_positive.ne']


private theorem profile_positive (x : SourceCoordinateSlice) : 0   <   scaledProfile x := by
  have hs:reciprocal x ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius x)
  unfold scaledProfile
  apply sub_pos.mpr
  apply (div_lt_one scale_positive).mpr
  linarith only [hs,scale_two]
private theorem boundary_positive (n : ℕ) (x : SourceCoordinateSlice) : 0   <   boundaryProfile n x := by
  unfold boundaryProfile
  have hp:=profile_positive x
  have hs:=scale_positive
  have hr:=radius_pos x
  have hi:0 < reciprocal x := inv_pos.mpr hr
  positivity
private theorem affine_inverse_smooth : ContDiff ℝ ∞ (fun x : SourceCoordinateSlice=>(affineRadius x)⁻¹) :=
  affine_radius_smooth.inv (fun x=>(affine_positive x).ne')
private theorem profile_smooth : ContDiff ℝ ∞ scaledProfile :=
  contDiff_const.sub (reciprocal_smooth.div_const _)
private theorem error_smooth (n : ℕ) : ContDiff ℝ ∞ (errorProfile n) :=
  affine_radius_smooth.mul (((contDiff_const.sub reciprocal_smooth).pow _).sub
    ((contDiff_const.sub affine_inverse_smooth).pow _))
private theorem boundary_smooth (n : ℕ) : ContDiff ℝ ∞ (boundaryProfile n) :=
  (contDiff_const.mul (reciprocal_smooth.div_const _)).mul (profile_smooth.pow _)
private theorem radius_affine_bound (x : SourceCoordinateSlice) : radius x ≤ scalePrice*affineRadius x := by
  have h:=original_radius_center_bound x
  have hp:=radius_lower x
  have hc:=mul_le_mul_of_nonneg_left hp center_nonnegative
  have hh:radius x-affineRadius x ≤ centerPrice := (abs_le.mp h).2
  unfold scalePrice
  nlinarith only [hh,hc,hp]
private theorem affine_radius_bound (x : SourceCoordinateSlice) : affineRadius x ≤ scalePrice*radius x := by
  have h:=original_radius_center_bound x
  have hp:=one_le_radius x
  have hc:=mul_le_mul_of_nonneg_left hp center_nonnegative
  have hh:-centerPrice ≤ radius x-affineRadius x := (abs_le.mp h).1
  unfold scalePrice
  nlinarith only [hh,hc,hp]
private theorem phi_profile_le (x : SourceCoordinateSlice) : 0 ≤ 1-(affineRadius x)⁻¹ ∧
    1-(affineRadius x)⁻¹ ≤ scaledProfile x := by
  constructor
  · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ (radius_lower x))
  · have h:reciprocal x/scalePrice ≤ (affineRadius x)⁻¹ := by
      calc _=1/(scalePrice*radius x) := by unfold reciprocal;field_simp
           _ ≤ (affineRadius x)⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le (affine_positive x) (affine_radius_bound x)
    exact sub_le_sub_left h 1

private def phiBoundaryRatio (n : ℕ) (x : SourceCoordinateSlice) : ℝ :=
  (scalePrice*radius x/affineRadius x)*((1-(affineRadius x)⁻¹)/scaledProfile x)^n
private theorem phi_boundary_ratio_smooth (n : ℕ) : ContDiff ℝ ∞ (phiBoundaryRatio n) :=
  ((contDiff_const.mul radius_smooth).div affine_radius_smooth (fun x=>(affine_positive x).ne')).mul
    (((contDiff_const.sub affine_inverse_smooth).div profile_smooth (fun x=>(profile_positive x).ne')).pow n)
private theorem phi_boundary_ratio_bound (n : ℕ) (x : SourceCoordinateSlice) :
    |phiBoundaryRatio n x| ≤ scalePrice^2 := by
  have hq:=phi_profile_le x
  have hp:=profile_positive x
  have hq0:0 ≤ (1-(affineRadius x)⁻¹)/scaledProfile x := div_nonneg hq.1 hp.le
  have hq1:(1-(affineRadius x)⁻¹)/scaledProfile x ≤ 1 := (div_le_one hp).mpr hq.2
  have hpow:((1-(affineRadius x)⁻¹)/scaledProfile x)^n ≤ 1 := pow_le_one₀ hq0 hq1
  have hpre:scalePrice*radius x/affineRadius x ≤ scalePrice^2 := by
    apply (div_le_iff₀ (affine_positive x)).mpr
    have h:=mul_le_mul_of_nonneg_left (radius_affine_bound x) scale_positive.le
    nlinarith only [h]
  have hpre0:0 ≤ scalePrice*radius x/affineRadius x :=
    div_nonneg (mul_nonneg scale_positive.le (radius_pos x).le) (affine_positive x).le
  rw [phiBoundaryRatio,abs_of_nonneg (mul_nonneg hpre0 (pow_nonneg hq0 n))]
  exact (mul_le_mul_of_nonneg_left hpow hpre0).trans (by simpa only [mul_one] using hpre)
private def thetaErrorRatio (n : ℕ) (x : SourceCoordinateSlice) : ℝ :=
  (affineRadius x)⁻¹*errorProfile n x/boundaryProfile n x
private theorem theta_error_ratio_smooth (n : ℕ) : ContDiff ℝ ∞ (thetaErrorRatio n) :=
  (affine_inverse_smooth.mul (error_smooth n)).div (boundary_smooth n) (fun x=>(boundary_positive n x).ne')
private theorem theta_error_ratio_bound (n : ℕ) (x : SourceCoordinateSlice) :
    |thetaErrorRatio n x| ≤ centerPrice*scalePrice := by
  rw [thetaErrorRatio,abs_div,abs_mul,abs_of_pos (boundary_positive n x),
    abs_inv,abs_of_pos (affine_positive x)]
  have hi:0 ≤ (affineRadius x)⁻¹ := inv_nonneg.mpr (affine_positive x).le
  have hi1:(affineRadius x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (radius_lower x)
  have he:=mul_le_mul_of_nonneg_left (error_profile_bound n x) hi
  apply (div_le_iff₀ (boundary_positive n x)).mpr
  have hp:0 ≤ centerPrice*scalePrice*boundaryProfile n x :=
    mul_nonneg (mul_nonneg center_nonnegative scale_positive.le) (boundary_nonnegative n x)
  have hcap:=mul_le_mul_of_nonneg_right hi1 hp
  exact he.trans (by nlinarith only [hcap])

private def scalarFiber (c : SourceCoordinateSlice → ℝ) (x : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (c x:ℂ) • ContinuousLinearMap.id ℂ FockFiber
private theorem scalar_fiber_smooth (c : SourceCoordinateSlice → ℝ) (hc:ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (scalarFiber c) := (Complex.ofRealCLM.contDiff.comp hc).smul contDiff_const
private theorem scalar_commutes (c : SourceCoordinateSlice → ℝ) (x : physicalChart) (w : ℕ → ℂ) :
    Commute (weight w) (scalarFiber c x) := (Commute.one_right _).smul_right _
private theorem scalar_bound (c : SourceCoordinateSlice → ℝ) (C : ℝ) (hb:∀x,|c x| ≤ C)
    (x : physicalChart) (f : FockFiber) : ‖scalarFiber c x f‖ ≤ C*‖f‖ := by
  change ‖(c x:ℂ) • f‖ ≤ _
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg f)
private def scalarReader (c : SourceCoordinateSlice → ℝ) (hc:ContDiff ℝ ∞ c) (C : ℝ)
    (hC:0 ≤ C) (hb:∀x,|c x| ≤ C) : Op := GaussBoundedMultiplier.extension (scalarFiber c)
      (fun _=>(scalar_fiber_smooth c hc).contDiffAt) (scalar_commutes c) C hC (scalar_bound c C hb)
private theorem scalar_reader_norm (c : SourceCoordinateSlice → ℝ) (hc:ContDiff ℝ ∞ c) (C : ℝ)
    (hC:0 ≤ C) (hb:∀x,|c x| ≤ C) : ‖scalarReader c hc C hC hb‖ ≤ C := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem scalar_reader_core (c : SourceCoordinateSlice → ℝ) (hc:ContDiff ℝ ∞ c) (C : ℝ)
    (hC:0 ≤ C) (hb:∀x,|c x| ≤ C) (f : QuantumTest) :
    scalarReader c hc C hC hb (embed f)=embed (multiply c (fun _=>hc.contDiffAt) f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private def phiBoundaryReader (n : ℕ) : Op := scalarReader (phiBoundaryRatio n) (phi_boundary_ratio_smooth n)
  (scalePrice^2) (sq_nonneg _) (phi_boundary_ratio_bound n)
private def thetaErrorReader (n : ℕ) : Op := scalarReader (thetaErrorRatio n) (theta_error_ratio_smooth n)
  (centerPrice*scalePrice) (mul_nonneg center_nonnegative scale_positive.le) (theta_error_ratio_bound n)
def phiBoundary (n : ℕ) : Op := phiBoundaryReader n*scaledBoundary n
private def thetaError (n : ℕ) : Op := thetaErrorReader n*scaledBoundary n
private def phiThetaBounded (m ell : ℕ) : Op := relativeTail m ell-thetaError m+thetaError ell
private def phiBoundaryCore (n : ℕ) : End := (n+1:ℂ) • (phiInverseAction*(1-phiInverseAction)^n)
private def scaledInverseCore : End := ((scalePrice⁻¹:ℝ):ℂ) • inverseAction
private def scaledComplementCore : End := 1-scaledInverseCore
private def scaledBoundaryCore (n : ℕ) : End := (n+1:ℂ) • (scaledInverseCore*scaledComplementCore^n)

private theorem scaled_inverse_core (f : QuantumTest) : scaledInverse (embed f)=embed (scaledInverseCore f) := by
  simp only [scaledInverse,scaledInverseCore,smul_apply,LinearMap.smul_apply,inverse_core,map_smul]
private theorem scaled_complement_core (n : ℕ) (f : QuantumTest) :
    (scaledComplement^n) (embed f)=embed ((scaledComplementCore^n) f) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change (scaledComplement^n) (embed f)-scaledInverse ((scaledComplement^n) (embed f))=
      embed ((scaledComplementCore^n) f-scaledInverseCore ((scaledComplementCore^n) f))
    rw [ih,scaled_inverse_core,map_sub]
private theorem scaled_boundary_core (n : ℕ) (f : QuantumTest) :
    scaledBoundary n (embed f)=embed (scaledBoundaryCore n f) := by
  simp only [scaledBoundary,scaledBoundaryCore,smul_apply,mul_apply_eq_comp,LinearMap.smul_apply,
    Module.End.mul_apply,scaled_complement_core,scaled_inverse_core,map_smul]
private theorem scaled_complement_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    (scaledComplementCore^n) f x=(scaledProfile x:ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((scaledComplementCore^n) f) x-((scalePrice⁻¹:ℝ):ℂ) •
      ((reciprocal x:ℂ) • (((scaledComplementCore^n) f) x))=_
    rw [ih,pow_succ',mul_smul]
    unfold scaledProfile
    push_cast
    simp only [div_eq_mul_inv]
    module
private theorem scaled_boundary_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    scaledBoundaryCore n f x=(boundaryProfile n x:ℂ) • f x := by
  change (n+1:ℂ) • (((scalePrice⁻¹:ℝ):ℂ) • ((reciprocal x:ℂ) • (((scaledComplementCore^n) f) x)))=_
  rw [scaled_complement_point]
  unfold boundaryProfile
  push_cast
  simp only [smul_smul,div_eq_mul_inv]
  congr 1
  ring

/-- The original and affine radial powers are compared on the same full Number-density carrier. -/

private theorem inverse_phi_core (f : QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem inverse_phi_norm : ‖phiInverseBounded‖ ≤ 1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem phi_power_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    ((1-phiInverseAction)^n) f x=((1-(affineRadius x)⁻¹:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((1-phiInverseAction)^n) f x-(((affineRadius x)⁻¹:ℝ):ℂ) • (((1-phiInverseAction)^n) f x)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module
private theorem phi_boundary_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    phiBoundaryCore n f x=(((n+1:ℝ)*(affineRadius x)⁻¹*(1-(affineRadius x)⁻¹)^n:ℝ):ℂ) • f x := by
  change (n+1:ℂ) • ((((affineRadius x)⁻¹:ℝ):ℂ) • (((1-phiInverseAction)^n) f x))=_
  rw [phi_power_point]
  push_cast
  simp only [smul_smul]
  congr 1
  ring
private theorem boundary_ratio_return (n : ℕ) (x : SourceCoordinateSlice) :
    phiBoundaryRatio n x*boundaryProfile n x=(n+1:ℝ)*(affineRadius x)⁻¹*(1-(affineRadius x)⁻¹)^n := by
  unfold phiBoundaryRatio boundaryProfile
  rw [div_pow]
  unfold reciprocal
  field_simp [(profile_positive x).ne',(affine_positive x).ne',(radius_pos x).ne',scale_positive.ne']
private theorem phi_boundary_core (n : ℕ) (f : QuantumTest) : phiBoundary n (embed f)=embed (phiBoundaryCore n f) := by
  rw [phiBoundary,mul_apply_eq_comp,scaled_boundary_core]
  unfold phiBoundaryReader
  rw [scalar_reader_core]
  congr 1
  apply DFunLike.ext
  intro x
  change (phiBoundaryRatio n x:ℂ) • (scaledBoundaryCore n f x)=phiBoundaryCore n f x
  rw [scaled_boundary_point,phi_boundary_point,smul_smul,←Complex.ofReal_mul,boundary_ratio_return]
private theorem error_ratio_return (n : ℕ) (x : SourceCoordinateSlice) :
    thetaErrorRatio n x*boundaryProfile n x=(1-reciprocal x)^(n+1)-(1-(affineRadius x)⁻¹)^(n+1) := by
  unfold thetaErrorRatio errorProfile
  field_simp [(boundary_positive n x).ne',(affine_positive x).ne']
private theorem old_power_point (n : ℕ) (f : QuantumTest) (x : SourceCoordinateSlice) :
    ((1-inverseAction)^n) f x=((1-reciprocal x:ℝ):ℂ)^n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change ((1-inverseAction)^n) f x-(reciprocal x:ℂ) • (((1-inverseAction)^n) f x)=_
    rw [ih,pow_succ',mul_smul]
    push_cast
    module
private theorem error_core (n : ℕ) (f : QuantumTest) : thetaError n (embed f)=
    embed (((1-inverseAction)^(n+1)-(1-phiInverseAction)^(n+1)) f) := by
  rw [thetaError,mul_apply_eq_comp,scaled_boundary_core]
  unfold thetaErrorReader
  rw [scalar_reader_core]
  congr 1
  apply DFunLike.ext
  intro x
  change (thetaErrorRatio n x:ℂ) • (scaledBoundaryCore n f x)=
    ((1-inverseAction)^(n+1)) f x-((1-phiInverseAction)^(n+1)) f x
  rw [scaled_boundary_point,old_power_point,phi_power_point,smul_smul,←Complex.ofReal_mul,error_ratio_return]
  push_cast
  module
private theorem phi_theta_core (m ell : ℕ) (f : QuantumTest) :
    phiThetaBounded m ell (embed f)=embed (phiThetaAction m ell f) := by
  simp only [phiThetaBounded,sub_apply,add_apply,error_core,theta_core]
  rw [←map_sub,←map_add]
  congr 1
  unfold phiThetaAction SourceMixedNativeReturn.thetaAction
  simp only [LinearMap.sub_apply]
  abel

private theorem phi_boundary_bound (n : ℕ) (x : H) :
    ‖phiBoundary n x‖^2 ≤ scalePrice^4*‖scaledBoundary n x‖^2 := by
  have hn:‖phiBoundaryReader n‖ ≤ scalePrice^2 := scalar_reader_norm _ _ _ _ _
  have h:=((phiBoundaryReader n).le_opNorm (scaledBoundary n x)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hs:=pow_le_pow_left₀ (norm_nonneg _) h 2
  have hpow:(scalePrice^2)^2=scalePrice^4 := by ring
  rw [mul_pow,hpow] at hs
  exact hs
private theorem theta_error_bound (n : ℕ) (x : H) :
    ‖thetaError n x‖^2 ≤ (centerPrice*scalePrice)^2*‖scaledBoundary n x‖^2 := by
  have hn:‖thetaErrorReader n‖ ≤ centerPrice*scalePrice := scalar_reader_norm _ _ _ _ _
  have h:=((thetaErrorReader n).le_opNorm (scaledBoundary n x)).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hs:=pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [thetaError,mul_apply_eq_comp,mul_pow] using hs
private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0   <   μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem finite_star (F : Index) (z : ℂ) :
    finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=
    (Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced : Bool) (μ : ℝ) (hμ : 0   <   μ) (F : Index) :
    Continuous (fun w : ℝ=>finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  · have he:(fun w : ℝ=>finiteResolvent F (actualFrequency true μ w))=
        (fun w : ℝ=>(finiteResolvent F (line μ w)).adjoint) := by funext w;exact finite_star F _
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F))

private theorem reader_integral_bound (A : Op) (C : ℝ) (hC:0 ≤ C) (n : ℕ)
    (hA:∀x,‖A x‖^2 ≤ C*‖scaledBoundary n x‖^2) (advanced : Bool) (μ : ℝ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖A (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal C*(∫⁻ w : ℝ,ENNReal.ofReal (‖scaledBoundary n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) := by
  calc _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal (‖scaledBoundary n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2) := by
         apply lintegral_mono
         intro w
         dsimp only
         rw [←ENNReal.ofReal_mul hC]
         exact ENNReal.ofReal_le_ofReal (hA _)
       _=_ := by rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
private theorem phi_boundary_tail (μ : ℝ) (hμ : 0   <   μ) (g : H) :
    ∀ε:ℝ,0   <   ε→∃N:ℕ,∀n,N ≤ n→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖phiBoundary n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hK:0   <   scalePrice^4 := pow_pos scale_positive _
  obtain ⟨N,hN⟩:=actual_scaled_boundary_common_tail μ hμ g (ε/scalePrice^4) (by positivity)
  refine ⟨N,fun n hn=>?_⟩
  filter_upwards [hN n hn] with F hF
  intro advanced
  have h:=(reader_integral_bound (phiBoundary n) (scalePrice^4) hK.le n (phi_boundary_bound n) advanced μ F g).trans
    (mul_le_mul le_rfl (hF advanced) zero_le zero_le)
  have he:ENNReal.ofReal (scalePrice^4)*ENNReal.ofReal (ε/scalePrice^4)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hK.le]
    congr 1
    field_simp [scale_positive.ne']
  exact h.trans_eq he
private theorem theta_error_tail (μ : ℝ) (hμ : 0   <   μ) (g : H) :
    ∀ε:ℝ,0   <   ε→∃N:ℕ,∀n,N ≤ n→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖thetaError n (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let C:=1+(centerPrice*scalePrice)^2
  have hC:0   <   C := by dsimp [C];positivity
  obtain ⟨N,hN⟩:=actual_scaled_boundary_common_tail μ hμ g (ε/C) (by positivity)
  refine ⟨N,fun n hn=>?_⟩
  filter_upwards [hN n hn] with F hF
  intro advanced
  have hb(x:H):‖thetaError n x‖^2 ≤ C*‖scaledBoundary n x‖^2 :=
    (theta_error_bound n x).trans (mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (sq_nonneg _))
  have h:=(reader_integral_bound (thetaError n) C hC.le n hb advanced μ F g).trans
    (mul_le_mul le_rfl (hF advanced) zero_le zero_le)
  have he:ENNReal.ofReal C*ENNReal.ofReal (ε/C)=ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hC.le]
    congr 1
    field_simp
  exact h.trans_eq he

private theorem frequency_norm (advanced : Bool) (μ : ℝ) (hμ : 0  <  μ) (F : Index) (g : H) (w : ℝ) :
    ‖finiteResolvent F (actualFrequency advanced μ w) g‖=‖finiteResolvent F (line μ w) g‖ := by
  cases advanced
  · rfl
  · exact SourceInverseSourceLeg.actual_conjugate_leg_norm F (line μ w)
      (by simpa only [line_im] using hμ.ne') g
private theorem whole_memLp (advanced : Bool) (μ : ℝ) (hμ : 0  <  μ) (F : Index) (g : H) :
    MemLp (fun w : ℝ=>finiteResolvent F (actualFrequency advanced μ w) g) 2 MeasureTheory.volume := by
  apply (memLp_two_iff_integrable_sq_norm
    (((frequency_continuous advanced μ hμ F).clm_apply continuous_const).aestronglyMeasurable)).mpr
  have hi:=SourceActualResolventEnergy.actual_square_integrable F μ hμ g
  simp only [frequency_norm advanced μ hμ F g]
  simpa only [line,mul_comm (μ:ℂ) Complex.I] using hi
private abbrev L2H := Lp H 2 (MeasureTheory.volume:Measure ℝ)
private def readFamily (A : Op) (f : Family L2H sourceFilter) : Family L2H sourceFilter :=
  act sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 MeasureTheory.volume)) f
private theorem read_family_norm (A : Op) (f : Family L2H sourceFilter) :
    ‖readFamily A f‖=‖familyReader (MeasureTheory.volume:Measure ℝ) A (f:TimeSpace (MeasureTheory.volume:Measure ℝ))‖ := by
  unfold familyReader
  rw [lift_coe,UniformSpace.Completion.norm_coe]
  rfl
private theorem acted_integral (A : Op) (advanced : Bool) (μ : ℝ) (hμ : 0  <  μ) (F : Index) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (‖A (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))=
      ENNReal.ofReal (‖value (readFamily A (wholeInputFamily advanced μ hμ g)) F‖^2) := by
  let I:L2H:=value (wholeInputFamily advanced μ hμ g) F
  have hR:(fun w : ℝ=>I w)=ᵐ[MeasureTheory.volume]
      (fun w : ℝ=>finiteResolvent F (actualFrequency advanced μ w) g) := by
    exact (whole_memLp advanced μ hμ F g).coeFn_toLp
  have he:(fun w=>‖A (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)=ᵐ[MeasureTheory.volume]
      (fun w=>‖value (readFamily A (wholeInputFamily advanced μ hμ g)) F w‖^2) := by
    filter_upwards [A.coeFn_compLpL I,hR] with w hA hI
    change _=‖(A.compLpL 2 MeasureTheory.volume I) w‖^2
    rw [hA,hI]
  have hi:=(square_integrable MeasureTheory.volume (value (readFamily A (wholeInputFamily advanced μ hμ g)) F)).congr he.symm
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _=>sq_nonneg _)),
    integral_congr_ae he,←square_integral]

private theorem old_theta_tail (μ : ℝ) (hμ : 0  <  μ) (g : H) :
    ∀ε:ℝ,0  <  ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  have helper(advanced:Bool):∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
    obtain ⟨N,hN⟩:=time_space_relative_tail MeasureTheory.volume (wholeInputFamily advanced μ hμ g:TimeSpace (MeasureTheory.volume:Measure ℝ))
      (Real.sqrt (ε/2)) (Real.sqrt_pos.mpr (by positivity))
    refine ⟨N,fun m hm ell hml=>?_⟩
    let f:=readFamily (relativeTail m ell) (wholeInputFamily advanced μ hμ g)
    have ht:‖f‖^2  <  ε := by
      have h:=hN m hm ell hml
      rw [←read_family_norm (relativeTail m ell) (wholeInputFamily advanced μ hμ g)] at h
      have hs:Real.sqrt (ε/2)^2=ε/2 := Real.sq_sqrt (by positivity)
      change ‖f‖  <  Real.sqrt (ε/2) at h
      nlinarith only [h,hs,norm_nonneg f,Real.sqrt_nonneg (ε/2)]
    filter_upwards [(square_tendsto sourceFilter f).eventually (gt_mem_nhds ht)] with F hF
    rw [acted_integral (relativeTail m ell) advanced μ hμ F g]
    exact ENNReal.ofReal_le_ofReal hF.le
  obtain ⟨Nf,hf⟩:=helper false
  obtain ⟨Nt,ht⟩:=helper true
  refine ⟨max Nf Nt,fun m hm ell hml=>?_⟩
  filter_upwards [hf m (by omega) ell hml,ht m (by omega) ell hml] with F hF hT
  intro advanced
  cases advanced
  · exact hF
  · exact hT
private theorem three_square (x y z : H) : ‖x-y+z‖^2 ≤ 3*(‖x‖^2+‖y‖^2+‖z‖^2) := by
  have h:=((norm_add_le (x-y) z).trans (add_le_add (norm_sub_le x y) le_rfl))
  have hs:=pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith only [hs,sq_nonneg (‖x‖-‖y‖),sq_nonneg (‖x‖-‖z‖),sq_nonneg (‖y‖-‖z‖)]
private theorem phi_theta_tail (μ : ℝ) (hμ : 0  <  μ) (g : H) :
    ∀ε:ℝ,0  <  ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖phiThetaBounded m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=old_theta_tail μ hμ g (ε/9) (by positivity)
  obtain ⟨N2,h2⟩:=theta_error_tail μ hμ g (ε/9) (by positivity)
  refine ⟨max N1 N2,fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega),h2 ell (by omega)] with F hOld hM hL
  intro advanced
  let X:=fun w:ℝ=>ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)
  let Y:=fun w:ℝ=>ENNReal.ofReal (‖thetaError m (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)
  let Z:=fun w:ℝ=>ENNReal.ofReal (‖thetaError ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)
  have hr:=frequency_continuous advanced μ hμ F
  have my:Measurable Y:=(((thetaError m).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have mz:Measurable Z:=(((thetaError ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  calc _ ≤ ∫⁻ w:ℝ,ENNReal.ofReal 3*(X w+Y w+Z w) := by
         apply lintegral_mono
         intro w
         dsimp only [X,Y,Z]
         rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_add (by positivity) (sq_nonneg _),
           ←ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 3)]
         exact ENNReal.ofReal_le_ofReal (three_square _ _ _)
       _=ENNReal.ofReal 3*((∫⁻w:ℝ,X w)+(∫⁻w:ℝ,Y w)+(∫⁻w:ℝ,Z w)) := by
         rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ mz,lintegral_add_right _ my]
       _ ≤ ENNReal.ofReal 3*(ENNReal.ofReal (ε/9)+ENNReal.ofReal (ε/9)+ENNReal.ofReal (ε/9)) :=
         mul_le_mul le_rfl (add_le_add (add_le_add (hOld advanced) (hM advanced)) (hL advanced)) zero_le zero_le
       _=ENNReal.ofReal ε := by
         rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity),
           ←ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 3)]
         congr 1
         ring

private theorem phi_boundary_difference_tail (μ : ℝ) (hμ : 0  <  μ) (g : H) :
    ∀ε:ℝ,0  <  ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻ w : ℝ,ENNReal.ofReal (‖(phiBoundary ell-phiBoundary m) (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=phi_boundary_tail μ hμ g (ε/4) (by positivity)
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm,hN ell (by omega)] with F hM hL
  intro advanced
  have hr:=frequency_continuous advanced μ hμ F
  have hm0:Measurable (fun w:ℝ=>ENNReal.ofReal (‖phiBoundary m (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)):=
    (((phiBoundary m).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  calc _ ≤ ∫⁻w:ℝ,ENNReal.ofReal 2*(ENNReal.ofReal (‖phiBoundary ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)+
        ENNReal.ofReal (‖phiBoundary m (finiteResolvent F (actualFrequency advanced μ w) g)‖^2)) := by
         apply lintegral_mono
         intro w
         dsimp only
         rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 2)]
         have h:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
           (phiBoundary ell (finiteResolvent F (actualFrequency advanced μ w) g))
           (phiBoundary m (finiteResolvent F (actualFrequency advanced μ w) g))) 2
         apply ENNReal.ofReal_le_ofReal
         change ‖phiBoundary ell _-phiBoundary m _‖^2 ≤ _
         nlinarith only [h,sq_nonneg (‖phiBoundary ell (finiteResolvent F (actualFrequency advanced μ w) g)‖-
           ‖phiBoundary m (finiteResolvent F (actualFrequency advanced μ w) g)‖)]
       _=ENNReal.ofReal 2*((∫⁻w:ℝ,ENNReal.ofReal (‖phiBoundary ell (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))+
         (∫⁻w:ℝ,ENNReal.ofReal (‖phiBoundary m (finiteResolvent F (actualFrequency advanced μ w) g)‖^2))) := by
         rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_add_right _ hm0]
       _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) :=
         mul_le_mul le_rfl (add_le_add (hL advanced) (hM advanced)) zero_le zero_le
       _ ≤ ENNReal.ofReal ε := by
         rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_mul (by norm_num:(0:ℝ) ≤ 2)]
         exact ENNReal.ofReal_le_ofReal (by linarith)

private def phiGradientCore (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) : QuantumTest :=
  (phiBoundaryCore ell-phiBoundaryCore m-phiThetaAction m ell) (resolventCore F z hz (coreEquiv.symm g))-
    phiInverseAction ((phiBoundaryCore ell-phiBoundaryCore m) (resolventCore F z hz (coreEquiv.symm (phiRadiusSource g))))
private def phiGradientInput (m ell : ℕ) (F : Index) (z : ℂ) (g : diagonal.domain) : H :=
  (phiBoundary ell-phiBoundary m-phiThetaBounded m ell) (finiteResolvent F z (g:H))-
    phiInverseBounded ((phiBoundary ell-phiBoundary m) (finiteResolvent F z (phiRadiusSource g:H)))
def phiNativeVector (a : ScalarIndex) (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) : QuantumTest :=
  phiDirectionAction (scalarBasis a) (phiGradientCore m ell F z hz g)
def phiNativeEnergy (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) : ℝ :=
  ∑ a:ScalarIndex,‖embed (phiNativeVector a m ell F z hz g)‖^2
def phiNativeDivergence (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) : QuantumTest :=
  (-Complex.I) • ∑ a:ScalarIndex,Pa a (W (phiNativeVector a m ell F z hz g))
private theorem resolvent_embed (F : Index) (z : ℂ) (hz:z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem gradient_core (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) :
    embed (phiGradientCore m ell F z hz g)=phiGradientInput m ell F z g := by
  have hg:embed (coreEquiv.symm g)=(g:H):=congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hpg:embed (coreEquiv.symm (phiRadiusSource g))=(phiRadiusSource g:H):=
    congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  unfold phiGradientInput phiGradientCore
  simp only [sub_apply,LinearMap.sub_apply,map_sub,←phi_boundary_core,←phi_theta_core,←inverse_phi_core,resolvent_embed,hg,hpg]

/-- The actual first-jet vector descends to the same bounded two-input reader before the source filter. -/
theorem original_phi_native_vector_core (a : ScalarIndex) (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) :
    embed (phiNativeVector a m ell F z hz g)=phiDirectionOperator (scalarBasis a) (phiGradientInput m ell F z g) := by
  unfold phiNativeVector
  rw [←original_phi_direction_core,gradient_core]
private theorem native_three_bound (m ell : ℕ) (F : Index) (z : ℂ) (hz:z.im≠0) (g : diagonal.domain) :
    phiNativeEnergy m ell F z hz g ≤ ‖(phiBoundary ell-phiBoundary m) (finiteResolvent F z (g:H))‖^2+
      ‖phiThetaBounded m ell (finiteResolvent F z (g:H))‖^2+
      ‖(phiBoundary ell-phiBoundary m) (finiteResolvent F z (phiRadiusSource g:H))‖^2 := by
  have hg:=original_phi_gradient_energy (phiGradientInput m ell F z g)
  have he:phiNativeEnergy m ell F z hz g ≤ (1/4:ℝ)*‖phiGradientInput m ell F z g‖^2 := by
    simp only [phiNativeEnergy,original_phi_native_vector_core]
    nlinarith only [hg,sq_nonneg ‖phiInverseBounded (phiGradientInput m ell F z g)‖]
  let x:=(phiBoundary ell-phiBoundary m) (finiteResolvent F z (g:H))
  let y:=phiThetaBounded m ell (finiteResolvent F z (g:H))
  let t:=(phiBoundary ell-phiBoundary m) (finiteResolvent F z (phiRadiusSource g:H))
  have hi:‖phiInverseBounded t‖ ≤ ‖t‖ := ((phiInverseBounded.le_opNorm t).trans
    ((mul_le_mul_of_nonneg_right inverse_phi_norm (norm_nonneg t)).trans_eq (one_mul _)))
  have hi2:=pow_le_pow_left₀ (norm_nonneg _) hi 2
  have hs:=three_square x y (-phiInverseBounded t)
  rw [norm_neg] at hs
  rw [←sub_eq_add_neg] at hs
  have hid:phiGradientInput m ell F z g=x-y-phiInverseBounded t := by
    unfold phiGradientInput
    simp only [sub_apply,x,y,t]
  rw [hid] at he
  change phiNativeEnergy m ell F z hz g ≤ ‖x‖^2+‖y‖^2+‖t‖^2
  nlinarith only [he,hs,hi2,sq_nonneg ‖x‖,sq_nonneg ‖y‖,sq_nonneg ‖t‖]

theorem actual_phi_native_energy_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ:0  <  μ) (g:diagonal.domain) (advanced:Bool) :
    Measurable (fun w:ℝ=>ENNReal.ofReal (phiNativeEnergy m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)) := by
  simp only [phiNativeEnergy,original_phi_native_vector_core]
  have hr:=frequency_continuous advanced μ hμ F
  have hg:Continuous (fun w:ℝ=>phiGradientInput m ell F (actualFrequency advanced μ w) g) := by
    unfold phiGradientInput
    exact (((phiBoundary ell-phiBoundary m-phiThetaBounded m ell).continuous.comp (hr.clm_apply continuous_const)).sub
      (phiInverseBounded.continuous.comp (((phiBoundary ell-phiBoundary m).continuous.comp (hr.clm_apply continuous_const)))))
  exact (Finset.measurable_sum Finset.univ (fun a _=>((phiDirectionOperator (scalarBasis a)).continuous.comp hg).norm.pow 2 |>.measurable)).ennreal_ofReal

theorem actual_phi_native_energy_common_tail (μ:ℝ) (hμ:0  <  μ) (g:diagonal.domain) :
    ∀ε:ℝ,0  <  ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (phiNativeEnergy m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N1,h1⟩:=phi_boundary_difference_tail μ hμ (g:H) (ε/3) (by positivity)
  obtain ⟨N2,h2⟩:=phi_theta_tail μ hμ (g:H) (ε/3) (by positivity)
  obtain ⟨N3,h3⟩:=phi_boundary_difference_tail μ hμ (phiRadiusSource g:H) (ε/3) (by positivity)
  refine ⟨max N1 (max N2 N3),fun m hm ell hml=>?_⟩
  filter_upwards [h1 m (by omega) ell hml,h2 m (by omega) ell hml,h3 m (by omega) ell hml] with F hX hY hZ
  intro advanced
  let X:=fun w:ℝ=>ENNReal.ofReal (‖(phiBoundary ell-phiBoundary m) (finiteResolvent F (actualFrequency advanced μ w) (g:H))‖^2)
  let Y:=fun w:ℝ=>ENNReal.ofReal (‖phiThetaBounded m ell (finiteResolvent F (actualFrequency advanced μ w) (g:H))‖^2)
  let Z:=fun w:ℝ=>ENNReal.ofReal (‖(phiBoundary ell-phiBoundary m) (finiteResolvent F (actualFrequency advanced μ w) (phiRadiusSource g:H))‖^2)
  have hr:=frequency_continuous advanced μ hμ F
  have my:Measurable Y:=(((phiThetaBounded m ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  have mz:Measurable Z:=(((phiBoundary ell-phiBoundary m).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal
  calc _ ≤ ∫⁻w:ℝ,X w+Y w+Z w := by
         apply lintegral_mono
         intro w
         change ENNReal.ofReal (phiNativeEnergy m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g) ≤ _
         exact (ENNReal.ofReal_le_ofReal (native_three_bound m ell F _ _ g)).trans
           (ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl))
       _=(∫⁻w:ℝ,X w)+(∫⁻w:ℝ,Y w)+(∫⁻w:ℝ,Z w) := by
         rw [lintegral_add_right _ mz,lintegral_add_right _ my]
       _ ≤ ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3)+ENNReal.ofReal (ε/3) :=
         add_le_add (add_le_add (hX advanced) (hY advanced)) (hZ advanced)
       _=ENNReal.ofReal ε := by
         rw [←ENNReal.ofReal_add (by positivity) (by positivity),←ENNReal.ofReal_add (by positivity) (by positivity)]
         congr 1
         ring

private theorem native_inverse (v : Ambient) : Commute (covariantMomentum v) inverseVolumeAction := by
  have h := SourceHamiltonianVolume.native_momentum_volume v
  have hVU : Commute inverseVolumeAction SourceCoframeVolume.volumeAction := by
    unfold inverseVolumeAction
    exact SourceHamiltonianVolume.real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (SourceCoframeVolume.volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem native_row_pair (a : ScalarIndex) (p f : QuantumTest) :
    sourcePair p (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth f))=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) (inverseVolumeAction p)) f := by
  rw [GaussNativeForm.adjoint_pair,weight_inverse,LinearMap.smul_apply]
  rw [show sourcePair (covariantMomentum (scalarDirection a) p) ((-(sourceTime 0:ℂ)) • inverseVolumeAction f)=
      (-(sourceTime 0:ℂ))*sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f) by
        simp only [sourcePair,map_smul,inner_smul_right]]
  have hp : sourcePair (covariantMomentum (scalarDirection a) p) (inverseVolumeAction f)=
      sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection a) p)) f := multiply_pair _ _ _ _
  have hc := LinearMap.congr_fun (native_inverse (scalarDirection a)).eq p
  change covariantMomentum (scalarDirection a) (inverseVolumeAction p)=
    inverseVolumeAction (covariantMomentum (scalarDirection a) p) at hc
  rw [hp,←hc]


private theorem gram_bound {ι : Type*} [Fintype ι] (p q : ι → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤ (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (𝕜 := ℂ) (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem young_square (a p e η : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) (hη : 0  <  η)
    (hs : a^2 ≤ p*e) : a ≤ η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0 ≤ η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]


private theorem native_pair (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (p : QuantumTest) :
    sourcePair p (phiNativeDivergence m ell F z hz g)=
      (Complex.I*(sourceTime 0:ℂ))*(∑ a : ScalarIndex,sourcePair
        (covariantMomentum (scalarDirection a) (inverseVolumeAction p)) (phiNativeVector a m ell F z hz g)) := by
  unfold phiNativeDivergence
  simp only [sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  change (-Complex.I)*(∑ a : ScalarIndex,sourcePair p
    (GaussMomentumAdjoint.adjoint (scalarDirection a) (multiply scalarWeight scalarWeight_smooth (phiNativeVector a m ell F z hz g))))=_
  simp_rw [native_row_pair]
  rw [←Finset.mul_sum]
  simp only [sourcePair]
  ring


/-- The complete original transpose divergence is paid by the actual scalar column and genuine small native energy. -/
theorem actual_phi_native_pair_price (p:QuantumTest) (m ell:ℕ) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain)
    (η:ℝ) (hη:0  <  η) :
    ‖sourcePair p (phiNativeDivergence m ell F z hz g)‖ ≤ η*((sourceTime 0)^2*scalarForm (inverseVolumeAction p))+phiNativeEnergy m ell F z hz g/(4*η) := by
  have hs:‖sourcePair p (phiNativeDivergence m ell F z hz g)‖^2 ≤ ((sourceTime 0)^2*scalarForm (inverseVolumeAction p))*phiNativeEnergy m ell F z hz g := by
    rw [native_pair,norm_mul,mul_pow]
    have hn:‖Complex.I*(sourceTime 0:ℂ)‖^2=(sourceTime 0)^2 := by
      simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [hn]
    exact (mul_le_mul_of_nonneg_left (gram_bound
      (fun a=>covariantMomentum (scalarDirection a) (inverseVolumeAction p))
      (fun a=>phiNativeVector a m ell F z hz g)) (sq_nonneg (sourceTime 0))).trans_eq (by
        simp only [scalarForm,phiNativeEnergy,mul_assoc])
  have hp:0 ≤ (sourceTime 0)^2*scalarForm (inverseVolumeAction p) := by
    unfold scalarForm
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  have he:0 ≤ phiNativeEnergy m ell F z hz g := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  exact young_square _ _ _ η hp he hη hs


/-- The fixed-source phi window pays the normalized Phi flux on both actual causal legs; no response tail is assumed. -/
theorem actual_phi_theta_common_tail (μ:ℝ) (hμ:0 < μ) (g:diagonal.domain) :
    ∀ε:ℝ,0 < ε→∃N:ℕ,∀m,N ≤ m→∀ell,m ≤ ell→∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (‖embed (phiThetaAction m ell (SourceScalarPositiveBulkWard.state F
        (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=phi_theta_tail μ hμ (g:H) ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have he(w:ℝ):embed (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)=finiteResolvent F (actualFrequency advanced μ w) (g:H) := by
    unfold SourceScalarPositiveBulkWard.state
    exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  simp_rw [←phi_theta_core,he]
  exact hF advanced

end LowEnergy.SourceClockPhiRadiusResponseNativeBudget
