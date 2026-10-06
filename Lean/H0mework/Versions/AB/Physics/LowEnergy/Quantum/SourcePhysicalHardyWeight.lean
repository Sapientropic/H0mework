import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourcePhysicalKineticSquare
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceGaugeRadialPair

/-! The original electric radius returns exactly the physical forcing weight. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourcePhysicalHardyWeight
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourcePhysicalKineticSquare
open SourceCornerWeight SourceGaugeRadiusMetric SourceGaugeRadialCurrent SourceGaugeRadialPair
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace

def reciprocalHardy (z : SourceCoordinateSlice) : ℝ := (hardyWeight z)⁻¹

theorem reciprocal_hardy_smooth (z : physicalChart) : ContDiffAt ℝ ∞ reciprocalHardy z.val :=
  (gauge_square_smooth.contDiffAt.sqrt (gauge_square_pos z).ne').inv
    (Real.sqrt_pos.mpr (gauge_square_pos z)).ne'

def inverseHardyAction : CoreEnd := multiply reciprocalHardy reciprocal_hardy_smooth

theorem physical_weight_coefficient (z : physicalChart) :
    sourceTime 0*(inverseRootVolume z.val*radialWeight z.val*inverseRootVolume z.val)=
      sourceSigma*(reciprocalHardy z.val*reciprocalHardy z.val) := by
  have hu : inverseRootVolume z.val*inverseRootVolume z.val=(volume z.val)⁻¹ := by
    unfold inverseRootVolume
    rw [←mul_inv,Real.mul_self_sqrt (volume_pos z).le]
  have hw : reciprocalHardy z.val*reciprocalHardy z.val=(gaugeSquare z.val)⁻¹ := by
    unfold reciprocalHardy hardyWeight
    rw [←mul_inv,Real.mul_self_sqrt (gauge_square_pos z).le]
  calc
    _ = sourceTime 0*(inverseRootVolume z.val*inverseRootVolume z.val)*radialWeight z.val := by ring
    _ = _ := by
      rw [hu,hw]
      unfold radialWeight electricSquare
      field_simp [source_time_nonzero,source_sigma_nonzero,(volume_pos z).ne',(gauge_square_pos z).ne']

theorem physical_weight_action (f : QuantumTest) :
    (sourceTime 0 : ℂ) • inverseRootAction (radialWeightAction (inverseRootAction f))=
      (sourceSigma : ℂ) • inverseHardyAction (inverseHardyAction f) := by
  apply DFunLike.ext
  intro z
  change (sourceTime 0 : ℂ) • ((inverseRootVolume z : ℂ) •
      ((radialWeight z : ℂ) • ((inverseRootVolume z : ℂ) • f z)))=
    (sourceSigma : ℂ) • ((reciprocalHardy z : ℂ) • ((reciprocalHardy z : ℂ) • f z))
  by_cases hz : z ∈ physicalChart
  · simp only [smul_smul]
    have h := congrArg Complex.ofReal (physical_weight_coefficient ⟨z,hz⟩)
    push_cast at h
    simp only [mul_assoc] at h ⊢
    rw [h]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))]
    simp only [smul_zero]

theorem physical_weight_pair (f : QuantumTest) :
    sourceTime 0*(sourcePair (inverseRootAction f) (radialWeightAction (inverseRootAction f))).re=
      sourceSigma*‖embed (inverseHardyAction f)‖^2 := by
  have hS (x y : QuantumTest) : sourcePair x (inverseRootAction y)=sourcePair (inverseRootAction x) y :=
    multiply_pair _ _ _ _
  have hW (x y : QuantumTest) : sourcePair x (inverseHardyAction y)=sourcePair (inverseHardyAction x) y :=
    multiply_pair _ _ _ _
  have h := congrArg (fun y => sourcePair f y) (physical_weight_action f)
  change inner ℂ (embed f) (embed ((sourceTime 0 : ℂ) • _))=
    inner ℂ (embed f) (embed ((sourceSigma : ℂ) • _)) at h
  simp only [map_smul,inner_smul_right] at h
  change (sourceTime 0 : ℂ)*sourcePair f (inverseRootAction (radialWeightAction (inverseRootAction f)))=
    (sourceSigma : ℂ)*sourcePair f (inverseHardyAction (inverseHardyAction f)) at h
  rw [hS,hW] at h
  have hr := congrArg Complex.re h
  have hn : (sourcePair (inverseHardyAction f) (inverseHardyAction f)).re=
      ‖embed (inverseHardyAction f)‖^2 :=
    inner_self_eq_norm_sq (𝕜 := ℂ) (embed (inverseHardyAction f))
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,hn] using hr

theorem source_hardy_coefficient (f : QuantumTest) :
    (289/2 : ℝ)*sourceTime 0*
      (sourcePair (inverseRootAction f) (radialWeightAction (inverseRootAction f))).re=
      (289/4 : ℝ)*‖embed (inverseHardyAction f)‖^2 := by
  rw [mul_assoc,physical_weight_pair]
  have hs : sourceSigma=(1/2 : ℝ) :=
    SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.sourceCoupling_eq
  rw [hs]
  ring

def localizedAction : CoreEnd := inverseHardyAction.comp forcingAction

theorem localized_action_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    localizedAction f z=(localizer z : ℂ) • f z := by
  change (reciprocalHardy z : ℂ) • (((hardyWeight z*localizer z : ℝ) : ℂ) • f z)=_
  by_cases hz : z ∈ physicalChart
  · have hw : hardyWeight z≠0 := (Real.sqrt_pos.mpr (gauge_square_pos ⟨z,hz⟩)).ne'
    simp only [reciprocalHardy,Complex.ofReal_mul,Complex.ofReal_inv,smul_smul]
    rw [←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast hw),one_mul]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))]
    simp only [smul_zero]

theorem weighted_forcing_pair (f g : QuantumTest) :
    sourcePair (inverseHardyAction f) (forcingAction g)=sourcePair f (localizedAction g) :=
  (multiply_pair reciprocalHardy reciprocal_hardy_smooth f (forcingAction g)).symm

end LowEnergy.SourcePhysicalHardyWeight
