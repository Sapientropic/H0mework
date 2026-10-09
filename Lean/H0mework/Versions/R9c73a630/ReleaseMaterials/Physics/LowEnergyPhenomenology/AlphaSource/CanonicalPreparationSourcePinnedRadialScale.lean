import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceStaticLaurentObserved

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticSpatialSource
open PreparationVacuumObservedPoleTensor PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalPinnedVelocity PreparationVacuumPhysicalSlowBlock
open PreparationVacuumSharedPoleCarrier CanonicalGradedSpatialSource
open Filter Set
open scoped Topology
attribute [local irreducible] sourcePinnedVelocity sourceVelocityLinear sourceEqualProjection
  sourcePinnedResolvent sourcePinnedPencil sourceResonanceProjection sourceOffPoleReturn

/-- The pinned velocity inherits the original momentum action's real linearity. -/
theorem sourcePinnedVelocity_radial (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (s : ℝ) :
    sourcePinnedVelocity F (s • n)=(s:ℂ) • sourcePinnedVelocity F n := by
  rw [sourcePinnedVelocity,map_smul,←algebraMap_smul ℂ s (sourceVelocityLinear F n),map_smul]
  rw [sourcePinnedVelocity]
  rfl

theorem sourcePinnedPencil_radial (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) (s : ℝ) (eta : ℂ) :
    sourcePinnedPencil F (s • n) ((s:ℂ)*eta)=(s:ℂ) • sourcePinnedPencil F n eta := by
  simp only [sourcePinnedPencil,sourcePinnedVelocity_radial,smul_add,smul_smul]
  module

/-- The actual two-sided inverse fixes scaling without choosing spectral labels. -/
theorem sourcePinnedResolvent_radial (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (eta : ℂ) (causal : 0<eta.re) :
    sourcePinnedResolvent F (s • n) ((s:ℂ)*eta)=(s:ℂ)⁻¹ • sourcePinnedResolvent F n eta := by
  have scaledCausal : 0<((s:ℂ)*eta).re := by simpa using mul_pos positive causal
  have inverse : sourcePinnedPencil F (s • n) ((s:ℂ)*eta)*
      ((s:ℂ)⁻¹ • sourcePinnedResolvent F n eta)=1 := by
    rw [sourcePinnedPencil_radial,smul_mul_assoc,mul_smul_comm,smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr positive.ne'),one_smul,
      sourcePinnedResolvent_right F n eta causal]
  exact left_inv_eq_right_inv (sourcePinnedResolvent_left F (s • n) _ scaledCausal) inverse

private theorem radial_approach (s : ℝ) (positive : 0<s) :
    Tendsto (fun eta : ℝ=>s*eta) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [mul_zero,id_eq] using ((tendsto_id : Tendsto (fun eta : ℝ=>eta) (𝓝 0) (𝓝 0)).const_mul s).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with eta h
    exact mul_pos positive h

private theorem static_resolvent (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • sourcePinnedResolvent F n (eta:ℂ))
      (𝓝[>] 0) (𝓝 (sourceResonanceProjection F n 0)) := by
  simpa only [sourcePoleSide,Complex.ofReal_zero,mul_zero,add_zero] using sourcePinnedResolvent_residue F n 0

/-- The source zero-velocity projector is independent of the positive radial momentum scale. -/
theorem sourceResonance_radial (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) :
    sourceResonanceProjection F (s • n) 0=sourceResonanceProjection F n 0 := by
  have scaled:=(static_resolvent F (s • n)).comp (radial_approach s positive)
  have equal : (fun eta : ℝ=>((s*eta:ℝ):ℂ) • sourcePinnedResolvent F (s • n) ((s*eta:ℝ):ℂ)) =ᶠ[𝓝[>] 0]
      (fun eta : ℝ=>(eta:ℂ) • sourcePinnedResolvent F n (eta:ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with eta h
    rw [Complex.ofReal_mul,sourcePinnedResolvent_radial F n s positive (eta:ℂ) h,smul_smul]
    have factor : (s:ℂ)*(eta:ℂ)*(s:ℂ)⁻¹=(eta:ℂ) := by
      field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
    rw [factor]
  exact tendsto_nhds_unique (scaled.congr' equal) (static_resolvent F n)

private theorem off_resolvent (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (eta : ℝ) (positive : 0<eta) :
    sourceOffPoleReturn F n 0 eta=sourcePinnedResolvent F n (eta:ℂ)-(eta:ℂ)⁻¹ • sourceResonanceProjection F n 0 := by
  have h:=sourcePinnedResolvent_boundary F n 0 eta positive
  have normal : sourcePinnedResolvent F n (eta:ℂ)=(eta:ℂ)⁻¹ • sourceResonanceProjection F n 0+sourceOffPoleReturn F n 0 eta := by
    simpa only [sourcePoleSide,Complex.ofReal_zero,mul_zero,add_zero] using h
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans normal.symm)

/-- The actual nonresonant resolvent follows the same source radial scale before the boundary. -/
theorem sourceOffReturn_radial (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (eta : ℝ) (causal : 0<eta) :
    sourceOffPoleReturn F (s • n) 0 (s*eta)=(s:ℂ)⁻¹ • sourceOffPoleReturn F n 0 eta := by
  rw [off_resolvent F (s • n) (s*eta) (mul_pos positive causal),Complex.ofReal_mul,
    sourcePinnedResolvent_radial F n s positive (eta:ℂ) causal,sourceResonance_radial F n s positive,
    off_resolvent F n eta causal,mul_inv_rev,smul_sub,smul_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [sub_apply,smul_apply]
  module

/-- The full off-resonant static operator scales reciprocally, including every source spectral channel. -/
theorem sourceOffStatic_radial (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) :
    sourceOffPoleReturn F (s • n) 0 0=(s:ℂ)⁻¹ • sourceOffPoleReturn F n 0 0 := by
  have left:=((sourceOffPoleReturn_limit F (s • n) 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0)).comp (radial_approach s positive)
  have right:=(tendsto_const_nhds (x:=(s:ℂ)⁻¹)).smul ((sourceOffPoleReturn_limit F n 0).mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ)≤𝓝 0))
  have equal : (fun eta : ℝ=>sourceOffPoleReturn F (s • n) 0 (s*eta)) =ᶠ[𝓝[>] 0]
      (fun eta : ℝ=>(s:ℂ)⁻¹ • sourceOffPoleReturn F n 0 eta) := by
    filter_upwards [self_mem_nhdsWithin] with eta h
    exact sourceOffReturn_radial F n s positive eta h
  exact tendsto_nhds_unique (left.congr' equal) right

/-- The original reciprocal-gap budget generates the full rescaled static operator price. -/
theorem sourceOffStatic_radial_price (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) :
    ‖sourceOffPoleReturn F (s • n) 0 0‖≤ s⁻¹*sourceOffPolePrice F n 0 := by
  rw [sourceOffStatic_radial F n s positive,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  exact mul_le_mul_of_nonneg_left (sourceOffPoleReturn_price F n 0 0) (inv_nonneg.mpr positive.le)

/-- The same source gap error survives the simultaneous momentum and causal-frequency rescaling. -/
theorem sourceOff_radial_error (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (s : ℝ) (positive : 0<s) (eta : ℝ) (causal : 0<eta) :
    ‖sourceOffPoleReturn F (s • n) 0 (s*eta)-sourceOffPoleReturn F (s • n) 0 0‖≤
      (|eta|/s)*sourceOffPoleError F n 0 := by
  rw [sourceOffReturn_radial F n s positive eta causal,sourceOffStatic_radial F n s positive]
  have difference : (s:ℂ)⁻¹ • sourceOffPoleReturn F n 0 eta-(s:ℂ)⁻¹ • sourceOffPoleReturn F n 0 0=
      (s:ℂ)⁻¹ • (sourceOffPoleReturn F n 0 eta-sourceOffPoleReturn F n 0 0) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (smul_sub ((s:ℂ)⁻¹) (sourceOffPoleReturn F n 0 eta x) (sourceOffPoleReturn F n 0 0 x)).symm
  rw [difference,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_left (sourceOffPoleReturn_error F n 0 eta) (inv_nonneg.mpr positive.le)).trans_eq (by ring)

end LowEnergy.PreparationVacuumStaticSpatialSource
