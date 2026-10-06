import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceYukawaMixedCurvature
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceClockSourceTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceYukawaMixedVacuumBound
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativePotential
open GaussNativeEnergy SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceMixedNativeReturn SourceScalarDoubleCurrent SourceInverseNeutralSpinCurrent
open GaussYukawaCoefficient GaussRadialDomain SourceScalarRadialContact GaussFockWeights GaussQuantumMultiplier
open SourcePhysicalKineticSquare SourceClockReflectedForm
open scoped ContDiff InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] fullAction

def vacuumFiber (sharp : Bool) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  bracket (branchMap sharp vacuum) (branchMap (!sharp) (scalarField z))+
    bracket (branchMap (!sharp) vacuum) (branchMap sharp (scalarField z))

def contactFiber (sharp : Bool) (m ell : ℕ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (radialProfile m ell z : ℂ) • vacuumFiber sharp z

private theorem fiber_smooth (sharp : Bool) : ContDiff ℝ ∞ (vacuumFiber sharp) := by
  unfold vacuumFiber bracket
  exact ((contDiff_const.mul ((branchMap (!sharp)).contDiff.comp scalarField_smooth)).sub
    (((branchMap (!sharp)).contDiff.comp scalarField_smooth).mul contDiff_const)).add
    ((contDiff_const.mul ((branchMap sharp).contDiff.comp scalarField_smooth)).sub
      (((branchMap sharp).contDiff.comp scalarField_smooth).mul contDiff_const))

private theorem contact_smooth (sharp : Bool) (m ell : ℕ) : ContDiff ℝ ∞ (contactFiber sharp m ell) :=
  (Complex.ofRealCLM.contDiff.comp (radial_profile_smooth m ell)).smul (fiber_smooth sharp)

private theorem quantized_adjoint (A : Matrix Mode Mode ℂ) :
    (quantized A).adjoint=quantized A.conjTranspose := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact SourceQuantumFockGauge.quantizedFiber_adjoint A g f

private theorem branch_weight (sharp : Bool) (phi : Scalar) (w : ℕ → ℂ) :
    Commute (weight w) (branchMap sharp phi) := by
  cases sharp
  · change Commute (weight w) (sourceMap phi)
    rw [source_map_return]
    exact weight_commute w _
  · change Commute (weight w) (sourceMap phi).adjoint
    rw [source_map_return,quantized_adjoint]
    exact weight_commute w _

private theorem contact_weight (sharp : Bool) (m ell : ℕ) (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (weight w) (contactFiber sharp m ell z) := by
  have h (s : Bool) : Commute (weight w) (bracket (branchMap s vacuum) (branchMap (!s) (scalarField z))) :=
    ((branch_weight s vacuum w).mul_right (branch_weight (!s) (scalarField z) w)).sub_right
      ((branch_weight (!s) (scalarField z) w).mul_right (branch_weight s vacuum w))
  unfold contactFiber vacuumFiber
  exact ((h sharp).add_right (by simpa only [Bool.not_not] using h (!sharp))).smul_right _

private theorem branch_bound (sharp : Bool) (phi : Scalar) :
    ‖branchMap sharp phi‖ ≤ ‖sourceMap‖*‖phi‖ := by
  cases sharp
  · exact sourceMap.le_opNorm phi
  · change ‖(sourceMap phi).adjoint‖ ≤ _
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact sourceMap.le_opNorm phi

private theorem bracket_bound (A B : FockFiber →L[ℂ] FockFiber) :
    ‖bracket A B‖ ≤ 2*‖A‖*‖B‖ := by
  have h := (norm_sub_le (A*B) (B*A)).trans (add_le_add (norm_mul_le A B) (norm_mul_le B A))
  calc
    _ ≤ ‖A‖*‖B‖+‖B‖*‖A‖ := h
    _ = _ := by ring

def vacuumPrice : ℝ := 4*‖sourceMap‖^2*‖vacuum‖*(‖vacuum‖+2)

private theorem fiber_bound (sharp : Bool) (z : SourceCoordinateSlice) :
    ‖vacuumFiber sharp z‖ ≤ vacuumPrice*radius z := by
  have hv (s : Bool) := branch_bound s vacuum
  have hy (s : Bool) : ‖branchMap s (scalarField z)‖ ≤ ‖sourceMap‖*(‖vacuum‖+2)*radius z :=
    (branch_bound s _).trans (by nlinarith only [mul_le_mul_of_nonneg_left (scalar_bound z) (norm_nonneg sourceMap)])
  have hb (s : Bool) : ‖bracket (branchMap s vacuum) (branchMap (!s) (scalarField z))‖ ≤
      2*(‖sourceMap‖*‖vacuum‖)*(‖sourceMap‖*(‖vacuum‖+2)*radius z) := by
    apply (bracket_bound _ _).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hv s) (by norm_num)) (hy (!s))
      (norm_nonneg _) (by positivity)
  have h := (norm_add_le _ _).trans (add_le_add (hb sharp) (by simpa only [Bool.not_not] using hb (!sharp)))
  change ‖vacuumFiber sharp z‖ ≤ _ at h
  unfold vacuumPrice
  nlinarith only [h]

/-- The same original S² peak pays the full radius left by the linear vacuum contact. -/
private theorem radial_profile_bound (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    radius z*|radialProfile m ell z| ≤ 1/(m+2 : ℝ) := by
  have hrpos := radius_pos z
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have hm := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 m
  have he := SourceNativeCutoffContact.squared_geometric_peak (reciprocal z) hs hs1 ell
  have hd : 2/(ell+2 : ℝ) ≤ 2/(m+2 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by exact_mod_cast Nat.add_le_add_right hml 2)
  have ha := abs_sub ((m+1 : ℝ)*(1-reciprocal z)^m) ((ell+1 : ℝ)*(1-reciprocal z)^ell)
  have hm0 : 0 ≤ (m+1 : ℝ)*(1-reciprocal z)^m := by positivity
  have he0 : 0 ≤ (ell+1 : ℝ)*(1-reciprocal z)^ell := by positivity
  rw [abs_of_nonneg hm0,abs_of_nonneg he0] at ha
  have hh := mul_le_mul_of_nonneg_right ha (sq_nonneg (reciprocal z))
  have hr : radius z*|radialProfile m ell z|=
      |(m+1 : ℝ)*(1-reciprocal z)^m-(ell+1 : ℝ)*(1-reciprocal z )^ell| * (reciprocal z)^2/4 := by
    rw [radialProfile,abs_div,abs_of_pos (show 0<4*radius z^3 by positivity)]
    unfold reciprocal
    push_cast
    field_simp [(radius_pos z).ne']
  rw [hr]
  have he' := he.trans hd
  simp only [div_eq_mul_inv] at hm he' ⊢
  nlinarith only [hm,he',hh]

private theorem contact_bound (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (z : SourceCoordinateSlice) :
    ‖contactFiber sharp m ell z‖ ≤ vacuumPrice/(m+2 : ℝ) := by
  have hC : 0 ≤ vacuumPrice := by unfold vacuumPrice;positivity
  rw [contactFiber,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left (fiber_bound sharp z) (abs_nonneg (radialProfile m ell z))
  have hp := mul_le_mul_of_nonneg_left (radial_profile_bound m ell hml z) hC
  calc
    _ ≤ |radialProfile m ell z| * (vacuumPrice*radius z) := h
    _ = vacuumPrice*(radius z*|radialProfile m ell z|) := by ring
    _ ≤ vacuumPrice*(1/(m+2 : ℝ)) := hp
    _ = _ := by ring

def contactCore (sharp : Bool) (m ell : ℕ) : End :=
  localMultiplier (contactFiber sharp m ell) (fun _ => (contact_smooth sharp m ell).contDiffAt)

def boundedContact (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (contactFiber sharp m ell) (fun _ => (contact_smooth sharp m ell).contDiffAt)
    (fun z => contact_weight sharp m ell z) (vacuumPrice/(m+2 : ℝ)) (by unfold vacuumPrice;positivity)
    (fun z f => ((contactFiber sharp m ell z).le_opNorm f).trans
      (mul_le_mul_of_nonneg_right (contact_bound sharp m ell hml z) (norm_nonneg f)))

theorem original_bounded_vacuum_contact_core (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) (f : QuantumTest) :
    boundedContact sharp m ell hml (embed f)=embed (contactCore sharp m ell f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

theorem original_bounded_vacuum_contact_norm (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell) :
    ‖boundedContact sharp m ell hml‖ ≤ vacuumPrice/(m+2 : ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

/-- Only the original inverse-volume spin weight remains unbounded; the entire
vacuum/Y coefficient and radius profile are a generated small bounded operator. -/
theorem original_vacuum_contact_factor (sharp : Bool) (m ell : ℕ) :
    (bracket (constantAction sharp vacuum) (fullAction (!sharp))+
      bracket (constantAction (!sharp) vacuum) (fullAction sharp))*weightedProfileAction m ell=
      spinVolume*contactCore sharp m ell := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have hf (s : Bool) (q : QuantumTest) : fullAction s q z=branchMap s (scalarField z) (q z) := by
    unfold SourceMixedNativeReturn.fullAction
    cases s <;> rfl
  have hconst (s : Bool) (v : Scalar) (q : QuantumTest) : constantAction s v q z=branchMap s v (q z) := rfl
  have hweight (q : QuantumTest) : weightedProfileAction m ell q z=
      ((GaussCoframeForm.inverseVolume z*radialProfile m ell z : ℝ) : ℂ) • q z := rfl
  have hspin (q : QuantumTest) : spinVolume q z=(GaussCoframeForm.inverseVolume z : ℂ) • q z := rfl
  have hcc (q : QuantumTest) : contactCore sharp m ell q z=
      (radialProfile m ell z : ℂ) • vacuumFiber sharp z (q z) := rfl
  simp only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,add_apply,sub_apply,
    bracket,hf,hconst,hweight,hspin,hcc]
  change vacuumFiber sharp z (((GaussCoframeForm.inverseVolume z*radialProfile m ell z : ℝ) : ℂ) • f z)=
    (GaussCoframeForm.inverseVolume z : ℂ) • ((radialProfile m ell z : ℂ) • vacuumFiber sharp z (f z))
  rw [map_smul,Complex.ofReal_mul,mul_smul]

private theorem spin_inverse_pair (p q : QuantumTest) :
    sourcePair p (spinVolume q)=(sourceTime 0 : ℂ)*sourcePair (inverseVolumeAction p) q := by
  have h : spinVolume q=(sourceTime 0 : ℂ) • inverseVolumeAction q := by
    apply DFunLike.ext
    intro z
    change (GaussCoframeForm.inverseVolume z : ℂ) • q z=
      (sourceTime 0 : ℂ) • ((reciprocalVolume z : ℂ) • q z)
    simp only [GaussCoframeForm.inverseVolume,reciprocalVolume,div_eq_mul_inv,
      Complex.ofReal_mul,Complex.ofReal_inv,mul_smul]
  rw [h]
  change inner ℂ (embed p) (embed ((sourceTime 0 : ℂ) • inverseVolumeAction q))=_
  rw [map_smul,inner_smul_right]
  congr 1
  exact multiply_pair _ _ p q

private theorem young (a b δ : ℝ) (hδ : 0<δ) : a*b ≤ δ*a^2+(4*δ)⁻¹*b^2 := by
  have he : (4*δ)*((4*δ)⁻¹*b^2)=b^2 := by
    rw [←mul_assoc,mul_inv_cancel₀ (by positivity),one_mul]
  nlinarith [sq_nonneg (2*δ*a-b)]

/-- The complete actual vacuum contact consumes the existing positive coframe
Gram; its other price is a source-generated O((m+2)⁻²) norm term. -/
theorem original_vacuum_contact_coframe_price (sharp : Bool) (m ell : ℕ) (hml : m ≤ ell)
    (p q : QuantumTest) (δ : ℝ) (hδ : 0<δ) :
    ‖sourcePair p (((bracket (constantAction sharp vacuum) (fullAction (!sharp))+
      bracket (constantAction (!sharp) vacuum) (fullAction sharp))*weightedProfileAction m ell) q)‖ ≤
      δ*(sourceTime 0)^2*coframeGram (inverseVolumeAction p)+
        (vacuumPrice^2/(100*δ*(m+2 : ℝ)^2))*‖embed q‖^2 := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hC : 0 ≤ vacuumPrice := by unfold vacuumPrice;positivity
  have hD : 0<(m+2 : ℝ) := by positivity
  rw [original_vacuum_contact_factor,Module.End.mul_apply,spin_inverse_pair,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
  have hB : ‖embed (contactCore sharp m ell q)‖ ≤ (vacuumPrice/(m+2 : ℝ))*‖embed q‖ := by
    rw [←original_bounded_vacuum_contact_core sharp m ell hml]
    exact ((boundedContact sharp m ell hml).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (original_bounded_vacuum_contact_norm sharp m ell hml) (norm_nonneg _))
  have hP := (norm_inner_le_norm (𝕜 := ℂ) (embed (inverseVolumeAction p))
    (embed (contactCore sharp m ell q))).trans (mul_le_mul_of_nonneg_left hB (norm_nonneg _))
  have hb := mul_le_mul_of_nonneg_left hP hn.le
  have hf := mul_le_mul_of_nonneg_left (SourceClockSourceTail.original_inverse_coframe_floor (inverseVolumeAction p))
    (show 0 ≤ δ*(sourceTime 0)^2 by positivity)
  have hy := young (5*sourceTime 0*‖embed (inverseVolumeAction p)‖)
    (vacuumPrice/(5*(m+2 : ℝ))*‖embed q‖) δ hδ
  have hl : (5*sourceTime 0*‖embed (inverseVolumeAction p)‖)*
      (vacuumPrice/(5*(m+2 : ℝ))*‖embed q‖)=
      sourceTime 0*(‖embed (inverseVolumeAction p)‖*((vacuumPrice/(m+2 : ℝ))*‖embed q‖)) := by
    field_simp
  have hr : (4*δ)⁻¹*(vacuumPrice/(5*(m+2 : ℝ))*‖embed q‖)^2=
      (vacuumPrice^2/(100*δ*(m+2 : ℝ)^2))*‖embed q‖^2 := by
    field_simp
    ring
  rw [hl,hr] at hy
  change sourceTime 0*‖sourcePair (inverseVolumeAction p) (contactCore sharp m ell q)‖ ≤ _ at hb
  nlinarith only [hb,hf,hy]

end LowEnergy.SourceYukawaMixedVacuumBound
