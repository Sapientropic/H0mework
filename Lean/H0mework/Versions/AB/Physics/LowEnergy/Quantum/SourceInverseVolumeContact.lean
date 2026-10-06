import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceInverseVolumeHardy
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceNativeCutoffContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseVolumeContact
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussYukawaCoefficient GaussRadialDomain GaussRadialMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceInverseVolumeHardy
open SourceNativeCutoffContact MeasureTheory
open scoped ContDiff InnerProductSpace BigOperators
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul

theorem geometric_peak (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    (n+1 : ℝ)*s*(1-s)^n ≤ 1 := by
  have hq : 0 ≤ 1-s := sub_nonneg.mpr hs1
  have h := Finset.single_le_sum
    (f := fun j => s^j*(1-s)^(n+1-j)*((n+1).choose j : ℝ))
    (fun j _ => by positivity) (show 1 ∈ Finset.range (n+1+1) by simp)
  rw [←add_pow,show s+(1-s)=1 by ring,one_pow] at h
  simp only [pow_one,Nat.add_sub_cancel,Nat.choose_one_right,Nat.cast_add,Nat.cast_one] at h
  nlinarith only [h]

def cutoffDifference (m ell : ℕ) (z : SourceCoordinateSlice) : ℝ :=
  (ell+1 : ℝ)*reciprocal z*(1-reciprocal z)^ell-
    (m+1 : ℝ)*reciprocal z*(1-reciprocal z)^m

theorem original_cutoff_difference_bound (m ell : ℕ) (z : SourceCoordinateSlice) :
    |cutoffDifference m ell z| ≤ 1 := by
  have hs : 0 ≤ reciprocal z := (inv_pos.mpr (radius_pos z)).le
  have hs1 : reciprocal z ≤ 1 := inv_le_one_of_one_le₀ (one_le_radius z)
  have hq : 0 ≤ 1-reciprocal z := sub_nonneg.mpr hs1
  have hm := geometric_peak (reciprocal z) hs hs1 m
  have he := geometric_peak (reciprocal z) hs hs1 ell
  have hm0 : 0 ≤ (m+1 : ℝ)*reciprocal z*(1-reciprocal z)^m := by positivity
  have he0 : 0 ≤ (ell+1 : ℝ)*reciprocal z*(1-reciprocal z)^ell := by positivity
  rw [abs_le]
  unfold cutoffDifference
  constructor <;> linarith

private theorem theta_row (i : ScalarIndex) (m ell : ℕ) (z : SourceCoordinateSlice) :
    thetaDerivative (scalarDirection i) m ell z=
      -(cutoffDifference m ell z/4)*inner ℝ (z.2.1 : Scalar) (scalarBasis i)*reciprocal z^2 := by
  unfold thetaDerivative radialDerivative cutoffDifference reciprocal
  change (((ell+1 : ℕ) : ℝ)*(1-(radius z)⁻¹)^ell-
    ((m+1 : ℕ) : ℝ)*(1-(radius z)⁻¹)^m)*
    (-inner ℝ (z.2.1 : Scalar) (scalarBasis i)/(4*radius z^3))=_
  push_cast
  field_simp [(radius_pos z).ne']

private theorem radial_square (z : SourceCoordinateSlice) :
    ‖(z.2.1 : Scalar)‖^2*reciprocal z^4=4*(reciprocal z^2-reciprocal z^4) := by
  have h : radius z^2=1+‖(z.2.1 : Scalar)‖^2/4 := Real.sq_sqrt (by positivity)
  unfold reciprocal
  field_simp [(radius_pos z).ne']
  nlinarith only [h]

/-- Parseval is taken over all seventy original native directions before any estimate. -/
theorem original_native_contact_square (m ell : ℕ) (z : SourceCoordinateSlice) :
    (∑ i : ScalarIndex,(thetaDerivative (scalarDirection i) m ell z)^2)=
      (cutoffDifference m ell z)^2/4*(reciprocal z^2-reciprocal z^4) := by
  simp_rw [theta_row,mul_pow,neg_sq,div_pow]
  simp only [←Finset.sum_mul,←Finset.mul_sum]
  rw [scalarBasis.sum_sq_inner_left]
  calc
    _=((cutoffDifference m ell z)^2/16)*(‖(z.2.1 : Scalar)‖^2*reciprocal z^4) := by ring
    _=_ := by rw [radial_square]; ring

theorem original_native_contact_bound (m ell : ℕ) (z : SourceCoordinateSlice) :
    (∑ i : ScalarIndex,(thetaDerivative (scalarDirection i) m ell z)^2) ≤ reciprocal z^2/4 := by
  rw [original_native_contact_square]
  have hd := pow_le_pow_left₀ (abs_nonneg _) (original_cutoff_difference_bound m ell z) 2
  rw [sq_abs,one_pow] at hd
  have hp := mul_le_mul_of_nonneg_right hd (sq_nonneg (reciprocal z))
  have hn := mul_nonneg (sq_nonneg (cutoffDifference m ell z)) (sq_nonneg (reciprocal z^2))
  nlinarith only [hp,hn]

private theorem complex_scaled_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (c : ℂ) (x : E) :
    (inner ℂ (A (c • x)) (c • x)).re=‖c‖^2*(inner ℂ (A x) x).re := by
  rw [map_smul,inner_smul_left,inner_smul_right,←mul_assoc,
    ←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

private theorem contact_density (v : Ambient) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (contactAction v m ell f) (contactAction v m ell f) z).re=
      (thetaDerivative v m ell z)^2*(densityPair f f z).re := by
  change (inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
    (((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • f z))
    (((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • f z)).re=_
  rw [complex_scaled_inner]
  simp only [norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

private theorem inverse_density (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (inverseAction f) (inverseAction f) z).re=
      reciprocal z^2*(densityPair f f z).re := by
  change (inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
    ((reciprocal z : ℂ) • f z)) ((reciprocal z : ℂ) • f z)).re=_
  rw [complex_scaled_inner]
  simp only [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) :
    0 ≤ (densityPair f f z).re := by
  by_cases hz : z ∈ physicalChart
  · change 0 ≤ RCLike.re (inner ℂ (GaussFockWeights.weight
      (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

private theorem norm_integral (f : QuantumTest) :
    ‖embed f‖^2=∫ z,(densityPair f f z).re ∂GaussHistoryHilbert.configurationMeasure :=
  GaussBoundedMultiplier.norm_square_integral f

/-- The actual whole native contact square has coefficient 1/4, with no factor seventy. -/
theorem original_contact_norm_bound (m ell : ℕ) (f : QuantumTest) :
    (∑ i : ScalarIndex,‖embed (contactAction (scalarDirection i) m ell f)‖^2) ≤
      (1/4 : ℝ)*‖embed (inverseAction f)‖^2 := by
  have hi (i : ScalarIndex) : Integrable (fun z =>
      (densityPair (contactAction (scalarDirection i) m ell f)
        (contactAction (scalarDirection i) m ell f) z).re) GaussHistoryHilbert.configurationMeasure :=
    (densityPair_integrable (contactAction (scalarDirection i) m ell f)
      (contactAction (scalarDirection i) m ell f)).re
  have hs : Integrable (fun z => (densityPair (inverseAction f) (inverseAction f) z).re)
      GaussHistoryHilbert.configurationMeasure :=
    (densityPair_integrable (inverseAction f) (inverseAction f)).re
  simp_rw [norm_integral]
  rw [←integral_finsetSum Finset.univ (fun i _ => hi i),←integral_const_mul]
  apply integral_mono (integrable_finsetSum Finset.univ (fun i _ => hi i)) (hs.const_mul (1/4 : ℝ))
  intro z
  simp only [contact_density,inverse_density,←Finset.sum_mul]
  have h := mul_le_mul_of_nonneg_right (original_native_contact_bound m ell z) (density_nonnegative f z)
  nlinarith only [h]

theorem original_inverse_contact_commute (v : Ambient) (m ell : ℕ) (f : QuantumTest) :
    inverseVolumeAction (contactAction v m ell f)=contactAction v m ell (inverseVolumeAction f) := by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z : ℂ) • (((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • f z)=
    ((-Complex.I)*(thetaDerivative v m ell z : ℂ)) • ((reciprocalVolume z : ℂ) • f z)
  exact smul_comm _ _ _

def inverseContactEnergy (m ell : ℕ) (f : QuantumTest) : ℝ :=
  ∑ i : ScalarIndex,‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell f))‖^2

theorem original_inverse_contact_native_bound (m ell : ℕ) (f : QuantumTest) :
    inverseContactEnergy m ell f ≤ (4/3481 : ℝ)*inverseNativeEnergy f := by
  have h := original_contact_norm_bound m ell (inverseVolumeAction f)
  have hh := original_inverse_native_hardy f
  simp only [inverseContactEnergy,original_inverse_contact_commute]
  norm_num at hh
  nlinarith only [h,hh]

/-- The source Ward form pays all original V-contact rows of the same unlocalized f. -/
theorem original_inverse_contact_form_bound (m ell : ℕ) (f : QuantumTest) :
    4*sourceTime 0*inverseContactEnergy m ell f ≤ (4/3481 : ℝ)*inverseForm f := by
  have hn : 0 < sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have h := mul_le_mul_of_nonneg_left (original_inverse_contact_native_bound m ell f)
    (show 0 ≤ 4*sourceTime 0 by positivity)
  have hh := original_inverse_native_bound f
  nlinarith only [h,hh]

end LowEnergy.SourceInverseVolumeContact
