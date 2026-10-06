import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceRadiusBandGradient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceRadiusBandContact
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussLiveMomentum GaussNativeEnergy GaussYukawaCoefficient GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceRadiusBandGradient SourceRadiusPairedScalarPrice MeasureTheory
open scoped ContDiff InnerProductSpace

def contactFiber (v : Ambient) (m ell : ℕ) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  ((-Complex.I)*(derivative v m ell z : ℂ)) • ContinuousLinearMap.id ℂ FockFiber
private theorem contact_smooth (v : Ambient) (m ell : ℕ) : ContDiff ℝ ∞ (contactFiber v m ell) :=
  (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (derivative_smooth v m ell))).smul contDiff_const

def contactAction (v : Ambient) (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (contactFiber v m ell) (fun _ => (contact_smooth v m ell).contDiffAt)

private theorem action_real (m ell : ℕ) (f : QuantumTest) :
    (bandAction m ell f : SourceCoordinateSlice → FockFiber)=fun z => coefficient m ell z • f z := by
  funext z
  apply PiLp.ext
  intro word
  exact Complex.real_smul.symm

private theorem directional_band (v : Ambient) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v (bandAction m ell f) z=coefficient m ell z • directional v f z+derivative v m ell z • f z := by
  rw [directional_apply,action_real,
    fderiv_fun_smul ((coefficient_smooth m ell).differentiable (by simp)).differentiableAt
      (f.contDiff.differentiable (by simp)).differentiableAt]
  change coefficient m ell z • directional v f z+fderiv ℝ (coefficient m ell) z (direction v z) • f z=_
  by_cases hz : z∈physicalChart
  · rw [original_direction_band v m ell ⟨z,hz⟩]
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    rw [hf,smul_zero,smul_zero]

/-- The error is the true original covariant momentum commutator, with its connection retained. -/
theorem original_native_contact (v : Ambient) (m ell : ℕ) (f : QuantumTest) :
    covariantMomentum v (bandAction m ell f)=bandAction m ell (covariantMomentum v f)+contactAction v m ell f := by
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional v (bandAction m ell f) z+connection v z (bandAction m ell f z))=
    (coefficient m ell z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))+
      ((-Complex.I)*(derivative v m ell z : ℂ)) • f z
  rw [directional_band]
  change (-Complex.I) • (coefficient m ell z • directional v f z+derivative v m ell z • f z+
    connection v z ((coefficient m ell z : ℂ) • f z))=_
  rw [map_smul]
  apply PiLp.ext
  intro word
  simp only [PiLp.smul_apply,PiLp.add_apply,Complex.real_smul]
  change (-Complex.I)*((coefficient m ell z : ℂ)*directional v f z word+
    (derivative v m ell z : ℂ)*f z word+(coefficient m ell z : ℂ)*connection v z (f z) word)=_
  ring

private theorem contact_density (v : Ambient) (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (contactAction v m ell f) (contactAction v m ell f) z).re=
      (derivative v m ell z)^2*(densityPair f f z).re := by
  change (inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z)
    (((-Complex.I)*(derivative v m ell z : ℂ)) • f z))
    (((-Complex.I)*(derivative v m ell z : ℂ)) • f z)).re=_
  rw [map_smul,inner_smul_left,inner_smul_right,←mul_assoc,
    ←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    norm_mul,norm_neg,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rfl

private theorem band_density (m ell : ℕ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair f (bandAction m ell f) z).re=coefficient m ell z*(densityPair f f z).re := by
  change (inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    ((coefficient m ell z : ℂ) • f z)).re=_
  simp only [inner_smul_right,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) : 0≤(densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · change 0≤RCLike.re (inner ℂ (GaussFockWeights.weight
      (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

/-- All native70 contact rows are paid by the original first-radius moment with no window-length norm. -/
theorem original_contact_energy (m ell : ℕ) (f : QuantumTest) :
    (∑ i : ScalarIndex,‖embed (contactAction (scalarDirection i) m ell f)‖^2) ≤
      (3/(m+1 : ℝ))*radiusMoment m ell (embed f) := by
  have hi (i : ScalarIndex) := (densityPair_integrable (contactAction (scalarDirection i) m ell f)
    (contactAction (scalarDirection i) m ell f)).re
  have hb := (densityPair_integrable f (bandAction m ell f)).re
  have he : radiusMoment m ell (embed f)=
      ∫ z,(densityPair f (bandAction m ell f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    unfold radiusMoment
    rw [←original_band_core]
    change (sourcePair f (bandAction m ell f)).re=_
    rw [sourcePair_integral]
    exact (integral_re (densityPair_integrable f (bandAction m ell f))).symm
  simp_rw [GaussBoundedMultiplier.norm_square_integral]
  rw [he,←integral_finsetSum Finset.univ (fun i _ => hi i),←integral_const_mul]
  apply integral_mono (integrable_finsetSum Finset.univ (fun i _ => hi i)) (hb.const_mul _)
  intro z
  change (∑ i : ScalarIndex,(densityPair (contactAction (scalarDirection i) m ell f)
    (contactAction (scalarDirection i) m ell f) z).re) ≤
    (3/(m+1 : ℝ))*(densityPair f (bandAction m ell f) z).re
  simp only [contact_density,band_density,←Finset.sum_mul]
  have h := mul_le_mul_of_nonneg_right (original_native_gradient_price m ell z) (density_nonnegative f z)
  exact h.trans_eq (by ring)

/-- The bound controls the actual derivative transport of the same radiusBand, not a substitute multiplier. -/
theorem original_native_transport_error (m ell : ℕ) (f : QuantumTest) :
    (∑ i : ScalarIndex,‖embed (covariantMomentum (scalarDirection i) (bandAction m ell f)-
      bandAction m ell (covariantMomentum (scalarDirection i) f))‖^2) ≤
      (3/(m+1 : ℝ))*radiusMoment m ell (embed f) := by
  simp_rw [original_native_contact,add_sub_cancel_left]
  exact original_contact_energy m ell f

end LowEnergy.SourceRadiusBandContact
