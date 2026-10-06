import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeContact
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseFullResponse
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarAffineSecondCutoffTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseContactHardy
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussHistoryHilbert
open GaussNativeEnergy GaussRadialDomain GaussRadialMomentum SourceNativeCutoffContact GaussFockWeights
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourcePhysicalKineticSquare SourceInverseVolumeHardy
open SourceScalarInverseNativeEnergy SourceScalarInverseEnergyExchange SourceInverseVolumeContact
open SourceScalarPositiveBulkWard GaussDiagonalHistory GaussUnitaryHistory
open scoped ContDiff InnerProductSpace BigOperators
open MeasureTheory

private def realContact (i : ScalarIndex) (m ell : ℕ) : QuantumTest →ₗ[ℂ] QuantumTest :=
  multiply (thetaDerivative (scalarDirection i) m ell)
    (fun _ => (theta_derivative_smooth (scalarDirection i) m ell).contDiffAt)

private theorem contact_real (i : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    inverseVolumeAction (contactAction (scalarDirection i) m ell f)=
      (-Complex.I) • realContact i m ell (inverseVolumeAction f) := by
  apply DFunLike.ext
  intro z
  change (reciprocalVolume z : ℂ) •
      (((-Complex.I)*(thetaDerivative (scalarDirection i) m ell z : ℂ)) • f z)=
    (-Complex.I) • ((thetaDerivative (scalarDirection i) m ell z : ℂ) •
      ((reciprocalVolume z : ℂ) • f z))
  simp only [smul_smul]
  congr 1
  ring

private theorem contact_real_norm (i : ScalarIndex) (m ell : ℕ) (f : QuantumTest) :
    ‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell f))‖^2=
      ‖embed (realContact i m ell (inverseVolumeAction f))‖^2 := by
  rw [contact_real,map_smul,norm_smul,norm_neg,Complex.norm_I,one_mul]

private theorem real_inner_scaled {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (r : ℝ) (x : E) :
    (inner ℂ (A ((r : ℂ) • x)) ((r : ℂ) • x)).re=r^2*(inner ℂ (A x) x).re := by
  rw [map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply,Complex.star_def,Complex.conj_ofReal]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

private theorem scalar_density (a : SourceCoordinateSlice → ℝ)
    (ha : ∀ z : physicalChart,ContDiffAt ℝ ∞ a z.val) (f : QuantumTest) (z : SourceCoordinateSlice) :
    (densityPair (multiply a ha f) (multiply a ha f) z).re=
      (a z)^2*(densityPair f f z).re := by
  change (inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z) ((a z : ℂ) • f z))
    ((a z : ℂ) • f z)).re=_
  exact real_inner_scaled _ _ _

private theorem density_nonnegative (f : QuantumTest) (z : SourceCoordinateSlice) :
    0  ≤  (densityPair f f z).re := by
  by_cases hz : z∈physicalChart
  · change 0  ≤  RCLike.re (inner ℂ (weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square _ (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]

/-- The original IMS diagonal is the complete positive native70 contact square. -/
theorem inverse_contact_real (m ell : ℕ) (f : QuantumTest) : (inverseContact m ell f f).re=
    4*sourceTime 0*∑ i : ScalarIndex,
      ‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell f))‖^2 := by
  simp [inverseContact,sourcePair,inner_self_eq_norm_sq_to_K,pow_two,
    Complex.mul_re,Complex.mul_im,Complex.re_sum]

private theorem gradient_localized (m ell : ℕ) (z : SourceCoordinateSlice) :
    (∑ i : ScalarIndex,thetaDerivative (scalarDirection i) m ell z^2)  ≤
      (1/4 : ℝ)*(SourceScalarAffineSecondCutoffTail.firstGeometricCoefficient m ell z)^2*
        (reciprocal z)^2 := by
  rw [original_native_contact_square]
  have he : cutoffDifference m ell z=
      -SourceScalarAffineSecondCutoffTail.firstGeometricCoefficient m ell z := by
    dsimp [cutoffDifference,SourceScalarAffineSecondCutoffTail.firstGeometricCoefficient,
      SourceScalarAffineSecondCutoffTail.firstBinomial]
    ring
  rw [he,neg_sq]
  nlinarith [mul_nonneg
    (sq_nonneg (SourceScalarAffineSecondCutoffTail.firstGeometricCoefficient m ell z))
    (sq_nonneg ((reciprocal z)^2))]

/-- The contact weight keeps the original binomial difference before invoking the source Hardy estimate. -/
theorem original_inverse_contact_localized_weight (m ell : ℕ) (f : QuantumTest) :
    (∑ i : ScalarIndex,‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell f))‖^2)  ≤
      (1/4 : ℝ)*‖embed (SourceScalarAffineSecondCutoffTail.firstGeometricAction m ell
        (inverseAction (inverseVolumeAction f)))‖^2 := by
  simp_rw [contact_real_norm,GaussBoundedMultiplier.norm_square_integral]
  have hi (i : ScalarIndex) := (densityPair_integrable (realContact i m ell (inverseVolumeAction f))
    (realContact i m ell (inverseVolumeAction f))).re
  have hj := (densityPair_integrable
    (SourceScalarAffineSecondCutoffTail.firstGeometricAction m ell (inverseAction (inverseVolumeAction f)))
    (SourceScalarAffineSecondCutoffTail.firstGeometricAction m ell (inverseAction (inverseVolumeAction f)))).re
  rw [←integral_finsetSum _ (fun i _ => hi i),←integral_const_mul]
  apply integral_mono (integrable_finsetSum _ (fun i _ => hi i)) (hj.const_mul _)
  intro z
  change (∑ i : ScalarIndex,(densityPair (realContact i m ell (inverseVolumeAction f))
    (realContact i m ell (inverseVolumeAction f)) z).re) ≤
    (1/4 : ℝ)*(densityPair
      (SourceScalarAffineSecondCutoffTail.firstGeometricAction m ell (inverseAction (inverseVolumeAction f)))
      (SourceScalarAffineSecondCutoffTail.firstGeometricAction m ell (inverseAction (inverseVolumeAction f))) z).re
  simp only [realContact,GaussRadialDomain.inverseAction,
    SourceScalarAffineSecondCutoffTail.firstGeometricAction,scalar_density]
  rw [←Finset.sum_mul]
  have h := mul_le_mul_of_nonneg_right (gradient_localized m ell z)
    (density_nonnegative (inverseVolumeAction f) z)
  exact h.trans_eq (by ring)

private theorem theta_hardy_commute (a b : ℕ) (f : QuantumTest) :
    SourceNativeCutoffContact.thetaAction a b (inverseAction (inverseVolumeAction f))=
      inverseAction (inverseVolumeAction (SourceNativeCutoffContact.thetaAction a b f)) := by
  apply DFunLike.ext
  intro z
  change (SourceNativeCutoffContact.theta a b z : ℂ) •
    ((reciprocal z : ℂ) • ((reciprocalVolume z : ℂ) • f z))=
    (reciprocal z : ℂ) • ((reciprocalVolume z : ℂ) •
      ((SourceNativeCutoffContact.theta a b z : ℂ) • f z))
  simp only [smul_smul]
  congr 1
  ring

/-- Both source cutoff windows enter before Hardy, so the right side contains localized native energies. -/
theorem original_inverse_contact_window_native (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell)
    (f : QuantumTest) :
    (∑ i : ScalarIndex,‖embed (inverseVolumeAction (contactAction (scalarDirection i) m ell f))‖^2)  ≤
      (72/3481 : ℝ)*(inverseNativeEnergy (SourceNativeCutoffContact.thetaAction (m/2) m f)+
        inverseNativeEnergy (SourceNativeCutoffContact.thetaAction (ell/2) ell f)) := by
  have hg := SourceScalarAffineSecondCutoffTail.actual_first_geometric_norm_domination m ell hm hell
    (inverseAction (inverseVolumeAction f))
  rw [←SourceNativeCutoffContact.theta_core,←SourceNativeCutoffContact.theta_core,
    theta_hardy_commute,theta_hardy_commute] at hg
  have hmH := original_inverse_native_hardy (SourceNativeCutoffContact.thetaAction (m/2) m f)
  have heH := original_inverse_native_hardy (SourceNativeCutoffContact.thetaAction (ell/2) ell f)
  have hc := original_inverse_contact_localized_weight m ell f
  norm_num at hmH heH
  nlinarith only [hg,hmH,heH,hc]

/-- The entire diagonal IMS correction is paid by two actual smaller-index energies, each with factor 72/3481. -/
theorem original_inverse_ims_window (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell) (f : QuantumTest) :
    (inverseContact m ell f f).re  ≤  (72/3481 : ℝ)*
      (inverseForm (SourceNativeCutoffContact.thetaAction (m/2) m f)+
        inverseForm (SourceNativeCutoffContact.thetaAction (ell/2) ell f)) := by
  have hn : 0<sourceTime 0 := by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hc := mul_le_mul_of_nonneg_left (original_inverse_contact_window_native m ell hm hell f)
    (show 0 ≤ 4*sourceTime 0 by positivity)
  have hmH := original_inverse_native_bound (SourceNativeCutoffContact.thetaAction (m/2) m f)
  have heH := original_inverse_native_bound (SourceNativeCutoffContact.thetaAction (ell/2) ell f)
  rw [inverse_contact_real]
  nlinarith only [hc,hmH,heH]

/-- The generated windows retain the same original varying resolvent state and the complete signed source exchange. -/
theorem actual_signed_contact_window (sharp : Bool) (m ell : ℕ) (hm : 1 ≤ m) (hell : m ≤ ell)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (inverseContact m ell (state F z hz g) (state F z hz g)).re  ≤  (72/3481 : ℝ)*
      ((signedPair sharp (m/2) m (state F z hz g) (state F z hz g)).re+
        (signedPair sharp (ell/2) ell (state F z hz g) (state F z hz g)).re) := by
  rw [original_diagonal_energy_exchange,original_diagonal_energy_exchange]
  exact original_inverse_ims_window m ell hm hell (state F z hz g)

end LowEnergy.SourceInverseContactHardy
