import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeHardy
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceScalarVolumePressure
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiForceNoetherCurrent
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedInputCommonPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ScalarInputJointNoether
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussYukawaCoefficient GaussRadialDomain GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarDoubleCurrent
open SourceClockPhiRadiusSourceCurrent SourceInverseVolumeHardy ReverseForceNoetherPayer
open SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceScalarVolumePressure SourceScalarSpatialCurrent
open MeasureTheory
open scoped InnerProductSpace ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev B:End:=scalarBulkComplete
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarBulkComplete sourceTime

def affineHardyCost:ℝ:=2+‖vacuum‖^2/2
private theorem cost_nonnegative:0 ≤ affineHardyCost:=by unfold affineHardyCost;positivity
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem radius_comparison(z:SourceCoordinateSlice):radius z^2 ≤ affineHardyCost*phiRadius z^2:=by
  have hsub:scalarField z-vacuum=(z.2.1:Scalar):=by unfold scalarField;abel
  have hnorm:‖(z.2.1:Scalar)‖ ≤ ‖scalarField z‖+‖vacuum‖:=by rw [←hsub];exact norm_sub_le _ _
  have hsq:=sq_le_sq₀ (norm_nonneg (z.2.1:Scalar)) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 hnorm
  have hr:radius z^2=1+‖(z.2.1:Scalar)‖^2/4:=Real.sq_sqrt (by positivity)
  have hp:phiRadius z^2=1+‖scalarField z‖^2/4:=Real.sq_sqrt (by positivity)
  rw [hr,hp]
  unfold affineHardyCost
  nlinarith [sq_nonneg (‖scalarField z‖-‖vacuum‖),mul_nonneg (sq_nonneg ‖scalarField z‖) (sq_nonneg ‖vacuum‖)]
private theorem inverse_comparison(z:SourceCoordinateSlice):
    phiReciprocal z^2 ≤ affineHardyCost*reciprocal z^2:=by
  have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
  have hr:=radius_pos z
  have h:(1:ℝ)/(phiRadius z)^2 ≤ affineHardyCost/(radius z)^2:=
    (div_le_div_iff₀ (sq_pos_of_pos hp) (sq_pos_of_pos hr)).mpr (by
    simpa only [one_mul] using radius_comparison z)
  unfold phiReciprocal reciprocal
  rw [inv_pow,inv_pow]
  simpa only [inv_eq_one_div,mul_one_div] using h
private theorem density_square(f g:QuantumTest)(z:SourceCoordinateSlice)(c:ℝ)
    (hg:g z=(c:ℂ) • f z):densityPair g g z=(c^2:ℝ)*densityPair f f z:=by
  change inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (g z)) (g z)=
    ((c^2:ℝ):ℂ)*inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (f z)) (f z)
  rw [hg,map_smul,inner_smul_left,inner_smul_right]
  simp only [Complex.conj_ofReal,Complex.ofReal_pow]
  ring
private theorem density_nonnegative(f:QuantumTest)(z:SourceCoordinateSlice):0 ≤ (densityPair f f z).re:=by
  by_cases hz:z∈physicalChart
  · change 0≤RCLike.re (inner ℂ (GaussFockWeights.weight (fun N=>(GaussDensityCore.density N z:ℂ)) (f z)) (f z))
    rw [GaussBoundedMultiplier.weighted_square (fun N=>GaussDensityCore.density N z)
      (fun N=>(GaussDensityCore.density_pos N ⟨z,hz⟩).le)]
    exact sq_nonneg _
  · have hf:f z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]
private theorem inverse_norm_comparison(f:QuantumTest):
    ‖embed (S f)‖^2 ≤ affineHardyCost*‖embed (inverseAction f)‖^2:=by
  have hp(z:SourceCoordinateSlice):RCLike.re (densityPair (S f) (S f) z) ≤
      affineHardyCost*RCLike.re (densityPair (inverseAction f) (inverseAction f) z):=by
    rw [density_square f (S f) z (phiReciprocal z) rfl,
      density_square f (inverseAction f) z (reciprocal z) rfl]
    simp only [RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact (mul_le_mul_of_nonneg_right (inverse_comparison z) (density_nonnegative f z)).trans_eq (mul_assoc _ _ _)
  have h:=integral_mono ((densityPair_integrable (S f) (S f)).re (𝕜:=ℂ))
    (((densityPair_integrable (inverseAction f) (inverseAction f)).re (𝕜:=ℂ)).const_mul affineHardyCost) hp
  rw [←GaussBoundedMultiplier.norm_square_integral,integral_const_mul,←GaussBoundedMultiplier.norm_square_integral] at h
  exact h

/-- The singular affine-field input price is generated by the original 61-dimensional native Hardy form. The vacuum translation is a fixed source constant. -/
theorem actual_affine_inverse_native_hardy(f:QuantumTest):
    ‖embed (S (U f))‖^2 ≤ (16*affineHardyCost/59^2)*inverseNativeEnergy f:=by
  have h:=inverse_norm_comparison (U f)
  have hn:=mul_le_mul_of_nonneg_left (original_inverse_native_hardy f) cost_nonnegative
  exact h.trans (hn.trans_eq (by ring))

theorem actual_affine_inverse_scalar_hardy(f:QuantumTest):
    ‖embed (S (U f))‖^2 ≤ (4*affineHardyCost/(59^2*n))*scalarEnergy f:=by
  have he:4*n*inverseNativeEnergy f ≤ scalarEnergy f:=by
    unfold scalarEnergy shiftedMoment
    have hs:0 ≤ ∑a:ScalarIndex,‖embed (shiftedColumn a f)‖^2:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
    have hn:=n_pos
    nlinarith only [mul_nonneg hn.le hs]
  have h:=mul_le_mul_of_nonneg_left he (show 0 ≤ 4*affineHardyCost/(59^2*n) by
    exact div_nonneg (mul_nonneg (by norm_num) cost_nonnegative) (mul_nonneg (by norm_num) n_pos.le))
  have hc:(4*affineHardyCost/(59^2*n))*(4*n*inverseNativeEnergy f)=
      (16*affineHardyCost/59^2)*inverseNativeEnergy f:=by field_simp [n_pos.ne'];ring
  rw [hc] at h
  exact (actual_affine_inverse_native_hardy f).trans h

def inputCausalSign(advanced:Bool):ℝ:=if advanced then -1 else 1
def inputScalarWardPrice(advanced:Bool)(w f:QuantumTest):ℝ:=
  inputCausalSign advanced*((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
    n^2*‖vacuum‖^2*‖embed w‖^2
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]

/-- The input Ward retains the entire covariant coframe pressure and original signed scalar-spatial current. -/
theorem actual_input_scalar_pressure_price(advanced:Bool)(w f:QuantumTest):
    inputScalarWardPrice advanced w f=
      inputCausalSign advanced*(sourcePair f (B w)).im-
      (inputCausalSign advanced/2)*(sourcePair w (volumePressureAction w)).im-
      4*inputCausalSign advanced*(sourcePair w (U (scalarSpatialDivergence w))).im+
      n^2*‖vacuum‖^2*‖embed w‖^2:=by
  unfold inputScalarWardPrice
  rw [original_geometric_pressure]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,pair_add_r,
    sourcePair,map_smul,inner_smul_right,Complex.add_im,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,
    zero_mul,add_zero]
  ring

/-- The actual oscillator gap pays the affine inverse input by its complete forcing and geometric scalar current. Projection and coframe/spatial terms remain in those original words. -/
theorem actual_full_source_input_scalar_gap(μ:ℝ)(hgap:2*n<μ)(advanced:Bool)(q:ℝ)(w f:QuantumTest)
    (he:diagonalAction w=f+actualFrequency advanced μ q • w):
    (μ-2*n)*scalarEnergy w ≤ inputScalarWardPrice advanced w f ∧
    ‖embed (S (U w))‖^2 ≤ (4*affineHardyCost/(59^2*n*(μ-2*n)))*inputScalarWardPrice advanced w f:=by
  have h:=actual_full_source_mixed_scalar_noether (actualFrequency advanced μ q) w f w f he he
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B w))
  simp only [Complex.conj_im] at hc
  rw [original_scalar_energy] at h
  have hg:bracket diagonalAction B=scalarCurrentComplete+geometricScalarCurrent:=original_scalar_current_geometric
  rw [hg] at h
  simp only [LinearMap.add_apply,pair_add_r,Complex.add_im] at h
  have ho:=original_scalar_oscillator_bound w
  have hu:0 ≤ μ-2*n:=sub_nonneg.mpr hgap.le
  have hprice:(μ-2*n)*scalarEnergy w ≤ inputScalarWardPrice advanced w f:=by
    unfold inputScalarWardPrice inputCausalSign
    cases advanced
    · simp only [Bool.false_eq_true,ite_false,actualFrequency,line_im,one_mul] at h ⊢
      have hh:=neg_le_abs ((sourcePair w (scalarCurrentComplete w)).im/2)
      linarith only [h,hc,ho,hh]
    · simp only [ite_true,actualFrequency,Complex.star_def,Complex.conj_im,line_im,neg_mul,one_mul] at h ⊢
      have hh:=le_abs_self ((sourcePair w (scalarCurrentComplete w)).im/2)
      linarith only [h,hc,ho,hh]
  refine ⟨hprice,?_⟩
  have hp:=mul_le_mul_of_nonneg_left hprice
    (show 0 ≤ 4*affineHardyCost/(59^2*n*(μ-2*n)) by
      exact div_nonneg (mul_nonneg (by norm_num) cost_nonnegative)
        (mul_nonneg (mul_nonneg (by norm_num) n_pos.le) hu))
  have hcoef:(4*affineHardyCost/(59^2*n*(μ-2*n)))*((μ-2*n)*scalarEnergy w)=
      (4*affineHardyCost/(59^2*n))*scalarEnergy w:=by
    rw [←div_div,←mul_assoc,div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hgap))]
  rw [hcoef] at hp
  exact (actual_affine_inverse_scalar_hardy w).trans hp
end LowEnergy.ScalarInputJointNoether
