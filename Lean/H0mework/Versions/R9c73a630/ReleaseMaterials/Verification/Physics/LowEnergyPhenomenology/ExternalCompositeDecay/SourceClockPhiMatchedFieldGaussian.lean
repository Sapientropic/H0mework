import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedConstantReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NativePointReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceCoframeVolumeCurrent SourceDilationRemainder
open SourceClockPhiCoframeForwardCore ClockPhiHeatCorrectedCovarianceSource SourceClockPhiForwardNativeReturn
open SourceClockPhiCorrectedWeightTransport SourceClockPhiProfileNativeReturn SourceClockPhiProfileLocalNativeReturn
open SourceClockPhiProfileCoframeReturn SourceClockPhiHeatLocalNativeGaussian SourceClockPhiCorrectedGaussianPair
open SourceClockReflectedForm SourceScalarVirialBulk SourceHamiltonianVolume
open SourceClockPhiMatchedDiffusionSource MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed
private theorem volume_pair(f g:QuantumTest):sourcePair f (volumeAction g)=sourcePair (volumeAction f) g:=multiply_pair _ _ _ _
private theorem pair_smul_right(f g:QuantumTest)(c:ℂ):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem pair_sum_right {ι:Type*}[Fintype ι](f:QuantumTest)(g:ι→QuantumTest):sourcePair f (∑i,g i)=∑i,sourcePair f (g i):=by simp only [sourcePair,map_sum,inner_sum]
private theorem coeff_first(t ξ η:ℝ)(x y:SourceCoordinateSlice)(h:x.1=y.1):
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rcases x with ⟨x₁,x₂⟩
  rcases y with ⟨y₁,y₂⟩
  dsimp at h
  subst y₁
  rfl
private theorem U_pair(f g:QuantumTest):sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g:=
  multiply_pair _ _ _ _
private theorem forwardU_pair(t:ℝ)(ht:0<t)(f g:QuantumTest):
    sourcePair f (forwardUAction t ht.le g)=sourcePair (forwardUAction t ht.le f) g:=multiply_pair _ _ _ _
private theorem U_return(t:ℝ)(ht:0<t)(ξ η:ℝ)(f:QuantumTest):
    inverseVolumeAction (correctedCompleteCore t ht ξ η f)=
      correctedCompleteCore t ht ξ η (forwardUAction t ht.le f):=
  LinearMap.congr_fun (actual_corrected_complete_inverse_volume t ht ξ η) f
private theorem inverse_sector(t:ℝ)(ht:0<t)(X:End)(p q:ℝ)
    (law:∀ξ η:ℝ,∀f g:QuantumTest,
      sourcePair (correctedCompleteCore t ht ξ η f) (X (correctedCompleteCore t ht ξ η g))=
        sourcePair f (correctedProfileWeight t ht p q ξ η (X g))) (f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g))) ∂γ.prod γ)=
      sourcePair (forwardUAction t ht.le f) (gaussianProfileWeight t ht (p+q*(q-3)/18) (X g)):=by
  have he(x:ℝ×ℝ):sourcePair (correctedCompleteCore t ht x.1 x.2 f)
      (inverseVolumeAction (X (correctedCompleteCore t ht x.1 x.2 g)))=
      sourcePair (forwardUAction t ht.le f) (correctedProfileWeight t ht p q x.1 x.2 (X g)):=by
    rw [U_pair,U_return,law]
  simpa only [he] using
    actual_corrected_gaussian_weighted_source_pair t ht p q (forwardUAction t ht.le f) (X g)

private theorem gauge_volume_smooth (i j : Fin 3) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => volume w*gaugeWeight w i j) z.val :=
  volume_smooth.contDiffAt.mul (gaugeWeight_smooth i j z)
private theorem gauge_volume_form (f : QuantumTest) :
    (sourcePair f (volumeAction (gaugeKinetic f))).re=gaugeForm f := by
  have ht (a : LieIndex) (i j : Fin 3) : sourcePair (volumeAction f)
      (sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j) f)=
      sourcePair (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f)
        (multiply (fun z => volume z*gaugeWeight z i j) (gauge_volume_smooth i j)
          (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)) := by
    change sourcePair (volumeAction f) (GaussMomentumAdjoint.adjoint (gaugeDirection i a)
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)
        (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f)))=_
    rw [GaussNativeForm.adjoint_pair]
    have hc := LinearMap.congr_fun (SourceHamiltonianVolume.native_momentum_volume (gaugeDirection i a)).eq f
    change GaussCoreDifferential.covariantMomentum (gaugeDirection i a) (volumeAction f)=
      volumeAction (GaussCoreDifferential.covariantMomentum (gaugeDirection i a) f) at hc
    rw [hc,←volume_pair]
    congr 1
    apply DFunLike.ext
    intro z
    change (volume z:ℂ) • ((gaugeWeight z i j:ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z))=
      ((volume z*gaugeWeight z i j:ℝ):ℂ) • (GaussCoreDifferential.covariantMomentum (gaugeDirection j a) f z)
    simp only [smul_smul,Complex.ofReal_mul]
  rw [volume_pair]
  simp only [gaugeKinetic,LinearMap.smul_apply,LinearMap.sum_apply,pair_smul_right,pair_sum_right,ht]
  unfold gaugeForm
  simp only [Complex.mul_re,Complex.div_re,Complex.div_im]
  norm_num


private theorem volume_inverse(f:QuantumTest):volumeAction (inverseVolumeAction f)=f:=by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (volume z:ℂ) • ((reciprocalVolume z:ℂ) • f z)=f z
    rw [smul_smul]
    have h:(volume z:ℂ)*(reciprocalVolume z:ℂ)=1:=by
      simp only [reciprocalVolume,Complex.ofReal_inv]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne')
    rw [h,one_smul]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem inverse_volume(f:QuantumTest):inverseVolumeAction (volumeAction f)=f:=by
  have h:inverseVolumeAction (volumeAction f)=volumeAction (inverseVolumeAction f):=by
    apply DFunLike.ext
    intro z
    change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=(volume z:ℂ) • ((reciprocalVolume z:ℂ) • f z)
    exact smul_comm _ _ _
  exact h.trans (volume_inverse f)

private theorem U_gauge(f:QuantumTest):gaugeKinetic (inverseVolumeAction f)=inverseVolumeAction (gaugeKinetic f):=by
  have h:=LinearMap.congr_fun SourceHamiltonianVolume.gauge_kinetic_volume.eq (inverseVolumeAction f)
  change gaugeKinetic (volumeAction (inverseVolumeAction f))=volumeAction (gaugeKinetic (inverseVolumeAction f)) at h
  rw [volume_inverse] at h
  have hi:=congrArg inverseVolumeAction h
  rw [inverse_volume] at hi
  exact hi.symm

private theorem gauge_inverse_form(f:QuantumTest):gaugeForm (inverseVolumeAction f)=
    (sourcePair f (inverseVolumeAction (gaugeKinetic f))).re:=by
  rw [←gauge_volume_form,volume_pair,volume_inverse,U_gauge]

private theorem spatial_split:spatialAction=scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((SourceDilationRemainder.spatialPotential z:ℝ):ℂ) • f z=_
  change (((_+_:ℝ):ℂ) • f z)=_
  rw [Complex.ofReal_add,add_smul]
  rfl


private theorem spatial_inverse_form(f:QuantumTest):spatialForm (inverseVolumeAction f)=
    (sourcePair f (inverseVolumeAction (spatialAction f))).re:=by
  unfold spatialForm
  rw [volume_pair,volume_inverse]
  have h:spatialAction (inverseVolumeAction f)=inverseVolumeAction (spatialAction f):=by
    apply DFunLike.ext
    intro z
    change (SourceDilationRemainder.spatialPotential z:ℂ) • ((reciprocalVolume z:ℂ) • f z)=
      (reciprocalVolume z:ℂ) • ((SourceDilationRemainder.spatialPotential z:ℂ) • f z)
    exact smul_comm _ _ _
  rw [h]


def matchedNativeMean(s:ℝ)(hs:0<s)(f:QuantumTest):ℂ:=
  (2:ℂ)*sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs (-1/9) (GaussMatterCore.matterAction f))+
  (8/5:ℂ)*sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs (4/3) (vacuumConstantAction f))-
  (12:ℂ)*sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs (11/9) (gaugeKinetic f))-
  (12:ℂ)*sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs (2/3) (scalarSpatialAction f))-
  (12:ℂ)*sourcePair (forwardUAction s hs.le f) (gaussianProfileWeight s hs (8/9) (magneticAction f))

private def matchedNativeWord(f:QuantumTest):ℂ:=
  (2:ℂ)*sourcePair f (inverseVolumeAction (GaussMatterCore.matterAction f))+
  (8/5:ℂ)*sourcePair f (inverseVolumeAction (vacuumConstantAction f))-
  (12:ℂ)*sourcePair f (inverseVolumeAction (gaugeKinetic f))-
  (12:ℂ)*sourcePair f (inverseVolumeAction (scalarSpatialAction f))-
  (12:ℂ)*sourcePair f (inverseVolumeAction (magneticAction f))

private theorem actual_matched_native_gaussian(s:ℝ)(hs:0<s)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>matchedNativeWord (correctedCompleteCore s hs x.1 x.2 f)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,matchedNativeWord (correctedCompleteCore s hs x.1 x.2 f) ∂γ.prod γ)=matchedNativeMean s hs f:=by
  have h1:=inverse_sector s hs GaussMatterCore.matterAction 0 1
    (fun ξ η p q=>actual_profile_complete_matter_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h2:=inverse_sector s hs vacuumConstantAction (4/3) 0
    (fun ξ η p q=>actual_profile_complete_vacuum_constant_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h3:=inverse_sector s hs gaugeKinetic (2/3) (-2)
    (fun ξ η p q=>actual_complete_profile_gauge_source s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h4:=inverse_sector s hs scalarSpatialAction (2/3) 0
    (fun ξ η p q=>actual_profile_complete_signed_spatial_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have h5:=inverse_sector s hs magneticAction (2/3) 4
    (fun ξ η p q=>actual_profile_complete_magnetic_pair s hs (correctedCoefficient s ξ η)
      (coefficient_smooth s hs ξ η) (coeff_first s ξ η) p q) f f
  have H1:=h1.1.const_mul (2:ℂ)
  have H2:=h2.1.const_mul (8/5:ℂ)
  have H3:=h3.1.const_mul (12:ℂ)
  have H4:=h4.1.const_mul (12:ℂ)
  have H5:=h5.1.const_mul (12:ℂ)
  refine ⟨(((H1.add H2).sub H3).sub H4).sub H5,?_⟩
  unfold matchedNativeWord
  erw [integral_sub ((H1.add H2).sub H3 |>.sub H4) H5,
    integral_sub ((H1.add H2).sub H3) H4,integral_sub (H1.add H2) H3,integral_add H1 H2]
  simp only [integral_const_mul,h1.2,h2.2,h3.2,h4.2,h5.2]
  norm_num [matchedNativeMean]

private theorem actual_matched_field_split(f:QuantumTest):
    matchedField f=(matchedNativeWord f).re+12*sourceTime 0*(spinForm (inverseVolumeAction f)+densityForm (inverseVolumeAction f)):=by
  unfold matchedField matchedNativeWord
  rw [gauge_inverse_form,spatial_inverse_form,spatial_split]
  simp only [Module.End.mul_apply,LinearMap.smul_apply,LinearMap.add_apply,map_add,
    sourcePair,map_smul,inner_add_right,inner_smul_right,Complex.add_re,Complex.sub_re,Complex.mul_re]
  norm_num only [Complex.re_ofNat,Complex.im_ofNat,Complex.div_re,Complex.div_im,
    zero_mul,mul_zero,sub_zero,add_zero,Complex.ofReal_re,Complex.ofReal_im]
  norm_num [Complex.normSq]
  ring

def matchedFieldMean(s:ℝ)(hs:0<s)(f:QuantumTest):ℝ:=
  (matchedNativeMean s hs f).re+12*sourceTime 0*
    (spinForm (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f))+
      densityForm (SourceClockPhiActualCovarianceStep.sourceGain (Real.sqrt s) (forwardUAction s hs.le f)))

/-- The whole literal field price is integrable and generated by the same complete two-noise source. -/
theorem actual_corrected_matched_field_gaussian(s:ℝ)(hs:0<s)(f:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>matchedField (correctedCompleteCore s hs x.1 x.2 f)) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,matchedField (correctedCompleteCore s hs x.1 x.2 f) ∂γ.prod γ)=matchedFieldMean s hs f:=by
  have hN:=actual_matched_native_gaussian s hs f
  have hC:=actual_matched_constant_gaussian s hs f
  have hr : Integrable (fun x:ℝ×ℝ=>(matchedNativeWord (correctedCompleteCore s hs x.1 x.2 f)).re) (γ.prod γ) := by
    simpa only [RCLike.re_eq_complex_re] using hN.1.re
  have hc:=hC.1.const_mul (12*sourceTime 0)
  simp_rw [actual_matched_field_split]
  refine ⟨hr.add hc,?_⟩
  rw [integral_add hr hc,integral_const_mul]
  have he: (∫x:ℝ×ℝ,matchedNativeWord (correctedCompleteCore s hs x.1 x.2 f) ∂γ.prod γ).re=
    ∫x:ℝ×ℝ,(matchedNativeWord (correctedCompleteCore s hs x.1 x.2 f)).re ∂γ.prod γ:=by
    exact (Complex.reCLM.integral_comp_comm hN.1).symm
  rw [←he,hN.2,hC.2]
  rfl

end LowEnergy.NativePointReturn
