import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseScalarNoetherPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare SourceCoframeVolumeCurrent SourceCoframeDilation
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarEssentialBudget SourceScalarShiftedBulk
open SourceScalarInverseNativeEnergy MeasureTheory
open SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource SourceClockPhiNativeMatchedSource
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceClockReflectedForm
open FirstCurrentJointBudget FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier OriginalRCommutatorSource
open ClockPhiHeatCorrectedCovarianceSource
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev D:End:=combinedGenerator
private abbrev B:End:=scalarBulkComplete
private abbrev Z:End:=reverseNativeClock
private abbrev U:End:=inverseVolumeAction
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarBulkComplete normalizedState normalizedForcing
  wholeSourceNext correctedCompleteCore reverseNativeClock
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only[sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem flow_pair_generator (flow:ℝ→End)(G:End)
    (hzero:∀f,flow 0 f=f)
    (hpair:∀t f g,sourcePair (flow t f) (flow t g)=sourcePair f g)
    (hderiv:∀f,HasDerivAt (fun t:ℝ=>embed (flow t f)) (embed (G f)) 0)
    (f g:QuantumTest):sourcePair f (G g)= -sourcePair (G f) g:=by
  unfold sourcePair at hpair ⊢
  have h:=(hderiv f).inner ℂ (hderiv g)
  simp only [hzero] at h
  have he:(fun t:ℝ=>inner ℂ (embed (flow t f)) (embed (flow t g)))=
      fun _=>inner ℂ (embed f) (embed g):=funext (fun t=>hpair t f g)
  rw [he] at h
  have heq:=h.unique (hasDerivAt_const (0:ℝ) (inner ℂ (embed f) (embed g)))
  exact eq_neg_of_add_eq_zero_left heq
private theorem phi_pair(f g:QuantumTest):
    sourcePair f (SourceScalarAffineScaleTransport.generator g)=
      -sourcePair (SourceScalarAffineScaleTransport.generator f) g:=
  flow_pair_generator SourceScalarAffineScaleTransport.coreFlow
    SourceScalarAffineScaleTransport.generator
    SourceScalarAffineScaleTransport.coreFlow_zero
    SourceScalarAffineScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceScalarAffineScaleTransport.coreFlow_zero] using!
      SourceScalarAffineScaleTransport.strong_core_derivative q 0) f g
private theorem gauge_pair(f g:QuantumTest):
    sourcePair f (SourceGaugeScaleTransport.generator g)=
      -sourcePair (SourceGaugeScaleTransport.generator f) g:=
  flow_pair_generator SourceGaugeScaleTransport.coreFlow
    SourceGaugeScaleTransport.generator
    SourceGaugeScaleTransport.coreFlow_zero
    SourceGaugeScaleTransport.coreFlow_pair
    (fun q=>by simpa only [SourceGaugeScaleTransport.coreFlow_zero] using!
      SourceGaugeScaleTransport.strong_core_derivative q 0) f g
private theorem combined_pair_source(f g:QuantumTest):sourcePair f (D g)= -sourcePair (D f) g:=by
  have hp:=phi_pair f g
  have hg:=gauge_pair f g
  change sourcePair f (SourceScalarAffineScaleTransport.generator g-
      SourceGaugeScaleTransport.generator g)=
    -sourcePair (SourceScalarAffineScaleTransport.generator f-
      SourceGaugeScaleTransport.generator f) g
  simp only [sourcePair,map_sub,inner_sub_left,inner_sub_right] at hp hg ⊢
  linear_combination hp-hg
private theorem combined_pair(f g:QuantumTest):sourcePair (D f) g= -sourcePair f (D g):=by
  simpa only [neg_neg] using congrArg Neg.neg (combined_pair_source f g).symm


private theorem scalar_multiplier_sign (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sign : ℝ)
    (hs : ∀ z : physicalChart,0 ≤ sign*c z.val) (f : QuantumTest) :
    0 ≤ sign*(sourcePair f (multiply c hc f)).re := by
  rw [sourcePair_integral]
  have hr : (∫ z, densityPair f (multiply c hc f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫ z, (densityPair f (multiply c hc f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only using! (integral_re (densityPair_integrable f (multiply c hc f))).symm
  rw [hr,←MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_nonneg
  intro z
  change 0 ≤ sign*(densityPair f (multiply c hc f) z).re
  have he : densityPair f (multiply c hc f) z=(c z : ℂ)*densityPair f f z := inner_smul_right _ _ _
  rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  by_cases hz : z∈physicalChart
  · have hp : 0 ≤ (densityPair f f z).re := by
      change 0 ≤ (inner ℂ (GaussFockWeights.weight (fun N => (GaussDensityCore.density N z : ℂ)) (f z)) (f z)).re
      have hw := GaussBoundedMultiplier.weighted_square (fun N => GaussDensityCore.density N z)
        (fun N => (GaussDensityCore.density_pos N ⟨z,hz⟩).le) (f z)
      have hp := (sq_nonneg ‖GaussBoundedMultiplier.halfWeight (fun N => GaussDensityCore.density N z) (f z)‖).trans_eq hw.symm
      simpa only using! hp
    simpa only [mul_assoc] using mul_nonneg (hs ⟨z,hz⟩) hp
  · have hf : f z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,mul_zero]
    exact le_refl _


private theorem center_nonnegative(w:QuantumTest):0≤(sourcePair w (U (centeredAction w))).re:=by
  let b:SourceCoordinateSlice→ℝ:=fun z=>sourceTime 0*‖scalarField z‖^2
  have hb(z:physicalChart):ContDiffAt ℝ ∞ b z.val:=contDiffAt_const.mul (scalarField_smooth.norm_sq ℝ).contDiffAt
  have he:U*centeredAction=multiply b hb:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    by_cases hz:z∈physicalChart
    · change (reciprocalVolume z:ℂ) • (((sourceTime 0*volume z*‖scalarField z‖^2:ℝ):ℂ) • f z)=
        (((sourceTime 0*‖scalarField z‖^2:ℝ):ℂ) • f z)
      rw [smul_smul,←Complex.ofReal_mul]
      congr 1;congr 1
      unfold reciprocalVolume
      field_simp [(volume_pos ⟨z,hz⟩).ne']
    · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
      exact (hzero _).trans (hzero _).symm
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hp:=scalar_multiplier_sign b hb 1 (fun z=>by dsimp[b];positivity) w
  change 0≤(sourcePair w ((U*centeredAction) w)).re
  rw [he]
  simpa only [one_mul] using hp

/-- Both reserves in the native payer have their original positive forms. -/
theorem actual_reverse_scalar_reserve_nonnegative(w:QuantumTest):0≤reverseScalarReserve w:=by
  have hn:0<n:=by
    rw [show n=sourceTime 0 from rfl,source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hI:0≤SourceScalarInverseNativeEnergy.inverseNativeEnergy w:=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hc:=center_nonnegative w
  unfold reverseScalarReserve
  positivity
private theorem Z_pair(f g:QuantumTest):sourcePair f (Z g)= -sourcePair (Z f) g:=by
  unfold Z reverseNativeClock
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,pair_sub_l,pair_sub_r,pair_smul_l,pair_smul_r,
    combined_pair_source,SourceCoframeDilation.dilation_pair,Complex.star_def,map_mul,map_ofNat,Complex.conj_I]
  ring
private theorem scalar_self (f:QuantumTest):sourcePair f (B f)=((scalarEnergy f:ℝ):ℂ) := by
  have hr:=original_scalar_energy f
  have hp:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B f))
  rw [←original_scalar_pair] at hp
  simp only [Complex.conj_im] at hp
  apply Complex.ext
  · exact hr
  · simp only [Complex.ofReal_im];linarith only [hp]
private theorem scalar_ward (w f:QuantumTest)(z:ℂ)(he:diagonalAction w=f+z • w):
    z.im*scalarEnergy w=(sourcePair f (B w)).im-
      (sourcePair w ((diagonalAction*B-B*diagonalAction) w)).im/2 := by
  have hp:sourcePair w ((diagonalAction*B-B*diagonalAction) w)=
      sourcePair (diagonalAction w) (B w)-sourcePair (B w) (diagonalAction w) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,diagonalAction_pair,original_scalar_pair]
  have hbself:sourcePair (B w) w=((scalarEnergy w:ℝ):ℂ) :=
    (original_scalar_pair w w).symm.trans (scalar_self w)
  rw [he,pair_add_l,pair_smul_l,pair_add_r,pair_smul_r,scalar_self,hbself] at hp
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate f (B w))
  simp only [Complex.conj_im] at hc
  have hi:=congrArg Complex.im hp
  simp only [Complex.sub_im,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.star_def,Complex.conj_re,Complex.conj_im,mul_zero,zero_add] at hi
  linarith only [hi,hc]


def reverseSourceEndpoint(h:ℝ)(forward:Bool)(w f:QuantumTest):QuantumTest×QuantumTest:=
  let c:ℂ:=if forward then (h:ℂ) else -(h:ℂ)
  (w+c • Z w,f+c • (Z f+bracket diagonalAction Z w))
def fullScalarNoether(w f:QuantumTest):ℝ:=
  (sourcePair f (B w)).im-(sourcePair w (bracket diagonalAction B w)).im/2

def reverseScalarNoetherWork(h:ℝ)(z:ℂ)(w f:QuantumTest):ℝ:=
  (fullScalarNoether (reverseSourceEndpoint h false w f).1 (reverseSourceEndpoint h false w f).2-
    fullScalarNoether (reverseSourceEndpoint h true w f).1 (reverseSourceEndpoint h true w f).2)/(2*h*z.im)

private theorem endpoint_source(h:ℝ)(forward:Bool)(z:ℂ)(w f:QuantumTest)(he:diagonalAction w=f+z • w):
    diagonalAction (reverseSourceEndpoint h forward w f).1=
      (reverseSourceEndpoint h forward w f).2+z • (reverseSourceEndpoint h forward w f).1:=by
  unfold reverseSourceEndpoint bracket
  simp only [map_add,map_smul,Module.End.mul_apply,LinearMap.sub_apply,he]
  module
private theorem scalar_midpoint(h:ℝ)(w:QuantumTest):
    scalarEnergy (w-(h:ℂ) • Z w)-scalarEnergy (w+(h:ℂ) • Z w)=2*h*reverseScalarCurrent w:=by
  have hc:sourcePair w (bracket Z B w)= -sourcePair (Z w) (B w)-sourcePair w (B (Z w)):=by
    simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r,Z_pair]
  rw [←original_scalar_energy,←original_scalar_energy]
  unfold reverseScalarCurrent
  rw [hc]
  simp only [map_add,map_sub,map_smul,pair_add_l,pair_add_r,pair_sub_l,pair_sub_r,pair_smul_l,pair_smul_r,
    Complex.add_re,Complex.sub_re,Complex.neg_re,Complex.mul_re,
    Complex.star_def,Complex.conj_ofReal,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- Both endpoints carry the same original H0 equation. Their exact finite Noether difference supplies the scalar-current payment, with no h-squared remainder and no endpoint upper premise. -/
theorem actual_reverse_scalar_noether_work(h:ℝ)(hh:0<h)(z:ℂ)(hz:z.im≠0)(w f:QuantumTest)
    (he:diagonalAction w=f+z • w):
    (∀forward:Bool,diagonalAction (reverseSourceEndpoint h forward w f).1=
      (reverseSourceEndpoint h forward w f).2+z • (reverseSourceEndpoint h forward w f).1) ∧
    reverseScalarNoetherWork h z w f=reverseScalarCurrent w:=by
  refine ⟨fun forward=>endpoint_source h forward z w f he,?_⟩
  have hp:=scalar_ward (reverseSourceEndpoint h true w f).1 (reverseSourceEndpoint h true w f).2 z
    (endpoint_source h true z w f he)
  have hm:=scalar_ward (reverseSourceEndpoint h false w f).1 (reverseSourceEndpoint h false w f).2 z
    (endpoint_source h false z w f he)
  change z.im*scalarEnergy (reverseSourceEndpoint h true w f).1=fullScalarNoether _ _ at hp
  change z.im*scalarEnergy (reverseSourceEndpoint h false w f).1=fullScalarNoether _ _ at hm
  unfold reverseScalarNoetherWork
  rw [←hp,←hm,←mul_sub]
  simp only [reverseSourceEndpoint,ite_true,Bool.false_eq_true,ite_false,neg_smul,←sub_eq_add_neg]
  rw [scalar_midpoint]
  field_simp [hh.ne',hz]

/-- The full native price receives the generated finite source work and retains its kinetic and scalar-square reserves. -/
def reverseNativeWorkPrice(half:Bool)(h:ℝ)(z:ℂ)(w f:QuantumTest):ℝ:=
  reverseNativePrice half w+reverseNoetherFactor half*(reverseScalarNoetherWork h z w f-reverseScalarCurrent w)

/-- This is the actual original clocked whole-source consumer. The electric update, complete forcing, negative matched square, gauge and magnetic fields remain unchanged. -/
theorem actual_original_whole_reverse_noether_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ)(h:ℝ)(hh:0<h):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=wholeSourceNext s hs half advanced m ell F g q
    let b:=clockSourcePair s hs x a
    physicalJointPrice half advanced z b≤reverseNativeWorkPrice half h z b.1 b.2+
      originalNormalizerPrice s hs x a-2*gaugeForm (U b.1)-8*(sourcePair b.1 (U (magneticAction b.1))).re:=by
  dsimp only
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  have hν:0<sourceNoetherFrequency half:=by linarith [actual_source_noether_gap half]
  have hz:(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
    cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
      Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hν.ne'
  have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have hp:=actual_full_source_native_reverse_payment half advanced m ell F q hz g _ _ he
  have hw:=(actual_reverse_scalar_noether_work h hh _ hz _ _ he).2
  unfold reverseNativeWorkPrice
  rw [hw,sub_self,mul_zero,add_zero]
  dsimp only [originalNormalizerPrice]
  linarith only [hp]
end LowEnergy.ReverseNativeClock
