import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseNativeClock
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourcePhysicalKineticSquare SourceCoframeVolume
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarEssentialBudget SourceScalarShiftedBulk
open SourceScalarInverseNativeEnergy SourceScalarNativeComparison SourceHamiltonianVolume SourceInverseNoetherEnergy
open SourceScalarPositiveBulkWard SourceClockPhiCombinedScalePressure SourceClockPhiMatchedDiffusionSource
open SourceClockPhiNormalizedScalarBudget SourceClockPhiNativeMatchedSource SourceClockReflectedForm
open SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentJointBudget FirstCurrentAdmissibleElectric OriginalRPrimitiveDifference FirstCurrentDilationPrimitive
open FirstCurrentWholeCarrier ClockPhiHeatCorrectedCovarianceSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev B:End:=scalarBulkComplete
private abbrev Z:End:=reverseNativeClock
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarKinetic scalarBulkComplete
  normalizedState normalizedForcing correctedCompleteCore matchedTester
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only[sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem pair_norm(f:QuantumTest):(sourcePair f f).re=‖embed f‖^2:=by
  simpa only[sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed f)
private theorem U_pair (f g : QuantumTest) : sourcePair f (U g)=sourcePair (U f) g := multiply_pair _ _ _ _
private theorem inverse_volume (f : QuantumTest) : U (volumeAction f)=f := by
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • ((volume z:ℂ) • f z)=f z
    rw [smul_smul]
    simp only [reciprocalVolume,Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (volume_pos ⟨z,hz⟩).ne'),one_smul]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm
private theorem scalar_U (f : QuantumTest) : scalarKinetic (U f)=U (scalarKinetic f) := by
  have h:=LinearMap.congr_fun scalar_kinetic_volume.eq (U f)
  change scalarKinetic (volumeAction (U f))=volumeAction (scalarKinetic (U f)) at h
  rw [volume_inverse] at h
  have hi:=congrArg U h
  rw [inverse_volume] at hi
  exact hi.symm
private theorem inverse_scalar_form (f : QuantumTest) :
    (sourcePair f (U (scalarKinetic f))).re= -(n/2)*inverseNativeEnergy f := by
  have h:=actual_native_scalar_form (U f)
  rw [scalar_U,volume_inverse,original_inverse_native_return] at h
  rw [U_pair]
  exact h

private theorem scalar_bulk_atoms:B=(-8:ℂ) • (U*scalarKinetic)+(8:ℂ) • (U*centeredAction)-
    (8:ℂ) • (U*vacuumLinearAction)+(2:ℂ) • (U*vacuumConstantAction):=by
  have h:=original_bulk_complete_split
  rw [bulkAction,positiveBulk,original_filtered_bulk] at h
  simp only [mul_add,mul_sub,mul_smul_comm] at h
  linear_combination (norm:=module) -h
private theorem constant_local:U*vacuumConstantAction=((n*‖vacuum‖^2:ℝ):ℂ) • (1:End):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  by_cases hz:z∈physicalChart
  · change (reciprocalVolume z:ℂ) • (((n*volume z*‖vacuum‖^2:ℝ):ℂ) • f z)=(((n*‖vacuum‖^2:ℝ):ℂ) • f z)
    rw [smul_smul,←Complex.ofReal_mul]
    congr 1;congr 1
    unfold reciprocalVolume
    field_simp [(volume_pos ⟨z,hz⟩).ne']
  · have hzero(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (hzero _).trans (hzero _).symm

def reverseScalarCurrent(w:QuantumTest):ℝ:=(sourcePair w (bracket Z B w)).re
def reverseScalarReserve(w:QuantumTest):ℝ:=
  108*n*inverseNativeEnergy w+24*(sourcePair w (U (centeredAction w))).re

/-- The same balanced source current generates the full scalar energy and its unused native kinetic and scalar-square reserves. -/
theorem actual_reverse_clock_scalar_form(w:QuantumTest):
    reverseScalarCurrent w=3*scalarEnergy w+reverseScalarReserve w-6*n*‖vacuum‖^2*‖embed w‖^2:=by
  have hop:bracket Z B=(3:ℂ) • B+(-216:ℂ) • (U*scalarKinetic)+(24:ℂ) • (U*centeredAction)-
      (6:ℂ) • (U*vacuumConstantAction):=by
    rw [actual_reverse_clock_scalar_current,scalar_bulk_atoms]
    module
  have h:=congrArg (fun T:End=>(sourcePair w (T w)).re) hop
  rw [constant_local] at h
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    Module.End.one_apply,pair_add_r,pair_sub_r,pair_smul_r,Complex.add_re,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,
    Complex.neg_re,Complex.neg_im,zero_mul,sub_zero] at h
  rw [original_scalar_energy,inverse_scalar_form,pair_norm] at h
  unfold reverseScalarCurrent reverseScalarReserve
  linear_combination (norm:=ring) h
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


private theorem scalar_source_upper(half advanced:Bool)(q:ℝ)(w f:QuantumTest)
    (he:diagonalAction w=f+actualFrequency advanced (sourceNoetherFrequency half) q • w):
    (if advanced then (-1:ℝ) else 1)*
      ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)≤
      (sourceNoetherFrequency half+2*n)*scalarEnergy w+n^2*‖vacuum‖^2*‖embed w‖^2:=by
  have h:=scalar_ward w f _ he
  rw [original_scalar_current_geometric] at h
  simp only [LinearMap.add_apply,pair_add_r,Complex.add_im] at h
  have hb:=original_scalar_oscillator_bound w
  cases advanced
  · simp only [actualFrequency,Bool.false_eq_true,ite_false,line_im,one_mul] at h ⊢
    have hi:=le_abs_self ((sourcePair w (scalarCurrentComplete w)).im/2)
    nlinarith only [h,hb,hi]
  · simp only [actualFrequency,ite_true,Complex.star_def,Complex.conj_im,line_im,neg_one_mul] at h ⊢
    have hi:=neg_le_abs ((sourcePair w (scalarCurrentComplete w)).im/2)
    nlinarith only [h,hb,hi]

def reverseNoetherFactor(half:Bool):ℝ:=scalarNoetherFactor half*(sourceNoetherFrequency half+2*n)/3
def reverseNoetherNormCost(half:Bool):ℝ:=
  (6*n*reverseNoetherFactor half+scalarNoetherFactor half*n^2)*‖vacuum‖^2

/-- The original complete scalar forcing test is paid by its actual balanced-clock current, retaining both newly generated native reserves. No scalar energy or endpoint upper is supplied. -/
theorem actual_full_source_scalar_reverse_payment(half advanced:Bool)(q:ℝ)(w f:QuantumTest)
    (he:diagonalAction w=f+actualFrequency advanced (sourceNoetherFrequency half) q • w):
    scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
      ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)≤
      reverseNoetherFactor half*(reverseScalarCurrent w-reverseScalarReserve w)+
        reverseNoetherNormCost half*‖embed w‖^2:=by
  have h:=mul_le_mul_of_nonneg_left (scalar_source_upper half advanced q w f he)
    (actual_scalar_noether_fraction half).1.le
  have hr:=actual_reverse_clock_scalar_form w
  unfold reverseNoetherNormCost reverseNoetherFactor
  nlinarith only [h,congrArg (fun a:ℝ=>scalarNoetherFactor half*(sourceNoetherFrequency half+2*n)*a) hr]

def reverseNativePrice(half:Bool)(w:QuantumTest):ℝ:=
  reverseNoetherFactor half*(reverseScalarCurrent w-reverseScalarReserve w)+reverseNoetherNormCost half*‖embed w‖^2-
  3*(sourcePair w (U (nativeDilationWord w))).re+
  12*n*spinForm (U w)+12*n*densityForm (U w)-24*n*radiusForm w-
  12*(sourcePair w (U (scalarSpatialAction w))).re-13*n*inverseNativeEnergy w+
  (35*n/96)*‖embed (U (D w))‖^2

/-- The complete original physical action directly consumes the generated scalar current price. The full forcing, matched negative square and all signed native/gauge/magnetic words stay in the same inequality. -/
theorem actual_full_source_native_reverse_payment(half advanced:Bool)(m ell:ℕ)(F:Index)(q:ℝ)
    (hz:(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0)(g:diagonal.domain)(w f:QuantumTest)
    (he:diagonalAction w=f+actualFrequency advanced (sourceNoetherFrequency half) q • w):
    physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q) (w,f)≤
      reverseNativePrice half w+(432/n)*‖embed f‖^2-
      (n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed f‖^2-
      2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re:=by
  have h:=actual_full_source_native_return half advanced m ell F _ hz g w f he
  have hp:=actual_full_source_scalar_reverse_payment half advanced q w f he
  unfold reverseNativePrice nativePhysicalFields at *
  linarith only [h,hp]
end LowEnergy.ReverseNativeClock
