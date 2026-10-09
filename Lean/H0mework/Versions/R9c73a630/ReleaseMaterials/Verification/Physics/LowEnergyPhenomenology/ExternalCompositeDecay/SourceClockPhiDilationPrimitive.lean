import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPrimitiveSquare
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentDilationPrimitive
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceScalarDoubleCurrent
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceCoframeDilation SourcePhysicalKineticSquare
open SourceClockPhiMatchedElectricSource SourceClockPhiNativeMatchedSource SourceClockPhiCombinedScalePressure
open SourceClockReflectedForm SourceScalarInverseNativeEnergy SourceScalarShiftedBulk SourceScalarEssentialBudget
open FirstCurrentJointBudget FirstCurrentJointBudgetNext FirstCurrentGeometricPayer
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ClockPhiHeatCorrectedCovarianceSource FirstCurrentPayerNext FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier
open SourceClockPhiRadiusAcceleration SourceClockPhiRadiusSourceCurrent SourceScalarVirialBulk
open FirstCurrentPrimitiveNoether SourceClockAcceleration SourceClockFixedInputSeed SourceDilationRemainder
open scoped ContDiff InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := inverseVolumeAction
private abbrev Dc : End := dilation
private abbrev D : End := combinedGenerator
private abbrev M : End := matchedTester
private abbrev X : End := weightedElectricCurrent
private abbrev P : End := electricPrimitive
private abbrev W : End := magneticVolumeWeight
private abbrev B : End := scalarBulkComplete
private abbrev H0 : End := diagonalAction
attribute [local irreducible] sourcePair embed diagonalAction normalizedState normalizedForcing correctedCompleteCore updatedForcing
  weightedElectricCurrent matchedTester combinedGenerator volumeAction inverseVolumeAction dilation scalarBulkComplete geometricScalarCurrent
open FirstCurrentClockPrimitive

open FirstCurrentClockPrimitiveSquare SourceScalarGaugeScale SourceScalarInverseRetardedBudget

private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only[sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only[sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only[sourcePair,map_smul,inner_smul_right]
private theorem U_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=by
  unfold U inverseVolumeAction
  exact multiply_pair _ _ _ _
private theorem UD_pair(f g:QuantumTest):sourcePair f ((U*D) g)= -sourcePair ((U*D) f) g:=by
  have h:=ClockPhiMatchedNoiseCore.noiseGenerator_pair 0 1 f g
  simpa only[ClockPhiMatchedNoiseCore.noiseGenerator,Complex.ofReal_zero,Complex.ofReal_one,
    zero_smul,one_smul,zero_add] using h

def nativeDilationWord:End:=
  (-2:ℂ) • scalarKinetic+(2:ℂ) • gaugeKinetic+(2:ℂ) • centeredAction-
  (2:ℂ) • vacuumLinearAction-(4:ℂ) • magneticAction-GaussMatterCore.matterAction

/-- The combined current is the original six native departments, with no coframe replacement. -/
theorem actual_combined_native_current:bracket D H0=nativeDilationWord:=by
  have he(A:End):bracket combinedGenerator A=deltaPhi A-deltaGauge A:=by
    have hp:=SourceScalarAffineScaleTransport.generator_commutator A
    have hg:=SourceGaugeScaleTransport.generator_commutator A
    unfold combinedGenerator bracket
    change (SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)*A-
      A*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)=_
    linear_combination (norm:=noncomm_ring) hp-hg
  change bracket combinedGenerator H0=nativeDilationWord
  rw [he]
  exact original_scalar_gauge_current
private abbrev c:ℂ:=3*Complex.I*(n:ℂ)/4
private theorem inverse_current:H0*U-U*H0=c • (U*Dc*U):=original_inverse_current
private theorem combined_weighted_current:
    (U*D)*H0-H0*(U*D)=U*nativeDilationWord-c • (U*Dc*U*D):=by
  have hD:=actual_combined_native_current
  unfold bracket at hD
  linear_combination (norm:=noncomm_ring) U*hD-inverse_current*D
private theorem native_pair_source(w:QuantumTest):
    6*(sourcePair (U (D w)) (H0 w)).re-
      (9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im=
        -3*(sourcePair w (U (nativeDilationWord w))).re:=by
  have h:=congrArg (sourcePair w) (LinearMap.congr_fun combined_weighted_current w)
  change sourcePair w ((U*D) (H0 w)-H0 (U (D w)))=
    sourcePair w (U (nativeDilationWord w)-c • U (Dc (U (D w)))) at h
  rw [pair_sub_r,pair_sub_r,UD_pair,diagonalAction_pair w (U (D w)),pair_smul_r,
    U_pair w (Dc (U (D w))),dilation_pair (U w) (U (D w))] at h
  change -sourcePair (U (D w)) (H0 w)-sourcePair (H0 w) (U (D w))=
    sourcePair w (U (nativeDilationWord w))-c*sourcePair (Dc (U w)) (U (D w)) at h
  rw [←GaussNativeForm.pair_conjugate (U (D w)) (H0 w),
    ←GaussNativeForm.pair_conjugate (U (D w)) (Dc (U w))] at h
  have hr:=congrArg Complex.re h
  simp only[Complex.sub_re,Complex.neg_re,Complex.conj_re,Complex.conj_im,c,
    Complex.mul_re,Complex.mul_im,Complex.div_re,Complex.div_im,Complex.normSq_ofNat,
    Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat] at hr
  nlinarith only[hr]
private theorem UD_self_real(w:QuantumTest):(sourcePair (U (D w)) w).re=0:=by
  have h:=UD_pair w w
  change sourcePair w (U (D w))= -sourcePair (U (D w)) w at h
  rw [←GaussNativeForm.pair_conjugate (U (D w)) w] at h
  have hr:=congrArg Complex.re h
  simp only[Complex.conj_re,Complex.neg_re] at hr
  linarith only[hr]

/-- The full source pays the entire UD/coframe cross word; all six native terms and the
literal imaginary frequency remain together. -/
theorem actual_full_source_dilation_balance(z:ℂ)(w f:QuantumTest)(he:H0 w=f+z • w):
    6*(sourcePair (U (D w)) f).re-(9*n/4)*(sourcePair (U (D w)) (Dc (U w))).im=
      -3*(sourcePair w (U (nativeDilationWord w))).re+
        6*z.im*(sourcePair (U (D w)) w).im:=by
  have h:=native_pair_source w
  rw [he,pair_add_r,pair_smul_r] at h
  simp only[Complex.add_re,Complex.mul_re,UD_self_real,mul_zero,zero_sub] at h
  linarith only[h]

def dilationSourcePrice(half advanced:Bool)(z:ℂ)(w f:QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
  3*primitiveEnergy f-3*(sourcePair w (U (nativeDilationWord w))).re+
  6*z.im*((sourcePair (U (D w)) w).im-(sourcePair w (coframeElectricCurrent w)).im)+
  12*n*spinForm (U w)+12*n*densityForm (U w)-24*n*radiusForm w-
  12*(sourcePair w (U (scalarSpatialAction w))).re-13*n*inverseNativeEnergy w+
  (35*n/96)*‖embed (U (D w))‖^2

/-- The full physical action now has no reflected or UD/Dc cross word. Its actual two forcing
legs, native fields and negative completed square remain in one source balance. -/
theorem actual_full_source_dilation_joint_balance(half advanced:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:diagonal.domain)(w f:QuantumTest)(he:H0 w=f+z • w):
    physicalJointPrice half advanced z (w,f)=dilationSourcePrice half advanced z w f-
      oppositePrimitiveDebit (oppositeForcing z w f)-
      (n/48)*‖embed (M w)+((144/n:ℝ):ℂ) • embed f‖^2-
      2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re:=by
  rw [actual_full_source_two_pole_joint_balance half advanced m ell F z hz g w f he]
  have h:=actual_full_source_dilation_balance z w f he
  unfold completeSourceRemainder dilationSourcePrice
  linarith only[h]


/-- The common fixed-pole update uses this field/cross cancellation before any estimate. -/
theorem actual_updated_dilation_joint_balance(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)
    physicalJointPrice half advanced z a=dilationSourcePrice half advanced z a.1 a.2-
      oppositePrimitiveDebit (oppositeForcing z a.1 a.2)-
      (n/48)*‖embed (M a.1)+((144/n:ℝ):ℂ) • embed a.2‖^2-
      2*gaugeForm (U a.1)-8*(sourcePair a.1 (U (magneticAction a.1))).re:=by
  dsimp only
  rw [actual_updated_two_pole_joint_balance s hs half advanced m ell F g q x]
  have h:=((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x
  have hp:=actual_full_source_dilation_balance _ _ _ h
  unfold completeSourceRemainder dilationSourcePrice
  linarith only[hp]
end LowEnergy.FirstCurrentDilationPrimitive
