import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPhysicalPrimitiveClockReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRPrimitiveDifference
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceClockPhiNormalizedScalarBudget
open SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceScalarDoubleCurrent
open SourceClockReflectedForm SourceScalarInverseNativeEnergy SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceClockPhiMatchedElectricSource SourceScalarVirialBulk ClockPhiHeatCorrectedCovarianceSource
open FirstCurrentPrimitiveNoether FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare FirstCurrentDilationPrimitive
open FirstCurrentJointBudget FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier OriginalRCommutatorSource
open SourceLocalizedInverseFormPayment SourceResolventBandLimit
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev B:End:=scalarBulkComplete
private abbrev P:End:=positivePrimitive
attribute [local irreducible] sourcePair embed diagonalAction positivePrimitive correctedCompleteCore sourceTime
  normalizedState normalizedForcing inverseVolumeAction combinedGenerator scalarBulkComplete matchedTester
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator
private theorem n_pos:0<n:=by
  change 0<sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem phi_pair(f g:QuantumTest):sourcePair f (phiSquare g)=sourcePair (phiSquare f) g:=by
  change sourcePair f (phiRadiusAction (phiRadiusAction g))=sourcePair (phiRadiusAction (phiRadiusAction f)) g
  have h(a b:QuantumTest):sourcePair a (phiRadiusAction b)=sourcePair (phiRadiusAction a) b:=multiply_pair _ _ _ _
  rw [h,h]
private theorem positive_pair(f g:QuantumTest):sourcePair f (P g)=sourcePair (P f) g:=by
  have he(a b:QuantumTest):sourcePair a (electricAction b)=sourcePair (electricAction a) b:=multiply_pair _ _ _ _
  unfold P positivePrimitive
  simp only [LinearMap.add_apply,LinearMap.smul_apply,pair_add_l,pair_add_r,pair_smul_l,pair_smul_r,
    phi_pair,he,Complex.star_def,map_div₀,map_ofNat,map_one,Complex.conj_ofReal]
private theorem primitive_self_im(w:QuantumTest):(sourcePair w (P w)).im=0:=by
  have h:=congrArg Complex.im (GaussNativeForm.pair_conjugate w (P w))
  rw [←positive_pair] at h
  simp only [Complex.conj_im] at h
  linarith only [h]

/-- The original affine scalar and full electric currents generate this first-order return; the logarithmic clock is absent because Pplus is kept literal. -/
theorem actual_positive_primitive_current(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    bracket diagonalAction P=U*D+coframeElectricCurrent:=by
  have hphi:bracket diagonalAction phiSquare=(n/2:ℂ) • (U*SourceScalarAffineScaleTransport.generator):=
    original_phi_square_current
  have he:fullElectricCurrent=coframeElectricCurrent-U*SourceGaugeScaleTransport.generator:=
    (actual_matched_electric_source m ell F z hz g).1
  have hp:bracket diagonalAction P=(2/(n:ℂ)) • bracket diagonalAction phiSquare+fullElectricCurrent:=by
    unfold P positivePrimitive fullElectricCurrent bracket
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    module
  rw [hp,hphi,he]
  simp only [smul_smul]
  have hc:(2/(n:ℂ))*(n/2:ℂ)=1:=by field_simp [Complex.ofReal_ne_zero.mpr n_pos.ne']
  rw [hc,one_smul]
  unfold D combinedGenerator
  change U*SourceScalarAffineScaleTransport.generator+(coframeElectricCurrent-U*SourceGaugeScaleTransport.generator)=
    U*(SourceScalarAffineScaleTransport.generator-SourceGaugeScaleTransport.generator)+coframeElectricCurrent
  noncomm_ring

/-- The two original full forcing legs differ by the same primitive current; no forcing-square estimate enters. -/
theorem actual_two_pole_primitive_current(z:ℂ)(w f:QuantumTest)(he:diagonalAction w=f+z • w):
    primitiveEnergy f-primitiveEnergy (oppositeForcing z w f)=
      2*z.im*(sourcePair w (bracket diagonalAction P w)).im:=by
  have hp:=actual_primitive_forcing_square z w f
  have hs:(sourcePair (diagonalAction w) (P w)).im=(sourcePair f (P w)).im-z.im*primitiveEnergy w:=by
    rw [he,pair_add_l,pair_smul_l]
    simp only [Complex.add_im,Complex.mul_im,Complex.star_def,Complex.conj_im,Complex.conj_re,
      primitive_self_im,mul_zero,zero_add,primitiveEnergy,P]
    ring
  have hc:(sourcePair w (bracket diagonalAction P w)).im=2*(sourcePair (diagonalAction w) (P w)).im:=by
    have hr:sourcePair w (bracket diagonalAction P w)=sourcePair (diagonalAction w) (P w)-sourcePair (P w) (diagonalAction w):=by
      simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,pair_sub_r]
      exact congrArg₂ (fun a b:ℂ=>a-b) (diagonalAction_pair w (P w)) (positive_pair w (diagonalAction w))
    rw [hr,Complex.sub_im]
    have hh:=congrArg Complex.im (GaussNativeForm.pair_conjugate (diagonalAction w) (P w))
    simp only [Complex.conj_im] at hh
    linarith only [hh]
  linear_combination (norm:=ring) -(1/3:ℝ)*hp-4*z.im*hs-2*z.im*hc

/-- The complete two-pole primitive difference cancels the complete dilation phase in the same physical source equation. -/
theorem actual_full_primitive_dilation_cancellation(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (w f:QuantumTest)(he:diagonalAction w=f+z • w):
    3*primitiveEnergy f-3*primitiveEnergy (oppositeForcing z w f)+
      6*z.im*((sourcePair (U (D w)) w).im-(sourcePair w (coframeElectricCurrent w)).im)=0:=by
  have h:=actual_two_pole_primitive_current z w f he
  rw [actual_positive_primitive_current m ell F z hz g] at h
  simp only [LinearMap.add_apply,Module.End.mul_apply,pair_add_r,Complex.add_im] at h
  have hc:=congrArg Complex.im (GaussNativeForm.pair_conjugate w (U (D w)))
  simp only [Complex.conj_im] at hc
  linear_combination (norm:=ring) 3*h-6*z.im*hc

def nativePhysicalFields(half advanced:Bool)(a:QuantumTest×QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair a.2 (B a.1)).im-(sourcePair a.1 (geometricScalarCurrent a.1)).im/2)-
  3*(sourcePair a.1 (U (nativeDilationWord a.1))).re+
  12*n*spinForm (U a.1)+12*n*densityForm (U a.1)-24*n*radiusForm a.1-
  12*(sourcePair a.1 (U (scalarSpatialAction a.1))).re-13*n*inverseNativeEnergy a.1+
  (35*n/96)*‖embed (U (D a.1))‖^2

/-- All primitive forcing and frequency-phase terms are eliminated together. The surviving native fields, scalar full-forcing Noether term, raw completed square, gauge and magnetic words remain literal. -/
theorem actual_full_source_native_return(half advanced:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain)
    (w f:QuantumTest)(he:diagonalAction w=f+z • w):
    physicalJointPrice half advanced z (w,f)=nativePhysicalFields half advanced (w,f)+
      (432/n)*‖embed f‖^2-(n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed f‖^2-
      2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re:=by
  have h:=actual_full_source_dilation_joint_balance half advanced m ell F z hz g w f he
  have hp:=actual_full_primitive_dilation_cancellation m ell F z hz g w f he
  have hn:=actual_opposite_forcing_norm z w f he
  rw [oppositePrimitiveDebit,hn] at h
  unfold dilationSourcePrice at h
  unfold nativePhysicalFields
  linarith only [h,hp]

/-- The original complete physical Gaussian input supplies every full source equation, including its own cutoff defect. -/
theorem actual_original_whole_native_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=wholeSourceNext s hs half advanced m ell F g q
    let b:=clockSourcePair s hs x a
    physicalJointPrice half advanced z b=nativePhysicalFields half advanced b+originalNormalizerPrice s hs x a-
      2*gaugeForm (U b.1)-8*(sourcePair b.1 (U (magneticAction b.1))).re:=by
  dsimp only
  have hμ:0<sourceNoetherFrequency half:=by linarith [n_pos,actual_source_noether_gap half]
  have hz:(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=by
    cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
      Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
  have h:=actual_full_source_native_return half advanced m ell F _ hz g _ _
    (((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  unfold originalNormalizerPrice
  linear_combination (norm:=ring) h
end LowEnergy.OriginalRPrimitiveDifference
