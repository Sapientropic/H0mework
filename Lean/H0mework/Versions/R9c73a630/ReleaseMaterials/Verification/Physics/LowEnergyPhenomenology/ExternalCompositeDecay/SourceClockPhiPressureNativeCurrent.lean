import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPressureForcingSource
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentForcingPressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceCoframeVolumeCurrent SourceClockReflectedForm SourceScalarInverseNativeEnergy SourceScalarVirialBulk GaussNativePotential
open SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration SourceClockPhiCombinedScalePressure
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedElectricSource
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard ReverseBalancedForcePayer
open PrimitiveInputPayer ScalarInputJointNoether FirstCurrentJointDifference FirstCurrentMatchedPressure
open JointDifferenceMatchedSource FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare FirstCurrentDilationPrimitive OriginalRPrimitiveDifference
open SourceLocalizedInverseFormPayment SourceResolventBandLimit ClockPhiHeatCorrectedCovarianceSource
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev B:End:=scalarBulkComplete
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore wholeClockState wholeSourceNext
  clockSourcePair sourcePressureVector oppositeCompressionSource pressureSourceRemainder positivePrimitive
  scalarBulkComplete matchedTester nativeDilationWord balancedCompressionForce
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem factor_positive(half:Bool):0<reverseNoetherFactor half:=by
  unfold reverseNoetherFactor
  have hk:0<scalarNoetherFactor half:=(actual_scalar_noether_fraction half).1
  have hg:=actual_source_noether_gap half
  have hp:0<sourceNoetherFrequency half+2*n:=by linarith [n_pos]
  exact div_pos (mul_pos hk hp) (by norm_num)
private theorem pair_norm(w:QuantumTest):(sourcePair w w).re=‖embed w‖^2:=by
  simpa only [sourcePair,RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜:=ℂ) (embed w)
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]

/-- The pressure test and its opposite primitive/electric source are kept together, before any absolute-value estimate. -/
def orderedPressureSourcePrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  let a:=reverseNoetherFactor half
  let w:=wholeClockState s hs half advanced m ell F g x q
  let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
  let p:=oppositeCompressionSource F z w f
  (sourcePair (sourcePressureVector s hs half advanced m ell F g x q) (phiRadiusAction f)).re/(14*n*a)-
    (sourcePair p (positivePrimitive w)).re/(28*a)+
    (sourcePair p (electricAction w)).re/(56*a)+
    (sourcePair (balancedCompressionForce F w) (U (SourceScalarAffineScaleTransport.generator w))).re/(28*a)

theorem actual_full_forcing_ordered_pressure_price(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (432/n)*‖embed (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2‖^2=
      orderedPressureSourcePrice s hs half advanced m ell F g x q-
        (sourcePair (pressureSourceRemainder s hs half advanced m ell F g x q)
          (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2).re:=by
  have h:=congrArg Complex.re (actual_whole_pressure_primitive_source s hs half advanced m ell F g x q)
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.div_re,Complex.div_im,Complex.normSq_ofNat,Complex.re_ofNat,Complex.im_ofNat,
    mul_zero,zero_mul,sub_zero,pair_norm] at h
  unfold orderedPressureSourcePrice
  dsimp only
  rw [h]
  have hn:=n_pos.ne'
  have ha:reverseNoetherFactor half≠0:=(factor_positive half).ne'
  field_simp [hn,ha]
  ring

/-- Removing the UD principal word leaves precisely the original mass, gauge, physical-frequency, clock and electric terms. -/
def nonDilationPressureRemainder(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  (-12:ℂ) • U w-(9:ℂ) • U (SourceGaugeScaleTransport.generator w)+
    (18:ℂ) • U (wholeFrequencyJet s hs half advanced m ell F g x q)-
    U (correctedCompleteCore s hs x.1 x.2 (reverseClockReturn s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1)))+
    (36*(wholeStep s hs half advanced m ell F g:ℂ)) •
      U (correctedCompleteCore s hs x.1 x.2 (weightedElectricCurrent (frequencyState half advanced m ell F g q)))

private theorem remainder_split(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    pressureSourceRemainder s hs half advanced m ell F g x q=
      (6:ℂ) • U (D (wholeClockState s hs half advanced m ell F g x q))+
        nonDilationPressureRemainder s hs half advanced m ell F g x q:=by
  unfold pressureSourceRemainder nonDilationPressureRemainder
  module

def nativePressureCurrentPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
  orderedPressureSourcePrice s hs half advanced m ell F g x q-
    (sourcePair (nonDilationPressureRemainder s hs half advanced m ell F g x q) f).re-
    (9*n/4)*(sourcePair (U (D w)) (dilation (U w))).im-
    6*(actualFrequency advanced (sourceNoetherFrequency half) q).im*(sourcePair (U (D w)) w).im

/-- The same source forcing and all six native dilation departments cancel their full H0 principal word. The remaining coframe and imaginary-frequency currents stay literal. -/
theorem actual_forcing_native_current_cancellation(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    (432/n)*‖embed (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2‖^2-
      3*(sourcePair (wholeClockState s hs half advanced m ell F g x q)
        (U (nativeDilationWord (wholeClockState s hs half advanced m ell F g x q)))).re=
      nativePressureCurrentPrice s hs half advanced m ell F g x q:=by
  have h:=actual_full_forcing_ordered_pressure_price s hs half advanced m ell F g x q
  rw [remainder_split] at h
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,
    Complex.add_re,Complex.mul_re,map_ofNat,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero] at h
  have he:=(((actual_whole_electric_source_carrier s hs half advanced m ell F g).2 q).2.2 x)
  have hd:=actual_full_source_dilation_balance _ _ _ he
  unfold wholeClockState
  unfold nativePressureCurrentPrice wholeClockState
  unfold wholeClockState at h
  unfold sourcePair at hd ⊢
  linear_combination (norm:=ring) h-hd

def nativePressureOtherFields(half advanced:Bool)(w f:QuantumTest):ℝ:=
  scalarNoetherFactor half*(if advanced then (-1:ℝ) else 1)*
    ((sourcePair f (B w)).im-(sourcePair w (geometricScalarCurrent w)).im/2)+
  12*n*spinForm (U w)+12*n*densityForm (U w)-24*n*radiusForm w-
  12*(sourcePair w (U (scalarSpatialAction w))).re-13*n*inverseNativeEnergy w+
  (35*n/96)*‖embed (U (D w))‖^2

/-- The original complete physical J consumes this coupled source current. Its literal matched completion and all other signed departments remain, with no standalone full-forcing square. -/
theorem actual_whole_physical_pressure_current(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let w:=wholeClockState s hs half advanced m ell F g x q
    let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
    physicalJointPrice half advanced z (w,f)=
      nativePressureOtherFields half advanced w f+nativePressureCurrentPrice s hs half advanced m ell F g x q-
      matchedSquarePrice s hs half advanced m ell F g x q-
      2*gaugeForm (U w)-8*(sourcePair w (U (magneticAction w))).re:=by
  dsimp only
  have h:=actual_original_whole_native_return s hs half advanced m ell F g q x
  dsimp only at h
  have hp:=actual_original_matched_price_return s hs half advanced m ell F g x q
  have hc:=actual_forcing_native_current_cancellation s hs half advanced m ell F g x q
  unfold nativePhysicalFields at h
  unfold nativePressureOtherFields
  unfold wholeClockState at hc ⊢
  simp only [Prod.mk.eta]
  linear_combination (norm:=ring) h+hp+hc
end LowEnergy.FirstCurrentForcingPressure
