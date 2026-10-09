import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiPressureNativeCurrent
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentForcingPressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarInverseNativeEnergy
open SourceClockPhiRadiusSourceCurrent SourceClockPhiCombinedScalePressure SourceClockReflectedForm SourceScalarVirialBulk
open SourceClockPhiNativeMatchedSource SourceClockPhiMatchedElectricSource
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard ReverseBalancedForcePayer ReverseForcePhysicalPayment
open BalancedInputPrimitivePayment PrimitiveInputPayer ScalarInputJointNoether FirstCurrentJointDifference FirstCurrentMatchedPressure FirstCurrentDifferenceFrequency
open FirstCurrentDilationPrimitive BalancedPrimitivePayer ScalarBalancedPrimitive OriginalRCommutatorSource
open SourceLocalizedInverseFormPayment SourceResolventBandLimit ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
open scoped ENNReal
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev n:ℝ:=sourceTime 0
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev B:End:=scalarBulkComplete
attribute [local irreducible] sourcePair embed diagonalAction wholeClockState wholeSourceNext clockSourcePair
  clearedNativePrice compensatedPrimitiveWork pressureSourceRemainder nativePressureCurrentPrice orderedPressureSourcePrice
  differenceFreeUpper differenceRadialUpper differenceWardUpper transportedDifferenceUpper sourcePressureUpper
  matchedSquarePrice originalNormalizerPrice scalarKinetic gaugeKinetic matterAction centeredAction vacuumLinearAction
  magneticAction scalarBulkComplete
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]

def pressureNativeFields(w:QuantumTest):ℝ:=
  -(12/7:ℝ)*(sourcePair w (U (scalarKinetic w))).re+
    6*(sourcePair w (U (centeredAction w))).re-6*(sourcePair w (U (vacuumLinearAction w))).re-
    8*(sourcePair w (U (magneticAction w))).re+
    12*n*spinForm (U w)+12*n*densityForm (U w)-13*n*inverseNativeEnergy w+
    (35*n/96)*‖embed (U (D w))‖^2-2*gaugeForm (U w)-72*n*‖embed w‖^2

/-- The native principal cancellation deletes the complete gauge-kinetic and matter prices; no H0 positivity is used. -/
theorem actual_pressure_native_departments(w:QuantumTest):
    clearedNativePrice w+3*(sourcePair w (U (nativeDilationWord w))).re=pressureNativeFields w:=by
  unfold clearedNativePrice pressureNativeFields
  simp only [nativeDilationWord,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    map_add,map_sub,map_smul,pair_add_r,pair_sub_r,pair_smul_r,
    Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  ring

/-- The original source upper now contains the ordered opposite primitive current instead of a standalone full-forcing square. Every transported Ward, own-defect and local cross remains. -/
def forcingPressureUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let a:=reverseNoetherFactor half
  let w:=wholeClockState s hs half advanced m ell F g x q
  let d:=jointDifference s hs half advanced m ell F g x q
  a*(18*scalarEnergy w+72*wholeStep s hs half advanced m ell F g*
    (sourcePair (correctedCompleteCore s hs x.1 x.2 (weightedElectricCurrent (frequencyState half advanced m ell F g q))) (B w)).re-
    2*(wholeClockWardKernel s hs half advanced m ell F g q x).re-reverseScalarReserve w)+
    reverseNoetherNormCost half*‖embed w‖^2+
    pressureNativeFields w+compensatedPrimitiveWork F w+nativePressureCurrentPrice s hs half advanced m ell F g x q+
    ((56*n*a^2/3)*(4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n))))*
      transportedDifferenceWard s hs half advanced m ell F g x q+
    (8*a/3)*(sourcePair (U d) (balancedOwnDefect F w)).re-2*a*(sourcePair d (bulkForceRemainder w)).re

theorem actual_forcing_pressure_upper_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    sourcePressureUpper s hs half advanced m ell F g x q=forcingPressureUpper s hs half advanced m ell F g x q:=by
  have hn:=actual_original_matched_price_return s hs half advanced m ell F g x q
  have hc:=actual_forcing_native_current_cancellation s hs half advanced m ell F g x q
  have hd:=actual_pressure_native_departments (wholeClockState s hs half advanced m ell F g x q)
  unfold sourcePressureUpper transportedDifferenceUpper differenceWardUpper differenceRadialUpper differenceFreeUpper forcingPressureUpper
  linear_combination (norm:=ring) hn+hc+hd

/-- The ordinary full-frequency current price is generated by the actual finite/escape source, not by a forcing norm bound. -/
theorem actual_native_pressure_current_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (nativePressureCurrentPrice s hs half advanced m ell F g x):=by
  have hf:=(actual_whole_completed_forcing_integrable s hs half advanced m ell F g x).1
  have hn:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x 1 (U*nativeDilationWord)).re
  simp only [Module.End.one_apply,Module.End.mul_apply,RCLike.re_eq_complex_re] at hn
  apply ((hf.const_mul (432/n)).sub (hn.const_mul 3)).congr
  exact Eventually.of_forall (fun q=>actual_forcing_native_current_cancellation s hs half advanced m ell F g x q)

/-- The complete original J inequality consumes the combined forcing/native current. Both positive native losses stay funded, and the actual own-cutoff and frequency Ward remain in the signed upper. -/
theorem actual_whole_forcing_pressure_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (forcingPressureUpper s hs half advanced m ell F g x) ∧
    (∫⁻q:ℝ,ENNReal.ofReal (sourcePressurePayment s hs half advanced m ell F g x q))<⊤ ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫⁻q:ℝ,ENNReal.ofReal (sourcePressurePayment s hs half advanced m ell F g x q)).toReal ≤
        ∫q:ℝ,forcingPressureUpper s hs half advanced m ell F g x q:=by
  have h:=actual_whole_matched_pressure_payment s hs half advanced m ell F g x
  have he:sourcePressureUpper s hs half advanced m ell F g x=forcingPressureUpper s hs half advanced m ell F g x:=
    funext (actual_forcing_pressure_upper_return s hs half advanced m ell F g x)
  simpa only [he] using h
end LowEnergy.FirstCurrentForcingPressure
