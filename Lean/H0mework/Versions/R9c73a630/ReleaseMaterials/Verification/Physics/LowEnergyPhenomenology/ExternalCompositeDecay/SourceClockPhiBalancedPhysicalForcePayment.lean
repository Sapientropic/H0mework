import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedWholeForceDebit
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholePhysicalForcePayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseBalancedForcePayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceScalarPairedTransport
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseForceNoetherPayer ReverseForcePhysicalPayment
open ReverseScalarGaugeWard ScalarCausalFrequencyMoment ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev B:End:=scalarBulkComplete
private abbrev X:End:=weightedElectricCurrent
attribute [local irreducible] sourcePair embed diagonalAction resolventCore
  reverseNativeClock reverseScaleForce reverseCompressionForce scalarBulkComplete
  normalizedState normalizedForcing wholeClockState wholeSourceNext wholeSourceMap correctedCompleteCore weightedElectricCurrent
  forceResponse phaseRow inputSeed wholeClockWord wholeForceState wholeForceNativeDebit balancedWholeForceState balancedWholeForceNativeDebit
  reverseScalarCurrent reverseScalarReserve reverseNoetherFactor reverseNoetherNormCost scalarNoetherFactor scalarEnergy clockSourcePair
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by rw [source_time_generated];exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by simp only [sourcePair,map_add,inner_add_left]
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_smul_l(c:ℂ)(f g:QuantumTest):sourcePair (c • f) g=star c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]

def balancedNativeNoetherPrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)+
    72*wholeStep s hs half advanced m ell F g*
      (sourcePair (correctedCompleteCore s hs x.1 x.2 (X (frequencyState half advanced m ell F g q)))
        (B (wholeClockState s hs half advanced m ell F g x q))).re-
    2*(sourcePair (correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)))
        (B (wholeClockState s hs half advanced m ell F g x q))).re+
    balancedWholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im-
      2*(wholeClockWardKernel s hs half advanced m ell F g q x).re

/-- The exact original causal price now consumes the gauge-free electric word and the compensated full-force native current. The clock word and both actual own-defect commutators remain. -/
theorem actual_balanced_native_noether_price(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)
    (g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeNoetherCausalPrice s hs half advanced m ell F g x q=balancedNativeNoetherPrice s hs half advanced m ell F g x q:=by
  rw [actual_full_noether_gauge_reduction]
  have hp:=actual_balanced_whole_force_native_noether s hs half advanced m ell F g x q
  have hd:balancedWholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im=
      2*(sourcePair (balancedWholeForceState s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
    rw [←hp]
    field_simp [hz half advanced q]
  unfold balancedFullNoetherPrice balancedNoetherPrice balancedWardWord balancedNativeNoetherPrice
  rw [hd,actual_balanced_whole_force_return]
  simp only [map_add,map_sub,map_smul,pair_add_l,pair_sub_l,pair_smul_l,
    Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.star_def,Complex.conj_ofReal,
    Complex.conj_ofNat,map_neg,Complex.ofReal_re,Complex.ofReal_im,Complex.neg_re,Complex.neg_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  ring
private theorem original_force_price(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeForceCausalPrice s hs half advanced m ell F g x q=wholeNoetherCausalPrice s hs half advanced m ell F g x q:=by
  have hspl:wholeReverseSource s hs half advanced m ell F g x q=
      wholeNonForceSource s hs half advanced m ell F g x q-wholeForceState s hs half advanced m ell F g x q:=by
    simp only [wholeReverseSource,wholeNonForceSource,wholeForceState,forceResponse,Finset.sum_sub_distrib]
  have hp:=actual_whole_force_native_noether s hs half advanced m ell F g x q
  have hd:wholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im=
      2*(sourcePair (wholeForceState s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
    rw [←hp]
    field_simp [hz half advanced q]
  unfold wholeNoetherCausalPrice wholeForceCausalPrice
  rw [hspl,hd]
  simp only [pair_sub_l,Complex.sub_re]
  ring

def balancedPhysicalForceUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  reverseNoetherFactor half*(balancedNativeNoetherPrice s hs half advanced m ell F g x q-
    reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q))+
    reverseNoetherNormCost half*‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2+
      wholeRetainedPhysicalPrice s hs half advanced m ell F g x q

/-- The starting complete physical action directly consumes the compensated native current. All its native fields, full forcing and negative matched completion stay in the same signed upper. -/
theorem actual_balanced_whole_physical_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (balancedPhysicalForceUpper s hs half advanced m ell F g x) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ≤
      ∫q:ℝ,balancedPhysicalForceUpper s hs half advanced m ell F g x q:=by
  have h:=actual_whole_physical_force_payment s hs half advanced m ell F g x
  have he:wholePhysicalForceUpper s hs half advanced m ell F g x=balancedPhysicalForceUpper s hs half advanced m ell F g x:=by
    funext q
    unfold wholePhysicalForceUpper wholeScalarForceUpper balancedPhysicalForceUpper
    rw [original_force_price,actual_balanced_native_noether_price]
  simpa only [he] using h
end LowEnergy.ReverseBalancedForcePayer
