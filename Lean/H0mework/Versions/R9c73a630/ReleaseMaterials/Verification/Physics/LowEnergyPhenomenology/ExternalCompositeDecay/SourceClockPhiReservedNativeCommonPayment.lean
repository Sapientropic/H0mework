import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholePressureReservePayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiMatchedCommonClockPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentPressureReserve
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourcePhysicalKineticSquare SourceClockPhiNativeMatchedSource FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ReverseBalancedForcePayer ReverseForcePhysicalPayment
open FirstCurrentJointDifference FirstCurrentMatchedPressure FirstCurrentDifferenceFrequency FirstCurrentForcingPressure
open FirstCurrentDilationPrimitive OriginalRMatchedVariance OriginalRMatchedCofinal OriginalRCommutatorSource
open PrimitiveInputPayer SourceLocalizedInverseFormPayment SourceResolventBandLimit ClockPhiHeatCorrectedCovarianceSource
open MeasureTheory Filter
open scoped ENNReal
private abbrev n:ℝ:=sourceTime 0
private abbrev U:=inverseVolumeAction
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] embed sourcePair wholeClockState wholeSourceNext clockSourcePair correctedCompleteCore
  nativePressureCurrentPrice totalPressureReserve differenceJointLoss matchedSquarePrice originalNormalizerPrice
  matchedTester diagonalAction forcingPressureUpper matchedRadialDebit

def reservedNativeWork(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  nativePressureCurrentPrice s hs half advanced m ell F g x q-totalPressureReserve s hs half advanced m ell F g x q+
    differenceJointLoss s hs half advanced m ell F g x q+3*(sourcePair w (U (nativeDilationWord w))).re+
    6*(sourcePair (matchedTester w) (diagonalAction w)).re

def reservedNativeRemainder(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  forcingPressureUpper s hs half advanced m ell F g x q-nativePressureCurrentPrice s hs half advanced m ell F g x q-
    3*(sourcePair w (U (nativeDilationWord w))).re-6*(sourcePair (matchedTester w) (diagonalAction w)).re

/-- The pressure and reserve are exchanged jointly for the same original matched source, leaving dLoss on the original J side. -/
theorem actual_reserved_native_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    reservedNativeWork s hs half advanced m ell F g x q=
      originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)+
        6*(sourcePair (matchedTester (wholeClockState s hs half advanced m ell F g x q))
          (diagonalAction (wholeClockState s hs half advanced m ell F g x q))).re:=by
  have hr:=(actual_whole_pressure_reserve_balance s hs half advanced m ell F g x q).1
  have hn:=actual_original_matched_price_return s hs half advanced m ell F g x q
  have hc:=actual_forcing_native_current_cancellation s hs half advanced m ell F g x q
  unfold reservedNativeWork totalPressureReserve
  linear_combination (norm:=ring) -hr-hn-hc

private theorem normalizer_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)):=by
  have h:=actual_whole_completed_forcing_integrable s hs half advanced m ell F g x
  simpa only [originalNormalizerPrice,wholeClockState,Pi.sub_apply] using! (h.1.const_mul (432/n)).sub (h.2.const_mul (n/48))

/-- Recombination spends each matched square once. The retained difference loss and the remaining full native/H0 current stay on their actual sides. -/
theorem actual_whole_reserved_native_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (reservedNativeWork s hs half advanced m ell F g x) ∧
    Integrable (reservedNativeRemainder s hs half advanced m ell F g x) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫q:ℝ,differenceJointLoss s hs half advanced m ell F g x q)≤
        (∫q:ℝ,reservedNativeRemainder s hs half advanced m ell F g x q)+
        (∫q:ℝ,reservedNativeWork s hs half advanced m ell F g x q):=by
  have h:=actual_whole_reserve_frequency_payment s hs half advanced m ell F g x
  have hd:=(actual_whole_joint_difference_payment s hs half advanced m ell F g x).2.2.1
  have hm:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x matchedTester diagonalAction).re
  have hn:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x 1 (U*nativeDilationWord)).re
  simp only [RCLike.re_eq_complex_re] at hm
  simp only [Module.End.one_apply,Module.End.mul_apply,RCLike.re_eq_complex_re] at hn
  have hw:Integrable (reservedNativeWork s hs half advanced m ell F g x):=
    ((normalizer_integrable s hs half advanced m ell F g x).add (hm.const_mul 6)).congr
      (Eventually.of_forall (fun q=>(actual_reserved_native_source s hs half advanced m ell F g x q).symm))
  have hr:Integrable (reservedNativeRemainder s hs half advanced m ell F g x):=by
    unfold reservedNativeRemainder
    exact ((h.2.1.sub (actual_native_pressure_current_integrable s hs half advanced m ell F g x)).sub (hn.const_mul 3)).sub (hm.const_mul 6)
  refine ⟨hw,hr,?_⟩
  have he:(fun q:ℝ=>reservedNativeRemainder s hs half advanced m ell F g x q+reservedNativeWork s hs half advanced m ell F g x q)=
      fun q:ℝ=>forcingPressureUpper s hs half advanced m ell F g x q-totalPressureReserve s hs half advanced m ell F g x q+
        differenceJointLoss s hs half advanced m ell F g x q:=by
    funext q
    unfold reservedNativeRemainder reservedNativeWork
    ring
  have hi:=congrArg (fun f:ℝ→ℝ=>∫q:ℝ,f q) he
  rw [integral_add hr hw] at hi
  have hsub:Integrable (fun q:ℝ=>forcingPressureUpper s hs half advanced m ell F g x q-totalPressureReserve s hs half advanced m ell F g x q):=h.2.1.sub h.1
  rw [integral_add hsub hd,integral_sub h.2.1 h.1] at hi
  linarith only [hi,h.2.2.2]

/-- The opposite-primitive/native/pressure reserve combination has its actual Gaussian mean from the same complete source equation. -/
theorem actual_reserved_native_gaussian(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ):
    Integrable (fun x:ℝ×ℝ=>reservedNativeWork s hs half advanced m ell F g x q) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,reservedNativeWork s hs half advanced m ell F g x q ∂γ.prod γ)=
      gainedMatchedPhysicalPrice s (actualFrequency advanced (sourceNoetherFrequency half) q)
        (wholeSourceNext s hs half advanced m ell F g q).1-
        matchedRadialDebit s hs (wholeSourceNext s hs half advanced m ell F g q).1:=by
  have h:=actual_original_whole_source_normalizer_payment s hs half advanced m ell F g q
  simpa only [actual_reserved_native_source,wholeClockState,clockSourcePair] using h

/-- One original N and cofinal event pay this complete signed reserved source; the clock window precedes both causes, all frequencies and both Gaussian noises. -/
theorem actual_reserved_native_common_payment(half:Bool)(g:diagonal.domain):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell → ∀ᶠF in (sourceFilter:Filter Index),
      ∃δ:ℝ,0<δ ∧ δ≤1 ∧ ∀advanced:Bool,∀s:ℝ,∀hs:0<s,s≤δ→
        (∫⁻q:ℝ,ENNReal.ofReal ((∫x:ℝ×ℝ,reservedNativeWork s hs half advanced m ell F g x q ∂γ.prod γ)+
          matchedRadialDebit s hs (wholeSourceNext s hs half advanced m ell F g q).1))≤ENNReal.ofReal ε:=by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_original_matched_common_clock_payment half g ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  obtain ⟨δ,hd,hδ⟩:=hF
  refine ⟨min 1 δ,lt_min (by norm_num) hd,min_le_left _ _,fun advanced s hs hsd=>?_⟩
  have h:=hδ advanced s hs (hsd.trans (min_le_right _ _))
  have he(q:ℝ):(∫x:ℝ×ℝ,reservedNativeWork s hs half advanced m ell F g x q ∂γ.prod γ)=
      matchedSourceMean s hs half advanced m ell F g q:=by
    rw [(actual_reserved_native_gaussian s hs half advanced m ell F g q).2]
    exact (actual_matched_physical_gaussian s hs _ (wholeSourceNext s hs half advanced m ell F g q).1).2.symm
  simpa only [he] using h
end LowEnergy.FirstCurrentPressureReserve
