import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointMatchedPressureSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiDifferenceWardFrequencyPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentMatchedPressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNativeMatchedSource SourceClockPhiRadiusSourceCurrent
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget ReverseNativeClock ReverseForcePhysicalPayment
open ReverseNativeFrequencyWard
open FirstCurrentJointDifference FirstCurrentDifferenceFrequency PrimitiveInputPayer SourceLocalizedInverseFormPayment SourceResolventBandLimit
open OriginalRCommutatorSource MeasureTheory Filter
open scoped ENNReal
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] embed sourcePair wholeClockState wholeSourceNext clockSourcePair
  completedMatchedSource sourcePressurePayment differenceJointLoss transportedDifferenceUpper
  physicalJointPrice matchedTester
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def matchedSquarePrice(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  (n/48)*‖embed (completedMatchedSource s hs half advanced m ell F g x q)‖^2
private theorem matched_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (matchedSquarePrice s hs half advanced m ell F g x):=by
  have h:=(actual_whole_completed_forcing_integrable s hs half advanced m ell F g x).2
  have hn:Integrable (fun q:ℝ=>‖embed (completedMatchedSource s hs half advanced m ell F g x q)‖^2):=by
    apply h.congr
    exact Eventually.of_forall (fun q=>by
      simp only [completedMatchedSource,map_add,map_smul,Complex.ofReal_div,Complex.ofReal_ofNat])
  exact hn.const_mul (n/48)

def sourcePressureUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  transportedDifferenceUpper s hs half advanced m ell F g x q+matchedSquarePrice s hs half advanced m ell F g x q

/-- This is the literal original positive full-forcing price when the matched negative square is moved into the joint pressure payment. -/
theorem actual_original_matched_price_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)+
      matchedSquarePrice s hs half advanced m ell F g x q=
        (432/n)*‖embed (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2‖^2:=by
  simp only [originalNormalizerPrice,matchedSquarePrice,completedMatchedSource,wholeClockState,
    map_add,map_smul,Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

/-- The actual full-forcing/native pressure is a finite positive frequency payment in the original J inequality. Both original negative squares fund it; every other signed field remains on the same source upper. -/
theorem actual_whole_matched_pressure_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (sourcePressureUpper s hs half advanced m ell F g x) ∧
    (∫⁻q:ℝ,ENNReal.ofReal (sourcePressurePayment s hs half advanced m ell F g x q))<⊤ ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫⁻q:ℝ,ENNReal.ofReal (sourcePressurePayment s hs half advanced m ell F g x q)).toReal ≤
        ∫q:ℝ,sourcePressureUpper s hs half advanced m ell F g x q:=by
  have hj:=actual_whole_transported_difference_payment s hs half advanced m ell F g x
  have hd:=actual_whole_joint_difference_payment s hs half advanced m ell F g x
  have hm:=matched_integrable s hs half advanced m ell F g x
  let P:=sourcePressurePayment s hs half advanced m ell F g x
  let E:=fun q:ℝ=>differenceJointLoss s hs half advanced m ell F g x q+matchedSquarePrice s hs half advanced m ell F g x q
  have hi:Integrable E:=hd.2.2.1.add hm
  have hn(q:ℝ):0 ≤ E q:=by
    have h:=actual_joint_matched_pressure_payment s hs half advanced m ell F g x q
    exact h.1.trans h.2
  have hbound:(∫⁻q:ℝ,ENNReal.ofReal (P q)) ≤ ENNReal.ofReal (∫q:ℝ,E q):=by
    calc
      _ ≤ ∫⁻q:ℝ,ENNReal.ofReal (E q):=lintegral_mono (fun q=>ENNReal.ofReal_le_ofReal
        (actual_joint_matched_pressure_payment s hs half advanced m ell F g x q).2)
      _=_:=(ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn)).symm
  have hfinite:(∫⁻q:ℝ,ENNReal.ofReal (P q))<⊤:=lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  have hreal:(∫⁻q:ℝ,ENNReal.ofReal (P q)).toReal ≤ ∫q:ℝ,E q:=by
    have h:=ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [ENNReal.toReal_ofReal (integral_nonneg hn)] at h
    exact h
  refine ⟨hj.1.add hm,hfinite,?_⟩
  have he:(∫q:ℝ,E q)=(∫q:ℝ,differenceJointLoss s hs half advanced m ell F g x q)+
      (∫q:ℝ,matchedSquarePrice s hs half advanced m ell F g x q):=integral_add hd.2.2.1 hm
  have hu:(∫q:ℝ,sourcePressureUpper s hs half advanced m ell F g x q)=
      (∫q:ℝ,transportedDifferenceUpper s hs half advanced m ell F g x q)+
      (∫q:ℝ,matchedSquarePrice s hs half advanced m ell F g x q):=integral_add hj.1 hm
  rw [he] at hreal
  rw [hu]
  linarith only [hreal,hj.2]
end LowEnergy.FirstCurrentMatchedPressure
