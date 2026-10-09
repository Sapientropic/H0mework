import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointInputScalarPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCompleteClockReverseReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.JointDifferenceMatchedSource
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceScalarDoubleCurrent
open SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource SourceClockPhiRadiusSourceCurrent
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseScalarGaugeWard ReverseBalancedForcePayer ReverseGaugeOuterPayment
open PrimitiveInputPayer ClockPhiHeatCorrectedCovarianceSource FirstCurrentGeometricPayer
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev D:End:=combinedGenerator
private abbrev Dc:End:=dilation
private abbrev M:End:=matchedTester
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • G
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore matchedTester reverseNativeClock
  SourceGaugeScaleTransport.generator wholeSourceMap wholeSourceNext wholeClockState wholeFrequencyJet wholeReverseSource
  wholeOuterSource balancedWardWord balancedWholeForceState completeBalancedInput weightedElectricCurrent
private theorem inverse_dilation:Dc*U-U*Dc=(2*Complex.I) • U:=by
  have h:=congrArg (fun A:End=>(-2*Complex.I/3) • A) SourceScalarInverseBulk.inverse_coframe
  change (-2*Complex.I/3) • ((3*Complex.I/2) • (Dc*U-U*Dc))=
    (-2*Complex.I/3) • ((-3:ℂ) • U) at h
  simp only [smul_smul] at h
  have hi:(-2*Complex.I/3)*(3*Complex.I/2)=(1:ℂ):=by
    calc _= -(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  rw [hi,one_smul] at h
  convert h using 1
  congr 1
  ring

/-- U times the actual compensated reverse clock has exactly the same matched tester as the physical negative completed square. The gauge generator is retained. -/
theorem actual_weighted_balanced_matched_source:
    U*Zbar=(6:ℂ) • (U*D)-(3:ℂ) • M-(12:ℂ) • U-(9:ℂ) • (U*G):=by
  have h:Dc*U=U*Dc+(2*Complex.I) • U:=by
    linear_combination (norm:=module) inverse_dilation
  have h6:(3*Complex.I)*(2*Complex.I)=(-6:ℂ):=by
    calc _=6*(Complex.I*Complex.I):=by ring
         _=_:=by rw [Complex.I_mul_I];ring
  unfold Zbar M matchedTester matchedColumn reverseNativeClock
  rw [h]
  simp only [mul_sub,mul_smul_comm,smul_add,smul_smul,h6]
  module

/-- The actual whole difference has the complete frequency source, both covariance noises and its selected electric outer correction. No cutoff term is dropped. -/
theorem actual_whole_difference_matched_transport(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    completeBalancedInput s hs half advanced m ell F g x q-balancedWholeForceState s hs half advanced m ell F g x q=
      Zbar (wholeClockState s hs half advanced m ell F g x q)+(18:ℂ) • wholeFrequencyJet s hs half advanced m ell F g x q-
        correctedCompleteCore s hs x.1 x.2 (reverseClockReturn s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1))+
        (36*(wholeStep s hs half advanced m ell F g:ℂ)) •
          correctedCompleteCore s hs x.1 x.2 (weightedElectricCurrent (frequencyState half advanced m ell F g q)):=by
  have h:=actual_whole_reverse_frequency_ward s hs half advanced m ell F g x q
  rw [actual_whole_reverse_source_split,actual_complete_reverse_clock_return] at h
  simp only [Module.End.mul_apply] at h
  have hg:=congrArg (correctedCompleteCore s hs x.1 x.2)
    (actual_outer_gauge_word_difference s hs half advanced m ell F g q)
  simp only [map_sub,map_smul] at hg
  have hk:correctedCompleteCore s hs x.1 x.2 (G ((wholeSourceNext s hs half advanced m ell F g q).1))=
      G (wholeClockState s hs half advanced m ell F g x q):=by
    have he:=LinearMap.congr_fun (actual_complete_gauge_commute s hs x.1 x.2).eq
      ((wholeSourceNext s hs half advanced m ell F g q).1)
    simpa only [wholeClockState,clockSourcePair,Module.End.mul_apply] using he.symm
  rw [hk] at hg
  have hb:correctedCompleteCore s hs x.1 x.2 (balancedWardWord s hs half advanced m ell F g q)=
      (-36*(wholeStep s hs half advanced m ell F g:ℂ)) •
        correctedCompleteCore s hs x.1 x.2 (weightedElectricCurrent (frequencyState half advanced m ell F g q))+
      completeBalancedInput s hs half advanced m ell F g x q-balancedWholeForceState s hs half advanced m ell F g x q:=by
    rw [actual_balanced_whole_force_return]
    unfold balancedWardWord completeBalancedInput
    simp only [map_add,map_sub,map_smul,smul_smul]
    module
  rw [hb] at hg
  simp only [Zbar,LinearMap.sub_apply,LinearMap.smul_apply]
  linear_combination (norm:=module) -h-hg

def matchedDifferenceRemainder(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  let w:=wholeClockState s hs half advanced m ell F g x q
  let f:=(clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2
  (432/(n:ℂ)) • S f+(6:ℂ) • S (U (D w))-(12:ℂ) • S (U w)-(9:ℂ) • S (U (G w))+
    (18:ℂ) • S (U (wholeFrequencyJet s hs half advanced m ell F g x q))-
    S (U (correctedCompleteCore s hs x.1 x.2 (reverseClockReturn s hs x.1 x.2 ((wholeSourceNext s hs half advanced m ell F g q).1))))+
    (36*(wholeStep s hs half advanced m ell F g:ℂ)) •
      S (U (correctedCompleteCore s hs x.1 x.2 (weightedElectricCurrent (frequencyState half advanced m ell F g q))))

/-- The SU-difference is coupled to the literal M + 144 fullforcing/n vector. This is a source equality before estimating either of the physical negative squares. -/
theorem actual_whole_matched_difference_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    S (U (completeBalancedInput s hs half advanced m ell F g x q-balancedWholeForceState s hs half advanced m ell F g x q))+
      (3:ℂ) • S (M (wholeClockState s hs half advanced m ell F g x q)+(144/(n:ℂ)) •
        (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)).2)=
      matchedDifferenceRemainder s hs half advanced m ell F g x q:=by
  have hw:=congrArg (fun f:QuantumTest=>S (U f))
    (actual_whole_difference_matched_transport s hs half advanced m ell F g x q)
  have hm:=congrArg S (LinearMap.congr_fun actual_weighted_balanced_matched_source
    (wholeClockState s hs half advanced m ell F g x q))
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul] at hm
  simp only [Zbar,LinearMap.sub_apply,LinearMap.smul_apply,map_add,map_sub,map_smul] at hw
  unfold matchedDifferenceRemainder
  simp only [map_add,map_sub,map_smul]
  linear_combination (norm:=module) hw+hm
end LowEnergy.JointDifferenceMatchedSource
