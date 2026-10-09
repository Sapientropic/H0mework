import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeJointDifferencePayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentDifferenceFrequency
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceClockPhiRadiusSourceCurrent
open SourcePhysicalKineticSquare SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard ReverseBalancedForcePayer
open BalancedPrimitivePayer PrimitiveInputPayer ScalarInputJointNoether PhaseCompressionCancellation
open InputForceFrequencyPayment FirstCurrentJointDifference MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev B:End:=scalarBulkComplete
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarBulkComplete wholeClockState wholeSourceNext clockSourcePair
  normalizedState normalizedForcing jointDifference jointDifferenceForcing wholeInputWord differenceWardUpper
  differenceRadialUpper differenceJointLoss physicalJointPrice reverseNoetherFactor phiInverseAction inverseVolumeAction
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by linarith [actual_source_noether_gap half,n_pos]
private abbrev hz(half advanced:Bool)(q:ℝ):(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private theorem difference_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeInputWord s hs half advanced m ell F g x
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g-
        balancedForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)=
      jointDifference s hs half advanced m ell F g x q:=by
  unfold jointDifference
  rw [actual_balanced_whole_force_return]
  simp only [wholeInputWord,completeBalancedInput,Module.End.mul_apply,map_sub]

def derivativeWord(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let z:=actualFrequency advanced (sourceNoetherFrequency half) q
  inputCausalSign advanced*(sourcePair ((18:ℂ) • (z • wholeInputWord s hs half advanced m ell F g x
    (phaseForcingFrequencySource m ell F z (hz half advanced q) g))) (B (jointDifference s hs half advanced m ell F g x q))).im
def plainWord(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*inputCausalSign advanced*(sourcePair (wholeInputWord s hs half advanced m ell F g x
    (normalizedForcing m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g))
      (B (jointDifference s hs half advanced m ell F g x q))).im
def shiftedWord(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  18*inputCausalSign advanced*(sourcePair (actualFrequency advanced (sourceNoetherFrequency half) q •
    wholeInputWord s hs half advanced m ell F g x
      (normalizedForcing m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g))
      (inputForceDifferenceDerivative (sourceNoetherFrequency half) advanced m ell F g
        (B*wholeInputWord s hs half advanced m ell F g x) q)).im

def transportedDifferenceWard(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  jointDifferenceScalarWard s hs half advanced m ell F g x q-derivativeWord s hs half advanced m ell F g x q-
    plainWord s hs half advanced m ell F g x q-shiftedWord s hs half advanced m ell F g x q
private theorem pair18(u v:QuantumTest):(sourcePair ((18:ℂ) • u) v).im=18*(sourcePair u v).im:=by
  simp only [sourcePair,map_smul,inner_smul_left,Complex.mul_im,map_ofNat,Complex.re_ofNat,Complex.im_ofNat,zero_mul,add_zero]

/-- The exact retained Ward has no forcing derivative: the derivative is transported onto the actual input-minus-force response, with the entire clock/electric H0 commutator retained. -/
theorem actual_transported_difference_ward_source(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let T:=wholeInputWord s hs half advanced m ell F g x
    let w0:=normalizedState m ell F z (hz half advanced q) g
    let f0:=normalizedForcing m ell F z (hz half advanced q) g
    let d0:=balancedInputVector m ell F z (hz half advanced q) g-balancedForceInput m ell F z (hz half advanced q) g
    let d:=jointDifference s hs half advanced m ell F g x q
    transportedDifferenceWard s hs half advanced m ell F g x q=
      inputCausalSign advanced*(sourcePair
        (T (Zbar f0-(18:ℂ) • f0-gaugeBalancedNativeForce w0)+bracket diagonalAction T d0) (B d)).im-
      shiftedWord s hs half advanced m ell F g x q-
      (inputCausalSign advanced/2)*(sourcePair d (geometricScalarCurrent d)).im+n^2*‖vacuum‖^2*‖embed d‖^2:=by
  dsimp only
  have he:=(actual_joint_difference_full_source s hs half advanced m ell F g x q).2
  dsimp only at he
  unfold transportedDifferenceWard jointDifferenceScalarWard inputScalarWardPrice
  rw [he]
  simp only [derivativeWord,plainWord,Zbar,map_add,map_sub,map_smul,sourcePair,
    inner_add_left,inner_sub_left,inner_smul_left,Complex.add_im,Complex.sub_im,Complex.mul_im,
    map_ofNat,Complex.re_ofNat,Complex.im_ofNat,zero_mul,add_zero]
  ring

private theorem frequency_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (derivativeWord s hs half advanced m ell F g x) ∧
    Integrable (plainWord s hs half advanced m ell F g x) ∧
    Integrable (shiftedWord s hs half advanced m ell F g x) ∧
    (∫q:ℝ,derivativeWord s hs half advanced m ell F g x q)=
      -(∫q:ℝ,plainWord s hs half advanced m ell F g x q)-(∫q:ℝ,shiftedWord s hs half advanced m ell F g x q):=by
  let T:=wholeInputWord s hs half advanced m ell F g x
  have h:=actual_input_force_frequency_pair _ (frequency_positive half) advanced m ell F g T (B*T)
  have hpay:=actual_input_force_signed_frequency_payment _ (frequency_positive half) advanced m ell F g T (B*T)
  dsimp only at h hpay
  simp only [Module.End.mul_apply,T,difference_return] at h hpay
  refine ⟨?_,?_,?_,?_⟩
  · apply (h.2.1.im.const_mul (inputCausalSign advanced*18)).congr
    exact Eventually.of_forall (fun q=>by
      dsimp only [derivativeWord]
      rw [pair18]
      simp only [RCLike.im_eq_complex_im]
      ring)
  · exact h.1.im.const_mul (18*inputCausalSign advanced)
  · exact h.2.2.1.im.const_mul (18*inputCausalSign advanced)
  · simpa only [derivativeWord,plainWord,shiftedWord,integral_const_mul,mul_assoc,neg_mul] using hpay

/-- The whole-frequency source Ward is unchanged by the actual signed transport, and both complete price functions are L1. -/
theorem actual_difference_ward_frequency_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (transportedDifferenceWard s hs half advanced m ell F g x) ∧
    (∫q:ℝ,transportedDifferenceWard s hs half advanced m ell F g x q)=
      ∫q:ℝ,jointDifferenceScalarWard s hs half advanced m ell F g x q:=by
  have hw:=actual_joint_difference_ward_integrable s hs half advanced m ell F g x
  have h:=frequency_payment s hs half advanced m ell F g x
  refine ⟨((hw.sub h.1).sub h.2.1).sub h.2.2.1,?_⟩
  unfold transportedDifferenceWard
  erw [integral_sub ((hw.sub h.1).sub h.2.1) h.2.2.1,integral_sub (hw.sub h.1) h.2.1,integral_sub hw h.1]
  linarith only [h.2.2.2]

def transportedDifferenceUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  differenceWardUpper s hs half advanced m ell F g x q+
    ((56*n*(reverseNoetherFactor half)^2/3)*(4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n))))*
      (transportedDifferenceWard s hs half advanced m ell F g x q-jointDifferenceScalarWard s hs half advanced m ell F g x q)

/-- The original J inequality consumes the real signed frequency transport. Both the complete d-force loss and the original matched completion remain available for joint payment. -/
theorem actual_whole_transported_difference_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (transportedDifferenceUpper s hs half advanced m ell F g x) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫q:ℝ,differenceJointLoss s hs half advanced m ell F g x q) ≤
        ∫q:ℝ,transportedDifferenceUpper s hs half advanced m ell F g x q:=by
  have hj:=actual_whole_joint_difference_ward_payment s hs half advanced m ell F g x
  have ht:=actual_difference_ward_frequency_return s hs half advanced m ell F g x
  let c:ℝ:=(56*n*(reverseNoetherFactor half)^2/3)*(4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))
  have he:Integrable (fun q:ℝ=>c*(transportedDifferenceWard s hs half advanced m ell F g x q-
      jointDifferenceScalarWard s hs half advanced m ell F g x q)):=(ht.1.sub hj.1).const_mul c
  refine ⟨hj.2.1.add he,?_⟩
  have hup:(∫q:ℝ,transportedDifferenceUpper s hs half advanced m ell F g x q)=
      ∫q:ℝ,differenceWardUpper s hs half advanced m ell F g x q:=by
    unfold transportedDifferenceUpper
    erw [integral_add hj.2.1 he,integral_const_mul,integral_sub ht.1 hj.1]
    rw [ht.2,sub_self,mul_zero,add_zero]
  rw [hup]
  exact hj.2.2
end LowEnergy.FirstCurrentDifferenceFrequency
