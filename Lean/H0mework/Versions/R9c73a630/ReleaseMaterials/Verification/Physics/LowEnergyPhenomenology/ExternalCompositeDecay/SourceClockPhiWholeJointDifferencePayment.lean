import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointDifferenceSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiActualInputFrequencyPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentJointDifference
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumScalarChart
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiNormalizedScalarBudget SourceClockPhiRadiusSourceCurrent SourceScalarEssentialBudget SourceScalarShiftedBulk
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare BalancedInputPrimitivePayment
open ScalarBalancedPrimitive ReverseScalarGaugeWard ReverseBalancedForcePayer BalancedPrimitivePayer PrimitiveInputPayer
open FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric FirstCurrentJointBudget ReverseForcePhysicalPayment
open ReverseNativeClock ReverseNativeFrequencyWard FirstCurrentGeometricPayer OriginalRCommutatorSource
open ClockPhiHeatCorrectedCovarianceSource SourceLocalizedInverseFormPayment SourceResolventBandLimit
open ScalarInputJointNoether InputForceFrequencyPayment MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev S:End:=phiInverseAction
private abbrev B:End:=scalarBulkComplete
private abbrev P:End:=positivePrimitive
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction wholeClockState wholeSourceNext clockSourcePair
  coercivePrimitiveUpper radialInputUpper physicalJointPrice jointDifference differenceJointLoss
  wholeSourceMap correctedCompleteCore balancedInputVector balancedWholeForceState wholeInputWord
  differenceFreeUpper differenceRadialUpper scalarBulkComplete normalizedState normalizedForcing
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by linarith [actual_source_noether_gap half,n_pos]
private abbrev hz(half advanced:Bool)(q:ℝ):(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private theorem whole_state_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeInputWord s hs half advanced m ell F g x (normalizedState m ell F
      (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)=
        wholeClockState s hs half advanced m ell F g x q:=by
  simp only [wholeInputWord,wholeClockState,clockSourcePair,wholeSourceNext,
    FirstCurrentElectricSuccessor.electricSourceDirection,Prod.fst_add,Prod.smul_fst,Module.End.mul_apply,
    wholeSourceMap,LinearMap.add_apply,LinearMap.smul_apply,Module.End.one_apply,frequencyState,map_add,map_smul]
private theorem whole_difference_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    wholeInputWord s hs half advanced m ell F g x
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g-
        balancedForceInput m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g)=
      jointDifference s hs half advanced m ell F g x q:=by
  unfold jointDifference
  rw [actual_balanced_whole_force_return]
  simp only [wholeInputWord,completeBalancedInput,Module.End.mul_apply,map_sub]
private theorem mixed_pair(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L R A C:End):
    Integrable (fun q:ℝ=>sourcePair
      (L (wholeClockState s hs half advanced m ell F g x q)+R (jointDifference s hs half advanced m ell F g x q))
      (A (wholeClockState s hs half advanced m ell F g x q)+C (jointDifference s hs half advanced m ell F g x q))):=by
  let T:=wholeInputWord s hs half advanced m ell F g x
  have h:=actual_input_force_joint_pair_integrable _ (frequency_positive half) advanced m ell F g (L*T) (R*T) (A*T) (C*T)
  simpa only [Module.End.mul_apply,T,whole_state_return,whole_difference_return] using h
private theorem difference_pair(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L R:End):
    Integrable (fun q:ℝ=>sourcePair (L (jointDifference s hs half advanced m ell F g x q))
      (R (jointDifference s hs half advanced m ell F g x q))):=by
  simpa only [LinearMap.zero_apply,zero_add] using mixed_pair s hs half advanced m ell F g x 0 L 0 R
private theorem difference_state_pair(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L R:End):
    Integrable (fun q:ℝ=>sourcePair (L (jointDifference s hs half advanced m ell F g x q))
      (R (wholeClockState s hs half advanced m ell F g x q))):=by
  simpa only [LinearMap.zero_apply,zero_add,add_zero] using mixed_pair s hs half advanced m ell F g x 0 L R 0
private theorem difference_square(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (jointDifference s hs half advanced m ell F g x q))‖^2):=by
  simpa only [sourcePair,inner_self_eq_norm_sq] using (difference_pair s hs half advanced m ell F g x L L).re
private theorem free_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    differenceFreeUpper s hs half advanced m ell F g x q=
      coercivePrimitiveUpper s hs half advanced m ell F g x q+2*reverseNoetherFactor half*
        (sourcePair (jointDifference s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
  unfold coercivePrimitiveUpper
  rw [actual_joint_difference_noether_price]
  unfold differenceFreeUpper differenceNoetherPrice
  ring

/-- The original physical price now spends the input and force response jointly; no separate force-response debit or norm price appears in this upper. -/
theorem actual_whole_joint_difference_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (fun q:ℝ=>scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ∧
    Integrable (differenceJointLoss s hs half advanced m ell F g x) ∧
    Integrable (differenceRadialUpper s hs half advanced m ell F g x) ∧
    0 ≤ (∫q:ℝ,differenceJointLoss s hs half advanced m ell F g x q) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫q:ℝ,differenceJointLoss s hs half advanced m ell F g x q) ≤
        ∫q:ℝ,differenceRadialUpper s hs half advanced m ell F g x q:=by
  have hC:=actual_coercive_primitive_joint_payment s hs half advanced m ell F g x
  have hR:=actual_whole_radial_input_payment s hs half advanced m ell F g x
  have hf:Integrable (differenceFreeUpper s hs half advanced m ell F g x):=by
    have hp:=(difference_state_pair s hs half advanced m ell F g x 1 B).re
    simp only [Module.End.one_apply] at hp
    exact (hC.2.2.1.add (hp.const_mul (2*reverseNoetherFactor half))).congr (Eventually.of_forall (fun q=>(free_return s hs half advanced m ell F g x q).symm))
  have hu:Integrable (differenceRadialUpper s hs half advanced m ell F g x):=by
    unfold differenceRadialUpper
    have hn:=difference_square s hs half advanced m ell F g x (S*U)
    have hq:=(difference_state_pair s hs half advanced m ell F g x U (balancedOwnDefect F)).re
    have hb:=(difference_state_pair s hs half advanced m ell F g x 1 bulkForceRemainder).re
    apply (((hf.add (hn.const_mul (56*n*(reverseNoetherFactor half)^2/3))).add
      (hq.const_mul (8*reverseNoetherFactor half/3))).sub (hb.const_mul (2*reverseNoetherFactor half))).congr
    exact Eventually.of_forall (fun q=>by
      dsimp only [Pi.add_apply,Pi.sub_apply,Module.End.mul_apply,Module.End.one_apply]
      rfl)
  let e(q:ℝ):=primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))/21
  have he:Integrable e:=by
    have hp:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x
      (balancedCompressionForce F) (P*balancedCompressionForce F)).re
    simpa only [e,primitiveEnergy,Module.End.mul_apply,RCLike.re_eq_complex_re] using hp.div_const 21
  have hl:Integrable (differenceJointLoss s hs half advanced m ell F g x):=by
    apply ((hu.sub hC.2.2.1).add he).congr
    exact Eventually.of_forall (fun q=>by
      dsimp only [Pi.add_apply,Pi.sub_apply,e]
      linarith only [(actual_joint_difference_force_balance s hs half advanced m ell F g x q).1])
  refine ⟨hR.1,hR.2.1,hl,hu,integral_nonneg (fun q=>?_),?_⟩
  · exact (actual_joint_difference_force_balance s hs half advanced m ell F g x q).2
  · have hfun:(fun q:ℝ=>coercivePrimitiveUpper s hs half advanced m ell F g x q+differenceJointLoss s hs half advanced m ell F g x q)=
      fun q:ℝ=>differenceRadialUpper s hs half advanced m ell F g x q+e q:=by
      funext q
      exact (actual_joint_difference_force_balance s hs half advanced m ell F g x q).1
    have hb:=congrArg (fun f:ℝ→ℝ=>∫q:ℝ,f q) hfun
    rw [integral_add hC.2.2.1 hl,integral_add hu he] at hb
    have hsplit:(fun q:ℝ=>primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q))=
        fun q:ℝ=>e q+scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q):=by
      funext q
      dsimp only [primitiveNativeLoss,scalarNativeLoss,e]
      ring
    have hpay:=hC.2.2.2.2
    rw [hsplit,integral_add he hR.2.1] at hpay
    linarith only [hpay,hb]
private theorem bulk_im_zero(w:QuantumTest):(sourcePair w (B w)).im=0:=by
  have h:=GaussNativeForm.pair_conjugate w (B w)
  rw [←original_scalar_pair] at h
  have hi:=congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  linarith only [hi]
private theorem full_source_forcing_im(z:ℂ)(w f:QuantumTest)(he:diagonalAction w=f+z • w):
    (sourcePair f (B w)).im=(sourcePair (diagonalAction w) (B w)).im+z.im*(sourcePair w (B w)).re:=by
  have h:=congrArg (fun v:QuantumTest=>(sourcePair v (B w)).im) he
  simp only [sourcePair,map_add,map_smul,inner_add_left,inner_smul_left,
    Complex.add_im,Complex.mul_im,Complex.conj_re,Complex.conj_im] at h
  have hw:=bulk_im_zero w
  unfold sourcePair at hw
  rw [hw,mul_zero,zero_add] at h
  unfold sourcePair
  linarith only [h]
private theorem frequency_im_const(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im=(actualFrequency advanced (sourceNoetherFrequency half) 0).im:=by
  cases advanced <;> simp only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,Complex.star_def,Complex.conj_im,line_im]
def jointDifferenceScalarWard(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  inputScalarWardPrice advanced (jointDifference s hs half advanced m ell F g x q)
    (jointDifferenceForcing s hs half advanced m ell F g x q)

/-- Its signed Ward has ordinary frequency L1 from the actual paired source; the real-frequency forcing term cancels in the self-adjoint B pairing. -/
theorem actual_joint_difference_ward_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (jointDifferenceScalarWard s hs half advanced m ell F g x):=by
  have hH:=(difference_pair s hs half advanced m ell F g x diagonalAction B).im
  have hB:=(difference_pair s hs half advanced m ell F g x 1 B).re
  have hG:=(difference_pair s hs half advanced m ell F g x 1 geometricScalarCurrent).im
  have hN:=difference_square s hs half advanced m ell F g x 1
  simp only [Module.End.one_apply] at hB hG hN
  apply ((((hH.add (hB.const_mul ((actualFrequency advanced (sourceNoetherFrequency half) 0).im))).sub
      (hG.div_const 2)).const_mul (inputCausalSign advanced)).add (hN.const_mul (n^2*‖vacuum‖^2))).congr
  apply Eventually.of_forall;intro q
  dsimp only [Pi.add_apply,Pi.sub_apply,jointDifferenceScalarWard,inputScalarWardPrice]
  rw [full_source_forcing_im _ _ _ (actual_joint_difference_full_source s hs half advanced m ell F g x q).1,
    frequency_im_const half advanced q]
  rfl

def differenceWardUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  differenceRadialUpper s hs half advanced m ell F g x q+(56*n*(reverseNoetherFactor half)^2/3)*
    ((4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))*jointDifferenceScalarWard s hs half advanced m ell F g x q-
      ‖embed (S (U (jointDifference s hs half advanced m ell F g x q)))‖^2)

/-- The same difference forcing now pays the remaining radial-input price in the original J inequality, while both native losses and the complete matched forcing square remain. -/
theorem actual_whole_joint_difference_ward_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (jointDifferenceScalarWard s hs half advanced m ell F g x) ∧
    Integrable (differenceWardUpper s hs half advanced m ell F g x) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫q:ℝ,differenceJointLoss s hs half advanced m ell F g x q) ≤
        ∫q:ℝ,differenceWardUpper s hs half advanced m ell F g x q:=by
  have h:=actual_whole_joint_difference_payment s hs half advanced m ell F g x
  have hw:=actual_joint_difference_ward_integrable s hs half advanced m ell F g x
  have hn:=difference_square s hs half advanced m ell F g x (S*U)
  have hi:Integrable (differenceWardUpper s hs half advanced m ell F g x):=
    h.2.2.2.1.add (((hw.const_mul (4*affineHardyCost/(59^2*n*(sourceNoetherFrequency half-2*n)))).sub hn).const_mul
      (56*n*(reverseNoetherFactor half)^2/3))
  refine ⟨hw,hi,h.2.2.2.2.2.trans (integral_mono h.2.2.2.1 hi (fun q=>?_))⟩
  have hc:0 ≤ 56*n*(reverseNoetherFactor half)^2/3:=by have hn:=n_pos;positivity
  have hp:=actual_joint_difference_scalar_ward s hs half advanced m ell F g x q
  unfold differenceWardUpper
  exact le_add_of_nonneg_right (mul_nonneg hc (sub_nonneg.mpr hp))
end LowEnergy.FirstCurrentJointDifference
