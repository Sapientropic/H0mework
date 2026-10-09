import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCoercivePrimitiveJointPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedScalarInputAbsorption
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.PrimitiveInputPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare SourceScalarDoubleCurrent
open SourceScalarShiftedBulk SourceScalarEssentialBudget SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit SourceScalarPositiveBulkWard
open SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceScalarPairedTransport SourceJointResidualEnergy SourceFourPoleEnergyClosed
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare OriginalRCommutatorSource
open ReverseNativeClock ReverseNativeFrequencyWard ReverseNativeOuterSource ReverseScalarGaugeWard ReverseForcePhysicalPayment ReverseBalancedForcePayer
open ScalarBalancedPrimitive BalancedPrimitivePayer BalancedInputPrimitivePayment ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev B:End:=scalarBulkComplete
private abbrev X:End:=weightedElectricCurrent
private abbrev P:End:=positivePrimitive
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction resolventCore balancedCompressionForce
  wholeClockState wholeSourceNext wholeSourceMap correctedCompleteCore clockSourcePair positivePrimitive originalNormalizerPrice
  phaseRow inputSeed balancedInputSeed balancedInputVector normalizedState normalizedForcing scalarBulkComplete weightedElectricCurrent
  reverseNoetherFactor reverseScalarReserve reverseNoetherNormCost scalarEnergy wholeStep
  reverseInputVector gaugeInputVector coreEquiv SourceGaugeScaleTransport.generator reverseNativeClock phiThetaAction phiInverseAction
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by linarith [n_pos,actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):(actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q
private def pole(advanced:Bool)(μ a q:ℝ):ℂ:=((a:ℂ)-actualFrequency advanced μ q)⁻¹
private theorem pole_pair(advanced:Bool)(μ:ℝ)(hμ:0<μ)(a b:ℝ):
    Integrable (fun q:ℝ=>star (pole advanced μ a q)*pole advanced μ b q):=by
  cases advanced
  · simpa only [pole,actualFrequency,Bool.false_eq_true,ite_false,SourceJointResidualEnergy.pole] using! two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (two_pole_integrable μ a b hμ)
    have he(q:ℝ):star (pole true μ a q)*pole true μ b q=star (star (SourceJointResidualEnergy.pole μ a q)*SourceJointResidualEnergy.pole μ b q):=by
      simp only [pole,actualFrequency,ite_true,SourceJointResidualEnergy.pole,star_mul,star_inv₀,star_sub,Complex.star_def,Complex.conj_ofReal]
      ring
    simpa only [he] using! h
private theorem finite_pair {ι:Type*}[Fintype ι](c d:ι→QuantumTest)(a:ι→ℂ):
    sourcePair (∑i,a i • c i) (∑j,a j • d j)=∑i,∑j,(star (a i)*a j)*sourcePair (c i) (d j):=by
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,starRingEnd_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  ring
private theorem finite_integrable {ι:Type*}[Fintype ι](a:ι→ℝ)(c d:ι→QuantumTest)(advanced:Bool)(μ:ℝ)(hμ:0<μ):
    Integrable (fun q:ℝ=>sourcePair (∑i,pole advanced μ (a i) q • c i) (∑i,pole advanced μ (a i) q • d i)):=by
  have hi:Integrable (fun q:ℝ=>∑i,∑j,(star (pole advanced μ (a i) q)*pole advanced μ (a j) q)*sourcePair (c i) (d j)):=
    integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>(pole_pair advanced μ hμ (a i) (a j)).mul_const _))
  exact hi.congr (Eventually.of_forall (fun q=>(finite_pair c d _).symm))
private theorem core_channels(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    resolventCore F z hz (coreEquiv.symm g)=∑j:Channel F,((channelValue F j:ℂ)-z)⁻¹ • channelTest F g j:=by
  have h:resolventCore F z hz (coreEquiv.symm g)=state F z hz g:=by
    simp only [resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
  rw [h,actual_state_channels]
private theorem input_rows(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:diagonal.domain):
    balancedInputVector m ell F z hz g=∑i:Fin 2,
      (bracket Zbar (phaseRow m ell i) (resolventCore F z hz (coreEquiv.symm (inputSeed g i)))+
        phaseRow m ell i (resolventCore F z hz (coreEquiv.symm (balancedInputSeed g i)))):=by
  have he:=congrArg (fun v:QuantumTest=>v-(9:ℂ) • gaugeInputVector m ell F z hz g)
    (actual_reverse_input_vector m ell F z hz g).symm
  unfold balancedInputVector
  refine he.trans ?_
  simp only [gaugeInputVector,balancedInputSeed,coreEquiv.symm_apply_apply,Finset.smul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl;intro i _
  simp only [Zbar,bracket,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sub,map_smul]
  module

def completeBalancedInput(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
    (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) (hz half advanced q) g))
private def inputColumn(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(j:Channel F):QuantumTest:=
  correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
    (∑i:Fin 2,(bracket Zbar (phaseRow m ell i) (channelTest F (inputSeed g i) j)+
      phaseRow m ell i (channelTest F (balancedInputSeed g i) j))))
private theorem input_channels(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    completeBalancedInput s hs half advanced m ell F g x q=
      ∑j:Channel F,pole advanced (sourceNoetherFrequency half) (channelValue F j) q • inputColumn s hs half advanced m ell F g x j:=by
  unfold completeBalancedInput
  rw [input_rows]
  simp_rw [core_channels,map_sum,map_smul]
  simp only [inputColumn,pole,map_sum,map_add,map_smul,Finset.smul_sum,smul_add,Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 1
  exact Finset.sum_comm
private theorem input_pair(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L R:End):
    Integrable (fun q:ℝ=>sourcePair (L (completeBalancedInput s hs half advanced m ell F g x q))
      (R (wholeClockState s hs half advanced m ell F g x q))):=by
  have hi:=finite_integrable (channelValue F) (fun j=>L (inputColumn s hs half advanced m ell F g x j))
    (fun j=>R (wholeClockColumn s hs half advanced m ell F g x j)) advanced _ (frequency_positive half)
  exact hi.congr (Eventually.of_forall (fun q=>by dsimp only;rw [input_channels,actual_whole_clock_channels];simp only [map_sum,map_smul,pole]))
private theorem input_square(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(L:End):
    Integrable (fun q:ℝ=>‖embed (L (completeBalancedInput s hs half advanced m ell F g x q))‖^2):=by
  have hi:=(finite_integrable (channelValue F) (fun j=>L (inputColumn s hs half advanced m ell F g x j))
    (fun j=>L (inputColumn s hs half advanced m ell F g x j)) advanced _ (frequency_positive half)).re
  apply hi.congr
  apply Eventually.of_forall;intro q
  dsimp only
  rw [input_channels]
  simp only [map_sum,map_smul,sourcePair,inner_self_eq_norm_sq]

def scalarNativeLoss(w:QuantumTest):ℝ:=
  (150*n/7)*(sourcePair w (balancedScalarSquare w)).re+(144*n/175)*‖vacuum‖^2*‖embed w‖^2
private def inputFreeUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  reverseNoetherFactor half*(18*scalarEnergy (wholeClockState s hs half advanced m ell F g x q)+
    72*wholeStep s hs half advanced m ell F g*
      (sourcePair (correctedCompleteCore s hs x.1 x.2 (X (frequencyState half advanced m ell F g q)))
        (B (wholeClockState s hs half advanced m ell F g x q))).re+
    balancedWholeForceNativeDebit s hs half advanced m ell F g x q/(actualFrequency advanced (sourceNoetherFrequency half) q).im-
    2*(wholeClockWardKernel s hs half advanced m ell F g q x).re-reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q))+
  reverseNoetherNormCost half*‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2+
    clearedNativePrice (wholeClockState s hs half advanced m ell F g x q)+
    compensatedPrimitiveWork F (wholeClockState s hs half advanced m ell F g x q)+
    originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)
def radialInputUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  let a:=reverseNoetherFactor half
  let I:=completeBalancedInput s hs half advanced m ell F g x q
  let w:=wholeClockState s hs half advanced m ell F g x q
  inputFreeUpper s hs half advanced m ell F g x q+(56*n*a^2/3)*‖embed (phiInverseAction (U I))‖^2+
    (8*a/3)*(sourcePair (U I) (balancedOwnDefect F w)).re-2*a*(sourcePair I (bulkForceRemainder w)).re
private theorem input_free_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    coercivePrimitiveUpper s hs half advanced m ell F g x q=
      inputFreeUpper s hs half advanced m ell F g x q-2*reverseNoetherFactor half*
        (sourcePair (completeBalancedInput s hs half advanced m ell F g x q) (B (wholeClockState s hs half advanced m ell F g x q))).re:=by
  unfold coercivePrimitiveUpper balancedNativeNoetherPrice inputFreeUpper completeBalancedInput
  ring

/-- The actual negative primitive force square pays the second-order input/B slot. Its generated price is the inverse-radius/inverse-volume input, with every own-defect and local field cross retained. -/
theorem actual_whole_radial_input_point(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    coercivePrimitiveUpper s hs half advanced m ell F g x q-
      primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))/21 ≤
      radialInputUpper s hs half advanced m ell F g x q:=by
  have h:=actual_scalar_input_radial_absorption F (reverseNoetherFactor half)
    (completeBalancedInput s hs half advanced m ell F g x q) (wholeClockState s hs half advanced m ell F g x q)
  rw [input_free_return]
  dsimp only [radialInputUpper]
  linarith only [h]

/-- This is the original complete physical action after its force-square payment: no input B-energy or force variance is an assumption, and the scalar/vacuum loss survives the payment. -/
theorem actual_whole_radial_input_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (fun q:ℝ=>scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ∧
    Integrable (radialInputUpper s hs half advanced m ell F g x) ∧
    0 ≤ (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ≤
        ∫q:ℝ,radialInputUpper s hs half advanced m ell F g x q:=by
  have hJ:=actual_coercive_primitive_joint_payment s hs half advanced m ell F g x
  let e:=fun q:ℝ=>primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))/21
  have he:Integrable e:=by
    have hp:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x
      (balancedCompressionForce F) (P*balancedCompressionForce F)).re
    simpa only [e,primitiveEnergy,Module.End.mul_apply,RCLike.re_eq_complex_re] using hp.div_const 21
  have hl:Integrable (fun q:ℝ=>scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)):=by
    apply (hJ.2.1.sub he).congr
    exact Eventually.of_forall (fun q=>by dsimp only [Pi.sub_apply,e,primitiveNativeLoss,scalarNativeLoss];ring)
  have hi:Integrable (inputFreeUpper s hs half advanced m ell F g x):=by
    have hb:Integrable (fun q:ℝ=>(sourcePair (completeBalancedInput s hs half advanced m ell F g x q)
      (B (wholeClockState s hs half advanced m ell F g x q))).re):=by
      simpa only [Module.End.one_apply,RCLike.re_eq_complex_re] using (input_pair s hs half advanced m ell F g x 1 B).re
    exact (hJ.2.2.1.add (hb.const_mul (2*reverseNoetherFactor half))).congr
      (Eventually.of_forall (fun q=>by simp only [Pi.add_apply,input_free_return];ring))
  have hr:Integrable (radialInputUpper s hs half advanced m ell F g x):=by
    have hn:=input_square s hs half advanced m ell F g x (phiInverseAction*U)
    have hq:=(input_pair s hs half advanced m ell F g x U (balancedOwnDefect F)).re
    have hb:=(input_pair s hs half advanced m ell F g x 1 bulkForceRemainder).re
    exact ((hi.add (hn.const_mul (56*n*(reverseNoetherFactor half)^2/3))).add
      (hq.const_mul (8*reverseNoetherFactor half/3))).sub (hb.const_mul (2*reverseNoetherFactor half))
  refine ⟨hJ.1,hl,hr,integral_nonneg (fun q=>?_),?_⟩
  · unfold scalarNativeLoss
    have hs0:=actual_balanced_scalar_square_nonnegative (wholeClockState s hs half advanced m ell F g x q)
    have hn:=n_pos
    positivity
  · have hupper:=integral_mono (hJ.2.2.1.sub he) hr (actual_whole_radial_input_point s hs half advanced m ell F g x)
    have hloss:(∫q:ℝ,primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q))=
      (∫q:ℝ,e q)+(∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)):=by
      have hfun:(fun q:ℝ=>primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q))=
          fun q:ℝ=>e q+scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q):=by
        funext q
        dsimp only [primitiveNativeLoss,scalarNativeLoss,e]
        ring
      rw [hfun]
      exact integral_add he hl
    erw [integral_sub hJ.2.2.1 he] at hupper
    have hp:=hJ.2.2.2.2
    rw [hloss] at hp
    linarith only [hp,hupper]
end LowEnergy.PrimitiveInputPayer
