import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointPrimitiveInputLoss
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentJointForceLoss
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare BalancedInputPrimitivePayment
open ScalarBalancedPrimitive ReverseScalarGaugeWard ReverseBalancedForcePayer BalancedPrimitivePayer PrimitiveInputPayer
open FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric FirstCurrentJointBudget ReverseForcePhysicalPayment
open ReverseNativeFrequencyWard SourceLocalizedInverseFormPayment SourceResolventBandLimit MeasureTheory Filter
private abbrev P:=positivePrimitive
attribute [local irreducible] sourcePair embed diagonalAction wholeClockState wholeSourceNext clockSourcePair
  coercivePrimitiveUpper radialInputUpper physicalJointPrice wholeJointForceInputLoss
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private abbrev hz(half advanced:Bool)(q:ℝ):
    (actualFrequency advanced (sourceNoetherFrequency half) q).im≠0:=
  reverse_frequency_nonreal advanced _ (frequency_positive half) q

/-- The new joint force/input loss is paid inside the original physical frequency inequality. Its L1 follows from the exact source balance and the already generated complete upper prices. -/
theorem actual_whole_joint_force_input_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (fun q:ℝ=>scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q)) ∧
    Integrable (wholeJointForceInputLoss s hs half advanced m ell F g x) ∧
    Integrable (radialInputUpper s hs half advanced m ell F g x) ∧
    0 ≤ (∫q:ℝ,wholeJointForceInputLoss s hs half advanced m ell F g x q) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q))+
      (∫q:ℝ,wholeJointForceInputLoss s hs half advanced m ell F g x q) ≤
        ∫q:ℝ,radialInputUpper s hs half advanced m ell F g x q:=by
  have hC:=actual_coercive_primitive_joint_payment s hs half advanced m ell F g x
  have hR:=actual_whole_radial_input_payment s hs half advanced m ell F g x
  let e(q:ℝ):=primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))/21
  have he:Integrable e:=by
    have hp:=(actual_whole_state_pair_integrable s hs half advanced m ell F g x
      (balancedCompressionForce F) (P*balancedCompressionForce F)).re
    simpa only [e,primitiveEnergy,Module.End.mul_apply,RCLike.re_eq_complex_re] using hp.div_const 21
  have hl:Integrable (wholeJointForceInputLoss s hs half advanced m ell F g x):=by
    apply ((hR.2.2.1.sub hC.2.2.1).add he).congr
    exact Eventually.of_forall (fun q=>by
      dsimp only [Pi.add_apply,Pi.sub_apply,e]
      linarith only [actual_whole_force_input_balance s hs half advanced m ell F g x q])
  refine ⟨hR.1,hR.2.1,hl,hR.2.2.1,integral_nonneg (fun q=>?_),?_⟩
  · simpa only [wholeJointForceInputLoss,Pi.zero_apply] using (actual_joint_force_input_loss F (ReverseNativeClock.reverseNoetherFactor half)
      (completeBalancedInput s hs half advanced m ell F g x q) (wholeClockState s hs half advanced m ell F g x q)).2
  · have hfun:(fun q:ℝ=>coercivePrimitiveUpper s hs half advanced m ell F g x q+
        wholeJointForceInputLoss s hs half advanced m ell F g x q)=
      fun q:ℝ=>radialInputUpper s hs half advanced m ell F g x q+e q:=by
      funext q
      exact actual_whole_force_input_balance s hs half advanced m ell F g x q
    have hb:=congrArg (fun f:ℝ→ℝ=>∫q:ℝ,f q) hfun
    rw [integral_add hC.2.2.1 hl,integral_add hR.2.2.1 he] at hb
    have hsplit:(fun q:ℝ=>primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q))=
        fun q:ℝ=>e q+scalarNativeLoss (wholeClockState s hs half advanced m ell F g x q):=by
      funext q
      dsimp only [primitiveNativeLoss,scalarNativeLoss,e]
      ring
    have hpay:=hC.2.2.2.2
    rw [hsplit,integral_add he hR.2.1] at hpay
    linarith only [hpay,hb]
end LowEnergy.FirstCurrentJointForceLoss
