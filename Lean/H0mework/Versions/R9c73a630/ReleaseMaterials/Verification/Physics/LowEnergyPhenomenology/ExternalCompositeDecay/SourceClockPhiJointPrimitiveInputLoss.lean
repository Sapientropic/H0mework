import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeRadialInputPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FirstCurrentJointForceLoss
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourcePhysicalKineticSquare
open SourceClockPhiNormalizedScalarBudget SourceClockPhiMatchedElectricSource ReverseNativeClock
open SourceScalarEssentialBudget
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceClockPhiRadiusSourceCurrent SourceClockPhiRadiusAcceleration
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare BalancedInputPrimitivePayment
open ScalarBalancedPrimitive ReverseScalarGaugeWard ReverseBalancedForcePayer BalancedPrimitivePayer PrimitiveInputPayer
open FirstCurrentWholeCarrier FirstCurrentAdmissibleElectric FirstCurrentJointBudget ReverseForcePhysicalPayment
open ReverseNativeFrequencyWard FirstCurrentGeometricPayer OriginalRCommutatorSource
open ClockPhiHeatCorrectedCovarianceSource SourceLocalizedInverseFormPayment SourceResolventBandLimit MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev B:End:=scalarBulkComplete
private abbrev P:End:=positivePrimitive
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction scalarBulkComplete balancedCompressionForce positivePrimitive
  wholeClockState wholeSourceNext correctedCompleteCore clockSourcePair originalNormalizerPrice
  normalizedState normalizedForcing scalarEnergy wholeStep reverseScalarReserve reverseNoetherFactor reverseNoetherNormCost
  wholeClockWardKernel balancedWholeForceNativeDebit clearedNativePrice compensatedPrimitiveWork
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem inverse_pair(f g:QuantumTest):sourcePair f (U g)=sourcePair (U f) g:=multiply_pair _ _ _ _
private theorem force_square(a:ℝ)(v y:QuantumTest):
    -(8*a/3)*(sourcePair v y).re-(2/(21*n))*‖embed y‖^2=
      (56*n*a^2/3)*‖embed v‖^2-
        (2/(21*n))*‖embed y+((14*n*a:ℝ):ℂ) • embed v‖^2:=by
  have he:=norm_add_sq (𝕜:=ℂ) (embed y) (((14*n*a:ℝ):ℂ) • embed v)
  simp only [inner_smul_right,RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at he
  have hc:(sourcePair y v).re=(sourcePair v y).re:=by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) (embed y) (embed v)
  have hc' : (inner ℂ (embed y) (embed v)).re=(sourcePair v y).re:=by
    unfold sourcePair at hc ⊢
    exact hc
  rw [hc'] at he
  rw [he]
  field_simp [n_pos.ne']
  ring

private theorem radius_inverse_pair(v y:QuantumTest):
    sourcePair (phiInverseAction v) (phiRadiusAction y)=sourcePair v y:=by
  have h:phiRadiusAction (phiInverseAction v)=v:=by
    apply DFunLike.ext;intro z
    change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • v z)=v z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [mul_inv_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  have hr(f g:QuantumTest):sourcePair f (phiRadiusAction g)=sourcePair (phiRadiusAction f) g:=multiply_pair _ _ _ _
  rw [hr,h]


def jointForceInputLoss(F:Index)(a:ℝ)(input w:QuantumTest):ℝ:=
  (2/(21*n))*‖embed (phiRadiusAction (balancedCompressionForce F w))+
    ((14*n*a:ℝ):ℂ) • embed (phiInverseAction (U input))‖^2+
      (sourcePair (balancedCompressionForce F w) (electricAction (balancedCompressionForce F w))).re/42

/-- The source retains both the completed radial force/input square and the actual electric force energy. -/
theorem actual_joint_force_input_loss(F:Index)(a:ℝ)(input w:QuantumTest):
    -2*a*(sourcePair input (B w)).re-primitiveEnergy (balancedCompressionForce F w)/21+
      jointForceInputLoss F a input w=
        (56*n*a^2/3)*‖embed (phiInverseAction (U input))‖^2+
        (8*a/3)*(sourcePair (U input) (balancedOwnDefect F w)).re-
        2*a*(sourcePair input (bulkForceRemainder w)).re ∧
    0 ≤ jointForceInputLoss F a input w:=by
  have hs:sourcePair input (B w)=(4/3:ℂ)*sourcePair (U input) (balancedCompressionForce F w)-
      (4/3:ℂ)*sourcePair (U input) (balancedOwnDefect F w)+sourcePair input (bulkForceRemainder w):=by
    have hB:B=(4/3:ℂ) • (U*balancedCompressionForce F)-
        (4/3:ℂ) • (U*balancedOwnDefect F)+bulkForceRemainder:=actual_scalar_bulk_compression F
    rw [hB]
    simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      pair_add_r,pair_sub_r,pair_smul_r,inverse_pair]
  have hr:=congrArg Complex.re hs
  norm_num only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.div_re,Complex.div_im,
    Complex.re_ofNat,Complex.im_ofNat,Complex.normSq_ofNat,zero_mul,sub_zero] at hr
  have he:=force_square a (phiInverseAction (U input)) (phiRadiusAction (balancedCompressionForce F w))
  rw [radius_inverse_pair] at he
  have hp:=(actual_positive_primitive_energy (balancedCompressionForce F w)).1
  constructor
  · unfold jointForceInputLoss
    rw [hp]
    have hc:(2/n)/21=2/(21*n):=by field_simp [n_pos.ne']
    rw [show ((2/n)*‖embed (phiRadiusAction (balancedCompressionForce F w))‖^2+
        (1/2:ℝ)*(sourcePair (balancedCompressionForce F w) (electricAction (balancedCompressionForce F w))).re)/21=
      (2/(21*n))*‖embed (phiRadiusAction (balancedCompressionForce F w))‖^2+
        (sourcePair (balancedCompressionForce F w) (electricAction (balancedCompressionForce F w))).re/42 by rw [add_div,mul_div_right_comm,hc];ring]
    linear_combination he-2*a*hr
  · unfold jointForceInputLoss
    have hn:=n_pos
    have hE:=JointElectricSource.actual_electric_energy_nonnegative (balancedCompressionForce F w)
    positivity

def wholeJointForceInputLoss(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  jointForceInputLoss F (reverseNoetherFactor half) (completeBalancedInput s hs half advanced m ell F g x q)
    (wholeClockState s hs half advanced m ell F g x q)

attribute [local irreducible] wholeSourceMap balancedInputVector frequencyState weightedElectricCurrent
  inverseVolumeAction phiInverseAction balancedOwnDefect bulkForceRemainder
  actualFrequency sourceNoetherFrequency sourceTime
private theorem upper_gap(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    radialInputUpper s hs half advanced m ell F g x q-coercivePrimitiveUpper s hs half advanced m ell F g x q=
      2*reverseNoetherFactor half*(sourcePair (completeBalancedInput s hs half advanced m ell F g x q)
        (B (wholeClockState s hs half advanced m ell F g x q))).re+
      (56*n*(reverseNoetherFactor half)^2/3)*‖embed (phiInverseAction (U (completeBalancedInput s hs half advanced m ell F g x q)))‖^2+
      (8*reverseNoetherFactor half/3)*(sourcePair (U (completeBalancedInput s hs half advanced m ell F g x q))
        (balancedOwnDefect F (wholeClockState s hs half advanced m ell F g x q))).re-
      2*reverseNoetherFactor half*(sourcePair (completeBalancedInput s hs half advanced m ell F g x q)
        (bulkForceRemainder (wholeClockState s hs half advanced m ell F g x q))).re:=by
  conv_lhs =>
    lhs
    unfold radialInputUpper
    dsimp only
    lhs
    lhs
    lhs
    whnf
    change (_:ℝ)+(_:ℝ)
  unfold coercivePrimitiveUpper
  unfold balancedNativeNoetherPrice
  have hi:correctedCompleteCore s hs x.1 x.2 (wholeSourceMap s hs half advanced m ell F g
      (balancedInputVector m ell F (actualFrequency advanced (sourceNoetherFrequency half) q) _ g))=
      completeBalancedInput s hs half advanced m ell F g x q:=rfl
  simp only [hi]
  ring

/-- The original signed physical upper retains the new positive loss exactly, before any integration or common-tail estimate. -/
theorem actual_whole_force_input_balance(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    coercivePrimitiveUpper s hs half advanced m ell F g x q+
      wholeJointForceInputLoss s hs half advanced m ell F g x q=
      radialInputUpper s hs half advanced m ell F g x q+
        primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))/21:=by
  have h:=(actual_joint_force_input_loss F (reverseNoetherFactor half)
    (completeBalancedInput s hs half advanced m ell F g x q) (wholeClockState s hs half advanced m ell F g x q)).1
  have hg:=upper_gap s hs half advanced m ell F g x q
  dsimp only [wholeJointForceInputLoss]
  linarith only [h,hg]
end LowEnergy.FirstCurrentJointForceLoss
