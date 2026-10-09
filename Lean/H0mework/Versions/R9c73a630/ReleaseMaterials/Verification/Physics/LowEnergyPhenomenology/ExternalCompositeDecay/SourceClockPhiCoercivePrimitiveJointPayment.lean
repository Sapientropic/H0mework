import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPrimitiveDefectPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedNativeScalarCompletion
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPhysicalForcePayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.BalancedPrimitivePayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore SourceQuantumConfigurationHilbert SourceQuantumScalarChart
open SourceClockYukawaCubicCurrent SourceClockPhiCombinedScalePressure SourcePhysicalKineticSquare SourceClockReflectedForm
open SourceScalarDoubleCurrent SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarVirialBulk SourceScalarInverseNativeEnergy
open SourceClockPhiNormalizedScalarBudget SourceLocalizedInverseFormPayment SourceResolventBandLimit
open SourceClockPhiNativeJointPayment SourceInverseNoetherChannelGap SourceScalarPairedTransport SourceClockPhiNativeMatchedSource
open FirstCurrentAdmissibleElectric FirstCurrentElectricSuccessor FirstCurrentWholeCarrier FirstCurrentJointBudget FirstCurrentGeometricPayer
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare OriginalRCommutatorSource FirstCurrentDilationPrimitive
open ReverseNativeClock ReverseNativeFrequencyWard ReverseForceNoetherPayer ReverseForcePhysicalPayment ReverseScalarGaugeWard ReverseBalancedForcePayer
open ScalarBalancedPrimitive ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev P:End:=positivePrimitive
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] sourcePair embed diagonalAction resolventCore balancedCompressionForce
  wholeClockState wholeSourceNext correctedCompleteCore clockSourcePair positivePrimitive originalNormalizerPrice
  nativeDilationWord scalarKinetic gaugeKinetic centeredAction vacuumLinearAction magneticAction scalarSpatialAction
private theorem pair_add_r(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h:=by simp only [sourcePair,map_add,inner_add_right]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_smul_r(c:ℂ)(f g:QuantumTest):sourcePair f (c • g)=c*sourcePair f g:=by simp only [sourcePair,map_smul,inner_smul_right]
private theorem n_pos:0<n:=by
  rw [show n=sourceTime 0 from rfl,source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

def clearedNativePrice(w:QuantumTest):ℝ:=
  (30/7:ℝ)*(sourcePair w (U (scalarKinetic w))).re-6*(sourcePair w (U (gaugeKinetic w))).re+
    3*(sourcePair w (U (matterAction w))).re+4*(sourcePair w (U (magneticAction w))).re+
    12*n*spinForm (U w)+12*n*densityForm (U w)-13*n*inverseNativeEnergy w+
    (35*n/96)*‖embed (U (D w))‖^2-2*gaugeForm (U w)-72*n*‖embed w‖^2

def compensatedPrimitiveWork(F:Index)(w:QuantumTest):ℝ:=
  (sourcePair (balancedCompressionForce F (balancedCompressionForce F w)) (P w)).re/21-
    (sourcePair w (balancedPrimitiveProjection F w)).re/42

def primitiveNativeLoss(F:Index)(w:QuantumTest):ℝ:=
  primitiveEnergy (balancedCompressionForce F w)/21+
    (150*n/7)*(sourcePair w (balancedScalarSquare w)).re+
      (144*n/175)*‖vacuum‖^2*‖embed w‖^2

/-- The full-CF primitive acceleration and original scalar radius jointly delete the signed spatial, centered and vacuum prices. Their debit is an actual positive primitive force square and the actual shifted scalar square. -/
theorem actual_native_primitive_joint_balance(F:Index)(w:QuantumTest):
    retainedNativePrice w+primitiveNativeLoss F w=clearedNativePrice w+compensatedPrimitiveWork F w ∧
      0 ≤ primitiveNativeLoss F w:=by
  have hsp:=actual_balanced_scalar_spatial_payment F w
  have hsc:=(actual_balanced_scalar_potential_payment w).1
  have hd:sourcePair w (U (nativeDilationWord w))=
      (-2:ℂ)*sourcePair w (U (scalarKinetic w))+(2:ℂ)*sourcePair w (U (gaugeKinetic w))+
        (2:ℂ)*sourcePair w (U (centeredAction w))-(2:ℂ)*sourcePair w (U (vacuumLinearAction w))-
        (4:ℂ)*sourcePair w (U (magneticAction w))-sourcePair w (U (matterAction w)):=by
    simp only [nativeDilationWord,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
      map_add,map_sub,map_smul,pair_add_r,pair_sub_r,pair_smul_r]
  constructor
  · unfold retainedNativePrice primitiveNativeLoss clearedNativePrice compensatedPrimitiveWork
    rw [hd]
    simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im,
      Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
    linarith only [hsp,hsc]
  · unfold primitiveNativeLoss
    have hp:0 ≤ primitiveEnergy (balancedCompressionForce F w):=(actual_positive_primitive_energy _).2
    have hs:=actual_balanced_scalar_square_nonnegative w
    have hn:=n_pos
    positivity

def completeForceEscape(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):QuantumTest:=
  -balancedWholeForceOuter s hs half advanced m ell F g x q+balancedWholeForceEscape s hs half advanced m ell F g x q

/-- The primitive square is the actual force-response forcing minus its full outer escape. The two original poles return the same residual. -/
theorem actual_complete_force_two_pole_residual(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let v:=balancedWholeForceState s hs half advanced m ell F g x q
    let p:=balancedWholeForceSource s hs half advanced m ell F g x q
    let e:=completeForceEscape s hs half advanced m ell F g x q
    p-e=balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q) ∧
      oppositeForcing z v p-(e+(2*(z.im:ℂ)*Complex.I) • v)=
        balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q):=by
  dsimp only
  constructor
  · simp only [balancedWholeForceSource,completeForceEscape]
    module
  · simp only [balancedWholeForceSource,completeForceEscape,oppositeForcing]
    module

def coercivePrimitiveUpper(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):ℝ:=
  reverseNoetherFactor half*(balancedNativeNoetherPrice s hs half advanced m ell F g x q-
    reverseScalarReserve (wholeClockState s hs half advanced m ell F g x q))+
    reverseNoetherNormCost half*‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2+
      clearedNativePrice (wholeClockState s hs half advanced m ell F g x q)+
      compensatedPrimitiveWork F (wholeClockState s hs half advanced m ell F g x q)+
      originalNormalizerPrice s hs x (wholeSourceNext s hs half advanced m ell F g q)
private theorem joint_upper_return(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ)(q:ℝ):
    balancedPhysicalForceUpper s hs half advanced m ell F g x q+
      primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q)=
        coercivePrimitiveUpper s hs half advanced m ell F g x q:=by
  have h:=(actual_native_primitive_joint_balance F (wholeClockState s hs half advanced m ell F g x q)).1
  unfold balancedPhysicalForceUpper wholeRetainedPhysicalPrice coercivePrimitiveUpper
  linarith only [h]
private theorem loss_integrable(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q)):=by
  have hP(L R:End):Integrable (fun q:ℝ=>sourcePair (L (wholeClockState s hs half advanced m ell F g x q))
      (R (wholeClockState s hs half advanced m ell F g x q))):=actual_whole_state_pair_integrable s hs half advanced m ell F g x L R
  have hf:Integrable (fun q:ℝ=>primitiveEnergy (balancedCompressionForce F (wholeClockState s hs half advanced m ell F g x q))):=by
    simpa only [primitiveEnergy,Module.End.mul_apply,RCLike.re_eq_complex_re] using
      (hP (balancedCompressionForce F) (P*balancedCompressionForce F)).re
  have hs0:Integrable (fun q:ℝ=>(sourcePair (wholeClockState s hs half advanced m ell F g x q)
      (balancedScalarSquare (wholeClockState s hs half advanced m ell F g x q))).re):=by
    simpa only [Module.End.one_apply,RCLike.re_eq_complex_re] using (hP 1 balancedScalarSquare).re
  have hn:Integrable (fun q:ℝ=>‖embed (wholeClockState s hs half advanced m ell F g x q)‖^2):=by
    simpa only [Module.End.one_apply] using actual_whole_state_square_integrable s hs half advanced m ell F g x 1
  exact ((hf.div_const 21).add (hs0.const_mul (150*n/7))).add (hn.const_mul ((144*n/175)*‖vacuum‖^2))

/-- The original starting physical action receives both generated positive losses. The upper retains the full own-CF projection, signed native current, complete forcing and negative M completion; no force or scalar budget is supplied. -/
theorem actual_coercive_primitive_joint_payment(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(x:ℝ×ℝ):
    Integrable (fun q:ℝ=>physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q))) ∧
    Integrable (fun q:ℝ=>primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q)) ∧
    Integrable (coercivePrimitiveUpper s hs half advanced m ell F g x) ∧
    0 ≤ (∫q:ℝ,primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q)) ∧
    (∫q:ℝ,physicalJointPrice half advanced (actualFrequency advanced (sourceNoetherFrequency half) q)
      (clockSourcePair s hs x (wholeSourceNext s hs half advanced m ell F g q)))+
      (∫q:ℝ,primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q)) ≤
        ∫q:ℝ,coercivePrimitiveUpper s hs half advanced m ell F g x q:=by
  have hJ:=actual_balanced_whole_physical_payment s hs half advanced m ell F g x
  have hL:=loss_integrable s hs half advanced m ell F g x
  have hU:Integrable (coercivePrimitiveUpper s hs half advanced m ell F g x):=
    (hJ.2.1.add hL).congr (Eventually.of_forall (joint_upper_return s hs half advanced m ell F g x))
  refine ⟨hJ.1,hL,hU,integral_nonneg (fun q=>(actual_native_primitive_joint_balance F _).2),?_⟩
  have he:(∫q:ℝ,coercivePrimitiveUpper s hs half advanced m ell F g x q)=
      (∫q:ℝ,balancedPhysicalForceUpper s hs half advanced m ell F g x q)+
        (∫q:ℝ,primitiveNativeLoss F (wholeClockState s hs half advanced m ell F g x q)):=by
    simp_rw [←joint_upper_return]
    exact integral_add hJ.2.1 hL
  rw [he]
  linarith only [hJ.2.2]
end LowEnergy.BalancedPrimitivePayer
