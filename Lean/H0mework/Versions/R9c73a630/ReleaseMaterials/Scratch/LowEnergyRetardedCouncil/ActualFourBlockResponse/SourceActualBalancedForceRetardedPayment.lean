import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressureMagneticPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSecondPressurePositiveStorage
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiScalarJointAbsorption
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualWholeGammaPressureReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedForceRetardedPayment
open GaussNativeEnergy SourceQuantumScalarChart GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceScalarPositiveBulkWard
open SourceScalarVirialBulk SourceScalarDoubleCurrent SourceScalarGaugeScale SourceHamiltonianScaleJet SourceCoframeVolumeCurrent
open SourceNativeCutoffContact SourceScalarInverseBulk SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard
open ActualWholeGammaPressureReturn SourceScalarNativeComparison ActualSecondPressurePositiveStorage ActualMixedCovarianceTail ActualMixedWindowGram ActualSecondPressureMagneticPayment ActualScalarPhaseFrequencyReturn
open FirstCurrentJointForceLoss FirstCurrentScalarForceAbsorption FirstCurrentClockPrimitiveSquare
open BalancedPrimitivePayer ReverseForcePhysicalPayment SourceClockPhiRadiusSourceCurrent SourceCoframeVolume
open Lean Meta Elab Term
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair compressionCore resolventCore coreWindow nonmagneticSecondField thetaAction diagonalAction

elab "paid_balanced_scale%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullReverseScale 0) "LowEnergy") "ReverseNativeClock"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
elab "paid_balanced_delta%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseNativeClock 0) "LowEnergy") "ReverseNativeClock"
  mkConstWithFreshMVarLevels (Name.str ns "combined_delta")

/-- Every compression derivative belongs to the original raw-F source. -/
theorem actual_balanced_compression_source(F:Index):
    balancedCompressionForce F=(3:ℂ) • deltaPhi (compressionCore F)-
      (12:ℂ) • deltaGauge (compressionCore F)-(6:ℂ) • scaleDerivative (compressionCore F)-
      (18:ℂ) • compressionCore F := by
  have h:=actual_reverse_compression_scale F
  rw [(paid_balanced_scale% Z_scale),paid_balanced_delta%] at h
  unfold balancedCompressionForce gaugeCompressionForce
  change reverseCompressionForce F-(9:ℂ) • (Gauge*compressionCore F-compressionCore F*Gauge)=_
  rw [SourceGaugeScaleTransport.generator_commutator]
  linear_combination (norm:=module) -h

theorem actual_gamma_source(F:Index):
    deltaGauge (compressionCore F)=(1/4:ℂ) • deltaPhi (compressionCore F)-
      (1/2:ℂ) • scaleDerivative (compressionCore F)-(3/2:ℂ) • compressionCore F-
      (1/12:ℂ) • balancedCompressionForce F := by
  rw [actual_balanced_compression_source]
  module

private def fourForm(Q R S T A W:End)(f h:QuantumTest):ℂ :=
  (0:ℂ)-sourcePair (A ((R*Q*R) f)) (A (T h))-
    sourcePair (W f) (A ((R*Q*T) h))-
    sourcePair (W f) (A ((T*Q*R) h))+
    sourcePair (W f) (A ((R*(Q*S-S*Q)*R) h))

private theorem fourForm_sub(Q Q' R S T A W:End)(f h:QuantumTest):
    fourForm (Q-Q') R S T A W f h=fourForm Q R S T A W f h-fourForm Q' R S T A W f h := by
  unfold fourForm
  simp only [sub_mul,mul_sub,Module.End.mul_apply,LinearMap.sub_apply,map_sub,sourcePair,
    inner_sub_left,inner_sub_right]
  ring
private theorem fourForm_real(r:ℝ)(Q R S T A W:End)(f h:QuantumTest):
    fourForm ((r:ℂ) • Q) R S T A W f h=(r:ℂ)*fourForm Q R S T A W f h := by
  have hQS:((r:ℂ) • Q)*S-S*((r:ℂ) • Q)=(r:ℂ) • (Q*S-S*Q) := by
    simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
  unfold fourForm
  rw [hQS]
  simp only [smul_mul_assoc,mul_smul_comm,Module.End.mul_apply,
    LinearMap.smul_apply,map_smul,sourcePair,inner_smul_left,inner_smul_right]
  rw [show starRingEnd ℂ (r:ℂ)=(r:ℂ) from Complex.conj_ofReal r]
  ring

/-- All four orders use one lower field and one actual resolvent. -/
def orderedForcing(Q:End)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):ℂ :=
  let R:=resolventCore F z hz
  let C:=compressionCore F
  let S:=nonmagneticSecondField
  fourForm Q R S (R*(C*S-S*C)*R) (thetaAction m ell) (coreWindow m ell F z hz) f h

theorem actual_whole_gamma_forcing_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (f h:QuantumTest):
    fieldForcing nonmagneticSecondField m ell F z hz f h=
      (1/4:ℂ)*orderedForcing (deltaPhi (compressionCore F)) m ell F z hz f h-
      (1/2:ℂ)*orderedForcing (scaleDerivative (compressionCore F)) m ell F z hz f h-
      (3/2:ℂ)*orderedForcing (compressionCore F) m ell F z hz f h-
      (1/12:ℂ)*orderedForcing (balancedCompressionForce F) m ell F z hz f h := by
  change orderedForcing (deltaGauge (compressionCore F)) m ell F z hz f h=_
  rw [actual_gamma_source]
  unfold orderedForcing
  dsimp only
  simp only [fourForm_sub]
  rw [show (1/4:ℂ)=((1/4:ℝ):ℂ) by norm_num,
    show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,
    show (3/2:ℂ)=((3/2:ℝ):ℂ) by norm_num,
    show (1/12:ℂ)=((1/12:ℝ):ℂ) by norm_num]
  simp only [fourForm_real]

/-- Direct consumer of the complete native-plus-Own insertion after the
magnetic sector has been cancelled inside the source. -/
theorem actual_native_own_balanced_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    ActualNativeOwnSquareWardPayment.nativeOwnFlux m ell F z hz g=
      (4:ℂ)*fieldFlux nonmagneticSecondField m ell F z hz g g+
      fieldFlux nonmagneticSecondField m ell F z hz (Gauge g) g+
      fieldFlux nonmagneticSecondField m ell F z hz g (Gauge g)+
      (1/4:ℂ)*orderedForcing (deltaPhi (compressionCore F)) m ell F z hz g g-
      (1/2:ℂ)*orderedForcing (scaleDerivative (compressionCore F)) m ell F z hz g g-
      (3/2:ℂ)*orderedForcing (compressionCore F) m ell F z hz g g-
      (1/12:ℂ)*orderedForcing (balancedCompressionForce F) m ell F z hz g g := by
  rw [actual_native_own_nonmagnetic_return,actual_whole_gamma_forcing_source]
  ring

elab "paid_balanced_joint%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiJointPrimitiveInputLoss 0) "LowEnergy") "FirstCurrentJointForceLoss"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem inverse_volume_left(k:QuantumTest):
    inverseVolumeAction (volumeAction k)=k := by
  have hc:inverseVolumeAction*volumeAction=volumeAction*inverseVolumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact smul_comm (reciprocalVolume z:ℂ) (GaussNativeEnergy.volume z:ℂ) (f z)
  exact (LinearMap.congr_fun hc k).trans (volume_inverse k)

/-- The reader is converted to the actual inverse-volume input inside the
source pairing, before any resolvent norm estimate is used. -/
theorem actual_balanced_reader_joint_square(F:Index)(k w:QuantumTest):
    (1/6:ℝ)*(sourcePair k (balancedCompressionForce F w)).re+
      primitiveEnergy (balancedCompressionForce F w)/21+
      (7*sourceTime 0/96)*‖embed (phiInverseAction k)‖^2=
      jointForceInputLoss F (1/16) (volumeAction k) w := by
  have he:=(paid_balanced_joint% force_square) (1/16:ℝ)
    (phiInverseAction k) (phiRadiusAction (balancedCompressionForce F w))
  rw [(paid_balanced_joint% radius_inverse_pair)] at he
  have hp:=(actual_positive_primitive_energy (balancedCompressionForce F w)).1
  unfold jointForceInputLoss
  rw [inverse_volume_left,hp]
  linear_combination (norm:=ring_nf) -he

/-- The primitive force square is paid from the actual coherent native and
projection current, leaving its original scalar and vacuum positive slots. -/
theorem actual_balanced_reader_native_payment(F:Index)(k w:QuantumTest):
    (1/6:ℝ)*(sourcePair k (balancedCompressionForce F w)).re ≥
      retainedNativePrice w-clearedNativePrice w-compensatedPrimitiveWork F w+
      (150*sourceTime 0/7)*(sourcePair w (balancedScalarSquare w)).re+
      (144*sourceTime 0/175)*‖vacuum‖^2*‖embed w‖^2-
      (7*sourceTime 0/96)*‖embed (phiInverseAction k)‖^2 := by
  have hs:=actual_balanced_reader_joint_square F k w
  have hn:=(actual_joint_force_input_loss F (1/16) (volumeAction k) w).2
  have hb:=(actual_native_primitive_joint_balance F w).1
  unfold primitiveNativeLoss at hb
  linarith only [hs,hn,hb]

private theorem pair_add_left(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem pair_add_right(f g h:QuantumTest):sourcePair f (g+h)=sourcePair f g+sourcePair f h := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem pair_real_left(a:ℝ)(f h:QuantumTest):
    sourcePair ((a:ℂ) • f) h=(a:ℂ)*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_left]
  rw [show starRingEnd ℂ (a:ℂ)=(a:ℂ) from Complex.conj_ofReal a]
private theorem pair_real_right(a:ℝ)(f h:QuantumTest):
    sourcePair f ((a:ℂ) • h)=(a:ℂ)*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem theta_pair(m ell:ℕ)(f h:QuantumTest):
    sourcePair f (thetaAction m ell h)=sourcePair (thetaAction m ell f) h := by
  unfold thetaAction
  exact GaussNativeForm.multiply_pair _ _ _ _

private theorem magnetic_pair(f h:QuantumTest):
    sourcePair f (magneticSecondField h)=sourcePair (magneticSecondField f) h := by
  have hm(a b:QuantumTest):sourcePair a (SourceScalarVirialBulk.magneticAction b)=
      sourcePair (SourceScalarVirialBulk.magneticAction a) b := by
    unfold SourceScalarVirialBulk.magneticAction
    exact GaussNativeForm.multiply_pair _ _ _ _
  have hu(a b:QuantumTest):sourcePair a (inverseVolumeAction b)=sourcePair (inverseVolumeAction a) b := by
    unfold inverseVolumeAction
    exact GaussNativeForm.multiply_pair _ _ _ _
  unfold magneticSecondField
  simp only [LinearMap.smul_apply,LinearMap.add_apply,Module.End.mul_apply]
  have hc:(-(12:ℂ)*(ActualScalarPhaseJet.phaseCoefficient:ℂ))=
      ((-12*ActualScalarPhaseJet.phaseCoefficient:ℝ):ℂ):=by push_cast;rfl
  rw [hc,pair_real_right,pair_real_left,pair_add_left,pair_add_right,hm,hu,hu,hm]
  ring

theorem actual_nonmagnetic_source_pair(f h:QuantumTest):
    sourcePair f (nonmagneticSecondField h)=sourcePair (nonmagneticSecondField f) h := by
  have hp:=actual_second_source_pair f h
  rw [actual_native_phase_second_pressure_split] at hp
  simp only [LinearMap.add_apply,pair_add_left,pair_add_right] at hp
  rw [magnetic_pair] at hp
  exact add_left_cancel hp

elab "paid_balanced_covariance%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCovarianceCore 0) "LowEnergy") "ActualMixedCovarianceTail"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)
private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- Both ordered theta/source-field legs are retained in the actual reader. -/
def pressureReader(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest :=
  let q:=resolventCore F z hz g
  resolventCore F (star z) (star_nonreal z hz)
    ((1/2:ℂ) • (thetaAction m ell (thetaAction m ell (nonmagneticSecondField q))+
      nonmagneticSecondField (thetaAction m ell (thetaAction m ell q))))

def balancedPressure(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  let q:=resolventCore F z hz g
  let v:=resolventCore F z hz (balancedCompressionForce F q)
  (1/12:ℝ)*((sourcePair (thetaAction m ell v)
      (thetaAction m ell (nonmagneticSecondField q))).re+
    (sourcePair (thetaAction m ell q)
      (thetaAction m ell (nonmagneticSecondField v))).re)

theorem actual_balanced_pressure_reader(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    balancedPressure m ell F z hz g=
      (1/6:ℝ)*(sourcePair (pressureReader m ell F z hz g)
        (balancedCompressionForce F (resolventCore F z hz g))).re := by
  let q:=resolventCore F z hz g
  let v:=resolventCore F z hz (balancedCompressionForce F q)
  have h1:sourcePair (thetaAction m ell v) (thetaAction m ell (nonmagneticSecondField q))=
      sourcePair (balancedCompressionForce F q)
        (resolventCore F (star z) (star_nonreal z hz)
          (thetaAction m ell (thetaAction m ell (nonmagneticSecondField q)))) := by
    rw [←theta_pair]
    exact ((paid_balanced_covariance% resolvent_pair) F z hz _ _).symm
  have h2:sourcePair (thetaAction m ell q) (thetaAction m ell (nonmagneticSecondField v))=
      sourcePair (resolventCore F (star z) (star_nonreal z hz)
        (nonmagneticSecondField (thetaAction m ell (thetaAction m ell q))))
        (balancedCompressionForce F q) := by
    rw [theta_pair,actual_nonmagnetic_source_pair]
    simpa only [star_star] using
      (paid_balanced_covariance% resolvent_pair) F (star z) (star_nonreal z hz) _ _
  unfold balancedPressure pressureReader
  dsimp only
  change (1/12:ℝ)*((sourcePair (thetaAction m ell v)
    (thetaAction m ell (nonmagneticSecondField q))).re+
    (sourcePair (thetaAction m ell q) (thetaAction m ell (nonmagneticSecondField v))).re)=_
  rw [h1,h2]
  have hr(a b:QuantumTest):(sourcePair a b).re=(sourcePair b a).re := by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  rw [hr (balancedCompressionForce F q)]
  simp only [map_add,map_smul]
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num,pair_real_left,pair_add_left]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

/-- The actual BF pressure slot is paid by one source joint square; the
primitive force norm is returned to its coherent native/Own source current. -/
theorem actual_balanced_pressure_native_payment(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    let q:=resolventCore F z hz g
    balancedPressure m ell F z hz g ≥
      retainedNativePrice q-clearedNativePrice q-compensatedPrimitiveWork F q+
      (150*sourceTime 0/7)*(sourcePair q (balancedScalarSquare q)).re+
      (144*sourceTime 0/175)*‖vacuum‖^2*‖embed q‖^2-
      (7*sourceTime 0/96)*‖embed (phiInverseAction (pressureReader m ell F z hz g))‖^2 := by
  dsimp only
  rw [actual_balanced_pressure_reader]
  exact actual_balanced_reader_native_payment F _ _

def localizedPressureReader(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest :=
  resolventCore F (star z) (star_nonreal z hz)
    (nonmagneticSecondField (thetaAction m ell (resolventCore F z hz g)))

def pressureReaderCorrection(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest :=
  let Rbar:=resolventCore F (star z) (star_nonreal z hz)
  let A:=thetaAction m ell
  let C:=compressionCore F
  let S:=nonmagneticSecondField
  (0:QuantumTest)-Rbar ((C*A-A*C) (localizedPressureReader m ell F z hz g))+
    (1/2:ℂ) • Rbar ((A*(A*S-S*A)-(A*S-S*A)*A) (resolventCore F z hz g))

elab "paid_balanced_inverse%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualShiftedQuadraticWardPayment 0) "LowEnergy") "ActualShiftedQuadraticWardPayment"
  mkConstWithFreshMVarLevels (Name.str ns "inverse_input")

/-- Both actual CF leakage and the mixed radial double commutator are kept;
no single-leg IMS or theta/field commutation is assumed. -/
theorem actual_pressure_reader_localization(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    pressureReader m ell F z hz g=
      thetaAction m ell (localizedPressureReader m ell F z hz g)+
        pressureReaderCorrection m ell F z hz g := by
  let A:=thetaAction m ell
  let C:=compressionCore F
  let S:=nonmagneticSecondField
  let Rb:=resolventCore F (star z) (star_nonreal z hz)
  have hR:A*Rb=Rb*A+Rb*(C*A-A*C)*Rb :=
    paid_balanced_inverse% A F (star z) (star_nonreal z hz)
  have hJ:(1/2:ℂ) • (A*A*S+S*A*A)=
      A*S*A+(1/2:ℂ) • (A*(A*S-S*A)-(A*S-S*A)*A) := by
    simp only [mul_sub,sub_mul,smul_sub,smul_add]
    module
  have he:Rb*((1/2:ℂ) • (A*A*S+S*A*A))=
      A*Rb*S*A-Rb*(C*A-A*C)*Rb*S*A+
        (1/2:ℂ) • (Rb*(A*(A*S-S*A)-(A*S-S*A)*A)) := by
    rw [hJ,mul_add,mul_smul_comm]
    have h:=congrArg (fun E:End=>E*S*A) hR
    linear_combination (norm:=noncomm_ring) -h
  have hg:=LinearMap.congr_fun he (resolventCore F z hz g)
  unfold pressureReader pressureReaderCorrection localizedPressureReader
  simpa only [A,C,S,Rb,Module.End.mul_apply,LinearMap.add_apply,LinearMap.sub_apply,
    LinearMap.smul_apply,LinearMap.neg_apply,map_add,map_smul,map_neg,zero_add,zero_sub,sub_eq_add_neg,add_assoc] using hg

def balancedLocalizationContact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  let q:=resolventCore F z hz g
  let k:=localizedPressureReader m ell F z hz g
  (1/6:ℝ)*((sourcePair (pressureReaderCorrection m ell F z hz g)
      (balancedCompressionForce F q)).re-
    (sourcePair k ((balancedCompressionForce F*thetaAction m ell-
      thetaAction m ell*balancedCompressionForce F) q)).re)

/-- The source BF is moved to the same actual theta-RF input, and its complete
commutator with theta stays in the coherent contact. -/
theorem actual_balanced_pressure_localized_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    balancedPressure m ell F z hz g=
      (1/6:ℝ)*(sourcePair (localizedPressureReader m ell F z hz g)
        (balancedCompressionForce F (thetaAction m ell (resolventCore F z hz g)))).re+
      balancedLocalizationContact m ell F z hz g := by
  rw [actual_balanced_pressure_reader,actual_pressure_reader_localization,pair_add_left]
  rw [←theta_pair]
  have he:thetaAction m ell (balancedCompressionForce F (resolventCore F z hz g))=
      balancedCompressionForce F (thetaAction m ell (resolventCore F z hz g))-
      ((balancedCompressionForce F*thetaAction m ell-thetaAction m ell*balancedCompressionForce F)
        (resolventCore F z hz g)) := by
    simp only [Module.End.mul_apply,LinearMap.sub_apply]
    abel
  rw [he,(paid_phase_frequency% pair_sub_right)]
  unfold balancedLocalizationContact
  dsimp only
  simp only [Complex.add_re,Complex.sub_re]
  ring

/-- The actual same-window pressure receives the positive joint primitive
payment. The complete localization/Own contact remains a signed source term. -/
theorem actual_localized_balanced_pressure_payment(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    let w:=thetaAction m ell (resolventCore F z hz g)
    balancedPressure m ell F z hz g ≥
      retainedNativePrice w-clearedNativePrice w-compensatedPrimitiveWork F w+
      (150*sourceTime 0/7)*(sourcePair w (balancedScalarSquare w)).re+
      (144*sourceTime 0/175)*‖vacuum‖^2*‖embed w‖^2-
      (7*sourceTime 0/96)*‖embed (phiInverseAction (localizedPressureReader m ell F z hz g))‖^2+
      balancedLocalizationContact m ell F z hz g := by
  dsimp only
  rw [actual_balanced_pressure_localized_return]
  exact add_le_add (actual_balanced_reader_native_payment F _ _) (le_refl _)

/-- The actual source Hardy mechanism pays the reader input with a strict
one-in-256 native coefficient on that same generated retarded reader. -/
theorem actual_localized_balanced_pressure_small_gain(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)
    (g:QuantumTest):
    let w:=thetaAction m ell (resolventCore F z hz g)
    balancedPressure m ell F z hz g ≥
      retainedNativePrice w-clearedNativePrice w-compensatedPrimitiveWork F w+
      (150*sourceTime 0/7)*(sourcePair w (balancedScalarSquare w)).re+
      (144*sourceTime 0/175)*‖vacuum‖^2*‖embed w‖^2-
      (sourceTime 0/256)*nativeScalarEnergy (localizedPressureReader m ell F z hz g)+
      balancedLocalizationContact m ell F z hz g := by
  dsimp only
  have hp:=actual_localized_balanced_pressure_payment m ell F z hz g
  dsimp only at hp
  have hi:=actual_inverse_radius_reader_price (localizedPressureReader m ell F z hz g)
  linarith only [hp,hi]

end LowEnergy.ActualBalancedForceRetardedPayment
