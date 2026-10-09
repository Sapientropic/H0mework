import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedPressureRadialPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiGaugeScalarSource
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseScalarSourceWork

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualScalarFieldDebitPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy GaussNativeForm
open SourceScalarVirialBulk SourceScalarGaugeScale SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourcePhysicalHamiltonianSquare
open SourceScalarInverseNativeEnergy SourceScalarEssentialBudget SourceScalarShiftedBulk SourceScalarPositiveBulkWard
open SourceClockPhiCombinedScalePressure SourceScalarPairedTransport SourceClockYukawaCubicCurrent SourceNativeCutoffContact
open SourceRetardedGraph ActualVectorJointCost ActualScalarPhaseJet ActualMixedWindowGram ActualMixedCovarianceTail
open ActualBalancedPressureRadialPayment ActualBalancedPressureWardPayment ActualBalancedLocalizationContactReturn ActualBalancedPressureMomentPayment
open ActualBalancedForceRetardedPayment ReverseNativeClock ReverseGaugeOuterPayment SourceQuantumScalarChart
open ActualRawResidualTailPayment ActualTwoResolventCascade ActualPhaseBulkSquare
open SourceScalarInverseBulk SourceJointResidualEnergy SourceResolventBandLimit SourceScalarDoubleCurrent ReverseNativeFrequencyWard SourceClockReflectedForm
open SourceLocalizedInverseFormPayment
open Lean Meta Elab Term MeasureTheory Filter
open scoped InnerProductSpace BigOperators
private abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair diagonalAction compressionCore resolventCore thetaAction
  scalarBulkComplete centeredAction inverseVolumeAction inverseRootAction balancedGenerator
  reverseNativeClock scalarEnergy inverseNativeEnergy shiftedMoment remainingFieldDebit
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator SourceGaugeCoframeJets.K

private theorem lapse_positive:0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem mu_positive:0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large
private theorem source_pair_add_right(f h k:QuantumTest):sourcePair f (h+k)=sourcePair f h+sourcePair f k := by
  simp only [sourcePair,map_add,inner_add_right]
private theorem source_pair_sub_right(f h k:QuantumTest):sourcePair f (h-k)=sourcePair f h-sourcePair f k := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem source_pair_smul_right(c:ℂ)(f h:QuantumTest):sourcePair f (c • h)=c*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_right]
private theorem source_pair_sub_left(f h k:QuantumTest):sourcePair (f-h) k=sourcePair f k-sourcePair h k := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem source_pair_add_left(f h k:QuantumTest):sourcePair (f+h) k=sourcePair f k+sourcePair h k := by
  simp only [sourcePair,map_add,inner_add_left]
private theorem source_pair_smul_left(c:ℂ)(f h:QuantumTest):sourcePair (c • f) h=star c*sourcePair f h := by
  simp only [sourcePair,map_smul,inner_smul_left,starRingEnd_apply]

/-- Both clocks are the same original source combination on the scalar
bulk: the extra gauge generator contributes exactly zero. -/
theorem actual_scalar_balanced_generator:
    balancedGenerator=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator := by
  unfold balancedGenerator reverseNativeClock
  change (3:ℂ) • Phi-(12:ℂ) • Gauge-(6:ℂ) • SourceGaugeCoframeJets.K=
    (3:ℂ) • (Phi-Gauge)-(9*Complex.I:ℂ) • dilation-(9:ℂ) • Gauge
  unfold SourceGaugeCoframeJets.K
  module

def scalarBalancedCurrent(f:QuantumTest):ℝ:=
  (sourcePair f ((balancedGenerator*scalarBulkComplete-scalarBulkComplete*balancedGenerator) f)).re

theorem actual_scalar_balanced_current_source(f:QuantumTest):
    scalarBalancedCurrent f=reverseScalarCurrent f := by
  have hG:Gauge*scalarBulkComplete=scalarBulkComplete*Gauge:=actual_gauge_scalar_commute.eq
  have hop:balancedGenerator*scalarBulkComplete-scalarBulkComplete*balancedGenerator=
      reverseNativeClock*scalarBulkComplete-scalarBulkComplete*reverseNativeClock := by
    rw [actual_scalar_balanced_generator]
    simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,hG]
    module
  change (sourcePair f ((balancedGenerator*scalarBulkComplete-scalarBulkComplete*balancedGenerator) f)).re=
    (sourcePair f ((reverseNativeClock*scalarBulkComplete-scalarBulkComplete*reverseNativeClock) f)).re
  rw [hop]

private theorem centered_root_pair(f:QuantumTest):
    sourcePair f (inverseVolumeAction (centeredAction f))=
      sourcePair (inverseRootAction f) (centeredAction (inverseRootAction f)) := by
  have hc:Commute inverseRootAction centeredAction := by
    unfold centeredAction
    exact inverse_root_real _ _
  have hp(a b:QuantumTest):sourcePair a (inverseRootAction b)=sourcePair (inverseRootAction a) b := by
    unfold inverseRootAction
    exact multiply_pair _ _ _ _
  rw [←inverse_root_square (centeredAction f),hp]
  exact congrArg (sourcePair (inverseRootAction f)) (by simpa only [Module.End.mul_apply] using LinearMap.congr_fun hc.eq f)

/-- The source current pays both distinct field squares. The full native
coefficient is 3 times 4 plus 108, hence exactly 120. -/
theorem actual_scalar_balanced_current_energy(f:QuantumTest):
    scalarBalancedCurrent f=120*sourceTime 0*inverseNativeEnergy f+
      24*sourceTime 0*shiftedMoment f+24*centeredRoot f-
      6*sourceTime 0*‖vacuum‖^2*‖embed f‖^2 := by
  rw [actual_scalar_balanced_current_source]
  have h:=actual_reverse_clock_scalar_form f
  unfold reverseScalarReserve scalarEnergy at h
  simp only [centered_root_pair] at h
  unfold centeredRoot
  linear_combination (norm:=ring) h

/-- Exact field payment releases native credit and preserves the true
vacuum-affine norm; no field energy or current budget is supplied. -/
theorem actual_scalar_field_debit_exchange(sharp:Bool)(f:QuantumTest):
    remainingFieldDebit sharp f=
      (coefficientCost sharp/(128*sourceTime 0*sourceMu))*scalarBalancedCurrent f-
      (15*coefficientCost sharp/(16*sourceMu))*inverseNativeEnergy f+
      (3*coefficientCost sharp*‖vacuum‖^2/(64*sourceMu))*‖embed f‖^2 := by
  rw [actual_scalar_balanced_current_energy]
  unfold remainingFieldDebit
  field_simp [lapse_positive.ne',mu_positive.ne']
  ring

/-- All raw Own and cutoff current forcing are generated on this same
original retarded orbit, rather than inserted as an equation hypothesis. -/
def scalarFieldForcing(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest :=
  let q:=resolventCore F z hz g
  thetaAction m ell g+(diagonalAction*thetaAction m ell-thetaAction m ell*diagonalAction) q+
    thetaAction m ell (defectAction F q)

theorem actual_scalar_field_full_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    diagonalAction (thetaAction m ell (resolventCore F z hz g))=
      scalarFieldForcing m ell F z hz g+z • thetaAction m ell (resolventCore F z hz g) := by
  have hi:=(actual_original_cf_inverses F z hz).1
  have h:=LinearMap.congr_fun hi g
  change compressionCore F (resolventCore F z hz g)-z • resolventCore F z hz g=g at h
  have ht:=congrArg (thetaAction m ell) h
  simp only [map_sub,map_smul] at ht
  unfold scalarFieldForcing defectAction
  simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub]
  linear_combination (norm:=module) ht

/-- The actual source Noether endpoints are generated by the original
clock, source time and complete H0 forcing. -/
theorem actual_scalar_field_noether_endpoints(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let w:=thetaAction m ell (resolventCore F z hz g)
    let f:=scalarFieldForcing m ell F z hz g
    (∀forward:Bool,diagonalAction (reverseSourceEndpoint (sourceTime 0) forward w f).1=
      (reverseSourceEndpoint (sourceTime 0) forward w f).2+z • (reverseSourceEndpoint (sourceTime 0) forward w f).1) ∧
    reverseScalarNoetherWork (sourceTime 0) z w f=scalarBalancedCurrent w := by
  dsimp only
  have h:=actual_reverse_scalar_noether_work (sourceTime 0) lapse_positive z hz
    (thetaAction m ell (resolventCore F z hz g)) (scalarFieldForcing m ell F z hz g)
    (actual_scalar_field_full_source m ell F z hz g)
  rw [←actual_scalar_balanced_current_source] at h
  exact h

/-- Direct same-RF field consumer: the whole debit is paid by actual
source-generated signed Noether work with an exact native credit. -/
theorem actual_scalar_field_noether_payment(sharp:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let w:=thetaAction m ell (resolventCore F z hz g)
    remainingFieldDebit sharp w+(15*coefficientCost sharp/(16*sourceMu))*inverseNativeEnergy w=
      (coefficientCost sharp/(128*sourceTime 0*sourceMu))*reverseScalarNoetherWork (sourceTime 0) z w
        (scalarFieldForcing m ell F z hz g)+
      (3*coefficientCost sharp*‖vacuum‖^2/(64*sourceMu))*‖embed w‖^2 := by
  dsimp only
  rw [(actual_scalar_field_noether_endpoints m ell F z hz g).2]
  have h:=actual_scalar_field_debit_exchange sharp (thetaAction m ell (resolventCore F z hz g))
  linear_combination (norm:=ring) h

/-- CF/theta is the true H0/theta current minus the raw Own current. -/
theorem actual_scalar_field_forcing_raw(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    scalarFieldForcing m ell F z hz g=thetaAction m ell g+
      cutoffLeak m ell F (resolventCore F z hz g)+
      defectAction F (thetaAction m ell (resolventCore F z hz g)) := by
  unfold scalarFieldForcing cutoffLeak defectAction
  dsimp only
  simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub]
  module

/-- The original A input keeps its true affine Phi/theta contact and the
whole raw BF forcing. No theta/scalar-bulk commutation is used. -/
theorem actual_scalar_balanced_retarded_input(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    balancedGenerator (thetaAction m ell q)=thetaAction m ell (resolventCore F z hz (balancedGenerator g))+
      ((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q-
      thetaAction m ell (resolventCore F z hz (ReverseScalarGaugeWard.balancedCompressionForce F q))-
      (18:ℂ) • thetaAction m ell (resolventCore F z hz (compressionCore F q)) := by
  dsimp only
  have hi:=paid_balanced_inverse% balancedGenerator F z hz
  have hb:compressionCore F*balancedGenerator-balancedGenerator*compressionCore F=
      -ReverseScalarGaugeWard.balancedCompressionForce F-(18:ℂ) • compressionCore F := by
    rw [actual_balanced_generator_source]
    module
  rw [hb] at hi
  have htheta:=actual_balanced_cutoff_source m ell
  have h:=congrArg (fun X:End=>X (resolventCore F z hz g)) htheta
  have hR:=congrArg (fun X:End=>thetaAction m ell (X g)) hi
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
    LinearMap.add_apply,LinearMap.neg_apply,map_add,map_sub,map_neg,map_smul] at h hR
  simp only [LinearMap.smul_apply]
  linear_combination (norm:=module) h+hR

private theorem scalar_current_pair(f:QuantumTest):
    scalarBalancedCurrent f= -2*(sourcePair (balancedGenerator f) (scalarBulkComplete f)).re := by
  have hA:sourcePair f (balancedGenerator (scalarBulkComplete f))=
      -sourcePair (balancedGenerator f) (scalarBulkComplete f) := (paid_pressure_ward% generator_skew) f _
  have hB:=original_scalar_pair f (balancedGenerator f)
  have hr:(sourcePair (scalarBulkComplete f) (balancedGenerator f)).re=
      (sourcePair (balancedGenerator f) (scalarBulkComplete f)).re := by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  unfold scalarBalancedCurrent
  simp only [LinearMap.sub_apply,Module.End.mul_apply,source_pair_sub_right,Complex.sub_re]
  rw [hA,hB,hr]
  simp only [Complex.neg_re]
  ring

/-- Fixed A input, actual affine contact, BF and CF mass stay ordered in
one signed source return to the field inventory. -/
theorem actual_scalar_balanced_forcing_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=thetaAction m ell q
    scalarBalancedCurrent w=
      -2*(sourcePair (thetaAction m ell (resolventCore F z hz (balancedGenerator g))) (scalarBulkComplete w)).re-
      2*(sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q) (scalarBulkComplete w)).re+
      2*(sourcePair (thetaAction m ell (resolventCore F z hz (ReverseScalarGaugeWard.balancedCompressionForce F q)))
        (scalarBulkComplete w)).re+
      36*(sourcePair (thetaAction m ell (resolventCore F z hz (compressionCore F q))) (scalarBulkComplete w)).re := by
  dsimp only
  rw [scalar_current_pair,actual_scalar_balanced_retarded_input]
  simp only [source_pair_add_left,source_pair_sub_left,source_pair_smul_left,Complex.add_re,Complex.sub_re,
    Complex.mul_re,star_ofNat,Complex.re_ofNat,Complex.im_ofNat]
  ring

/-- The existing same-RF reserve and force consumer receives the source
field work with its exact fifteen-native credit, rather than a field budget. -/
theorem actual_retarded_scalar_field_gain(sharp:Bool)(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    let q:=resolventCore F z hz g
    let w:=thetaAction m ell q
    (3/4:ℝ)*(2/sourceMu)*sourceReserve sharp m ell q+
      (24*ActualTwoResolventCascade.bulkCoefficient sharp*sourceMu/phaseCoefficient)*‖embed (phaseForce w)‖^2+
      (3*ActualTwoResolventCascade.bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)/12)*
        (sourcePair w (balancedPressureJet ActualSecondPressureMagneticPayment.nonmagneticSecondField w)).re=
      nativePressureGain sharp w+(15*coefficientCost sharp/(16*sourceMu))*inverseNativeEnergy w-
      (3*coefficientCost sharp*‖vacuum‖^2/(64*sourceMu))*‖embed w‖^2-
      (coefficientCost sharp/(128*sourceTime 0*sourceMu))*reverseScalarNoetherWork (sourceTime 0) z w
        (scalarFieldForcing m ell F z hz g) := by
  dsimp only
  have h:=actual_retarded_pressure_three_gain sharp m ell F z hz g
  dsimp only at h
  have hw:=actual_scalar_field_noether_payment sharp m ell F z hz g
  dsimp only at hw
  linear_combination (norm:=ring) h-hw

private theorem nonreal(advanced:Bool)(w:ℝ):(actualFrequency advanced sourceMu w).im≠0 :=
  reverse_frequency_nonreal advanced sourceMu mu_positive w

def scalarFieldNoetherFrequency(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest)(w:ℝ):ℝ :=
  let z:=actualFrequency advanced sourceMu w
  let q:=thetaAction m ell (resolventCore F z (nonreal advanced w) g)
  reverseScalarNoetherWork (sourceTime 0) z q (scalarFieldForcing m ell F z (nonreal advanced w) g)

/-- Frequency is integrated only after the whole actual Noether endpoint
work has returned to the scalar current. Escape is retained in the core R. -/
theorem actual_scalar_field_noether_integrable(advanced:Bool)(m ell:ℕ)(F:Index)(g:QuantumTest):
    Integrable (scalarFieldNoetherFrequency advanced m ell F g) := by
  have hi:=((paid_pressure_single%) advanced F (thetaAction m ell)
    ((balancedGenerator*scalarBulkComplete-scalarBulkComplete*balancedGenerator)*thetaAction m ell) g).re
  apply hi.congr
  apply Eventually.of_forall
  intro w
  unfold scalarFieldNoetherFrequency
  rw [(actual_scalar_field_noether_endpoints m ell F _ _ g).2]
  rfl

elab "paid_scalar_field_source%" field:ident : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseScalarNoetherPayment 0) "LowEnergy") "ReverseNativeClock"
  mkConstWithFreshMVarLevels (Name.str ns field.getId.eraseMacroScopes.toString)

private theorem root_to_inverse(A:End)(hr:Commute inverseRootAction A):A*inverseVolumeAction=inverseVolumeAction*A := by
  apply LinearMap.ext
  intro f
  change A (inverseVolumeAction f)=inverseVolumeAction (A f)
  rw [←SourcePhysicalKineticSquare.inverse_root_square f,←SourcePhysicalKineticSquare.inverse_root_square (A f)]
  have hh(q:QuantumTest):inverseRootAction (A q)=A (inverseRootAction q) := by
    simpa only [Module.End.mul_apply] using LinearMap.congr_fun hr.eq q
  rw [←hh (inverseRootAction f),←hh f]

/-- The original scalar part, including all vacuum-affine terms, is the
same inverse-volume shifted oscillator used by the pressure source. -/
theorem actual_scalar_bulk_shifted_source:
    scalarBulkComplete=(-8:ℂ) • (inverseVolumeAction*scalarKinetic)+
      (8:ℂ) • (inverseVolumeAction*shiftedAction) := by
  have h:scalarBulkComplete=(-8:ℂ) • (inverseVolumeAction*scalarKinetic)+(8:ℂ) • (inverseVolumeAction*centeredAction)-
      (8:ℂ) • (inverseVolumeAction*vacuumLinearAction)+(2:ℂ) • (inverseVolumeAction*vacuumConstantAction):=
    paid_scalar_field_source% scalar_bulk_atoms
  rw [(paid_pressure_ward% shifted_source)]
  simp only [mul_add,mul_sub,mul_smul_comm]
  linear_combination (norm:=module) h

/-- This generated joint field cancels the entire scalar kinetic and
shifted departments. U is never commuted through the phase force. -/
def scalarFreePressureField:End:=ActualSecondPressureMagneticPayment.nonmagneticSecondField+
  ((phaseCoefficient/2:ℝ):ℂ) • scalarBulkComplete

theorem actual_scalar_free_pressure_source:
    scalarFreePressureField=(-12*(phaseCoefficient:ℂ)) • (inverseVolumeAction*gaugeKinetic)-
      (4:ℂ) • (phaseForce*phaseForce)+(phaseCoefficient:ℂ) • (inverseVolumeAction*vacuumConstantAction) := by
  have hK:=root_to_inverse scalarKinetic (paid_pressure_storage% root_scalar)
  have hG:=root_to_inverse gaugeKinetic inverse_root_electric
  have hS:=root_to_inverse shiftedAction (by unfold shiftedAction;exact inverse_root_real _ _)
  have hV:=root_to_inverse vacuumConstantAction (by unfold vacuumConstantAction;exact inverse_root_real _ _)
  unfold scalarFreePressureField ActualSecondPressureMagneticPayment.nonmagneticSecondField
    ActualSecondPressureMagneticPayment.nonmagneticBulk
  rw [actual_scalar_bulk_shifted_source]
  simp only [sub_mul,mul_sub,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,hK,hG,hS,hV,
    smul_add,smul_sub,smul_smul,Complex.ofReal_div,Complex.ofReal_ofNat]
  module

/-- The A-current of the generated field has only the original positive
 gauge and phase-force prices. The affine vacuum cancels in the current. -/
theorem actual_scalar_free_pressure_current(f:QuantumTest):
    (sourcePair f (balancedPressureJet scalarFreePressureField f)).re=
      -432*phaseCoefficient*(sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re-
      120*‖embed (phaseForce f)‖^2 := by
  have hop:balancedPressureJet scalarFreePressureField=
      balancedPressureJet ActualSecondPressureMagneticPayment.nonmagneticSecondField+
      ((phaseCoefficient/2:ℝ):ℂ) • (balancedGenerator*scalarBulkComplete-scalarBulkComplete*balancedGenerator) := by
    unfold scalarFreePressureField balancedPressureJet
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    module
  have h:=congrArg (fun X:End=>(sourcePair f (X f)).re) hop
  simp only [LinearMap.add_apply,LinearMap.smul_apply,source_pair_add_right,source_pair_smul_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  change (sourcePair f (balancedPressureJet scalarFreePressureField f)).re=
    (sourcePair f (balancedPressureJet ActualSecondPressureMagneticPayment.nonmagneticSecondField f)).re+
    (phaseCoefficient/2)*scalarBalancedCurrent f at h
  rw [actual_pressure_source_energy,actual_scalar_balanced_current_energy] at h
  linear_combination (norm:=ring) h

private def scalarBFPair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ:=
  (sourcePair (thetaAction m ell (resolventCore F z hz
    (ReverseScalarGaugeWard.balancedCompressionForce F (resolventCore F z hz g))))
    (scalarBulkComplete (thetaAction m ell (resolventCore F z hz g)))).re

/-- Same original native invoice and radial price, with the generated
scalar-free field on all three pressure legs. No source word is dropped. -/
def scalarFreePressureSource(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  let q:=resolventCore F z hz g
  let w:=thetaAction m ell q
  let u:=ActualBalancedLocalizationContactReturn.compensatedReader m ell F z hz g
  ActualLocalizedNativeWorkReturn.sourceNativeInvoice m ell F z hz g+
    (1/6:ℝ)*((sourcePair (thetaAction m ell (resolventCore F z hz (balancedGenerator g)))
      (scalarFreePressureField w)).re-18*(sourcePair u (compressionCore F q)).re-
      18*((phaseCoefficient/2)*(sourcePair (thetaAction m ell (resolventCore F z hz (compressionCore F q)))
        (scalarBulkComplete w)).re)+
      (sourcePair (((3:ℂ) • SourceScalarAffineCutoffTail.affineCutoff m ell) q) (scalarFreePressureField w)).re+
      (3*phaseCoefficient*sourceTime 0*‖vacuum‖^2/2)*‖embed w‖^2)+
    radialBalancedContact m ell F z hz g

theorem actual_scalar_pressure_joint_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    retardedPressureSource m ell F z hz g-(phaseCoefficient/24)*
      scalarBalancedCurrent (thetaAction m ell (resolventCore F z hz g))=
      scalarFreePressureSource m ell F z hz g-(phaseCoefficient/12)*scalarBFPair m ell F z hz g := by
  have h:=actual_scalar_balanced_forcing_return m ell F z hz g
  dsimp only at h
  unfold retardedPressureSource scalarFreePressureSource scalarFreePressureField scalarBFPair
  dsimp only
  simp only [LinearMap.add_apply,LinearMap.smul_apply,source_pair_add_right,source_pair_smul_right,
    Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [LinearMap.smul_apply] at h ⊢
  linear_combination (norm:=ring) -(phaseCoefficient/24)*h

private def rawScalarCoefficient(sharp:Bool):ℝ:=3*bulkCoefficient sharp*sourceMu/(2*phaseCoefficient)

/-- The original raw normalization fixes the scalar work coefficient. -/
theorem actual_scalar_field_raw_coefficient(sharp:Bool):
    coefficientCost sharp/(128*sourceTime 0*sourceMu)=
      rawScalarCoefficient sharp*(phaseCoefficient/24) := by
  unfold rawScalarCoefficient bulkCoefficient
  change coefficientCost sharp/(128*sourceTime 0*sourceMu)=
    (3*(coefficientCost sharp/(8*sourceTime 0*sourceMu^2))*sourceMu/(2*phaseCoefficient))*(phaseCoefficient/24)
  field_simp [lapse_positive.ne',mu_positive.ne',actual_phase_coefficient_positive.ne']
  ring

/-- The field payment turns the existing three-sixteenths native remainder
into nine-eighths on the same source state, retaining every other source gain. -/
theorem actual_scalar_field_native_credit(sharp:Bool)(f:QuantumTest):
    nativePressureGain sharp f+(15*coefficientCost sharp/(16*sourceMu))*inverseNativeEnergy f-
      (3*coefficientCost sharp*‖vacuum‖^2/(64*sourceMu))*‖embed f‖^2=
      (9*coefficientCost sharp/(8*sourceMu))*inverseNativeEnergy f+
      (27*coefficientCost sharp/(8*sourceTime 0*sourceMu))*
        (sourcePair (inverseRootAction f) (gaugeKinetic (inverseRootAction f))).re+
      (9*coefficientCost sharp/(8*sourceTime 0*sourceMu*phaseCoefficient))*‖embed (phaseForce f)‖^2+
      (9*coefficientCost sharp*‖vacuum‖^2/(16*sourceMu)+9*sourceMu/4)*‖embed f‖^2 := by
  unfold nativePressureGain
  ring


end LowEnergy.ActualScalarFieldDebitPayment
