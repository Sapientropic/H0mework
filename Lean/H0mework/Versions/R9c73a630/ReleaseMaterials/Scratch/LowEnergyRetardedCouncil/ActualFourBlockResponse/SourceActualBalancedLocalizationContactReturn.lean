import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualBalancedForceRetardedPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualNonmagneticRadialCrossPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCoframeTailPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualBalancedLocalizationContactReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open GaussNativeForm GaussNativeEnergy SourceScalarPairedTransport SourceClockYukawaCubicCurrent
open SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale SourceHamiltonianScaleJet
open SourceNativeCutoffContact SourceCoframeVolumeCurrent SourceInverseFullResponse
open ActualBalancedForceRetardedPayment ActualNonmagneticRadialCrossPayment
open ActualSecondPressureMagneticPayment ActualNonmagneticPressureStorage
open ActualScalarPhaseFrequencyReturn ActualShiftedQuadraticWardPayment ActualMixedWindowGram
open ActualUnweightedSquareCurrentPayment ActualMixedCovarianceTail ReverseScalarGaugeWard
open SourceScalarAffineCutoffTail
open Lean Meta Elab Term
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair compressionCore resolventCore thetaAction diagonalAction
  nonmagneticSecondField balancedCompressionForce localizedPressureReader pressureReaderCorrection

elab "paid_localization_coframe%" : term => do
  let ns:=Name.str (Name.str (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualMixedCoframeTailPayment 0) "LowEnergy") "ActualMixedCoframeTailPayment"
  mkConstWithFreshMVarLevels (Name.str ns "actual_coframe_theta_zero")

/-- The generator is fixed by the original BF source polynomial. -/
def balancedGenerator:End:=(3:ℂ) • Phi-(12:ℂ) • Gauge-(6:ℂ) • Coframe
/-- The true raw-CF leakage keeps both the Hamiltonian and Own parts. -/
def cutoffLeak(m ell:ℕ)(F:Index):End:=compressionCore F*thetaAction m ell-thetaAction m ell*compressionCore F

theorem actual_cutoff_leak_source(m ell:ℕ)(F:Index):
    cutoffLeak m ell F=(diagonalAction*thetaAction m ell-thetaAction m ell*diagonalAction)-
      (defectAction F*thetaAction m ell-thetaAction m ell*defectAction F) := by
  unfold cutoffLeak defectAction
  noncomm_ring

theorem actual_balanced_generator_source(F:Index):
    balancedCompressionForce F=balancedGenerator*compressionCore F-compressionCore F*balancedGenerator-
      (18:ℂ) • compressionCore F := by
  rw [actual_balanced_compression_source]
  rw [←SourceScalarAffineScaleTransport.generator_commutator,←SourceGaugeScaleTransport.generator_commutator,
    ←SourceGaugeCoframeJets.K_commutator]
  unfold balancedGenerator
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  module

theorem actual_balanced_cutoff_source(m ell:ℕ):
    balancedGenerator*thetaAction m ell-thetaAction m ell*balancedGenerator=(3:ℂ) • affineCutoff m ell := by
  have hp:Phi*thetaAction m ell-thetaAction m ell*Phi=affineCutoff m ell := by
    rw [SourceScalarAffineScaleTransport.generator_commutator]
    rfl
  have hg:Gauge*thetaAction m ell-thetaAction m ell*Gauge=0 := by
    rw [SourceGaugeScaleTransport.generator_commutator]
    exact ActualAffineCutoffCausalTail.actual_gauge_cutoff_zero m ell
  have hc:Coframe*thetaAction m ell-thetaAction m ell*Coframe=0 := by
    rw [SourceGaugeCoframeJets.K_commutator]
    exact paid_localization_coframe% m ell
  unfold balancedGenerator
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  linear_combination (norm:=module) (3:ℂ) • hp-(12:ℂ) • hg-(6:ℂ) • hc

/-- All source jets differentiate the same CF/theta commutator. Only the
actual affine Phi contact remains; neither Own nor a leakage leg is removed. -/
theorem actual_balanced_cutoff_jet(m ell:ℕ)(F:Index):
    balancedCompressionForce F*thetaAction m ell-thetaAction m ell*balancedCompressionForce F=
      balancedGenerator*cutoffLeak m ell F-cutoffLeak m ell F*balancedGenerator-
      (3:ℂ) • (compressionCore F*affineCutoff m ell-affineCutoff m ell*compressionCore F)-
      (18:ℂ) • cutoffLeak m ell F := by
  have hV:=actual_balanced_cutoff_source m ell
  rw [actual_balanced_generator_source]
  have hJ:((balancedGenerator*compressionCore F-compressionCore F*balancedGenerator)*thetaAction m ell-
      thetaAction m ell*(balancedGenerator*compressionCore F-compressionCore F*balancedGenerator))=
      balancedGenerator*cutoffLeak m ell F-cutoffLeak m ell F*balancedGenerator-
      (compressionCore F*(balancedGenerator*thetaAction m ell-thetaAction m ell*balancedGenerator)-
        (balancedGenerator*thetaAction m ell-thetaAction m ell*balancedGenerator)*compressionCore F) := by
    unfold cutoffLeak
    noncomm_ring
  rw [hV] at hJ
  simp only [mul_smul_comm,smul_mul_assoc] at hJ
  unfold cutoffLeak at hJ ⊢
  simp only [sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  linear_combination (norm:=(noncomm_ring;module)) hJ

private theorem star_nonreal(z:ℂ)(hz:z.im≠0):(star z).im≠0 := by
  simpa only [Complex.star_def,Complex.conj_im,neg_ne_zero] using hz

/-- The two ordered leakage legs share this actual opposite-cause reader. -/
def compensatedReader(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):QuantumTest :=
  resolventCore F (star z) (star_nonreal z hz)
    (thetaAction m ell (nonmagneticSecondField (thetaAction m ell (resolventCore F z hz g))))

theorem actual_compensated_reader_source(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    compensatedReader m ell F z hz g=thetaAction m ell (localizedPressureReader m ell F z hz g)-
      resolventCore F (star z) (star_nonreal z hz)
        (cutoffLeak m ell F (localizedPressureReader m ell F z hz g)) := by
  have h:=paid_balanced_inverse% (thetaAction m ell) F (star z) (star_nonreal z hz)
  have he:=LinearMap.congr_fun h (nonmagneticSecondField (thetaAction m ell (resolventCore F z hz g)))
  unfold compensatedReader localizedPressureReader cutoffLeak
  simp only [Module.End.mul_apply,LinearMap.add_apply] at he
  linear_combination (norm:=module) -he

/-- The same genuine mixed radial correction which has a source Gram price. -/
def radialBalancedContact(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℝ :=
  (1/12:ℝ)*(sourcePair (resolventCore F z hz (balancedCompressionForce F (resolventCore F z hz g)))
    (radialDouble m ell nonmagneticSecondField (resolventCore F z hz g))).re

/-- The leakage responsibility is the joint BF source difference, with the
same q, theta-q and their two original readers. -/
def jointBalancedNoether(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  sourcePair (compensatedReader m ell F z hz g) (balancedCompressionForce F (resolventCore F z hz g))-
    sourcePair (localizedPressureReader m ell F z hz g)
      (balancedCompressionForce F (thetaAction m ell (resolventCore F z hz g)))

/-- Both CF/reader and BF/window leakages are returned before taking the
signed frequency price. The paid mixed radial source is kept in the same equation. -/
theorem actual_balanced_localization_joint_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    balancedLocalizationContact m ell F z hz g=
      (1/6:ℝ)*(jointBalancedNoether m ell F z hz g).re+radialBalancedContact m ell F z hz g := by
  have hc:=actual_compensated_reader_source m ell F z hz g
  have hp:=actual_pressure_reader_localization m ell F z hz g
  have hJ:pressureReader m ell F z hz g=compensatedReader m ell F z hz g+
      (1/2:ℂ) • resolventCore F (star z) (star_nonreal z hz)
        (radialDouble m ell nonmagneticSecondField (resolventCore F z hz g)) := by
    rw [hp,hc]
    unfold pressureReaderCorrection radialDouble cutoffLeak
    module
  have hr(q v:QuantumTest):(sourcePair q v).re=(sourcePair v q).re := by
    unfold sourcePair
    exact inner_re_symm (𝕜:=ℂ) _ _
  have hR(q v:QuantumTest):sourcePair (resolventCore F (star z) (star_nonreal z hz) q) v=
      sourcePair q (resolventCore F z hz v) := by
    simpa only [star_star] using
      ((paid_balanced_covariance% resolvent_pair) F (star z) (star_nonreal z hz) q v).symm
  have hb:=actual_balanced_pressure_reader m ell F z hz g
  rw [hJ] at hb
  have ha:=actual_balanced_pressure_localized_return m ell F z hz g
  have padd(f h v:QuantumTest):sourcePair (f+h) v=sourcePair f v+sourcePair h v := by
    simp only [sourcePair,map_add,inner_add_left]
  have phalf(f h:QuantumTest):sourcePair ((1/2:ℂ) • f) h=(1/2:ℂ)*sourcePair f h := by
    simp only [sourcePair,map_smul,inner_smul_left,map_div₀,map_one,map_ofNat]
  rw [padd,phalf,hR] at hb
  rw [show (1/2:ℂ)=((1/2:ℝ):ℂ) by norm_num] at hb
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hb
  rw [hr (radialDouble m ell nonmagneticSecondField (resolventCore F z hz g))] at hb
  unfold jointBalancedNoether radialBalancedContact
  simp only [Complex.sub_re]
  linear_combination hb-ha


private theorem generator_skew(f h:QuantumTest):
    sourcePair f (balancedGenerator h)= -sourcePair (balancedGenerator f) h := by
  have hp:=(paid_shifted_response% phi_pair) f h
  have hg:=(paid_shifted_response% gauge_pair) f h
  have hc:=(paid_shifted_response% coframe_pair) f h
  unfold balancedGenerator
  simp only [LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,starRingEnd_apply,star_ofNat] at hp hg hc ⊢
  rw [hp,hg,hc]
  ring

private theorem balanced_noether_pair(F:Index)(z:ℂ)(u v:QuantumTest):
    sourcePair u (balancedCompressionForce F v)=
      -sourcePair (balancedGenerator u) (compressionCore F v-z • v)-
      sourcePair (compressionCore F u-star z • u) (balancedGenerator v)-
      (18:ℂ)*sourcePair u (compressionCore F v-z • v)-
      (18:ℂ)*z*sourcePair u v := by
  rw [actual_balanced_generator_source]
  have hc:=(paid_unweighted_frequency% compression_pair) F u (balancedGenerator v)
  have ha:=generator_skew u (compressionCore F v)
  have hb:=generator_skew u v
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,sourcePair,map_sub,map_smul,
    inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,starRingEnd_apply,star_star] at ha hb hc ⊢
  rw [ha,hc,hb]
  ring

private theorem resolvent_forcing(F:Index)(z:ℂ)(hz:z.im≠0)(f:QuantumTest):
    compressionCore F (resolventCore F z hz f)-z • resolventCore F z hz f=f := by
  have h:=LinearMap.congr_fun ((paid_phase_inverse% actual_inverse) F z hz).2 f
  simpa only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.one_apply] using h

/-- The two leakage legs form one original generator/forcing inventory;
real frequency, Phi contact and the raw-CF source equation remain together. -/
def jointNoetherForcing(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):ℂ :=
  let q:=resolventCore F z hz g
  let w:=thetaAction m ell q
  let k:=localizedPressureReader m ell F z hz g
  let u:=compensatedReader m ell F z hz g
  let f:=thetaAction m ell g+cutoffLeak m ell F q
  sourcePair (balancedGenerator k) f-sourcePair (balancedGenerator u) g+
    sourcePair (nonmagneticSecondField w) (((3:ℂ) • affineCutoff m ell) q)+
    (18:ℂ)*(sourcePair k f-sourcePair u g)-
    (18:ℂ)*z*(sourcePair u q-sourcePair k w)

theorem actual_joint_noether_source_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    jointBalancedNoether m ell F z hz g=jointNoetherForcing m ell F z hz g := by
  let q:=resolventCore F z hz g
  let w:=thetaAction m ell q
  let k:=localizedPressureReader m ell F z hz g
  let u:=compensatedReader m ell F z hz g
  have hq:compressionCore F q-z • q=g:=resolvent_forcing F z hz g
  have hk:compressionCore F k-star z • k=nonmagneticSecondField w := by
    unfold k localizedPressureReader
    exact resolvent_forcing F (star z) _ _
  have hu:compressionCore F u-star z • u=thetaAction m ell (nonmagneticSecondField w) := by
    unfold u compensatedReader
    exact resolvent_forcing F (star z) _ _
  have hw:compressionCore F w-z • w=thetaAction m ell g+cutoffLeak m ell F q := by
    have h:=congrArg (thetaAction m ell) hq
    unfold w cutoffLeak
    simp only [Module.End.mul_apply,LinearMap.sub_apply,map_sub,map_smul] at h ⊢
    linear_combination (norm:=module) h
  have hv:=LinearMap.congr_fun (actual_balanced_cutoff_source m ell) q
  simp only [Module.End.mul_apply,LinearMap.sub_apply,LinearMap.smul_apply] at hv
  have htheta(f h:QuantumTest):sourcePair (thetaAction m ell f) h=sourcePair f (thetaAction m ell h) := by
    unfold thetaAction
    exact (multiply_pair _ _ _ _).symm
  have hb0:=balanced_noether_pair F z u q
  have hb1:=balanced_noether_pair F z k w
  rw [hq,hu,htheta] at hb0
  rw [hk,hw] at hb1
  have hsource:sourcePair (nonmagneticSecondField w) (balancedGenerator w)=
      sourcePair (nonmagneticSecondField w) (thetaAction m ell (balancedGenerator q))+
      sourcePair (nonmagneticSecondField w) (((3:ℂ) • affineCutoff m ell) q) := by
    have he:balancedGenerator w=thetaAction m ell (balancedGenerator q)+((3:ℂ) • affineCutoff m ell) q := by
      unfold w
      simp only [LinearMap.smul_apply]
      linear_combination (norm:=module) hv
    rw [he,(paid_phase_frequency% pair_add_right)]
  unfold jointBalancedNoether jointNoetherForcing
  dsimp only
  change sourcePair u (balancedCompressionForce F q)-sourcePair k (balancedCompressionForce F w)=_
  rw [hb0,hb1,hsource]
  ring

/-- Only the already-paid mixed radial contact separates the complete
localization responsibility from the original joint Noether source inventory. -/
theorem actual_localization_noether_return(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    balancedLocalizationContact m ell F z hz g=
      (1/6:ℝ)*(jointNoetherForcing m ell F z hz g).re+radialBalancedContact m ell F z hz g := by
  rw [actual_balanced_localization_joint_return,actual_joint_noether_source_return]

/-- The residual is paid by true source storage at both retarded inputs,
with coefficient 3/6962 below 1/2048; no localization budget is a premise. -/
theorem actual_localization_radial_source_price(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(g:QuantumTest):
    |balancedLocalizationContact m ell F z hz g-(1/6:ℝ)*(jointNoetherForcing m ell F z hz g).re|/
      (2*ActualScalarPhaseJet.phaseCoefficient) ≤
      (3/6962:ℝ)*(nonmagneticStorage
        (resolventCore F z hz (balancedCompressionForce F (resolventCore F z hz g)))+
        nonmagneticStorage (resolventCore F z hz g)) := by
  rw [actual_localization_noether_return,add_sub_cancel_left]
  unfold radialBalancedContact
  rw [abs_mul,abs_of_nonneg (by norm_num:(0:ℝ) ≤ 1/12)]
  have hp:=actual_nonmagnetic_radial_storage_price m ell
    (resolventCore F z hz (balancedCompressionForce F (resolventCore F z hz g))) (resolventCore F z hz g)
  have ha:=Complex.abs_re_le_norm (sourcePair
    (resolventCore F z hz (balancedCompressionForce F (resolventCore F z hz g)))
    (radialDouble m ell nonmagneticSecondField (resolventCore F z hz g)))
  have hc:=ActualScalarPhaseJet.actual_phase_coefficient_positive
  have hb:=(div_le_iff₀ (by positivity:0 < 2*ActualScalarPhaseJet.phaseCoefficient)).mp hp
  apply (div_le_iff₀ (by positivity:0 < 2*ActualScalarPhaseJet.phaseCoefficient)).mpr
  nlinarith only [ha,hb]

end LowEnergy.ActualBalancedLocalizationContactReturn
