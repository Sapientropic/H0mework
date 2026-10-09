import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedPrimitiveDefectPayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiBalancedInputCommonPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.PhaseCompressionCancellation
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open SourceScalarPairedTransport
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarGaugeScale SourceDilationRemainder SourcePhysicalKineticSquare
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiCombinedScalePressure
open ReverseNativeClock ReverseNativeFrequencyWard ReverseScalarGaugeWard ReverseBalancedForcePayer ScalarBalancedPrimitive
open FullYSourceResolventGraphSplice ReverseForceNoetherPayer
open scoped ContDiff
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev A:End:=gaugeBalancedNativeForce
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev Zbar:End:=reverseNativeClock-(9:ℂ) • SourceGaugeScaleTransport.generator
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic matterAction gaugeBalancedNativeForce
  reverseNativeClock SourceGaugeScaleTransport.generator compressionCore balancedCompressionForce phaseRow
private theorem real_commute(c d:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hd:∀z:physicalChart,ContDiffAt ℝ ∞ d z.val):
    Commute (multiply c hc) (multiply d hd):=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (d z:ℂ) (f z)
private theorem radius_inverse:r*S=1 ∧ S*r=1:=by
  have hi:r*S=1:=by
    apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
    change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
    rw [smul_smul,←Complex.ofReal_mul]
    have hp:0<phiRadius z:=Real.sqrt_pos.2 (by positivity)
    unfold phiReciprocal
    rw [mul_inv_cancel₀ hp.ne',Complex.ofReal_one,one_smul]
  exact ⟨hi,(real_commute _ _ _ _).eq.trans hi⟩
private theorem inverse_commute(T:End)(h:Commute T r):Commute T S:=by
  change T*S=S*T
  calc
    T*S=(S*r)*T*S:=by rw [radius_inverse.2,one_mul]
    _=S*(r*T)*S:=by noncomm_ring
    _=S*(T*r)*S:=by rw [h.eq]
    _=S*T*(r*S):=by noncomm_ring
    _=S*T:=by rw [radius_inverse.1,mul_one]
private theorem poly_commute {R:Type*}[Ring R](T S:R)(h:Commute T S)(m ell:ℕ):
    Commute T ((1-S)^(m+1)-(1-S)^(ell+1)):=by
  have hq:Commute T (1-S):=(Commute.one_right T).sub_right h
  exact (hq.pow_right (m+1)).sub_right (hq.pow_right (ell+1))
private theorem neg_mul_commute {R:Type*}[Ring R](T S C:R)(hS:Commute T S)(hC:Commute T C):
    Commute T (-(S*C)):=(hS.mul_right hC).neg_right
private theorem row_commute(T:End)(h:Commute T r)(m ell:ℕ)(i:Fin 2):Commute T (phaseRow m ell i):=by
  have hs:=inverse_commute T h
  have ht:Commute T (phiThetaAction m ell):=poly_commute T S hs m ell
  unfold phaseRow
  fin_cases i
  · exact ht
  · exact neg_mul_commute T S (phiThetaAction m ell) hs ht
private theorem real_row(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(m ell:ℕ)(i:Fin 2):
    bracket (multiply c hc) (phaseRow m ell i)=0:=
  sub_eq_zero.mpr (row_commute _ (real_commute _ _ _ _) m ell i).eq

/-- Every non-scalar-kinetic original department commutes with both actual phase rows. -/
theorem actual_phase_non_scalar_commute(m ell:ℕ)(i:Fin 2):
    Commute (H0-scalarKinetic) (phaseRow m ell i):=
  row_commute _ original_phi_radius_non_scalar_commute.2.2.2 m ell i

/-- The complete balanced native force cancels six copies of the actual H0 phase current. -/
theorem actual_balanced_native_phase_current(m ell:ℕ)(i:Fin 2):
    bracket A (phaseRow m ell i)=(-6:ℂ) • bracket H0 (phaseRow m ell i):=by
  have hcenter:bracket centeredAction (phaseRow m ell i)=0:=real_row _ _ m ell i
  have hv:bracket vacuumLinearAction (phaseRow m ell i)=0:=real_row _ _ m ell i
  have hm:bracket magneticAction (phaseRow m ell i)=0:=real_row _ _ m ell i
  have hl:bracket localAction (phaseRow m ell i)=0:=real_row _ _ m ell i
  have hs:bracket scalarSpatialAction (phaseRow m ell i)=0:=real_row _ _ m ell i
  have hM:bracket matterAction (phaseRow m ell i)=0:=
    sub_eq_zero.mpr (row_commute _ original_phi_radius_non_scalar_commute.2.2.1 m ell i).eq
  have hk:bracket H0 (phaseRow m ell i)=bracket scalarKinetic (phaseRow m ell i):=by
    have he:=(actual_phase_non_scalar_commute m ell i).eq
    unfold bracket
    linear_combination (norm:=noncomm_ring) he
  rw [show A=gaugeBalancedNativeForce from rfl,actual_balanced_native_departments,hk]
  unfold bracket at hcenter hv hm hl hs hM ⊢
  linear_combination (norm:=(noncomm_ring;module)) (-24:ℂ) • hM+(6:ℂ) • hcenter-
    (6:ℂ) • hv-(72:ℂ) • hm-(36:ℂ) • hl-(42:ℂ) • hs

def phaseCompressionDefect(F:Index):End:=
  (12:ℂ) • defectAction F-bracket Zbar (defectAction F)

/-- Native phase force and physical compression current reduce to the same own-cutoff derivation. -/
theorem actual_balanced_compression_phase_current(F:Index)(m ell:ℕ)(i:Fin 2):
    bracket (balancedCompressionForce F) (phaseRow m ell i)+
      (6:ℂ) • bracket (compressionCore F) (phaseRow m ell i)=
        bracket (phaseCompressionDefect F) (phaseRow m ell i):=by
  have h:=actual_balanced_native_phase_current m ell i
  have hc:=actual_balanced_compression_departments F
  have hA:reverseScaleForce-(9:ℂ) • bracket SourceGaugeScaleTransport.generator H0=A:=by
    unfold A gaugeBalancedNativeForce
    rfl
  rw [hA] at hc
  rw [hc]
  unfold bracket at h
  unfold phaseCompressionDefect defectAction bracket
  linear_combination (norm:=(noncomm_ring;module)) h

private theorem balanced_full_scale:bracket Zbar H0=(18:ℂ) • H0+A:=by
  have h:=actual_reverse_full_hamiltonian_scale
  unfold bracket at h
  unfold Zbar A gaugeBalancedNativeForce bracket
  linear_combination (norm:=(noncomm_ring;module)) h

/-- The derivative of the phase current retains its actual Hamiltonian coefficient twelve. -/
theorem actual_balanced_phase_differentiated_current(m ell:ℕ)(i:Fin 2):
    bracket H0 (bracket Zbar (phaseRow m ell i))=
      bracket Zbar (bracket H0 (phaseRow m ell i))-(12:ℂ) • bracket H0 (phaseRow m ell i):=by
  have h:=actual_balanced_native_phase_current m ell i
  have he:=balanced_full_scale
  have hj:bracket H0 (bracket Zbar (phaseRow m ell i))=
      bracket Zbar (bracket H0 (phaseRow m ell i))-bracket (bracket Zbar H0) (phaseRow m ell i):=by
    unfold bracket;noncomm_ring;module
  rw [he] at hj
  unfold bracket at h hj ⊢
  linear_combination (norm:=(noncomm_ring;module)) hj-h

/-- Complete physical forcing of the differentiated phase reduces to the same own-cutoff derivation; the Hamiltonian escape is retained in full. -/
theorem actual_balanced_phase_input_escape(F:Index)(m ell:ℕ)(i:Fin 2):
    wordPhysicalEscape F (bracket Zbar (phaseRow m ell i))=
      bracket Zbar (wordPhysicalEscape F (phaseRow m ell i))-
        (12:ℂ) • wordPhysicalEscape F (phaseRow m ell i)+phaseRow m ell i*phaseCompressionDefect F:=by
  have h:=actual_balanced_phase_differentiated_current m ell i
  unfold bracket at h
  unfold wordPhysicalEscape phaseCompressionDefect bracket
  linear_combination (norm:=(noncomm_ring;module)) h
end LowEnergy.PhaseCompressionCancellation
