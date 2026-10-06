import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceScalarEssentialBudget
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarSpatialCurrent
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceDilationMomentum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarVolumePressure
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussMatterCore GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumScalarChart
open SourcePhysicalKineticSquare SourceScalarInverseNativeEnergy SourceInverseNoetherEnergy
open SourceScalarPositiveBulkWard
open SourceScalarShiftedBulk SourceScalarOscillatorAbsorption SourceScalarVirialBulk SourceScalarEssentialBudget
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceNativeCoframeCompatibility SourceScalarSpatialCurrent
open SourceNativeMatterCovarianceCancellation SourceUnmixedPotentialCancellation SourceDoubleGramCurvatureForm
open SourceHamiltonianVolume SourceScalarDoubleCurrent SourceDilationRemainder SourceDilationMomentum SourceCoframeDilation
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic matterAction inverseVolumeAction
  scalarBulk scalarBulkComplete scalarGram GaussCoframeForm.coframeAction dilation localAction scalarSpatialAction

private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := by
    unfold inverseVolumeAction
    exact real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0 : ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z : ℂ) • f z=(-(sourceTime 0 : ℂ)) • ((reciprocalVolume z : ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem scalar_kinetic_gram : scalarKinetic=(-(sourceTime 0 : ℂ)/2) • (inverseVolumeAction*scalarGram) := by
  have hr (i : ScalarIndex) : sandwich (scalarDirection i) (scalarDirection i) scalarWeight scalarWeight_smooth=
      (-(sourceTime 0 : ℂ)) • (inverseVolumeAction*(GaussMomentumAdjoint.adjoint (scalarDirection i)*covariantMomentum (scalarDirection i))) := by
    change GaussMomentumAdjoint.adjoint (scalarDirection i)*(multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection i))=_
    rw [weight_inverse,smul_mul_assoc,mul_smul_comm,←mul_assoc,
      (inverse_commute _ (native_adjoint_volume (scalarDirection i))).eq,mul_assoc]
  simp only [scalarKinetic,hr,←Finset.smul_sum,←Finset.mul_sum,smul_smul,scalarGram]
  congr 1
  ring

private theorem local_factor : localAction=(sourceTime 0 : ℂ) • (volumeAction*quadAction) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  unfold localAction
  change (localPotential z : ℂ)*f z word=
    (sourceTime 0 : ℂ)*((volume z : ℂ)*((quadPotential z : ℂ)*f z word))
  unfold localPotential GaussCoframeForm.volumePotential quadPotential
  rw [real_inner_self_eq_norm_sq]
  push_cast
  ring

private theorem inverse_local : inverseVolumeAction*localAction=(sourceTime 0 : ℂ) • quadAction := by
  rw [local_factor,mul_smul_comm,←mul_assoc]
  have h : inverseVolumeAction*volumeAction=1 := by
    have hc : Commute inverseVolumeAction volumeAction := by unfold inverseVolumeAction;exact real_volume _ _
    exact hc.eq.trans (LinearMap.ext volume_inverse)
  rw [h,one_mul]

private theorem coframe_local : GaussCoframeForm.coframeAction*localAction-localAction*GaussCoframeForm.coframeAction=
    -(3*Complex.I*(sourceTime 0 : ℂ)^2/4) • (dilation*quadAction) := by
  have hh := original_local_hamiltonian_current
  have hs := original_scalar_local_current
  have hp : Commute localAction (multiply GaussNativePotential.potential GaussNativePotential.potential_smooth) := by
    unfold localAction
    exact real_commute _ _ _ _
  unfold SourceScalarDoubleCurrent.bracket at hh hs
  have he : diagonalAction=scalarKinetic+gaugeKinetic+multiply GaussNativePotential.potential
      GaussNativePotential.potential_smooth+GaussCoframeForm.coframeAction+matterAction := by
    unfold diagonalAction nativeAction
    rfl
  rw [he] at hh
  simp only [add_mul,mul_add,original_gauge_local_commute.eq,hp.eq,local_matter.eq] at hh
  linear_combination (norm := module) -hh-hs

private theorem coframe_inverse_local : Commute GaussCoframeForm.coframeAction (inverseVolumeAction*localAction) := by
  have he : GaussCoframeForm.coframeAction*(inverseVolumeAction*localAction)-
      (inverseVolumeAction*localAction)*GaussCoframeForm.coframeAction=
      (GaussCoframeForm.coframeAction*inverseVolumeAction-inverseVolumeAction*GaussCoframeForm.coframeAction)*localAction+
        inverseVolumeAction*(GaussCoframeForm.coframeAction*localAction-localAction*GaussCoframeForm.coframeAction) := by noncomm_ring
  rw [original_coframe_inverse_current,coframe_local] at he
  have hz : (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction)*localAction+
      inverseVolumeAction*(-(3*Complex.I*(sourceTime 0 : ℂ)^2/4) • (dilation*quadAction))=0 := by
    simp only [smul_mul_assoc,mul_smul_comm,mul_assoc]
    rw [inverse_local]
    simp only [mul_smul_comm,smul_smul]
    module
  exact sub_eq_zero.mp (he.trans hz)

private theorem volume_potential : multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth=
    (3*(sourceTime 0 : ℂ)) • volumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((3*sourceTime 0*volume z : ℝ) : ℂ) • f z=(3*(sourceTime 0 : ℂ)) • ((volume z : ℂ) • f z)
  simp only [smul_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]

private theorem volume_scalar_bulk : Commute volumeAction scalarBulk := by
  unfold scalarBulk
  have hv : Commute volumeAction inverseVolumeAction := by
    unfold inverseVolumeAction
    exact (real_volume _ _).symm
  have hl : Commute volumeAction localAction := by unfold localAction;exact (real_volume _ _).symm
  exact ((hv.mul_right scalar_kinetic_volume.symm).smul_right _).add_right ((hv.mul_right hl).smul_right _)

private theorem spatial_real : Commute scalarSpatialAction inverseVolumeAction ∧ Commute scalarSpatialAction localAction := by
  unfold scalarSpatialAction inverseVolumeAction localAction
  exact ⟨real_commute _ _ _ _,real_commute _ _ _ _⟩

/-- The two inverse-volume fluxes carry the same source sign. -/
def volumePressureAction : End := (3*Complex.I*(sourceTime 0 : ℂ)^2) •
  ((inverseVolumeAction*dilation*inverseVolumeAction*inverseVolumeAction+
    inverseVolumeAction*inverseVolumeAction*dilation*inverseVolumeAction)*scalarGram)

/-- The whole coframe current reduces to a single symmetrized volume word; the original spatial force remains explicit. -/
theorem original_geometric_pressure : geometricScalarCurrent=volumePressureAction+
    (8 : ℂ) • (inverseVolumeAction*scalarSpatialDivergence) := by
  have hsplit : geometricAction=GaussCoframeForm.coframeAction-
      multiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth+scalarSpatialAction := by
    unfold geometricAction GaussCoframeForm.coframeAction
    abel
  have hs : scalarSpatialAction*scalarBulk-scalarBulk*scalarSpatialAction=
      (8 : ℂ) • (inverseVolumeAction*scalarSpatialDivergence) := by
    have hl : Commute scalarSpatialAction (inverseVolumeAction*localAction) :=
      spatial_real.1.mul_right spatial_real.2
    have hk : scalarSpatialAction*(inverseVolumeAction*scalarKinetic)-
        (inverseVolumeAction*scalarKinetic)*scalarSpatialAction= -inverseVolumeAction*scalarSpatialDivergence := by
      rw [←original_scalar_spatial_current]
      linear_combination (norm := noncomm_ring) spatial_real.1.eq*scalarKinetic
    simp only [neg_mul] at hk
    unfold scalarBulk
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,hl.eq]
    linear_combination (norm := module) (-8 : ℂ) • hk
  have hk : GaussCoframeForm.coframeAction*scalarBulk-scalarBulk*GaussCoframeForm.coframeAction=volumePressureAction := by
    have hprod : GaussCoframeForm.coframeAction*(inverseVolumeAction*scalarKinetic)-
        (inverseVolumeAction*scalarKinetic)*GaussCoframeForm.coframeAction=
        (GaussCoframeForm.coframeAction*inverseVolumeAction-inverseVolumeAction*GaussCoframeForm.coframeAction)*scalarKinetic+
          inverseVolumeAction*(GaussCoframeForm.coframeAction*scalarKinetic-scalarKinetic*GaussCoframeForm.coframeAction) := by noncomm_ring
    rw [original_coframe_inverse_current,original_coframe_scalar_current] at hprod
    have hc : GaussCoframeForm.coframeAction*scalarBulk-scalarBulk*GaussCoframeForm.coframeAction=
        (-8 : ℂ) • (GaussCoframeForm.coframeAction*(inverseVolumeAction*scalarKinetic)-
          (inverseVolumeAction*scalarKinetic)*GaussCoframeForm.coframeAction) := by
      unfold scalarBulk
      simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,coframe_inverse_local.eq,smul_sub]
      module
    rw [hc,hprod,scalar_kinetic_gram]
    unfold volumePressureAction
    simp only [mul_smul_comm,smul_mul_assoc,smul_add,smul_smul,add_mul,mul_assoc]
    module
  unfold geometricScalarCurrent
  rw [hsplit,volume_potential]
  simp only [add_mul,mul_add,sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm,volume_scalar_bulk.eq]
  linear_combination (norm := module) hk+hs

private theorem inverse_pair (f g : QuantumTest) :
    sourcePair f (inverseVolumeAction g)=sourcePair (inverseVolumeAction f) g := by
  unfold inverseVolumeAction
  exact multiply_pair _ _ _ _

private def pressureMetric : End := inverseVolumeAction*dilation*inverseVolumeAction*inverseVolumeAction+
    inverseVolumeAction*inverseVolumeAction*dilation*inverseVolumeAction

private theorem pressure_adjoint (v : Ambient) : Commute pressureMetric (GaussMomentumAdjoint.adjoint v) := by
  have hv := (inverse_commute _ (native_adjoint_volume v)).symm
  have hd : Commute dilation (GaussMomentumAdjoint.adjoint v) := sub_eq_zero.mp (native_adjoint_current v)
  exact (((hv.mul_left hd).mul_left hv).mul_left hv).add_left (((hv.mul_left hv).mul_left hd).mul_left hv)

private theorem pressure_metric_diagonal (f : QuantumTest) :
    sourcePair f (pressureMetric f)=
      sourcePair (inverseVolumeAction f) (dilation (inverseVolumeAction (inverseVolumeAction f)))+
        starRingEnd ℂ (sourcePair (inverseVolumeAction f) (dilation (inverseVolumeAction (inverseVolumeAction f)))) := by
  have he : sourcePair f (inverseVolumeAction (inverseVolumeAction (dilation (inverseVolumeAction f))))=
      starRingEnd ℂ (sourcePair (inverseVolumeAction f) (dilation (inverseVolumeAction (inverseVolumeAction f)))) := by
    rw [inverse_pair,inverse_pair,dilation_pair,pair_conjugate]
  change sourcePair f (inverseVolumeAction (dilation (inverseVolumeAction (inverseVolumeAction f)))+
    inverseVolumeAction (inverseVolumeAction (dilation (inverseVolumeAction f))))=_
  simp only [sourcePair,map_add,inner_add_right]
  change sourcePair f (inverseVolumeAction (dilation (inverseVolumeAction (inverseVolumeAction f))))+
    sourcePair f (inverseVolumeAction (inverseVolumeAction (dilation (inverseVolumeAction f))))=_
  rw [inverse_pair,he]
  rfl

/-- A single volume-pressure pairing on the actual seventy native scalar legs. -/
def volumePressurePair (f : QuantumTest) : ℂ := ∑ r : ScalarIndex,
  sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection r) f))
    (dilation (inverseVolumeAction (inverseVolumeAction (covariantMomentum (scalarDirection r) f))))

private theorem pressure_gram_pair (f : QuantumTest) :
    sourcePair f ((pressureMetric*scalarGram) f)=volumePressurePair f+starRingEnd ℂ (volumePressurePair f) := by
  have ht (r : ScalarIndex) : sourcePair f
      (pressureMetric (GaussMomentumAdjoint.adjoint (scalarDirection r) (covariantMomentum (scalarDirection r) f)))=
      sourcePair (covariantMomentum (scalarDirection r) f) (pressureMetric (covariantMomentum (scalarDirection r) f)) := by
    have hc := LinearMap.congr_fun (pressure_adjoint (scalarDirection r)).eq (covariantMomentum (scalarDirection r) f)
    change pressureMetric (GaussMomentumAdjoint.adjoint (scalarDirection r) (covariantMomentum (scalarDirection r) f))=
      GaussMomentumAdjoint.adjoint (scalarDirection r) (pressureMetric (covariantMomentum (scalarDirection r) f)) at hc
    rw [hc,GaussNativeForm.adjoint_pair]
  change sourcePair f (pressureMetric (scalarGram f))=_
  unfold scalarGram
  simp only [LinearMap.sum_apply,Module.End.mul_apply,map_sum,sourcePair,inner_sum]
  change (∑ r : ScalarIndex,sourcePair f
    (pressureMetric (GaussMomentumAdjoint.adjoint (scalarDirection r) (covariantMomentum (scalarDirection r) f))))=_
  simp only [ht,pressure_metric_diagonal,Finset.sum_add_distrib,volumePressurePair,map_sum]

/-- The symmetrized volume flux is exactly first order in the coframe dilation on the same VP leg. -/
theorem original_volume_pressure_form (f : QuantumTest) :
    (sourcePair f (volumePressureAction f)).im/2=3*(sourceTime 0)^2*(volumePressurePair f).re := by
  change (sourcePair f (((3*Complex.I*(sourceTime 0 : ℂ)^2) • (pressureMetric*scalarGram)) f)).im/2=_
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_right]
  change ((3*Complex.I*(sourceTime 0 : ℂ)^2)*sourcePair f ((pressureMetric*scalarGram) f)).im/2=_
  rw [pressure_gram_pair]
  simp [Complex.mul_im,Complex.mul_re,←Complex.ofReal_pow]
  ring

/-- The spatial source force uses the same VP leg, retaining the original scalar weight's sign. -/
def spatialForcePair (f : QuantumTest) : ℂ := ∑ r : ScalarIndex,
  sourcePair (inverseVolumeAction (covariantMomentum (scalarDirection r) f))
    (inverseVolumeAction (scalarForceAction (scalarDirection r) f))

private theorem spatial_row_pair (v : Ambient) (f : QuantumTest) :
    sourcePair f ((inverseVolumeAction*(GaussMomentumAdjoint.adjoint v*(inverseVolumeAction*scalarForceAction v)+
      scalarForceAction v*(inverseVolumeAction*covariantMomentum v))) f)=
      sourcePair (inverseVolumeAction (covariantMomentum v f)) (inverseVolumeAction (scalarForceAction v f))+
        starRingEnd ℂ (sourcePair (inverseVolumeAction (covariantMomentum v f)) (inverseVolumeAction (scalarForceAction v f))) := by
  have hp := LinearMap.congr_fun (original_native_inverse_commute v).eq f
  change covariantMomentum v (inverseVolumeAction f)=inverseVolumeAction (covariantMomentum v f) at hp
  have hf : Commute (scalarForceAction v) inverseVolumeAction := by
    unfold scalarForceAction inverseVolumeAction
    exact real_commute _ _ _ _
  have hfc := LinearMap.congr_fun hf.eq f
  change scalarForceAction v (inverseVolumeAction f)=inverseVolumeAction (scalarForceAction v f) at hfc
  have hfp (p q : QuantumTest) : sourcePair p (scalarForceAction v q)=sourcePair (scalarForceAction v p) q := by
    unfold scalarForceAction
    exact multiply_pair _ _ _ _
  change sourcePair f (inverseVolumeAction (GaussMomentumAdjoint.adjoint v (inverseVolumeAction (scalarForceAction v f))+
    scalarForceAction v (inverseVolumeAction (covariantMomentum v f))))=_
  rw [map_add]
  simp only [sourcePair,map_add,inner_add_right]
  change sourcePair f (inverseVolumeAction (GaussMomentumAdjoint.adjoint v (inverseVolumeAction (scalarForceAction v f))))+
    sourcePair f (inverseVolumeAction (scalarForceAction v (inverseVolumeAction (covariantMomentum v f))))=_
  rw [inverse_pair,inverse_pair,GaussNativeForm.adjoint_pair,hp,hfp,hfc]
  exact congrArg (fun z : ℂ => sourcePair (inverseVolumeAction (covariantMomentum v f))
    (inverseVolumeAction (scalarForceAction v f))+z)
      (pair_conjugate (inverseVolumeAction (covariantMomentum v f))
        (inverseVolumeAction (scalarForceAction v f))).symm

/-- Both independent transpose legs return the same signed real spatial force. -/
theorem original_spatial_pressure_form (f : QuantumTest) :
    (sourcePair f ((inverseVolumeAction*scalarSpatialDivergence) f)).im=
      sourceTime 0*(spatialForcePair f).re := by
  have he : inverseVolumeAction*scalarSpatialDivergence=(Complex.I*(sourceTime 0 : ℂ)/2) •
      ∑ r : ScalarIndex,inverseVolumeAction*(GaussMomentumAdjoint.adjoint (scalarDirection r)*
        (inverseVolumeAction*scalarForceAction (scalarDirection r))+
        scalarForceAction (scalarDirection r)*(inverseVolumeAction*covariantMomentum (scalarDirection r))) := by
    unfold scalarSpatialDivergence
    rw [weight_inverse]
    simp only [mul_smul_comm,smul_mul_assoc,←smul_add,←Finset.smul_sum,smul_smul,←Finset.mul_sum]
    congr 1
    ring
  rw [he]
  simp only [LinearMap.smul_apply,LinearMap.sum_apply,sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  change ((Complex.I*(sourceTime 0 : ℂ)/2)*(∑ r : ScalarIndex,sourcePair f
    ((inverseVolumeAction*(GaussMomentumAdjoint.adjoint (scalarDirection r)*(inverseVolumeAction*scalarForceAction (scalarDirection r))+
      scalarForceAction (scalarDirection r)*(inverseVolumeAction*covariantMomentum (scalarDirection r)))) f))).im=_
  simp only [spatial_row_pair,Finset.sum_add_distrib,←map_sum]
  change ((Complex.I*(sourceTime 0 : ℂ)/2)*(spatialForcePair f+starRingEnd ℂ (spatialForcePair f))).im=_
  simp [Complex.mul_im,Complex.mul_re]
  ring

/-- The only remaining geometric source pairing, with both contributions kept signed and joined. -/
def scalarPressure (f : QuantumTest) : ℝ :=
  3*(sourceTime 0)^2*(volumePressurePair f).re+4*sourceTime 0*(spatialForcePair f).re

/-- All six coframe derivatives, mixed spin, spin squares and Number reduce to one dilation pressure and the actual spatial force. -/
theorem original_geometric_pressure_form (f : QuantumTest) :
    (sourcePair f (geometricScalarCurrent f)).im/2=scalarPressure f := by
  rw [original_geometric_pressure]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,sourcePair,map_add,map_smul,inner_add_right,
    inner_smul_right,Complex.add_im,Complex.mul_im,Complex.re_ofNat,Complex.im_ofNat,zero_mul,add_zero]
  change ((sourcePair f (volumePressureAction f)).im+
    8*(sourcePair f ((inverseVolumeAction*scalarSpatialDivergence) f)).im)/2=_
  rw [add_div,original_volume_pressure_form,original_spatial_pressure_form]
  unfold scalarPressure
  ring

/-- Same F and full raised defect: the necessary scalar cost reads the joint pressure directly. -/
theorem actual_scalar_raised_pressure (F : Index) (T : End) (q : QuantumTest) :
    scalarRaised F T q=(sourcePair (raisedDefect F T q) (scalarBulkComplete (T q))).im-scalarPressure (T q) := by
  unfold scalarRaised
  rw [original_geometric_pressure_form]

/-- The original μ−2n absorption consumes the reduced source pressure without a new moving coframe norm. -/
theorem actual_scalar_pressure_absorption (μ : ℝ) (F : Index) (T : End) (q : QuantumTest) :
    (μ-2*sourceTime 0)*scalarEnergy (T q) ≤
      μ*scalarEnergy (T q)-scalarNoether F T q+
        ((sourcePair (raisedDefect F T q) (scalarBulkComplete (T q))).im-scalarPressure (T q))+
        (sourceTime 0)^2*‖vacuum‖^2*‖embed (T q)‖^2 := by
  simpa only [actual_scalar_raised_pressure] using actual_scalar_absorption μ F T q

end LowEnergy.SourceScalarVolumePressure
