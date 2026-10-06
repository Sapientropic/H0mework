import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeIntrinsicJointCancellation
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeScalarOscillatorAbsorption

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceMixedCurrentCancellation
open GaussLiveMomentum GaussCoreDifferential GaussCoreHilbert GaussHistoryHilbert
open GaussNativeForm GaussNativeEnergy GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPositiveBulkWard
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceDoubleGramCurvatureForm SourceJointScalarGaugeCoefficientForm SourceIntrinsicJointCancellation
open SourceCoframeVolume SourcePhysicalKineticSquare SourceHamiltonianVolume SourceCoframeVolumeCurrent
open SourceInverseNoetherEnergy SourceScalarVirialBulk SourceScalarOscillatorAbsorption
open SourceScalarInverseRetardedBudget SourceScalarInverseNativeEnergy SourceGammaNativeBudget
open scoped InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem scalar_gram_pair (f g : QuantumTest) : sourcePair f (scalarGram g)=sourcePair (scalarGram f) g := by
  simp only [scalarGram,LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,inner_sum,sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  exact (GaussNativeForm.adjoint_pair _ _ _).trans (GaussMomentumAdjoint.momentum_pair _ _ _)

private theorem pair_polarization (A : End) (f g : QuantumTest) :
    sourcePair f (A g)=(sourcePair (f+g) (A (f+g))-sourcePair (f-g) (A (f-g))-
      Complex.I*sourcePair (f+Complex.I • g) (A (f+Complex.I • g))+
      Complex.I*sourcePair (f-Complex.I • g) (A (f-Complex.I • g)))/4 := by
  simp only [sourcePair,map_add,map_sub,map_smul,inner_add_left,inner_add_right,inner_sub_left,
    inner_sub_right,inner_smul_left,inner_smul_right,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

private theorem end_zero_of_pair_self (A : End) (h : ∀ f,sourcePair f (A f)=0) : A=0 := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  rw [pair_polarization,h,h,h,h]
  simp only [sub_zero,mul_zero,add_zero,zero_div,LinearMap.zero_apply,sourcePair,map_zero,inner_zero_right]

/-- The exact joint cancellation polarizes to core commutation of the complete scalar Gram and electric kinetic action. -/
theorem original_scalar_gram_gauge_commute : Commute scalarGram gaugeKinetic := by
  apply sub_eq_zero.mp
  apply end_zero_of_pair_self
  intro f
  have hi := original_mixed_gram_energy_form f
  rw [original_mixed_joint_scalar_gauge_form,original_joint_scalar_gauge_form_zero] at hi
  have hd : sourcePair f ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)=
      sourcePair (scalarGram f) (gaugeKinetic f)-sourcePair (gaugeKinetic f) (scalarGram f) := by
    simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_right]
    change sourcePair f (scalarGram (gaugeKinetic f))-sourcePair f (gaugeKinetic (scalarGram f))=_
    exact congrArg₂ (fun x y : ℂ => x-y) (scalar_gram_pair f (gaugeKinetic f))
      (gaugeKinetic_pair f (scalarGram f))
  apply Complex.ext
  · have hc := congrArg Complex.re (pair_conjugate (scalarGram f) (gaugeKinetic f))
    simp only [Complex.conj_re] at hc
    rw [hd,Complex.sub_re]
    exact sub_eq_zero.mpr hc
  · change (sourcePair f ((scalarGram*gaugeKinetic-gaugeKinetic*scalarGram) f)).im=0
    linarith

private theorem inverse_commute (A : End) (h : Commute A volumeAction) : Commute A inverseVolumeAction := by
  have hVU : Commute inverseVolumeAction volumeAction := real_volume _ _
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

/-- The true negative scalar weight preserves the source-generated kinetic commutation. -/
theorem original_scalar_gauge_commute : Commute scalarKinetic gaugeKinetic := by
  rw [scalar_kinetic_gram]
  exact (((inverse_commute _ gauge_kinetic_volume).symm).mul_left original_scalar_gram_gauge_commute).smul_left _

/-- The original source current after removing its now vanishing mixed44 block. -/
def unmixedBulkCurrent : End :=
  (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
    inverseVolumeAction*(-(8 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*scalarKinetic-
      scalarKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
      (36 : ℂ) • ((diagonalAction-scalarKinetic-gaugeKinetic)*gaugeKinetic-
        gaugeKinetic*(diagonalAction-scalarKinetic-gaugeKinetic))+
      (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction))

/-- Exact whole-source operator deletion, retaining the coframe, spatial, matter and shifted-scalar terms. -/
theorem original_bulk_current_without_mixed : bulkCurrent=unmixedBulkCurrent := by
  rw [original_current_kinetic_source,original_scalar_gauge_commute.eq,sub_self,smul_zero,zero_sub]
  simp only [unmixedBulkCurrent,neg_smul]

/-- The oscillator remainder consumes the same exact operator cancellation. -/
theorem original_remaining_current_without_mixed : remainingCurrent=unmixedBulkCurrent-scalarCurrent := by
  have h := original_current_split
  rw [original_bulk_current_without_mixed] at h
  linear_combination (norm := module) -h

/-- Same original compression, core state and raised operator; the full defect remains unchanged. -/
theorem original_remaining_raised_without_mixed (F : Index) (A : End) (q : QuantumTest) :
    remainingRaisedCurrent F A q=(sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
      (sourcePair (A q) ((unmixedBulkCurrent-scalarCurrent) (A q))).im/2 := by
  rw [remainingRaisedCurrent,original_remaining_current_without_mixed]

end LowEnergy.SourceMixedCurrentCancellation
