import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeUnmixedPotentialCancellation
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceScalarBalancedForce

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceNativeMatterCovarianceCancellation
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussMatterCore GaussQuantumMultiplier SourceCartanCubic SourceScalarBalancedForce
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceDilationRemainder SourceScalarDoubleCurrent
open SourceUnmixedPotentialCancellation SourceScalarOscillatorAbsorption SourceInverseNoetherEnergy SourceScalarPositiveBulkWard
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem scalar_contact_zero (v : Ambient) (hv : v.2=0) : matterContact v=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change contactFiber v z (f z)=0
  simp only [contactFiber,sum_apply,smul_apply,hv,map_zero,zero_apply,smul_zero,Finset.sum_const_zero]

/-- Original all-CAR covariance eliminates the actual scalar native matter contact. -/
theorem original_scalar_matter_momentum (v : Ambient) (hv : v.2=0) : Commute (covariantMomentum v) matterAction := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (matterAction f)=matterAction (covariantMomentum v f)
  rw [original_matter_momentum,scalar_contact_zero v hv,LinearMap.zero_apply,smul_zero,add_zero]

/-- The original Number-weighted formal transpose consumes the same vanishing source contact. -/
theorem original_scalar_matter_adjoint (v : Ambient) (hv : v.2=0) :
    Commute (GaussMomentumAdjoint.adjoint v) matterAction := by
  apply LinearMap.ext
  intro f
  change GaussMomentumAdjoint.adjoint v (matterAction f)=matterAction (GaussMomentumAdjoint.adjoint v f)
  rw [original_matter_adjoint,scalar_contact_zero v hv,LinearMap.zero_apply,smul_zero,add_zero]

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  unfold matterAction
  apply Commute.sum_left
  intro i _
  apply Commute.sum_left
  intro b _
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (localMatrix i b z)) (c z : ℂ) (f z)

/-- The full negative-weight scalar kinetic operator commutes with the original local matter action. -/
theorem original_scalar_matter_commute : Commute scalarKinetic matterAction := by
  unfold scalarKinetic
  apply Commute.smul_left
  apply Commute.sum_left
  intro r _
  change Commute (GaussMomentumAdjoint.adjoint (scalarDirection r)*
    (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection r))) matterAction
  exact (original_scalar_matter_adjoint _ rfl).mul_left
    ((matter_real _ _).symm.mul_left (original_scalar_matter_momentum _ rfl))

/-- The surviving gauge contact has only the original coframe coefficient and fixed Lie basis; no moving gauge or inverse-chart coefficient remains. -/
theorem original_gauge_matter_contact (j : Fin 3) (a : LieIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    matterContact (gaugeDirection j a) f z=
      (∑ b : Fin 3,(GaussMatterCore.coefficient j b z : ℂ) • quantumTerm b (lieBasis a)) (f z) := by
  change contactFiber (gaugeDirection j a) z (f z)=_
  have hc (i : Fin 3) : gaugeCoordinate i (gaugeDirection j a).2=if i=j then lieBasis a else 0 := by
    change (Pi.single j (lieBasis a) : Fin 3 → NativeLie) i=_
    simp only [Pi.single_apply]
  simp only [contactFiber,sum_apply,smul_apply]
  rw [Finset.sum_eq_single j]
  · apply Finset.sum_congr rfl
    intro b _
    rw [hc,if_pos rfl]
  · intro i _ hij
    apply Finset.sum_eq_zero
    intro b _
    rw [hc,if_neg hij,map_zero,zero_apply,smul_zero]
  · simp only [Finset.mem_univ,not_true_eq_false,false_implies]

private theorem momentum_contact (v : Ambient) :
    covariantMomentum v*matterAction-matterAction*covariantMomentum v=(-Complex.I) • matterContact v := by
  apply LinearMap.ext
  intro f
  change covariantMomentum v (matterAction f)-matterAction (covariantMomentum v f)=(-Complex.I) • matterContact v f
  rw [original_matter_momentum,add_sub_cancel_left]

private theorem adjoint_contact (v : Ambient) :
    GaussMomentumAdjoint.adjoint v*matterAction-matterAction*GaussMomentumAdjoint.adjoint v=(-Complex.I) • matterContact v := by
  apply LinearMap.ext
  intro f
  change GaussMomentumAdjoint.adjoint v (matterAction f)-matterAction (GaussMomentumAdjoint.adjoint v f)=(-Complex.I) • matterContact v f
  rw [original_matter_adjoint,add_sub_cancel_left]

private theorem product_contact {R : Type*} [Ring R] [Algebra ℂ R] (P W Q M CP CQ : R) (c : ℂ)
    (hP : P*M-M*P=c • CP) (hQ : Q*M-M*Q=c • CQ) (hW : Commute W M) :
    (P*(W*Q))*M-M*(P*(W*Q))=c • (P*(W*CQ)+CP*(W*Q)) := by
  calc
    _=P*(W*(Q*M-M*Q))+(P*M-M*P)*(W*Q) := by
      linear_combination (norm := noncomm_ring) P*hW.eq*Q
    _=_ := by rw [hP,hQ,mul_smul_comm,mul_smul_comm,smul_mul_assoc,smul_add]

/-- Literal first-order native divergence with the true independent transpose and every original gauge metric entry. -/
def gaugeMatterDivergence : End := (-Complex.I/2 : ℂ) • ∑ a : LieIndex,∑ i : Fin 3,∑ j : Fin 3,
  (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*matterContact (gaugeDirection j a))+
    matterContact (gaugeDirection i a)*
      (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a)))

/-- The complete electric/matter kinetic current consumes the source contact before taking any norm. -/
theorem original_gauge_matter_current : gaugeKinetic*matterAction-matterAction*gaugeKinetic=gaugeMatterDivergence := by
  have h (a : LieIndex) (i j : Fin 3) :
      sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*matterAction-
        matterAction*sandwich (gaugeDirection i a) (gaugeDirection j a) (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)=
      (-Complex.I) • (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
        (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*matterContact (gaugeDirection j a))+
        matterContact (gaugeDirection i a)*
          (multiply (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) :=
    product_contact _ _ _ _ _ _ _ (adjoint_contact _) (momentum_contact _) (matter_real _ _).symm
  simp only [gaugeKinetic,smul_mul_assoc,mul_smul_comm,←smul_sub,Finset.sum_mul,Finset.mul_sum,
    ←Finset.sum_sub_distrib,h,←Finset.smul_sum,smul_smul,gaugeMatterDivergence]
  congr 1
  ring

/-- All actual coframe rows and the signed scalar spatial potential remain in the geometric interaction. -/
def geometricAction : End :=
  (GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+
    (∑ a : Fin 7,GaussCoframeForm.spinSquare a)+GaussCoframeForm.numberShift)+scalarSpatialAction

private theorem interaction_split : interactionAction=geometricAction+matterAction := by
  unfold interactionAction geometricAction
  abel

/-- The matter contribution now occupies only the explicit first-order gauge divergence. -/
def matterReducedBulkCurrent : End :=
  (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
    inverseVolumeAction*(-(8 : ℂ) • ((localAction+geometricAction)*scalarKinetic-
      scalarKinetic*(localAction+geometricAction))+
      (36 : ℂ) • ((magneticAction+geometricAction)*gaugeKinetic-
        gaugeKinetic*(magneticAction+geometricAction))-
      (36 : ℂ) • gaugeMatterDivergence+
      (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction))

/-- Both native covariance and the first-order electric contact are consumed by the complete original bulk current. -/
theorem original_bulk_current_matter_reduced : bulkCurrent=matterReducedBulkCurrent := by
  have hs : (localAction+(geometricAction+matterAction))*scalarKinetic-
      scalarKinetic*(localAction+(geometricAction+matterAction))=
      (localAction+geometricAction)*scalarKinetic-scalarKinetic*(localAction+geometricAction) := by
    simp only [add_mul,mul_add]
    rw [←original_scalar_matter_commute.eq]
    module
  have hg : (magneticAction+(geometricAction+matterAction))*gaugeKinetic-
      gaugeKinetic*(magneticAction+(geometricAction+matterAction))=
      (magneticAction+geometricAction)*gaugeKinetic-gaugeKinetic*(magneticAction+geometricAction)-gaugeMatterDivergence := by
    rw [←original_gauge_matter_current]
    simp only [add_mul,mul_add]
    module
  rw [original_bulk_current_separated]
  unfold separatedBulkCurrent matterReducedBulkCurrent
  rw [interaction_split,hs,hg,smul_sub]
  congr 2
  module

/-- Same F and full raised defect; scalar matter derivatives have been removed and electric matter derivatives are explicit first-order source contacts. -/
theorem original_remaining_raised_matter_reduced (F : Index) (A : End) (q : QuantumTest) :
    remainingRaisedCurrent F A q=(sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
      (sourcePair (A q) ((matterReducedBulkCurrent-scalarCurrent) (A q))).im/2 := by
  have h := original_current_split
  rw [original_bulk_current_matter_reduced] at h
  have hr : remainingCurrent=matterReducedBulkCurrent-scalarCurrent := by
    linear_combination (norm := module) -h
  rw [remainingRaisedCurrent,hr]

end LowEnergy.SourceNativeMatterCovarianceCancellation
