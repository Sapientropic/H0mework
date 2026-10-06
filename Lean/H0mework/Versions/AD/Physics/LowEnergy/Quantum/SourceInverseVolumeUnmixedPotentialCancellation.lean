import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeMixedCurrentCancellation
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeMagneticForceCancellation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceUnmixedPotentialCancellation
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourceHamiltonianVolume SourcePhysicalKineticSquare
open SourceScalarVirialBulk SourceDilationRemainder SourceScalarDoubleCurrent SourceKineticTranspose
open SourceInverseMagneticForceCancellation SourceMixedCurrentCancellation SourceScalarOscillatorAbsorption
open SourceInverseNoetherEnergy SourceScalarPositiveBulkWard
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

private theorem multiply_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • ((d z : ℂ) • f z)=(d z : ℂ) • ((c z : ℂ) • f z)
  exact smul_comm _ _ _

private theorem magnetic_smooth (z : physicalChart) : ContDiffAt ℝ ∞ magneticPotential z.val :=
  (volume_smooth.contDiffAt.div_const _).mul
    (ContDiffAt.sum (fun i _ => ContDiffAt.sum (fun j _ =>
      (inverseSpatial_smooth i j z).mul ((magneticField_smooth i).contDiffAt.inner ℝ (magneticField_smooth j).contDiffAt))))

private theorem magnetic_directional (v : Ambient) (hv : v.2=0) (f : QuantumTest) (z : physicalChart) :
    directional v (magneticAction f) z.val=(magneticPotential z.val : ℂ) • directional v f z.val := by
  have he : (magneticAction f : SourceCoordinateSlice → FockFiber)=fun x => magneticPotential x • f x := by
    funext x
    apply PiLp.ext
    intro word
    exact Complex.real_smul.symm
  rw [directional_apply,he,fderiv_fun_smul ((magnetic_smooth z).differentiableAt (by simp))
    (f.contDiff.differentiable (by simp)).differentiableAt]
  change magneticPotential z.val • fderiv ℝ f z.val (direction v z.val)+
    fderiv ℝ magneticPotential z.val (direction v z.val) • f z.val=_
  rw [original_scalar_magnetic_derivative v hv z,zero_smul,add_zero]
  apply PiLp.ext
  intro word
  exact Complex.real_smul

private theorem magnetic_momentum (v : Ambient) (hv : v.2=0) : Commute magneticAction (covariantMomentum v) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz : z ∈ physicalChart
  · change (magneticPotential z : ℂ) • ((-Complex.I) • (directional v f z+connection v z (f z)))=
      (-Complex.I) • (directional v (magneticAction f) z+connection v z ((magneticPotential z : ℂ) • f z))
    rw [magnetic_directional v hv f ⟨z,hz⟩,map_smul,←smul_add,smul_comm]
  · have h0 (q : QuantumTest) : q z=0 := image_eq_zero_of_notMem_tsupport (fun h => hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

private theorem magnetic_adjoint (v : Ambient) (hv : v.2=0) :
    Commute magneticAction (GaussMomentumAdjoint.adjoint v) := by
  apply LinearMap.ext
  intro g
  apply pair_ext
  intro f
  have hp (f g : QuantumTest) : sourcePair f (magneticAction g)=sourcePair (magneticAction f) g := by
    unfold magneticAction
    exact multiply_pair _ _ _ _
  have he := LinearMap.congr_fun (magnetic_momentum v hv).eq f
  change sourcePair f (magneticAction (GaussMomentumAdjoint.adjoint v g))=
    sourcePair f (GaussMomentumAdjoint.adjoint v (magneticAction g))
  calc
    _=sourcePair (magneticAction f) (GaussMomentumAdjoint.adjoint v g) := hp _ _
    _=sourcePair (covariantMomentum v (magneticAction f)) g := adjoint_pair _ _ _
    _=sourcePair (magneticAction (covariantMomentum v f)) g := congrArg (fun x => sourcePair x g) he.symm
    _=sourcePair (covariantMomentum v f) (magneticAction g) := (hp _ _).symm
    _=_ := (adjoint_pair _ _ _).symm

/-- The actual magnetic multiplier commutes with the full negative-weight scalar kinetic action. -/
theorem original_scalar_magnetic_commute : Commute scalarKinetic magneticAction := by
  apply Commute.symm
  unfold scalarKinetic
  apply Commute.smul_right
  apply Commute.sum_right
  intro r _
  change Commute magneticAction (GaussMomentumAdjoint.adjoint (scalarDirection r)*
    (multiply scalarWeight scalarWeight_smooth*covariantMomentum (scalarDirection r)))
  apply Commute.mul_right
  · exact magnetic_adjoint _ rfl
  · apply Commute.mul_right
    · unfold magneticAction
      exact multiply_commute _ _ _ _
    · exact magnetic_momentum _ rfl

/-- The paid local/electric-spatial source relation deletes its real multiplier and returns the true gauge kinetic commutation. -/
theorem original_gauge_local_commute : Commute gaugeKinetic localAction := by
  have he := local_electric_spatial
  have hs : Commute localAction spatialAction := by
    unfold localAction spatialAction
    exact multiply_commute _ _ _ _
  have h := he.sub_right hs
  simpa only [electricSpatial,add_sub_cancel_right] using h.symm

/-- The full coframe action retains its kinetic, four mixed currents, seven spin squares and Number shift. -/
def interactionAction : End :=
  (GaussCoframeKinetic.kinetic+GaussCoframeForm.currentAction+
    (∑ a : Fin 7,GaussCoframeForm.spinSquare a)+GaussCoframeForm.numberShift)+
    GaussMatterCore.matterAction+scalarSpatialAction

private theorem spatial_split : spatialAction=scalarSpatialAction+magneticAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  let d : ℝ := -(sourceTime 0*volume z/2*(∑ i : Fin 3,∑ j : Fin 3,
    inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)))
  change ((d+magneticPotential z : ℝ) : ℂ) • f z=(d : ℂ) • f z+(magneticPotential z : ℂ) • f z
  rw [Complex.ofReal_add,add_smul]

/-- Exact original-H source decomposition, with signed spatial and matter terms preserved. -/
theorem original_interaction_decomposition :
    diagonalAction-scalarKinetic-gaugeKinetic=localAction+magneticAction+interactionAction := by
  rw [SourceDilationRemainder.original_action_split,spatial_split]
  unfold kineticAction interactionAction GaussCoframeForm.coframeAction
  abel

/-- The full remaining current keeps each potential only against the kinetic sector that actually differentiates it. -/
def separatedBulkCurrent : End :=
  (3*Complex.I*(sourceTime 0 : ℂ)/4) • (inverseVolumeAction*dilation*inverseVolumeAction*positiveBulk)+
    inverseVolumeAction*(-(8 : ℂ) • ((localAction+interactionAction)*scalarKinetic-
      scalarKinetic*(localAction+interactionAction))+
      (36 : ℂ) • ((magneticAction+interactionAction)*gaugeKinetic-
        gaugeKinetic*(magneticAction+interactionAction))+
      (8 : ℂ) • (diagonalAction*shiftedAction-shiftedAction*diagonalAction))

/-- The magnetic/scalar and local/electric cross terms are deleted in the complete original bulk operator. -/
theorem original_bulk_current_separated : bulkCurrent=separatedBulkCurrent := by
  have hs : (localAction+magneticAction+interactionAction)*scalarKinetic-
      scalarKinetic*(localAction+magneticAction+interactionAction)=
      (localAction+interactionAction)*scalarKinetic-scalarKinetic*(localAction+interactionAction) := by
    simp only [add_mul,mul_add]
    rw [←original_scalar_magnetic_commute.eq]
    module
  have hg : (localAction+magneticAction+interactionAction)*gaugeKinetic-
      gaugeKinetic*(localAction+magneticAction+interactionAction)=
      (magneticAction+interactionAction)*gaugeKinetic-gaugeKinetic*(magneticAction+interactionAction) := by
    simp only [add_mul,mul_add]
    rw [←original_gauge_local_commute.eq]
    module
  rw [original_bulk_current_without_mixed]
  unfold unmixedBulkCurrent separatedBulkCurrent
  rw [original_interaction_decomposition,hs,hg]

/-- The same complete oscillator remainder consumes both actual potential cancellations. -/
theorem original_remaining_current_separated : remainingCurrent=separatedBulkCurrent-scalarCurrent := by
  have h := original_current_split
  rw [original_bulk_current_separated] at h
  linear_combination (norm := module) -h

/-- Original F and raised defect remain joined to the unchanged positive bulk. -/
theorem original_remaining_raised_separated (F : Index) (A : End) (q : QuantumTest) :
    remainingRaisedCurrent F A q=(sourcePair (raisedDefect F A q) (bulkAction (A q))).im-
      (sourcePair (A q) ((separatedBulkCurrent-scalarCurrent) (A q))).im/2 := by
  rw [remainingRaisedCurrent,original_remaining_current_separated]

end LowEnergy.SourceUnmixedPotentialCancellation
