import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedMovingCoulomb

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCoulombWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource PreparationVacuumStaticSpatialSource
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullFieldRiesz
open PreparationVacuumStaticPoleResponse PreparationPhysicalStaticSpatialCouplingReturn
open ActualWholeStatic ActualEMCarrierOwn MeasureTheory Filter Set
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert
open PreparationVacuumSourcePreparedResponse PreparationVacuumFieldCovector
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open ActualDressedSourcePreparation ActualDressedSourceResponse ActualDressedJointWard ActualDressedActionPhase
open ActualDressedFullCoulomb ActualDressedMovingCoulomb CanonicalPhysicalYResolvent
open CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open scoped Matrix BigOperators Topology Matrix.Norms.Operator SchwartzMap InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull
  currentVertex chargeReader dressedJointInput sourceDressedResponse

/-- The background uses exactly the same original source profile and full propagators. -/
def dressedBackgroundCurrent (event : DressedEvent) (transfer : PhysicalMomentum) : Fin 289→ℂ :=
  fun i=>inner ℂ (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))
    (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
      (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))

def dressedBackgroundChargedCurrent (event : DressedEvent) (transfer : PhysicalMomentum) : Fin 289→ℂ :=
  fun i=>inner ℂ (chargeReader sourcePhaseGaugeLie
      (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))
    (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
      (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))+
    inner ℂ (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))
      (currentVertex (fieldBasis i) event.momentum (-transfer) event.frame event.cut event.energy event.energy
        (chargeReader sourcePhaseGaugeLie
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))))

/-- Both joint-charge endpoint reads subtract their own unchanged prepared background. -/
def dressedJointConnectedCurrent (event : DressedEvent) (transfer : PhysicalMomentum) : Fin 289→ℂ :=
  dressedJointChargedCurrent event.epsilon event.precision event.momentum (-transfer)
      event.frame event.cut event.energy event.energy-dressedBackgroundChargedCurrent event transfer

/-- The genuine scalar/input and background joint return remains on the same event. -/
def dressedJointCurrentRemainder (event : DressedEvent) (transfer : PhysicalMomentum) : Fin 289→ℂ :=
  dressedJointInputCurrent event.epsilon event.precision event.momentum (-transfer)
      event.frame event.cut event.energy event.energy+dressedBackgroundCurrent event transfer-
    dressedBackgroundChargedCurrent event transfer

theorem dressed_joint_connected_current_return (event : DressedEvent) (transfer : PhysicalMomentum) :
    dressedJointConnectedCurrent event transfer=
      dressedCurrent event transfer+dressedJointCurrentRemainder event transfer := by
  rw [dressedJointConnectedCurrent,dressed_joint_current_return]
  ext i
  simp only [Pi.sub_apply,Pi.add_apply,dressedCurrent,sourceDressedConnectedCurrent,
    dressedBackgroundCurrent,dressedJointCurrentRemainder]
  ring

/-- The joint read retains the connected observable, both cross returns and the return-return term. -/
theorem dressed_joint_whole_four_terms (detector source : DressedEvent) (transfer : PhysicalMomentum)
    (M : WholeMatrix) :
    dotProduct (dressedJointConnectedCurrent detector (-transfer)) (M*ᵥdressedJointConnectedCurrent source transfer)=
      dressedMatrixRead detector source transfer M+
      dotProduct (dressedCurrent detector (-transfer)) (M*ᵥdressedJointCurrentRemainder source transfer)+
      dotProduct (dressedJointCurrentRemainder detector (-transfer)) (M*ᵥdressedCurrent source transfer)+
      dotProduct (dressedJointCurrentRemainder detector (-transfer)) (M*ᵥdressedJointCurrentRemainder source transfer) := by
  rw [dressed_joint_connected_current_return,dressed_joint_connected_current_return,dressed_matrix_read]
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add]
  ring

/-- The complete original massless tensor consumes every joint/input remainder without replacing it by a charge eigenvalue. -/
theorem dressed_joint_static_four_terms (detector source : DressedEvent) :
    dotProduct (dressedJointConnectedCurrent detector 0) (wholeStaticLimit*ᵥdressedJointConnectedCurrent source 0)=
      -dotProduct (dressedOriginCurrent detector) (staticInverse*ᵥdressedOriginCurrent source)+
      dotProduct (dressedCurrent detector 0) (wholeStaticLimit*ᵥdressedJointCurrentRemainder source 0)+
      dotProduct (dressedJointCurrentRemainder detector 0) (wholeStaticLimit*ᵥdressedCurrent source 0)+
      dotProduct (dressedJointCurrentRemainder detector 0) (wholeStaticLimit*ᵥdressedJointCurrentRemainder source 0) := by
  simpa only [neg_zero,dressed_static_full_origin] using
    dressed_joint_whole_four_terms detector source 0 wholeStaticLimit

attribute [local irreducible] dressedCurrent sourceTestApprox fieldForm fieldJets sourceCovector

/-- This is the original action's second field derivative, separately from the Green algebraic contact. -/
theorem dressed_connected_reader_contact (event : DressedEvent) (transfer : PhysicalMomentum) (f : Field289) :
    inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (contactVertex f event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (sourceDressedUnit event.epsilon event.precision))-
      inner ℂ (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))
        (contactVertex f event.momentum (-transfer) event.frame event.cut event.energy event.energy
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))=
      (fieldJets f event.momentum
        (sourceTestApprox event.frame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
          (sourceDressedUnit event.epsilon event.precision)))
        (sourceTestApprox event.frame (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy))).second-
      (fieldJets f event.momentum
        (sourceTestApprox event.frame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))))
        (sourceTestApprox event.frame (finiteFull event.momentum event.frame event.cut event.energy
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))))).second := by
  exact congrArg₂ (fun a b : ℂ=>a-b)
    (source_dressed_contact_original event.epsilon event.precision event.momentum (-transfer)
      event.frame event.cut event.energy event.energy f)
    (contactVertex_original_pair f event.momentum (-transfer) event.frame event.cut event.energy event.energy
      (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))
      (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))

private theorem original_connected_derivative (f : Field289) (p : PhysicalMomentum) (a b c d : QuantumTest) :
    HasDerivAt (fun scale : ℝ=>fieldForm f p a b scale-fieldForm f p c d scale)
      (∑i : Fin 289,(f i:ℂ)*(sourceCovector p a b i-sourceCovector p c d i)) 0 := by
  apply ((sourceCovector_derivative f p a b).sub (sourceCovector_derivative f p c d)).congr_deriv
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The two unchanged original action pairs generate this connected field form. -/
def dressedConnectedForm (event : DressedEvent) (transfer : PhysicalMomentum) (f : Field289) : ℝ→ℂ :=
    fun scale : ℝ=>
      fieldForm f event.momentum
        (sourceTestApprox event.frame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
          (sourceDressedUnit event.epsilon event.precision)))
        (sourceTestApprox event.frame (sourceDressedResponse event.epsilon event.precision event.momentum event.frame event.cut event.energy)) scale-
      fieldForm f event.momentum
        (sourceTestApprox event.frame ((finiteFull (event.momentum-transfer) event.frame event.cut event.energy).adjoint
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision))))
        (sourceTestApprox event.frame (finiteFull event.momentum event.frame event.cut event.energy
          (GaussComposite.SourceGraph.prepared (sourceProfile event.epsilon event.precision)))) scale

attribute [local irreducible] dressedConnectedForm

/-- The actual connected observation differentiates its original action occurrence. -/
theorem dressed_connected_action_derivative (event : DressedEvent) (transfer : PhysicalMomentum) (f : Field289) :
    HasDerivAt (dressedConnectedForm event transfer f)
      (∑i : Fin 289,(f i:ℂ)*dressedCurrent event transfer i) 0 := by
  rw [dressed_current_original]
  unfold dressedConnectedForm
  simp only [Pi.sub_apply]
  exact original_connected_derivative f event.momentum _ _ _ _

/-- Actual moving exterior legs, all289 massless projection and one true Newton convolution share this source event. -/
theorem dressed_moving_origin_spatial_limit (detector source : DressedEvent)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Tendsto (fun scale : ℝ=>movingCoulombPacket detector source scale test x) (𝓝[>] 0)
      (𝓝 ((∫ y,(4*(Real.pi:ℂ)*(Real.sqrt (spatialSquare y):ℂ))⁻¹*emPacket test (x-y))*
        (-dotProduct (dressedOriginCurrent detector) (staticInverse*ᵥdressedOriginCurrent source)))) := by
  simpa only [dressed_static_full_origin] using moving_coulomb_spatial_limit detector source test x

end LowEnergy.GaussComposite.ActualDressedCoulombWard
