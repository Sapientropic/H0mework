import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSourceResponse
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointPreparedCoupling
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMOriginWardRead

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedJointWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalFirstGaugeBackgroundReturn
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates GaussCoreHilbert GaussCoreDifferential GaussFockLift
open GaussComposite.SourceGraph Electromagnetic.Identification
open CanonicalGradedCurrent GaussQuantumMultiplier CanonicalGradedSpatialSource GaussDensityCore
open PreparationVacuumFullFieldRiesz PreparationVacuumFieldConstraintResponse
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction
open PreparationVacuumFieldCovector PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalPhysicalYResolvent
open GaussUnitaryHistory (Index)
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction Stage9C.Material.SpinPair
open PreparationPhysicalDressedSpinChargeReturn
open GaussComposite.PhysicalEMGaugeRealization GaussComposite.PhysicalEMVoltage
open GaussComposite.PhysicalEMDressedCharacter
open scoped BigOperators ContDiff InnerProductSpace Matrix
open PhysicalEMDressedPreparedRead PreparationVacuumSourcePreparedState
open CanonicalScalarPreparation PreparationChartGuard PreparationScalarCoordinates PreparationCoordinates CanonicalPreparationCutoff PreparationVacuumNativeClosure PreparationVacuumLocalizedYukawa PreparationVacuumPreparedCurrent
open MeasureTheory Filter Set GaussHistoryHilbert GaussHalfDensity

open ActualDressedSourcePreparation PreparationVacuumMixedFieldReturn
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceDressedAddition sourceProfile finiteFull

open ActualDressedSourceResponse PreparationPhysicalJointEMCouplingUnitReturn ActualEMOriginWard PreparationPhysicalPhaseGaugeRealization
open CanonicalGradedCharge CanonicalPhysicalWardCore PreparationVacuumActionDecomposition PreparationVacuumFullElectricWard PreparationVacuumFieldConstraintResponse

/-- The completed scalar variation and charged input use exactly the normalization of the actual creation unit. -/
def dressedJointInput (epsilon : ℝ) (precision : 0<epsilon) : H :=
  ((‖sourceDressedExcitation epsilon precision‖:ℂ)⁻¹*emDressedCharacter true) •
    sourceJointInputCompleted true 1 0 (sourceProfile epsilon precision)

attribute [local irreducible] dressedJointInput sourceJointInputCompleted chargeReader

theorem dressed_joint_unit_return (epsilon : ℝ) (precision : 0<epsilon) :
    chargeReader sourcePhaseGaugeLie (sourceDressedUnit epsilon precision)=
      (1/2:ℂ) • sourceDressedUnit epsilon precision+dressedJointInput epsilon precision := by
  rw [source_dressed_unit_original,sourceDressedAddition,map_smul,sourceJointCompleted_charge]
  simp only [sourceJointIncrement,if_true,smul_add,smul_smul,dressedJointInput]
  module

theorem dressed_joint_input_core (f : ScalarTest) :
    sourceJointInputCompleted true 1 0 (core f)=
      creationSource 1 0 (chargeAction sourcePhaseGaugeLie (seedSection f))+
        Complex.I • embed (sourceJointScalarTest true 1 0 (seedSection f)) := by
  rw [sourceJointInputCompleted_core]
  rfl

private theorem inverse_charge_return {V : Type*} [AddCommGroup V] [Module ℂ V]
    (R B Q : V→ₗ[ℂ]V) (v b d : V) (q : ℂ)
    (left : R (B (Q v))=Q v) (input : B v=b) (charge : Q b=q • b+d) (back : R b=v) :
    Q v=q • v+R (d+B (Q v)-Q (B v)) := by
  rw [map_sub,map_add,left,input,charge,map_add,map_smul,back]
  abel

/-- The real propagation keeps the same original scalar/input return and the actual full inverse commutator. -/
theorem dressed_joint_propagated_return (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (F : Index) (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    chargeReader sourcePhaseGaugeLie (sourceDressedResponse epsilon precision p F cut z)=
      (1/2:ℂ) • sourceDressedResponse epsilon precision p F cut z+
        finiteFull p F cut z
          (dressedJointInput epsilon precision+
            (CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1)
              (chargeReader sourcePhaseGaugeLie (sourceDressedResponse epsilon precision p F cut z))-
            chargeReader sourcePhaseGaugeLie
              ((CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1)
                (sourceDressedResponse epsilon precision p F cut z))) := by
  exact inverse_charge_return (finiteFull p F cut z).toLinearMap
    (CanonicalPhysicalSpatial.compression p F+FullYSourceCutoffVolterra.cutoff cut-z • 1).toLinearMap
    (chargeReader sourcePhaseGaugeLie).toLinearMap (sourceDressedResponse epsilon precision p F cut z)
    (sourceDressedUnit epsilon precision) (dressedJointInput epsilon precision) (1/2:ℂ)
    (congrArg (fun A : H→L[ℂ]H=>A (chargeReader sourcePhaseGaugeLie
      (sourceDressedResponse epsilon precision p F cut z))) (finiteFull_left p F cut z nonreal))
    (source_dressed_response_equation epsilon precision p F cut z nonreal)
    (dressed_joint_unit_return epsilon precision) rfl

/-- The two actual unit endpoints are acted on by the original source joint Noether reader. -/
def dressedJointChargedCurrent (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) : Fin 289→ℂ :=
  fun i=>inner ℂ (chargeReader sourcePhaseGaugeLie (sourceDressedUnit epsilon precision))
      (currentVertex (fieldBasis i) p k F cut z w (sourceDressedUnit epsilon precision))+
    inner ℂ (sourceDressedUnit epsilon precision)
      (currentVertex (fieldBasis i) p k F cut z w
        (chargeReader sourcePhaseGaugeLie (sourceDressedUnit epsilon precision)))

def dressedJointInputCurrent (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) : Fin 289→ℂ :=
  fun i=>inner ℂ (dressedJointInput epsilon precision)
      (currentVertex (fieldBasis i) p k F cut z w (sourceDressedUnit epsilon precision))+
    inner ℂ (sourceDressedUnit epsilon precision)
      (currentVertex (fieldBasis i) p k F cut z w (dressedJointInput epsilon precision))

theorem dressed_joint_current_return (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z w : ℂ) :
    dressedJointChargedCurrent epsilon precision p k F cut z w=
      sourceDressedCurrent epsilon precision p k F cut z w+
        dressedJointInputCurrent epsilon precision p k F cut z w := by
  funext i
  simp only [dressedJointChargedCurrent,dressed_joint_unit_return,inner_add_left,
    inner_smul_left,map_add,map_smul,inner_add_right,inner_smul_right,starRingEnd_apply,
    dressedJointInputCurrent,sourceDressedCurrent,Pi.add_apply]
  norm_num
  ring

/-- The full original scalar/configuration/current/pair/Yukawa Ward acts on the actual propagated source test. -/
theorem dressed_joint_original_action (epsilon : ℝ) (precision : 0<epsilon) (p k : PhysicalMomentum)
    (F : Index) (cut : ℕ) (z : ℂ) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore (p+k)-retainedCore)
        (chargeAction sourcePhaseGaugeLie (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut z)))-
      chargeAction sourcePhaseGaugeLie
        ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore)
          (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut z)))=
      configurationTorque sourcePhaseGaugeLie (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut z))+
        CanonicalPhysicalWardCore.currentAction k sourcePhaseGaugeLie (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut z))+
        pairCurrent k sourcePhaseGaugeLie (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut z))+
        yukawaTorque sourcePhaseGaugeLie (sourceTestApprox F (sourceDressedResponse epsilon precision p F cut z)) := by
  exact em_origin_original_action_ward p k _

end LowEnergy.GaussComposite.ActualDressedJointWard
