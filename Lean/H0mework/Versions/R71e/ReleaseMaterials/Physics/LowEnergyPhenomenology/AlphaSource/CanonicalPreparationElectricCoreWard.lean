import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationElectricPairCurrent

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFullElectricWard
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceQuantumScalarChart GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalGradedCharge
open CanonicalPhysicalWardCore GaussDiagonalHistory
open GaussUnitaryHistory (Index sourceFilter)
open FullYSourceCutoffVolterra (cutoff)
open Filter
open scoped Topology InnerProductSpace

theorem physical_full_ward (p k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    physicalAction (p+k) (chargeAction a f)-chargeAction a (physicalAction p f)=
      configurationTorque a f+CanonicalPhysicalWardCore.currentAction k a f+pairCurrent k a f := by
  have comm:=LinearMap.congr_fun (momentum_charge_commutes p a).eq f
  change momentumAction p (chargeAction a f)=chargeAction a (momentumAction p f) at comm
  simp only [physicalAction,momentumAction_add,LinearMap.add_apply,map_add,
    configurationTorque,LinearMap.sub_apply,LinearMap.comp_apply]
  rw [comm,full_current]
  abel

def yukawaTorque (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  GaussYukawaOperator.originalAction.comp (chargeAction a)-
    (chargeAction a).comp GaussYukawaOperator.originalAction

def wardCore (k : PhysicalMomentum) (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  configurationTorque a+CanonicalPhysicalWardCore.currentAction k a+pairCurrent k a+yukawaTorque a

theorem original_full_ward (p k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    (physicalAction (p+k)+GaussYukawaOperator.originalAction) (chargeAction a f)-
      chargeAction a ((physicalAction p+GaussYukawaOperator.originalAction) f)=wardCore k a f := by
  simp only [LinearMap.add_apply,map_add,wardCore,yukawaTorque,
    LinearMap.sub_apply,LinearMap.comp_apply]
  have h:=physical_full_ward p k a f
  rw [←h]
  abel

theorem original_action_components (p k : PhysicalMomentum) (a : NativeLie) (f : QuantumTest) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
      PreparationVacuumActionDecomposition.actualCore (p+k)-PreparationVacuumActionDecomposition.retainedCore)
        (chargeAction a f)-
    chargeAction a ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
      PreparationVacuumActionDecomposition.actualCore p-PreparationVacuumActionDecomposition.retainedCore) f)=
    wardCore k a f := by
  rw [←PreparationVacuumActionDecomposition.physical_action_decomposition,
    ←PreparationVacuumActionDecomposition.physical_action_decomposition]
  exact original_full_ward p k a f

def compressionDefect (p : PhysicalMomentum) (F : Index) (f : QuantumTest) : H :=
  compression p F (embed f)-embed (physicalAction p f)

def yukawaCutDefect (cut : ℕ) (f : QuantumTest) : H :=
  cutoff cut (embed f)-embed (GaussYukawaOperator.originalAction f)

def wardDefect (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (F : Index)
    (f : QuantumTest) : H :=
  compressionDefect (p+k) F (chargeAction a f)-chargeReader a (compressionDefect p F f)+
    yukawaCutDefect cut (chargeAction a f)-chargeReader a (yukawaCutDefect cut f)

theorem finite_full_core (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ) (F : Index)
    (f : QuantumTest) :
    CanonicalPhysicalWard.finiteInsertion p k a cut F (embed f)=
      embed (wardCore k a f)+wardDefect p k a cut F f := by
  have core:=congrArg embed (original_full_ward p k a f)
  simp only [map_sub,LinearMap.add_apply,map_add] at core
  unfold CanonicalPhysicalWard.finiteInsertion wardDefect compressionDefect yukawaCutDefect
  simp only [sub_apply,add_apply,mul_apply_eq_comp,map_sub,map_add,
    CanonicalGradedCharge.chargeReader_core]
  rw [←core]
  abel

theorem compressionDefect_eventually (p : PhysicalMomentum) (f : QuantumTest) :
    ∀ᶠ F in sourceFilter,compressionDefect p F f=0 := by
  filter_upwards [eventually_exact p (coreEquiv f)] with F h
  change compression p F (embed f)=physical p (coreEquiv f) at h
  have original : physical p (coreEquiv f)=embed (physicalAction p f) := by
    change embed (physicalAction p (coreEquiv.symm (coreEquiv f)))=_
    rw [coreEquiv.symm_apply_apply]
  rw [original] at h
  exact sub_eq_zero.mpr h

theorem finite_full_core_eventually (p k : PhysicalMomentum) (a : NativeLie) (cut : ℕ)
    (f : QuantumTest) :
    ∀ᶠ F in sourceFilter,CanonicalPhysicalWard.finiteInsertion p k a cut F (embed f)=
      embed (wardCore k a f)+yukawaCutDefect cut (chargeAction a f)-
        chargeReader a (yukawaCutDefect cut f) := by
  filter_upwards [compressionDefect_eventually (p+k) (chargeAction a f),
    compressionDefect_eventually p f] with F hleft hright
  rw [finite_full_core,wardDefect,hleft,hright,map_zero,sub_zero,zero_add]
  abel

end LowEnergy.PreparationVacuumFullElectricWard
