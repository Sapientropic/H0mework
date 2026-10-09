import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFilteredSoftCharge

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFilteredLockedChargeReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction DiracCliffordRepresentation YangMills.FullPairing
open FullQuantum FullSpace FullQuantum.Triangular FullQuantum.StateGreen
open Stage10.CanonicalMatter StageNineHolonomicField
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumElectromagneticIdentity PreparationVacuumChargedPacketGreen PreparationVacuumActualSpatialPacket
open PreparationPhysicalChargedPacketVoltage PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalFilteredChargeVoltage
open MeasureTheory Filter
open scoped InnerProductSpace Topology BigOperators

/-- This is the original locked current's canonical momentum dual, not nativeY renamed. -/
def sourceLockedFiberCharge : FiberOperators := operator (sourceLockedCurrentDirection 0 2)

def sourceLockedSpatialCharge : FullMatterL2→L[ℂ] FullMatterL2:=sourceLockedFiberCharge.compLpL 2 volume

def sourceLockedDiracMatrix (p : Fin 3→ℝ) : FiberOperators :=
  operator (diracKernel actual 0 p (Retarded.spectralParameter 0 1))

/-- The whole original Dirac operator supplies this torque, including principal and zero-order terms. -/
def sourceLockedDiracTorque (p : Fin 3→ℝ) : FiberOperators :=
  sourceLockedDiracMatrix p*sourceLockedFiberCharge-sourceLockedFiberCharge*sourceLockedDiracMatrix p

/-- Both original inverse identities generate the sign and order of the charge correction. -/
theorem sourceLockedGreen_commutator (p : Fin 3→ℝ) :
    sourceLockedFiberCharge*Retarded.diracValue 0 p 0 1=
      Retarded.diracValue 0 p 0 1*sourceLockedFiberCharge+
      Retarded.diracValue 0 p 0 1*sourceLockedDiracTorque p*Retarded.diracValue 0 p 0 1 := by
  have inverse:=Retarded.diracValue_two_sided 0 p 0 1 (by norm_num)
  change sourceLockedDiracMatrix p*Retarded.diracValue 0 p 0 1=1 ∧
    Retarded.diracValue 0 p 0 1*sourceLockedDiracMatrix p=1 at inverse
  rw [sourceLockedDiracTorque,mul_sub,sub_mul]
  calc
    _=Retarded.diracValue 0 p 0 1*sourceLockedFiberCharge+
      (Retarded.diracValue 0 p 0 1*sourceLockedDiracMatrix p)*sourceLockedFiberCharge*Retarded.diracValue 0 p 0 1-
      Retarded.diracValue 0 p 0 1*sourceLockedFiberCharge*(sourceLockedDiracMatrix p*Retarded.diracValue 0 p 0 1) := by
        rw [inverse.1,inverse.2,one_mul,mul_one]
        abel
    _=_ := by noncomm_ring

theorem sourceLockedChargedMaker (side edge : Fin 2) :
    sourceLockedFiberCharge (naturalCoordinates (sourceChargedRestriction side edge))=
      -(sourceChargedPolarity edge:ℂ) • naturalCoordinates (sourceChargedRestriction side edge) := by
  have native : diracExteriorMotherLieAction
      (SU7MotherLieAlgebra.p286LieBlockEmbed HyperchargeResponse.chargeDirection)
      (sourceChargedRestriction side edge)=Complex.I • sourceChargedRestriction side edge := by
    unfold sourceChargedRestriction
    rw [actualRestState_source,actualRestStateCoordinates]
    exact GaussComposite.source_embedding_charge _
  rw [sourceLockedFiberCharge,operator_coordinates]
  simp only [sourceLockedCurrentDirection,sourceLockedCurrent,LinearMap.comp_apply,LinearMap.smul_apply,
    map_smul,diracGamma,Matrix.cons_val_zero,phase_inverse_source]
  rw [sourceChargedRestriction_locked,native]
  simp only [map_smul,smul_smul]
  congr 1
  ring_nf
  simp only [Complex.I_sq,neg_one_mul]

/-- The original unit-ball preparation has the actual source polarity before filtering. -/
theorem sourceLockedSpatialPacket (side edge : Fin 2) :
    sourceLockedSpatialCharge (sourceChargedSpatialPacket side edge)=
      -(sourceChargedPolarity edge:ℂ) • sourceChargedSpatialPacket side edge := by
  apply Lp.ext
  filter_upwards [sourceLockedFiberCharge.coeFn_compLpL (sourceChargedSpatialPacket side edge),
    sourcePacketShape_original (naturalCoordinates (sourceChargedRestriction side edge)),
    Lp.coeFn_smul (-(sourceChargedPolarity edge:ℂ)) (sourceChargedSpatialPacket side edge)] with x reader shape scaled
  change sourceLockedFiberCharge.compLpL 2 volume (sourceChargedSpatialPacket side edge) x=_
  rw [reader,scaled]
  simp only [Pi.smul_apply]
  change sourceChargedSpatialPacket side edge x=_ at shape
  rw [shape,map_smul,sourceLockedChargedMaker]
  exact smul_comm (sourcePacketShape x) (-(sourceChargedPolarity edge:ℂ))
    (naturalCoordinates (sourceChargedRestriction side edge))

theorem sourceLockedPacket_fourier (side edge : Fin 2) :
    (fun k=>sourceLockedFiberCharge (fourier (sourceChargedSpatialPacket side edge) k))=ᵐ[volume]
      fun k=>-(sourceChargedPolarity edge:ℂ) • fourier (sourceChargedSpatialPacket side edge) k := by
  have original:=congrArg FullSpace.fourier (sourceLockedSpatialPacket side edge)
  rw [sourceLockedSpatialCharge,GaugeGreen.constant_fourier,map_smul] at original
  have read:=sourceLockedFiberCharge.coeFn_compLpL (fourier (sourceChargedSpatialPacket side edge))
  rw [original] at read
  exact read.symm.trans (Lp.coeFn_smul _ _)

end LowEnergy.PreparationPhysicalFilteredLockedChargeReturn
