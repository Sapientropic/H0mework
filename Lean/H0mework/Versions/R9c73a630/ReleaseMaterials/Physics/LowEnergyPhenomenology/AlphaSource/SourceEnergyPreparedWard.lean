import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceEnergyDiracWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalEnergyCurrentWardReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance energyPreparedWardQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open StageNineCurrentCoframeMatterTemporalPrincipal

open ActiveSector FullQuantum.FullCurrentSymbol StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum

/-- Each actual unit-ball source keeps the normalization produced by its own full Dirac response. -/
def sourceEnergyInputPacket (side edge : Fin 2) : FullMatterL2 :=
  ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) • sourceChargedSpatialPacket side edge

theorem sourceEnergyFiltered_input (side edge : Fin 2) :
    sourceChargedFilteredPacket side edge=sourcePacketDiracFilter (sourceEnergyInputPacket side edge) := by
  change sourceChargedFilter side edge (sourceChargedSpatialPacket side edge)=_
  simp only [sourceChargedFilter,sourceEnergyInputPacket,smul_apply,map_smul]

theorem sourceEnergyFiltered_fourier (side edge : Fin 2) :
    fourier (sourceChargedFilteredPacket side edge)=ᵐ[volume]
      fun k=>Retarded.diracValue 0 (physicalMomentum k) 0 1 (fourier (sourceEnergyInputPacket side edge) k) := by
  rw [sourceEnergyFiltered_input]
  exact SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) (sourceEnergyInputPacket side edge)

/-- The original projection kills the Yukawa output, using its true spin reduction. -/
private theorem sourceEnergyYukawa_projected :
    sourceVoltageFiberProjection*operator (interactionHamiltonian actual 0)=0 := by
  let C:=currentCoframeMatterTemporalPrincipalInverse (actual.coframe 0)
  have reducing : Commute ActiveSector.projection C:=
    ((spin_reducing _).smul_right Complex.I).smul_right _
  have zero : ActiveSector.projection*diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (actual.scalar 0))=0:=projection_yukawa_zero _
  have killed : ActiveSector.projection*(C*
      diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (actual.scalar 0)))=0 := by
    rw [←mul_assoc,reducing.eq,mul_assoc,zero,mul_zero]
  have source : ActiveSector.projection*interactionHamiltonian actual 0=0 := by
    unfold interactionHamiltonian interaction
    change ActiveSector.projection*(Complex.I • (-C*diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (actual.scalar 0))))=0
    rw [mul_smul_comm]
    have negative : ActiveSector.projection*(-C*diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (actual.scalar 0)))=
        -(ActiveSector.projection*(C*diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (actual.scalar 0)))) := by
      apply LinearMap.ext
      intro matter
      change ActiveSector.projection (-(C (diracDualRightChiralYukawaAction
        (scalarCoordinateEquiv.symm (actual.scalar 0)) matter)))=
        -(ActiveSector.projection (C (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (actual.scalar 0)) matter)))
      exact map_neg _ _
    rw [negative,killed]
    exact (congrArg (fun A : Module.End ℂ DiracExteriorMatterCarrier=>Complex.I • A)
      (@_root_.neg_zero (Module.End ℂ DiracExteriorMatterCarrier) inferInstance)).trans
        (_root_.smul_zero Complex.I)
  rw [sourceVoltageFiberProjection,←operator_mul,source,operator_zero]

/-- The Yukawa defect vanishes only in this actual retained pairing; the full operator remains in the general Ward law. -/
theorem sourceEnergyYukawaDefect_pair (u v : YangMills.FullPairing.Hilbert)
    (left : sourceVoltageFiberProjection u=u) (right : sourceVoltageFiberProjection v=v) :
    inner ℂ u (sourceEnergyYukawaDefect v)=0 := by
  let Y:=operator (interactionHamiltonian actual 0)
  have projection (w : YangMills.FullPairing.Hilbert) : sourceVoltageFiberProjection (Y w)=0 := by
    change (sourceVoltageFiberProjection*Y) w=0
    rw [show sourceVoltageFiberProjection*Y=0 from sourceEnergyYukawa_projected]
    rfl
  have first : inner ℂ u (Y v)=0 := by
    calc
      _=inner ℂ (sourceVoltageFiberProjection u) (Y v):=by rw [left]
      _=inner ℂ u (sourceVoltageFiberProjection (Y v)):=sourceVoltageProjection_pair _ _
      _=0:=by rw [projection,inner_zero_right]
  have second : inner ℂ u (Y.adjoint v)=0 := by
    calc
      _=inner ℂ (Y u) v:=ContinuousLinearMap.adjoint_inner_right Y u v
      _=inner ℂ (Y u) (sourceVoltageFiberProjection v):=by rw [right]
      _=inner ℂ (sourceVoltageFiberProjection (Y u)) v:=(sourceVoltageProjection_pair _ _).symm
      _=0:=by rw [projection,inner_zero_left]
  change inner ℂ u ((Y-Y.adjoint) v)=0
  rw [sub_apply,inner_sub_right,first,second,sub_zero]

private theorem sourceEnergyFiltered_retained (side edge : Fin 2) :
    (fun frequency=>sourceVoltageFiberProjection (fourier (sourceChargedFilteredPacket side edge) frequency))=ᵐ[volume]
      fourier (sourceChargedFilteredPacket side edge) := by
  have fixed : sourceVoltageFiberProjection.compLpL 2 volume (fourier (sourceChargedFilteredPacket side edge))=
      fourier (sourceChargedFilteredPacket side edge) := by
    rw [←GaugeGreen.constant_fourier]
    exact congrArg FullSpace.fourier (sourceChargedFilteredPacket_retained side edge)
  have generated:=sourceVoltageFiberProjection.coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge))
  rw [fixed] at generated
  exact generated.symm

theorem sourceEnergyPreparedYukawa_zero (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (fun frequency=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyYukawaDefect (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))))=ᵐ[volume]
      fun _=>0 := by
  have moved:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (sourceEnergyFiltered_retained sideR edgeR)
  filter_upwards [sourceEnergyFiltered_retained sideL edgeL,moved] with frequency left right
  exact sourceEnergyYukawaDefect_pair _ _ left right

/-- The full same-preparation Ward expression: damping, both original input legs and the actual Yukawa defect. -/
def sourceEnergyPreparedWardIntegrand (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (frequency : Position) : ℂ :=
  (-2*Complex.I)*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))+
    Complex.I*inner ℂ (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideL edgeL) frequency))
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))+
    Complex.I*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideR edgeR) (frequency-shift)))+
    inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyYukawaDefect (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift)))

/-- The actual independently filtered legs satisfy the original full-Green Ward identity almost everywhere. -/
theorem sourceEnergyPreparedWard_generated (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceHamiltonianTransferIntegrand shift sideL edgeL sideR edgeR=ᵐ[volume]
      sourceEnergyPreparedWardIntegrand shift sideL edgeL sideR edgeR := by
  have shifted:=(measurePreserving_sub_right volume shift).quasiMeasurePreserving.ae
    (sourceEnergyFiltered_fourier sideR edgeR)
  filter_upwards [sourceEnergyFiltered_fourier sideL edgeL,shifted] with frequency left right
  have source:=congrArg (fun A : FiberOperators=>
    inner ℂ (fourier (sourceEnergyInputPacket sideL edgeL) frequency)
      (A (fourier (sourceEnergyInputPacket sideR edgeR) (frequency-shift))))
    (sourceEnergyDiracWard_preparation (physicalMomentum frequency) (physicalMomentum (frequency-shift)))
  simp only [mul_apply_eq_comp,add_apply,smul_apply,inner_add_right,inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right] at source
  simp only [sourceHamiltonianTransferIntegrand,sourceEnergyPreparedWardIntegrand,left,right]
  exact source

theorem sourceEnergyPreparedWard_integrable (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceEnergyPreparedWardIntegrand shift sideL edgeL sideR edgeR) volume :=
  (sourceHamiltonianTransfer_integrable shift sideL edgeL sideR edgeR).congr
    (sourceEnergyPreparedWard_generated shift sideL edgeL sideR edgeR)

theorem sourceEnergyPreparedWard_integral (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    (∫frequency : Position,sourceHamiltonianTransferIntegrand shift sideL edgeL sideR edgeR frequency)=
      ∫frequency : Position,sourceEnergyPreparedWardIntegrand shift sideL edgeL sideR edgeR frequency :=
  integral_congr_ae (sourceEnergyPreparedWard_generated shift sideL edgeL sideR edgeR)

/-- The same-Phi native energy weight now returns its actual charge and all source/input Ward terms. -/
theorem sourceEnergyChannel_two_preparedWard (shift : Position) (frequency : ℝ)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR=
      (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceEnergyPreparedWardIntegrand shift sideL edgeL sideR edgeR k := by
  rw [sourceEnergyChannel_two_hamiltonian,sourceEnergyPreparedWard_integral]

/-- The original cubic retainer boundary consumes the complete actual Ward return, not a zero-current premise. -/
theorem sourceEnergyBoundary_two_preparedWard (q : PhysicalResponsePoint) (shift : Position) (frequency : ℝ)
    (nonzero : frequency≠0) (pole : sourceChargedDenominator (physicalMomentum shift) (Complex.I*(frequency:ℂ)) 2=0)
    (a b c d sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyBoundary q shift a b c d sideL edgeL sideR edgeR frequency=
      ((sourceChargedTemporalCoefficient 2:ℂ)*(2*Complex.I*(frequency:ℂ)))⁻¹*
        sourceEnergyEmitterMatrix q shift frequency 2 (a,b) (c,d)*
        ((frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR-
          ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
            ∫k : Position,sourceEnergyPreparedWardIntegrand shift sideL edgeL sideR edgeR k) := by
  rw [sourcePhysicalEnergyBoundary_two_charge_tensor q shift frequency nonzero pole,
    sourceEnergySpatialRemainder_hamiltonian,sourceEnergyPreparedWard_integral]
  simp only [sourceEnergyEmitterMatrix]
  ring

/-- Actual retained packets reduce the Ward return to its damping and two source-input legs. -/
def sourceEnergyRetainedWardIntegrand (shift : Position) (sideL edgeL sideR edgeR : Fin 2) (frequency : Position) : ℂ :=
  (-2*Complex.I)*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))+
    Complex.I*inner ℂ (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideL edgeL) frequency))
      (fourier (sourceChargedFilteredPacket sideR edgeR) (frequency-shift))+
    Complex.I*inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) frequency)
      (sourceEnergyTemporalInverse (fourier (sourceEnergyInputPacket sideR edgeR) (frequency-shift)))

theorem sourceEnergyRetainedWard_generated (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    sourceEnergyPreparedWardIntegrand shift sideL edgeL sideR edgeR=ᵐ[volume]
      sourceEnergyRetainedWardIntegrand shift sideL edgeL sideR edgeR := by
  filter_upwards [sourceEnergyPreparedYukawa_zero shift sideL edgeL sideR edgeR] with frequency zero
  simp only [sourceEnergyPreparedWardIntegrand,sourceEnergyRetainedWardIntegrand,zero,add_zero]

theorem sourceEnergyRetainedWard_integrable (shift : Position) (sideL edgeL sideR edgeR : Fin 2) :
    Integrable (sourceEnergyRetainedWardIntegrand shift sideL edgeL sideR edgeR) volume :=
  (sourceEnergyPreparedWard_integrable shift sideL edgeL sideR edgeR).congr
    (sourceEnergyRetainedWard_generated shift sideL edgeL sideR edgeR)

/-- This is an unconditional actual-state energy return; no caller supplies a zero Yukawa or spatial-current premise. -/
theorem sourceEnergyChannel_two_retainedWard (shift : Position) (frequency : ℝ)
    (sideL edgeL sideR edgeR : Fin 2) :
    (ActionNormalization.phaseMomentum:ℂ)*sourcePhysicalEnergyChannel shift (Complex.I*(frequency:ℂ)) 2 sideL edgeL sideR edgeR=
      (frequency:ℂ)*sourceFilteredChargeFormFactor shift sideL edgeL sideR edgeR-
        ((5/3:ℂ)*(ActionNormalization.phaseMomentum:ℂ))*
          ∫k : Position,sourceEnergyRetainedWardIntegrand shift sideL edgeL sideR edgeR k := by
  rw [sourceEnergyChannel_two_preparedWard,
    integral_congr_ae (sourceEnergyRetainedWard_generated shift sideL edgeL sideR edgeR)]

end LowEnergy.PreparationPhysicalEnergyCurrentWardReturn
