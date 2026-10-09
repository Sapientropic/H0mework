import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualFilteredCharge

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualPhaseChargeReturn
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
local instance actualPhaseTorqueIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalNativePhaseChargeInventory
open SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction

open Stage9DEF Stage9DEF.Compatibility PreparationVacuumActualSpatialPacket
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel SourceCoulomb

def sourceActualChargeFiber : FiberOperators := Electromagnetic.CanonicalPacket.densityReader sourcePhaseNoether

def sourceActualChargeSpatial : FullMatterL2→L[ℂ]FullMatterL2 := sourceActualChargeFiber.compLpL 2 volume

theorem sourceActualCharge_maker (side edge : Fin 2) :
    sourceActualChargeFiber (naturalCoordinates (sourceChargedRestriction side edge))=
      (sourceActualPhaseCharge edge:ℂ) • naturalCoordinates (sourceChargedRestriction side edge) := by
  have generated:=congrArg naturalCoordinates (sourceActualRestriction_noether side edge)
  simpa only [sourceActualChargeFiber,Electromagnetic.CanonicalPacket.densityReader,operator_coordinates,map_smul] using generated

/-- The original unit spatial maker carries its source-generated charge before the Dirac filter. -/
theorem sourceActualCharge_packet (side edge : Fin 2) :
    sourceActualChargeSpatial (sourceChargedSpatialPacket side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedSpatialPacket side edge := by
  apply Lp.ext
  filter_upwards [sourceActualChargeFiber.coeFn_compLpL (sourceChargedSpatialPacket side edge),
    sourcePacketShape_original (naturalCoordinates (sourceChargedRestriction side edge)),
    Lp.coeFn_smul (sourceActualPhaseCharge edge:ℂ) (sourceChargedSpatialPacket side edge)] with x reader shape scaled
  change sourceActualChargeFiber.compLpL 2 volume (sourceChargedSpatialPacket side edge) x=_
  rw [reader,scaled]
  simp only [Pi.smul_apply]
  change sourceChargedSpatialPacket side edge x=_ at shape
  rw [shape,map_smul,sourceActualCharge_maker]
  exact smul_comm _ _ _

/-- The original independent spatial matter and dual give the source charge density in the same action unit. -/
theorem sourceActualPacket_current (side edge : Fin 2) (x : Point) :
    sourceChargedPacketDual side edge x (sourcePhaseNoether (sourceChargedPacketMatter side edge x))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edge:ℂ)*
        (sourcePacketDensity x:ℂ) := by
  simp only [sourceChargedPacketDual,sourceChargedPacketMatter,LinearMap.smul_apply,
    LinearMap.comp_apply,map_smul,smul_eq_mul]
  rw [sourceActualIndependent_current]
  by_cases inside : WithLp.toLp 2 x ∈ Metric.ball (0:FullSpace.Position) 1
  · simp only [sourceChargedPacketAmplitude,if_pos inside,sourcePacketDensity,sourcePacketDensityE,
      indicator_of_mem inside,Complex.star_def,Complex.conj_ofReal]
    push_cast
    ring
  · simp [sourceChargedPacketAmplitude,sourcePacketDensity,sourcePacketDensityE,inside]

def sourceActualChargeCorrection (side edge : Fin 2) : FullMatterL2 :=
  (sourceActualChargeSpatial*sourceChargedFilter side edge-
    sourceChargedFilter side edge*sourceActualChargeSpatial) (sourceChargedSpatialPacket side edge)

/-- The actual normalized filter returns its exact charge-transition amplitude. -/
theorem sourceActualCharge_filtered (side edge : Fin 2) :
    sourceActualChargeSpatial (sourceChargedFilteredPacket side edge)=
      (sourceActualPhaseCharge edge:ℂ) • sourceChargedFilteredPacket side edge+
        sourceActualChargeCorrection side edge := by
  simp only [sourceActualChargeCorrection,sub_apply,mul_apply_eq_comp,sourceActualCharge_packet,
    map_smul,sourceChargedFilteredPacket]
  abel

/-- The original h-current on both actual legs retains the complete filter correction. -/
theorem sourceActualCharge_current (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourceActualPhaseCharge edgeR:ℂ)*
        inner ℂ (sourceChargedFilteredPacket sideL edgeL) (sourceChargedFilteredPacket sideR edgeR)+
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
        (sourceActualChargeCorrection sideR edgeR) := by
  rw [sourceChargedQuantumRead_generated]
  change inner ℂ _ (((Stage10.ActionNormalization.phaseMomentum:ℂ) • sourceActualChargeSpatial) _)=_
  rw [smul_apply,inner_smul_right,sourceActualCharge_filtered,inner_add_right,inner_smul_right]
  ring

def sourceActualChargeDiracTorque (p : Fin 3→ℝ) : FiberOperators :=
  operator (diracKernel actual 0 p (Retarded.spectralParameter 0 1))*sourceActualChargeFiber-
    sourceActualChargeFiber*operator (diracKernel actual 0 p (Retarded.spectralParameter 0 1))

/-- Both original Dirac inverse identities pay the exact noncommuting charge insertion. -/
theorem sourceActualCharge_green (p : Fin 3→ℝ) :
    sourceActualChargeFiber*Retarded.diracValue 0 p 0 1=
      Retarded.diracValue 0 p 0 1*sourceActualChargeFiber+
      Retarded.diracValue 0 p 0 1*sourceActualChargeDiracTorque p*Retarded.diracValue 0 p 0 1 := by
  have inverse:=Retarded.diracValue_two_sided 0 p 0 1 (by norm_num)
  rw [sourceActualChargeDiracTorque,mul_sub,sub_mul]
  calc
    _=Retarded.diracValue 0 p 0 1*sourceActualChargeFiber+
      (Retarded.diracValue 0 p 0 1*operator (diracKernel actual 0 p (Retarded.spectralParameter 0 1)))*
        sourceActualChargeFiber*Retarded.diracValue 0 p 0 1-
      Retarded.diracValue 0 p 0 1*sourceActualChargeFiber*
        (operator (diracKernel actual 0 p (Retarded.spectralParameter 0 1))*Retarded.diracValue 0 p 0 1) := by
          rw [inverse.1,inverse.2,one_mul,mul_one]
          abel
    _=_ := by noncomm_ring

attribute [local irreducible] sourceChargedFilteredPacket sourceChargedRawPacket sourceChargedSpatialPacket
  sourceActualChargeFiber sourceActualChargeCorrection sourceActualPreparedPoleWeight sourceMovingPoleValues

/-- The same eight source poles calculate the correction, with no spectral purity premise. -/
theorem sourceActualChargeCorrection_poles (side edge : Fin 2) :
    fourier (sourceActualChargeCorrection side edge)=ᵐ[volume]
      fun k=>∑state : RestStateIndex,sourceActualPreparedPoleWeight side edge k state •
        (sourceActualChargeFiber (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) state)))-
          (sourceActualPhaseCharge edge:ℂ) • naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) state))) := by
  have correction : sourceActualChargeCorrection side edge=
      sourceActualChargeSpatial (sourceChargedFilteredPacket side edge)-
        (sourceActualPhaseCharge edge:ℂ) • sourceChargedFilteredPacket side edge := by
    have generated:=sourceActualCharge_filtered side edge
    rw [generated]
    abel
  rw [correction,map_sub,sourceActualChargeSpatial,FullQuantum.GaugeGreen.constant_fourier,map_smul]
  filter_upwards [Lp.coeFn_sub
      (sourceActualChargeFiber.compLpL 2 volume (fourier (sourceChargedFilteredPacket side edge)))
      ((sourceActualPhaseCharge edge:ℂ) • fourier (sourceChargedFilteredPacket side edge)),
    sourceActualChargeFiber.coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge)),
    Lp.coeFn_smul (sourceActualPhaseCharge edge:ℂ) (fourier (sourceChargedFilteredPacket side edge)),
    sourceActualFilteredPacket_poles side edge] with k subtracted acted scaled poles
  rw [subtracted]
  simp only [Pi.sub_apply]
  rw [acted,scaled]
  simp only [Pi.smul_apply]
  rw [poles]
  simp only [map_sum,map_smul,Finset.smul_sum,smul_sub]
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro state _
  congr 1
  exact smul_comm _ _ _

/-- Unit and neutral source columns are compared through the actual filtered current, not substituted for it. -/
theorem sourceActualCharge_sector_return (side edge : Fin 2) :
    (sourcePhasePreparedShare 0 side edge:ℂ)=
      (sourceActualPhaseCharge edge:ℂ)+inner ℂ (sourceChargedFilteredPacket side edge)
        (sourceActualChargeCorrection side edge) := by
  have generated:=sourceActualCharge_current side edge side edge
  rw [sourceActualFiltered_current_diagonal,inner_self_eq_norm_sq_to_K,sourceChargedFilteredPacket_unit] at generated
  norm_num at generated
  have nonzero : (Stage10.ActionNormalization.phaseMomentum:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  apply mul_left_cancel₀ nonzero
  rw [mul_add]
  exact generated

end LowEnergy.PreparationPhysicalActualPhaseChargeReturn
