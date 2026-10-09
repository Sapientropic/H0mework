import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualChargeColumns

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
local instance actualPhaseFilteredIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open Stage9DEF Stage9DEF.Compatibility

private theorem source_basis (i : Source.Index) :
    Quantum.wholeBasis ⟨i.1,Sum.inr (Sum.inl (sourceColorDoubletIndex i.2))⟩=
      Stage9DEF.Compatibility.embed (Pi.single i 1) := by
  rcases i with ⟨s,e⟩
  unfold Quantum.wholeBasis
  rw [Pi.basis_apply]
  funext spin
  by_cases same : spin=s
  · rw [same]
    fin_cases e <;>
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq]
  · fin_cases e <;>
      simp [Quantum.internalBasis,Module.Basis.prod_apply,Stage9DEF.Compatibility.embed,
        sourceColorDiracMatter,sourceColorDoubletMatter,Pi.single_apply,Prod.mk.injEq] at same ⊢

/-- Every original eight-source vector stays outside the half-charge sector; the full 252 spectrum is unchanged. -/
theorem sourceActualEight_half_zero (v : Source.Index→ℂ) :
    sourcePhaseProjection 1 (Stage9DEF.Compatibility.embed v)=0 := by
  have basis (i : Source.Index) : sourcePhaseProjection 1 (Stage9DEF.Compatibility.embed (Pi.single i 1))=0 := by
    rw [←source_basis]
    let qi : Quantum.Index:=⟨i.1,Sum.inr (Sum.inl (sourceColorDoubletIndex i.2))⟩
    have bad : sourceWholeWeight qi≠sourcePhaseLevel 1 := by
      have weight : (sourceWholeWeight qi:ℂ)= -(sourceActualPhaseCharge i.2:ℂ) :=
        sourceActualColumn_weight 0 i.2
      intro same
      rw [same] at weight
      rcases i with ⟨spin,e⟩
      fin_cases e <;> norm_num [sourceActualPhaseCharge,sourcePhaseLevel] at weight
    apply Quantum.coordinates.injective
    ext j
    rw [sourcePhaseProjection_coordinates]
    by_cases same : j=qi
    · subst j
      simp [bad,Quantum.coordinates]
    · change j≠⟨i.1,Sum.inr (Sum.inl (sourceColorDoubletIndex i.2))⟩ at same
      simp [Quantum.coordinates,same,eq_comm]
  have split : v=∑i : Source.Index,v i • Pi.single i 1 := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [split,map_sum]
  simp only [map_sum,map_smul,basis,smul_zero,Finset.sum_const_zero]

/-- The actual full Dirac filter, including its C0 inverse, retains all eight poles while producing zero half-sector amplitude. -/
theorem sourceActualFiltered_half_zero (side edge : Fin 2) :
    sourcePhaseSpatial 1 (sourceChargedFilteredPacket side edge)=0 := by
  apply fourier.injective
  rw [sourcePhaseSpatial,FullQuantum.GaugeGreen.constant_fourier,map_zero]
  apply Lp.ext
  filter_upwards [(sourcePhaseFiber 1).coeFn_compLpL (fourier (sourceChargedFilteredPacket side edge)),
    sourceActualFilteredPacket_poles side edge,Lp.coeFn_zero (E:=Hilbert) (μ:=volume) (p:=2)] with k acted poles zero
  rw [acted,poles,zero]
  simp only [map_sum,map_smul,sourcePhaseFiber,operator_coordinates,sourceActualEight_half_zero,
    map_zero,smul_zero,Finset.sum_const_zero,Pi.zero_apply]

theorem sourceActualFiltered_half_share (side edge : Fin 2) :
    sourcePhasePreparedShare 1 side edge=0 := by
  rw [sourcePhasePreparedShare,sourceActualFiltered_half_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem sourceActualFiltered_unit_neutral (side edge : Fin 2) :
    sourcePhasePreparedShare 0 side edge+sourcePhasePreparedShare 2 side edge=1 := by
  have generated:=sourcePhasePreparedShare_total side edge
  simpa only [Fin.sum_univ_three,sourceActualFiltered_half_share,add_zero] using generated

/-- The same full current has an actual unit-sector matrix element, without imposing charge purity on the filtered state. -/
theorem sourceActualFiltered_current (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
        (sourcePhaseSpatial 0 (sourceChargedFilteredPacket sideR edgeR)) := by
  rw [sourcePhaseActualCurrent_generated,Fin.sum_univ_three,sourceActualFiltered_half_zero]
  norm_num [sourcePhaseLevel,Matrix.cons_val_two]

theorem sourceActualFiltered_current_diagonal (side edge : Fin 2) :
    sourceChargedQuantumRead side edge side edge sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*(sourcePhasePreparedShare 0 side edge:ℂ) := by
  rw [sourceActualFiltered_current,sourcePhasePreparedShare_return]

/-- The unit-sector read is still the original complete eight-by-eight spectral current. -/
theorem sourceActualFiltered_current_poles (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*
        ∫k,sourcePhasePolePair 0 sideL edgeL sideR edgeR k := by
  rw [sourceActualFiltered_current,sourcePhasePair_poles]

end LowEnergy.PreparationPhysicalActualPhaseChargeReturn
