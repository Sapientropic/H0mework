import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualDiracPoleExpansion

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalChargedScatteringPoleReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open DiracExteriorMatterAction YangMills.FullPairing FullQuantum FullSpace FullQuantum.Triangular
open PreparationPhysicalJointRotationCharge PreparationVacuumElectromagneticIdentity
open PreparationPhysicalJointGeneratorEnergyReturn PreparationPhysicalChargedPacketVoltage
open PreparationPhysicalChargedPacketQuantumReturn PreparationVacuumPhysicalQuantumLockedCharge
open Electromagnetic.CanonicalCoframe MeasureTheory Filter
open scoped InnerProductSpace BigOperators Matrix

private theorem source_projector (v : Hilbert) :
    sourceInternalFiber 0 v=naturalCoordinates (embed (coordinates (naturalCoordinates.symm v))) := by
  obtain ⟨matter,rfl⟩:=naturalCoordinates.surjective v
  simp only [sourceInternalFiber,operator_coordinates,LinearMap.comp_apply,sourceInternalRotation_zero,
    Matrix.mulVecLin_apply,Matrix.one_mulVec,naturalCoordinates.symm_apply_apply]

private theorem maker_retained (side edge : Fin 2) :
    sourceInternalFiber 0 (naturalCoordinates (sourceChargedRestriction side edge))=
      naturalCoordinates (sourceChargedRestriction side edge) := by
  rw [source_projector,naturalCoordinates.symm_apply_apply]
  unfold sourceChargedRestriction
  rw [actualRestState_source,coordinates_embed]

private theorem packet_retained (side edge : Fin 2) :
    (sourceInternalFiber 0).compLpL 2 volume (sourceChargedSpatialPacket side edge)=
      sourceChargedSpatialPacket side edge := by
  apply Lp.ext
  filter_upwards [(sourceInternalFiber 0).coeFn_compLpL (sourceChargedSpatialPacket side edge),
    PreparationVacuumActualSpatialPacket.sourcePacketShape_original
      (naturalCoordinates (sourceChargedRestriction side edge))] with x read prepared
  rw [read]
  change sourceChargedSpatialPacket side edge x=_ at prepared
  rw [prepared,map_smul,maker_retained]

/-- Read from the actual Fourier transform of the original charged maker packet. -/
def sourceActualPacketFourierValues (side edge : Fin 2) (k : Position) : Source.Index→ℂ :=
  coordinates (naturalCoordinates.symm (fourier (sourceChargedSpatialPacket side edge) k))

theorem sourceActualPacketFourierValues_source (side edge : Fin 2) :
    (fun k=>naturalCoordinates (embed (sourceActualPacketFourierValues side edge k)))=ᵐ[volume]
      fourier (sourceChargedSpatialPacket side edge) := by
  have fixed:=congrArg FullSpace.fourier (packet_retained side edge)
  rw [GaugeGreen.constant_fourier] at fixed
  have read:=(sourceInternalFiber 0).coeFn_compLpL (fourier (sourceChargedSpatialPacket side edge))
  rw [fixed] at read
  simpa only [source_projector,sourceActualPacketFourierValues] using read.symm

/-- All spectral coefficients include the same existing preparation norm and temporal-principal inverse. -/
def sourceActualPreparedPoleWeight (side edge : Fin 2) (k : Position) (state : RestStateIndex) : ℂ :=
  ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ)*
    sourceActualPoleCoefficient (physicalMomentum k) (sourceActualPacketFourierValues side edge k) state *
      (Complex.I/(Retarded.spectralParameter 0 1-(sourceMovingPoleEnergy (physicalMomentum k) state:ℂ)))

/-- The existing filtered state has the full generated eight-branch expansion, not a replacement wavefunction. -/
theorem sourceActualFilteredPacket_poles (side edge : Fin 2) :
    fourier (sourceChargedFilteredPacket side edge)=ᵐ[volume]
      fun k=>∑state : RestStateIndex,sourceActualPreparedPoleWeight side edge k state •
        naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) state)) := by
  have filtered : sourceChargedFilteredPacket side edge=((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
      sourceChargedRawPacket side edge:=rfl
  rw [filtered,map_smul]
  filter_upwards [Lp.coeFn_smul ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ)
      (fourier (sourceChargedRawPacket side edge)),
    SpatialGreen.green_fourier_ae 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge),
    sourceActualPacketFourierValues_source side edge] with k scaled green source
  rw [scaled]
  change ((‖sourceChargedRawPacket side edge‖⁻¹:ℝ):ℂ) •
    fourier (SpatialGreen.green 0 0 1 (by norm_num) (sourceChargedSpatialPacket side edge)) k=_
  rw [green,←source,sourceActualDiracGreen_poles _ 0 1 (by norm_num)]
  simp only [Finset.smul_sum,smul_smul,sourceActualPreparedPoleWeight,mul_assoc]

/-- Every original coordinate leg has its source Fourier momentum factor; the time-independent first leg is one. -/
def sourceActualCoordinateMomentum (i : Fin 4) (p : Fin 3→ℝ) : ℂ :=
  Fin.cases 1 (fun j=>(p j:ℂ)) i

private theorem coordinate_affine (i : Fin 4) (p : Fin 3→ℝ) :
    affine (coordinateCoefficients i) p=sourceActualCoordinateMomentum i p • (1:FiberOperators) := by
  apply ContinuousLinearMap.ext
  intro v
  fin_cases i <;>
    simp [affine,coordinateCoefficients,sourceActualCoordinateMomentum,Fin.sum_univ_three,
      Fin.cases,Fin.induction,Fin.induction.go,smul_apply,add_apply,one_apply_eq_self]

/-- These are exactly the external legs already present in both ordered vertices and the mixed contact. -/
theorem sourceActualScatteringCoordinateLeg_fourier (side edge : Fin 2) (i : Fin 4) :
    fourier (coordinateLeg i (sourceActualScatteringInput side edge))=ᵐ[volume]
      fun k=>sourceActualCoordinateMomentum i (physicalMomentum k) •
        fourier (sourceChargedFilteredPacket side edge) k := by
  have first:=spatialLeg_fourier (coordinateCoefficients 0) (sourceActualScatteringInput side edge)
  change fourier (coordinateLeg 0 (sourceActualScatteringInput side edge))=ᵐ[volume] _ at first
  rw [sourceActualScatteringInput_return] at first
  filter_upwards [spatialLeg_fourier (coordinateCoefficients i) (sourceActualScatteringInput side edge),first]
    with k actual original
  change fourier (coordinateLeg i (sourceActualScatteringInput side edge)) k=_ at actual
  rw [actual,coordinate_affine,smul_apply,one_apply_eq_self]
  rw [original,coordinate_affine]
  simp only [sourceActualCoordinateMomentum,Fin.cases_zero,one_smul,one_apply_eq_self]

/-- All four original scattering legs consume the same eight source poles and the original normalization. -/
theorem sourceActualScatteringCoordinateLeg_poles (side edge : Fin 2) (i : Fin 4) :
    fourier (coordinateLeg i (sourceActualScatteringInput side edge))=ᵐ[volume]
      fun k=>∑state : RestStateIndex,
        (sourceActualCoordinateMomentum i (physicalMomentum k)*sourceActualPreparedPoleWeight side edge k state) •
          naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) state)) := by
  filter_upwards [sourceActualScatteringCoordinateLeg_fourier side edge i,sourceActualFilteredPacket_poles side edge]
    with k leg poles
  rw [leg,poles,Finset.smul_sum]
  simp only [smul_smul]

end LowEnergy.PreparationPhysicalChargedScatteringPoleReturn
