import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceModeGaussRead
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationWeightedChargeCoreWard

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalLockedGaussBalance
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.StateGreen FullQuantum.CoframeResponse
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumSourceActionJets PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumMixedFieldReturn PreparationVacuumRawJointFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumPhysicalModeChargeRead
open PreparationVacuumPhysicalElectromagneticDirection PreparationVacuumWeightedChargeActionWard
open PreparationVacuumFullElectricWard PreparationVacuumPhysicalLockedCurrentFirstResidue
open CanonicalGradedSpatialSource PreparationVacuumNonlinearFieldCurve
open Filter Set MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology ContDiff
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local irreducible] sourceLockedAction sourceLockedField sourceActionWeight
  weightFiber weightCore sourceWeightSymbol

/-- The fixed source gauge plus spin action supplies both original independent-dual branches. -/
def sourceLockedChargeMatrix : FullMatrix :=
  realFourierMatrix (fun k : Fin 4=>if k=0 then Complex.I •
    Quantum.operatorMatrix (sourceLockedAction 2) else 0) 0

theorem sourceLocked_normalized_density (s : ActionState) (valid : s∈validStates) (k : Fin 4) :
    statePhase s*densityVariation (sourceLockedField 0 2) s k=
      if k=0 then Complex.I • Quantum.operatorMatrix (sourceLockedAction 2) else 0 := by
  rw [sourceLockedField_density 0 2 s valid.1 k]
  split_ifs with same
  · rw [←principalMatrix_coefficient]
    have unit:=principalMatrix_regular s.1 valid.2
    have volume : stateVolume s≠0:=Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr valid.1)
    unfold statePhase
    rw [smul_mul_assoc,mul_smul_comm,←mul_assoc,Ring.inverse_mul_cancel _ unit,one_mul,smul_smul]
    congr 1
    field_simp
  · rw [mul_zero]

theorem sourceLockedCharge_fourier (p : PhysicalMomentum) :
    realFourierMatrix (fun k : Fin 4=>if k=0 then Complex.I •
      Quantum.operatorMatrix (sourceLockedAction 2) else 0) p=sourceLockedChargeMatrix := by
  simp [realFourierMatrix,affineMatrix,sourceLockedChargeMatrix]

theorem sourceLockedRawCharge_generated (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    rawActionSymbol (sourceLockedField 0 2) p s=
      (4:ℂ) • (sourceActionWeight s*sourceLockedChargeMatrix) := by
  unfold rawActionSymbol
  rw [raw_source_weight _ p s valid.1 valid.2]
  simp_rw [sourceLocked_normalized_density s valid]
  change (4:ℂ) • (sourceActionWeight s*realFourierMatrix _ p)=_
  rw [sourceLockedCharge_fourier]

def sourceLockedChargeFiber : FockFiber→L[ℂ] FockFiber:=quantizer sourceLockedChargeMatrix

def sourceLockedPairFiber (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber:=
  pairFiber (sourceWeightSymbol z) sourceLockedChargeMatrix

def sourceLockedRawChargeFiber (z : SourceCoordinateSlice) : FockFiber→L[ℂ] FockFiber:=
  rawFiber (sourceLockedField 0 2) 0 (0,z)

/-- Normal ordering keeps the full pair term on the original Fock carrier. -/
theorem sourceLockedRawCharge_fullCAR (z : physicalChart) :
    sourceLockedRawChargeFiber z.val=weightFiber z.val*sourceLockedChargeFiber-sourceLockedPairFiber z.val := by
  unfold sourceLockedRawChargeFiber rawFiber
  rw [ambientState_zero,sourceLockedRawCharge_generated 0 _ (sourceState_valid z),←smul_mul_assoc]
  rw [←sourceWeightSymbol]
  have paid:=quantized_normal_order (sourceWeightSymbol z.val) sourceLockedChargeMatrix
  simpa only [weightFiber,sourceLockedChargeFiber,sourceLockedPairFiber,
    GaussQuantumMultiplier.quantizer,LinearMap.coe_mk,AddHom.coe_mk] using eq_sub_of_add_eq paid.symm

theorem sourceLockedRawChargeFiber_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ sourceLockedRawChargeFiber z.val := by
  have valid : ambientState (0,z.val)∈validStates:=by rw [ambientState_zero];exact sourceState_valid z
  exact (rawFiber_smooth (sourceLockedField 0 2) 0 (0,z.val) valid).comp z.val
    (contDiffAt_const.prodMk contDiffAt_id)

theorem sourceLockedPairFiber_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ sourceLockedPairFiber z.val := by
  have formula (x : SourceCoordinateSlice) : sourceLockedPairFiber x=
      weightFiber x*sourceLockedChargeFiber-quantizer (sourceWeightSymbol x*sourceLockedChargeMatrix) := by
    unfold sourceLockedPairFiber weightFiber sourceLockedChargeFiber
    exact eq_sub_of_add_eq' (quantized_normal_order _ _).symm
  have same : sourceLockedPairFiber=fun x=>weightFiber x*sourceLockedChargeFiber-
      quantizer (sourceWeightSymbol x*sourceLockedChargeMatrix):=funext formula
  rw [same]
  exact ((weightFiber_smooth z).mul contDiffAt_const).sub
    ((quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val
      ((sourceWeightSymbol_smooth z).mul contDiffAt_const))

def sourceLockedChargeCore : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier (fun _=>sourceLockedChargeFiber) (fun _=>contDiffAt_const)

def sourceLockedPairCore : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier sourceLockedPairFiber sourceLockedPairFiber_smooth

def sourceLockedRawChargeCore : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier sourceLockedRawChargeFiber sourceLockedRawChargeFiber_smooth

/-- The generated raw locked charge acts on the same full Gauss core, with no sector premise. -/
theorem sourceLockedRawCore_generated :
    sourceLockedRawChargeCore=weightCore.comp sourceLockedChargeCore-sourceLockedPairCore := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [sourceLockedRawChargeCore,weightCore,sourceLockedChargeCore,sourceLockedPairCore,
    LinearMap.sub_apply,LinearMap.comp_apply]
  change sourceLockedRawChargeFiber z (f z)=weightFiber z (sourceLockedChargeFiber (f z))-
    sourceLockedPairFiber z (f z)
  by_cases inside : z∈physicalChart
  · rw [sourceLockedRawCharge_fullCAR ⟨z,inside⟩]
    simp only [sub_apply,mul_apply_eq_comp]
  · have outside : f z=0:=image_eq_zero_of_notMem_tsupport (fun hz=>inside (f.tsupport_subset hz))
    rw [outside,map_zero,map_zero,map_zero,map_zero,sub_zero]

end LowEnergy.PreparationVacuumPhysicalLockedGaussBalance
