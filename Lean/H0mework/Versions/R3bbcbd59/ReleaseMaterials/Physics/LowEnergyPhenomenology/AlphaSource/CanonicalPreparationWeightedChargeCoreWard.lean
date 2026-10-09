import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourcePreparedChargeAction
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationElectricCoreWard
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationActionFieldLift

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumWeightedChargeActionWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open CanonicalGradedSpatialSource CanonicalPhysicalSpatial CanonicalGradedCharge
open PreparationVacuumSourceFieldFamily PreparationVacuumSourceActionJets PreparationVacuumNoetherChart
open PreparationVacuumSourceChargeWard PreparationVacuumTemporalCharge PreparationVacuumLowerClassical
open PreparationVacuumFullElectricWard PreparationVacuumActionFieldLift PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumNonlinearFieldCurve
open FullQuantum.StateGreen PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
abbrev WardFiberMap:=FockFiber→L[ℂ] FockFiber
local instance : NormedAlgebra ℝ WardFiberMap:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] sourceActionWeight rawActionSymbol rawMomentumMatrix

def sourceWeightSymbol (z : SourceCoordinateSlice) : FullMatrix:=(4:ℂ) • sourceActionWeight (sourceState z)

theorem sourceWeightSymbol_smooth (z : physicalChart) : ContDiffAt ℝ ∞ sourceWeightSymbol z.val:=
  ((sourceActionWeight_smooth _ (sourceState_valid z)).comp z.val sourceState_smooth.contDiffAt).const_smul (4:ℂ)

def weightFiber (z : SourceCoordinateSlice) : WardFiberMap:=quantizer (sourceWeightSymbol z)
def normalChargeFiber (a : Fin 12) (z : SourceCoordinateSlice) : WardFiberMap:=
  pairFiber (sourceWeightSymbol z) (chargeMatrix (originalUnit a))
def rawChargeFiber (a : Fin 12) (z : SourceCoordinateSlice) : WardFiberMap:=
  rawFiber (temporalField a) 0 (0,z)

theorem weightFiber_smooth (z : physicalChart) : ContDiffAt ℝ ∞ weightFiber z.val:=
  (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val (sourceWeightSymbol_smooth z)

private theorem normalFormula (B Q : FullMatrix) :
    pairFiber B Q=quantizer B*quantizer Q-quantizer (B*Q) :=by
  have source:=quantized_normal_order B Q
  exact eq_sub_of_add_eq' source.symm

theorem normalChargeFiber_smooth (a : Fin 12) (z : physicalChart) :
    ContDiffAt ℝ ∞ (normalChargeFiber a) z.val :=by
  have same : normalChargeFiber a=fun x=>weightFiber x*quantizer (chargeMatrix (originalUnit a))-
      quantizer (sourceWeightSymbol x*chargeMatrix (originalUnit a)):=funext fun x=>normalFormula _ _
  rw [same]
  exact ((weightFiber_smooth z).mul contDiffAt_const).sub
    ((quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val
      ((sourceWeightSymbol_smooth z).mul contDiffAt_const))

theorem rawChargeFiber_smooth (a : Fin 12) (z : physicalChart) :
    ContDiffAt ℝ ∞ (rawChargeFiber a) z.val :=by
  have valid : ambientState (0,z.val)∈validStates:=by rw [ambientState_zero];exact sourceState_valid z
  exact (rawFiber_smooth (temporalField a) 0 (0,z.val) valid).comp z.val (contDiffAt_const.prodMk contDiffAt_id)

def weightCore : QuantumTest→ₗ[ℂ] QuantumTest:=localMultiplier weightFiber weightFiber_smooth

def normalChargeCore (a : Fin 12) : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier (normalChargeFiber a) (normalChargeFiber_smooth a)

def rawChargeCore (a : Fin 12) : QuantumTest→ₗ[ℂ] QuantumTest:=
  localMultiplier (rawChargeFiber a) (rawChargeFiber_smooth a)

theorem rawChargeFiber_source (a : Fin 12) (z : physicalChart) :
    rawChargeFiber a z.val=weightFiber z.val*quantizer (chargeMatrix (originalUnit a))-normalChargeFiber a z.val :=by
  unfold rawChargeFiber rawFiber
  rw [ambientState_zero,rawTemporalSourceFactor a _ (sourceState_valid z)]
  rw [←smul_mul_assoc]
  change quantizer (sourceWeightSymbol z.val*chargeMatrix (originalUnit a))=_
  unfold normalChargeFiber weightFiber
  rw [normalFormula]
  abel

theorem rawChargeCore_source (a : Fin 12) :
    rawChargeCore a=weightCore.comp (chargeAction (originalUnit a))-normalChargeCore a :=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · change rawChargeFiber a z (f z)=weightFiber z (quantizer (chargeMatrix (originalUnit a)) (f z))-normalChargeFiber a z (f z)
    rw [rawChargeFiber_source a ⟨z,inside⟩]
    simp only [sub_apply,mul_apply_eq_comp]
  · have outside : f z=0:=image_eq_zero_of_notMem_tsupport (fun hz=>inside (f.tsupport_subset hz))
    change rawChargeFiber a z (f z)=weightFiber z (quantizer (chargeMatrix (originalUnit a)) (f z))-normalChargeFiber a z (f z)
    rw [outside,map_zero,map_zero,map_zero,map_zero,sub_zero]

def fullSourceAction (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  physicalAction p+GaussYukawaOperator.originalAction

def weightActionTorque (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest:=
  (fullSourceAction p).comp weightCore-weightCore.comp (fullSourceAction p)

def normalActionTorque (p k : PhysicalMomentum) (a : Fin 12) : QuantumTest→ₗ[ℂ] QuantumTest:=
  (fullSourceAction (p+k)).comp (normalChargeCore a)-(normalChargeCore a).comp (fullSourceAction p)

def weightedWardCore (p k : PhysicalMomentum) (a : Fin 12) : QuantumTest→ₗ[ℂ] QuantumTest:=
  weightCore.comp (wardCore k (originalUnit a))+
    (weightActionTorque (p+k)).comp (chargeAction (originalUnit a))-normalActionTorque p k a

theorem rawCharge_original_action_ward (p k : PhysicalMomentum) (a : Fin 12) (f : QuantumTest) :
    fullSourceAction (p+k) (rawChargeCore a f)-rawChargeCore a (fullSourceAction p f)=
      weightedWardCore p k a f :=by
  have source:=original_full_ward p k (originalUnit a) f
  change fullSourceAction (p+k) (chargeAction (originalUnit a) f)-
    chargeAction (originalUnit a) (fullSourceAction p f)=wardCore k (originalUnit a) f at source
  simp only [rawChargeCore_source,weightedWardCore,weightActionTorque,normalActionTorque,
    LinearMap.comp_apply,LinearMap.add_apply,LinearMap.sub_apply,map_sub,map_add]
  rw [←source,map_sub]
  abel

theorem rawCharge_original_components (p k : PhysicalMomentum) (a : Fin 12) (f : QuantumTest) :
    (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
      PreparationVacuumActionDecomposition.actualCore (p+k)-PreparationVacuumActionDecomposition.retainedCore)
        (rawChargeCore a f)-
    rawChargeCore a ((GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+
      PreparationVacuumActionDecomposition.actualCore p-PreparationVacuumActionDecomposition.retainedCore) f)=
      weightedWardCore p k a f :=by
  rw [←PreparationVacuumActionDecomposition.physical_action_decomposition,
    ←PreparationVacuumActionDecomposition.physical_action_decomposition]
  exact rawCharge_original_action_ward p k a f

end LowEnergy.PreparationVacuumWeightedChargeActionWard
