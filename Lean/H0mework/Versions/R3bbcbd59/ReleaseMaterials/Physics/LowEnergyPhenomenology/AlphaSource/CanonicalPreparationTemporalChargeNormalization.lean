import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationNoetherSourceInitialReturn
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationTemporalGlobalCharge
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationElectricPairCurrent

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceChargeWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussQuantumMultiplier GaussHistoryHilbert CanonicalGradedSpatialSource
open FullQuantum.StateGreen PreparationVacuumMixedFieldReturn PreparationVacuumOriginalDensity
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumNoetherChart PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumTemporalCharge PreparationVacuumFullElectricWard CanonicalGradedCharge PreparationVacuumLowerClassical
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] densityActionMatrix densityActionInverse rawMomentumMatrix rawMomentumInverse
  transportedDensity transportedRawSymbol noetherContactCoefficient noetherContactSymbol
  rawActionSymbol sourceActionWeight statePhase inversePhase

/-- The original temporal reader is transported with the actual canonical momentum held fixed. -/
theorem transportedTemporalCoefficient (a : Fin 12) (base candidate : ActionState)
    (valid : candidate∈validStates) (i : Fin 4) :
    transportedDensity (temporalField a) base candidate i=rawMomentumMatrix base*temporalCoefficient a i :=by
  have normalized:=temporal_normalized_reader a candidate valid.1 valid.2 i
  unfold transportedDensity rawMomentumInverse
  simp only [mul_assoc]
  rw [←mul_assoc densityActionInverse densityActionMatrix,densityAction_two_sided.2,one_mul,normalized]
  rfl

private theorem affine_left (G : SourceMatrix) (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) :
    affineMatrix (fun i=>G*A i) p=G*affineMatrix A p :=by
  simp only [affineMatrix,mul_add,Finset.mul_sum,mul_smul_comm]

private theorem rawFourier_left (G : SourceMatrix) (A : Fin 4→SourceMatrix) (p : PhysicalMomentum) :
    rawFourier p (fun i=>G*A i)=SourceRealScalarFock.branches G*realFourierMatrix A p :=by
  rw [rawFourier_blocks,affine_left,affine_left,realFourierMatrix,SourceRealScalarFock.branches,Matrix.fromBlocks_multiply]
  ext i j
  cases i <;> cases j <;>
    simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,Matrix.neg_apply,neg_mul_neg,Matrix.map_apply,Matrix.mul_apply,star_sum,star_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

theorem transportedTemporalSymbol (a : Fin 12) (base candidate : ActionState)
    (valid : candidate∈validStates) (p : PhysicalMomentum) :
    transportedRawSymbol (temporalField a) base candidate p=
      SourceRealScalarFock.branches (rawMomentumMatrix base)*chargeMatrix (originalUnit a) :=by
  rw [transportedRawSymbol]
  have coefficients : transportedDensity (temporalField a) base candidate=
      fun i=>rawMomentumMatrix base*temporalCoefficient a i :=
    funext (transportedTemporalCoefficient a base candidate valid)
  rw [coefficients,rawFourier_left,temporal_full_matrix]

/-- The complete source action weight is kept before quantization, with no extra 4pi. -/
theorem rawTemporalSourceFactor (a : Fin 12) (s : ActionState) (valid : s∈validStates) (p : PhysicalMomentum) :
    rawActionSymbol (temporalField a) p s=
      (4:ℂ) • (sourceActionWeight s*chargeMatrix (originalUnit a)) :=by
  rw [←transportedRawSymbol_source (temporalField a) s valid p,
    transportedTemporalSymbol a s s valid p,rawMomentum_source_weight,smul_mul_assoc]

/-- This contact cancels in the original fixed-pi chart; the other propagation legs remain. -/
theorem temporalNoetherContactCoefficient (a : Fin 12) (force : Field289) (z : physicalChart) (i : Fin 4) :
    noetherContactCoefficient (temporalField a) force (sourceState z.val) i=0 :=by
  let s:=sourceState z.val
  have source:=transportedDensity_generated (temporalField a) force z i
  have path : ContinuousAt (fun r : ℝ=>s+r • fieldDirection force) 0 :=by fun_prop
  have base : s+(0:ℝ) • fieldDirection force∈validStates:=by
    simpa only [s,zero_smul,add_zero] using sourceState_valid z
  have remains:=path.eventually (validStates_open.mem_nhds base)
  have actual : (fun r : ℝ=>transportedDensity (temporalField a) s (s+r • fieldDirection force) i)=ᶠ[𝓝 0]
      fun _=>rawMomentumMatrix s*temporalCoefficient a i:=by
    filter_upwards [remains] with r hr
    exact transportedTemporalCoefficient a s _ hr i
  have constant:=(hasDerivAt_const 0 (rawMomentumMatrix s*temporalCoefficient a i)).congr_of_eventuallyEq actual
  exact source.unique constant

theorem temporalNoetherContactSymbol (a : Fin 12) (force : Field289) (z : physicalChart) (p : PhysicalMomentum) :
    noetherContactSymbol (temporalField a) force (sourceState z.val) p=0 :=by
  have coefficients : noetherContactCoefficient (temporalField a) force (sourceState z.val)=0:=
    funext (temporalNoetherContactCoefficient a force z)
  rw [noetherContactSymbol,coefficients,map_zero]

/-- The original all-occupation product includes its four-CAR normal term. -/
theorem temporalSource_fullCAR (a : Fin 12) (s : ActionState) (valid : s∈validStates)
    (p : PhysicalMomentum) (v : FockFiber) :
    quantizer (rawActionSymbol (temporalField a) p s) v=
      quantizer (SourceRealScalarFock.branches (rawMomentumMatrix s))
        (quantizer (chargeMatrix (originalUnit a)) v)-
      pairFiber (SourceRealScalarFock.branches (rawMomentumMatrix s)) (chargeMatrix (originalUnit a)) v :=by
  rw [←transportedRawSymbol_source (temporalField a) s valid p,transportedTemporalSymbol a s s valid p]
  have ordered:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T v)
    (quantized_normal_order (SourceRealScalarFock.branches (rawMomentumMatrix s)) (chargeMatrix (originalUnit a)))
  simp only [mul_apply_eq_comp,add_apply] at ordered
  exact eq_sub_of_add_eq ordered.symm

end LowEnergy.PreparationVacuumSourceChargeWard
