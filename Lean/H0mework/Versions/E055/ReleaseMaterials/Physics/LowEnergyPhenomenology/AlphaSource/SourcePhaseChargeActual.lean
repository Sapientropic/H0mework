import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseChargeProjection
import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceColourSymbolCovariance

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhaseChargeInventory
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField
open Stage10.CanonicalMatter YangMills.FullPairing PreparationPhysicalNativeOriginPhaseWard
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open FullQuantum.FullSpace FullQuantum.Triangular FullQuantum.StateGreen
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedScatteringPoleReturn
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumSourceFieldFamily
open PreparationVacuumPhysicalGaussMaterialContact GaussNativeMatter SourceQuantumResidualGaugeSlice
open SU7MotherLieAlgebra PreparationVacuumActionFieldLift
open PreparationVacuumNativeLocalWard Stage10.ChargedPreparation.SpatialSpectrum Stage10.ChargedPreparation.Dynamics
open PreparationVacuumElectromagneticIdentity
open MeasureTheory Filter
open scoped BigOperators Matrix InnerProductSpace Topology
local instance : DecidableEq Quantum.Index:=Classical.decEq _
private theorem matrix_sub (A B : Mother) : Quantum.operatorMatrix (A-B)=
    Quantum.operatorMatrix A-Quantum.operatorMatrix B := by
  ext i j
  simp only [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,LinearMap.sub_apply,
    map_sub,Finsupp.sub_apply,Matrix.sub_apply]

private theorem matrix_neg (A : Mother) : Quantum.operatorMatrix (-A)= -Quantum.operatorMatrix A := by
  ext i j
  simp only [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply,LinearMap.neg_apply,
    map_neg,Finsupp.neg_apply,Matrix.neg_apply]

theorem sourcePhaseNoether_native :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=
      (-Complex.I) • nativePrimal (colorGenerator 2)+(1/2:ℂ) • (1:SourceMatrix) := by
  rw [sourcePhaseNoether_canonical,sourceNativeOriginGenerator,map_smul,
    matrix_sub,matrix_neg,map_smul]
  have native : nativePrimal (colorGenerator 2)=
      Quantum.operatorMatrix (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator 2))) := by
    change Quantum.operatorMatrix (diracExteriorMotherLieAction
      (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv (sourceColorP286Generator 2)))))=_
    rw [LinearEquiv.symm_apply_apply]
  rw [native]
  change Complex.I • (-Quantum.operatorMatrix (diracExteriorMotherLieAction
    (p286LieBlockEmbed (sourceColorP286Generator 2)))-(Complex.I/2) • Quantum.operatorMatrix (1:Mother))=_
  rw [map_one]
  simp only [smul_sub,smul_neg,smul_smul]
  have c : Complex.I*(Complex.I/2)= -(1/2:ℂ) := by
    rw [←mul_div_assoc,Complex.I_mul_I]
    norm_num
  rw [c,neg_smul,sub_neg_eq_add,neg_smul]

/-- Original complete Hamiltonian covariance, expressed in the generated signed charge. -/
theorem sourcePhaseHamiltonian_return (s : ActionState) (r : ℝ) (i : Fin 4) :
    stateHamiltonian (s+r • stateContact (Fin.castAdd 6 (2:Fin 3)) 1 s) i=stateHamiltonian s i+
      ((r:ℂ)*Complex.I) •
        (Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)*stateHamiltonian s i-
          stateHamiltonian s i*Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)) := by
  rw [sourceColourHamiltonian_line,sourcePhaseNoether_native]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]
  have difference :
      ((-Complex.I) • (nativePrimal (colorGenerator 2)*stateHamiltonian s i)+(1/2:ℂ) • stateHamiltonian s i)-
      ((-Complex.I) • (stateHamiltonian s i*nativePrimal (colorGenerator 2))+(1/2:ℂ) • stateHamiltonian s i)=
      (-Complex.I) • (nativePrimal (colorGenerator 2)*stateHamiltonian s i-
        stateHamiltonian s i*nativePrimal (colorGenerator 2)) := by module
  rw [difference,smul_smul]
  have coefficient : ((r:ℂ)*Complex.I)*(-Complex.I)=(r:ℂ) := by
    calc
      _= -(r:ℂ)*(Complex.I*Complex.I) := by ring
      _=_ := by rw [Complex.I_mul_I]; ring
  rw [coefficient]
  rfl

/-- Every full-matter transition keeps the original momentum Hamiltonian entry. -/
theorem sourcePhaseHamiltonian_entries (p : Fin 3→ℝ) (i j : Quantum.Index) :
    Quantum.operatorMatrix
      ((phaseInverse.comp sourcePhaseNoether)*FullQuantum.hamiltonian Stage10.Runtime.configuration 0 p-
        FullQuantum.hamiltonian Stage10.Runtime.configuration 0 p*(phaseInverse.comp sourcePhaseNoether)) i j=
      (((sourceWholeWeight j-sourceWholeWeight i:ℚ):ℂ))*
        Quantum.operatorMatrix (FullQuantum.hamiltonian Stage10.Runtime.configuration 0 p) i j := by
  rw [matrix_sub,map_mul,map_mul,
    sourcePhaseNoether_matrix]
  simp only [Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  push_cast
  ring

def sourcePhaseSpatial (a : Fin 3) : FullMatterL2→L[ℂ]FullMatterL2 :=
  (sourcePhaseFiber a).compLpL 2 volume

private theorem spatial_one : (1:FiberOperators).compLpL 2 volume=(1:FullMatterL2→L[ℂ]FullMatterL2) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [(1:FiberOperators).coeFn_compLpL v] with x h
  exact h

theorem sourcePhaseSpatial_total : ∑a : Fin 3,sourcePhaseSpatial a=1 := by
  have h:=congrArg (fun A : FiberOperators=>A.compLpL 2 (volume:Measure Position)) sourcePhaseFiber_total
  simpa only [Fin.sum_univ_three,ContinuousLinearMap.add_compLpL,spatial_one,sourcePhaseSpatial] using h

theorem sourcePhaseSpatial_idempotent (a : Fin 3) (v : FullMatterL2) :
    sourcePhaseSpatial a (sourcePhaseSpatial a v)=sourcePhaseSpatial a v := by
  apply Lp.ext
  filter_upwards [(sourcePhaseFiber a).coeFn_compLpL (sourcePhaseSpatial a v),
    (sourcePhaseFiber a).coeFn_compLpL v] with x outer inner
  change sourcePhaseSpatial a (sourcePhaseSpatial a v) x=_ at outer
  change sourcePhaseSpatial a v x=_ at inner
  rw [outer,inner]
  change (sourcePhaseFiber a*sourcePhaseFiber a) (v x)=_
  rw [sourcePhaseFiber_idempotent]

theorem sourcePhaseSpatial_inner (a : Fin 3) (v w : FullMatterL2) :
    inner ℂ (sourcePhaseSpatial a v) w=inner ℂ v (sourcePhaseSpatial a w) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(sourcePhaseFiber a).coeFn_compLpL v,(sourcePhaseFiber a).coeFn_compLpL w] with x hv hw
  change sourcePhaseSpatial a v x=_ at hv
  change sourcePhaseSpatial a w x=_ at hw
  rw [hv,hw,sourcePhaseFiber_inner]

def sourcePhasePreparedShare (a : Fin 3) (side edge : Fin 2) : ℝ :=
  ‖sourcePhaseSpatial a (sourceChargedFilteredPacket side edge)‖^2

theorem sourcePhasePreparedShare_return (a : Fin 3) (side edge : Fin 2) :
    inner ℂ (sourceChargedFilteredPacket side edge)
      (sourcePhaseSpatial a (sourceChargedFilteredPacket side edge))=
        (sourcePhasePreparedShare a side edge:ℂ) := by
  calc
    _=inner ℂ (sourcePhaseSpatial a (sourceChargedFilteredPacket side edge))
        (sourcePhaseSpatial a (sourceChargedFilteredPacket side edge)) := by
      rw [sourcePhaseSpatial_inner,sourcePhaseSpatial_idempotent]
    _=_ := by
      rw [inner_self_eq_norm_sq_to_K]
      exact (Complex.ofReal_pow _ _).symm

theorem sourcePhasePreparedShare_total (side edge : Fin 2) :
    ∑a : Fin 3,sourcePhasePreparedShare a side edge=1 := by
  have h:=congrArg (fun A : FullMatterL2→L[ℂ]FullMatterL2=>
    inner ℂ (sourceChargedFilteredPacket side edge) (A (sourceChargedFilteredPacket side edge))) sourcePhaseSpatial_total
  simp only [sum_apply,inner_sum,sourcePhasePreparedShare_return,
    one_apply_eq_self,inner_self_eq_norm_sq_to_K,sourceChargedFilteredPacket_unit] at h
  have re:=congrArg Complex.re h
  simpa using re

def sourcePhasePolePair (a : Fin 3) (sideL edgeL sideR edgeR : Fin 2) (k : Position) : ℂ :=
  ∑left : RestStateIndex,∑right : RestStateIndex,
    star (sourceActualPreparedPoleWeight sideL edgeL k left)*sourceActualPreparedPoleWeight sideR edgeR k right*
      inner ℂ (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) left)))
        (sourcePhaseFiber a (naturalCoordinates (embed (sourceMovingPoleValues (physicalMomentum k) right))))

theorem sourcePhaseFiltered_poles (a : Fin 3) (sideL edgeL sideR edgeR : Fin 2) :
    (fun k=>inner ℂ (fourier (sourceChargedFilteredPacket sideL edgeL) k)
      (fourier (sourcePhaseSpatial a (sourceChargedFilteredPacket sideR edgeR)) k))=ᵐ[volume]
        sourcePhasePolePair a sideL edgeL sideR edgeR := by
  rw [sourcePhaseSpatial,FullQuantum.GaugeGreen.constant_fourier]
  filter_upwards [sourceActualFilteredPacket_poles sideL edgeL,sourceActualFilteredPacket_poles sideR edgeR,
    (sourcePhaseFiber a).coeFn_compLpL (fourier (sourceChargedFilteredPacket sideR edgeR))] with k left right acted
  rw [acted,left,right]
  simp only [map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,sourcePhasePolePair,mul_assoc,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem sourcePhaseShare_poles (a : Fin 3) (side edge : Fin 2) :
    (sourcePhasePreparedShare a side edge:ℂ)=∫k,sourcePhasePolePair a side edge side edge k := by
  rw [←sourcePhasePreparedShare_return,←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae (sourcePhaseFiltered_poles a side edge side edge)

theorem sourcePhasePair_poles (a : Fin 3) (sideL edgeL sideR edgeR : Fin 2) :
    inner ℂ (sourceChargedFilteredPacket sideL edgeL)
      (sourcePhaseSpatial a (sourceChargedFilteredPacket sideR edgeR))=
        ∫k,sourcePhasePolePair a sideL edgeL sideR edgeR k := by
  rw [←fourier.inner_map_map,L2.inner_def]
  exact integral_congr_ae (sourcePhaseFiltered_poles a sideL edgeL sideR edgeR)

def sourcePhaseCurrentOperator : FullMatterL2→L[ℂ]FullMatterL2 :=
  (Stage10.ActionNormalization.phaseMomentum:ℂ) •
    (Electromagnetic.CanonicalPacket.densityReader sourcePhaseNoether).compLpL 2 volume

theorem sourcePhaseActualCurrent_generated (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*∑a : Fin 3,
        (-(sourcePhaseLevel a:ℂ))*inner ℂ (sourceChargedFilteredPacket sideL edgeL)
          (sourcePhaseSpatial a (sourceChargedFilteredPacket sideR edgeR)) := by
  rw [sourceChargedQuantumRead_generated,sourcePhaseCurrentOperator,sourcePhaseDensity_resolution]
  simp only [Fin.sum_univ_three,ContinuousLinearMap.add_compLpL,ContinuousLinearMap.smul_compLpL,
    add_apply,smul_apply,inner_add_right,inner_smul_right,sourcePhaseSpatial]

theorem sourcePhaseActualCurrent_diagonal (side edge : Fin 2) :
    sourceChargedQuantumRead side edge side edge sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*∑a : Fin 3,
        (-(sourcePhaseLevel a:ℂ))*(sourcePhasePreparedShare a side edge:ℂ) := by
  rw [sourcePhaseActualCurrent_generated]
  simp_rw [sourcePhasePreparedShare_return]

theorem sourcePhaseActualCurrent_poles (sideL edgeL sideR edgeR : Fin 2) :
    sourceChargedQuantumRead sideL edgeL sideR edgeR sourcePhaseCurrentOperator=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*∑a : Fin 3,
        (-(sourcePhaseLevel a:ℂ))*(∫k,sourcePhasePolePair a sideL edgeL sideR edgeR k) := by
  rw [sourcePhaseActualCurrent_generated]
  simp_rw [sourcePhasePair_poles]

/-- The original full Green and actual normalization retain the complete charge-transition defect. -/
theorem sourcePhaseFiltered_transition (a : Fin 3) (side edge : Fin 2) :
    sourcePhaseSpatial a (sourceChargedFilteredPacket side edge)=
      sourceChargedFilter side edge
        (sourcePhaseSpatial a (PreparationPhysicalChargedPacketVoltage.sourceChargedSpatialPacket side edge))+
      ((sourcePhaseSpatial a*sourceChargedFilter side edge-sourceChargedFilter side edge*sourcePhaseSpatial a)
        (PreparationPhysicalChargedPacketVoltage.sourceChargedSpatialPacket side edge)) := by
  simp only [sourceChargedFilteredPacket,sub_apply,mul_apply_eq_comp]
  abel

end LowEnergy.PreparationPhysicalNativePhaseChargeInventory
