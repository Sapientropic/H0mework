import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseChargeBasis
import H0mework.Versions.AB.Physics.LowEnergyQuantum.Preparation

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhaseChargeInventory
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField
open Stage10.CanonicalMatter YangMills.FullPairing PreparationPhysicalNativeOriginPhaseWard
open FullQuantum.FullSpace FullQuantum.Triangular
open scoped BigOperators Matrix InnerProductSpace
local instance : DecidableEq Quantum.Index:=Classical.decEq _

def sourcePhaseLevel : Fin 3→ℚ := ![-1,-1/2,0]

def sourcePhaseProjectionMatrix (a : Fin 3) : Matrix Quantum.Index Quantum.Index ℂ :=
  Matrix.diagonal (fun i=>if sourceWholeWeight i=sourcePhaseLevel a then 1 else 0)

def sourcePhaseProjection (a : Fin 3) : Mother :=
  Quantum.operatorMatrix.symm (sourcePhaseProjectionMatrix a)

theorem sourcePhaseProjection_idempotent (a : Fin 3) :
    sourcePhaseProjection a*sourcePhaseProjection a=sourcePhaseProjection a := by
  apply Quantum.operatorMatrix.injective
  simp only [map_mul,sourcePhaseProjection,AlgEquiv.apply_symm_apply,sourcePhaseProjectionMatrix,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> norm_num

theorem sourcePhaseProjection_orthogonal (a b : Fin 3) (different : a≠b) :
    sourcePhaseProjection a*sourcePhaseProjection b=0 := by
  apply Quantum.operatorMatrix.injective
  simp only [map_mul,map_zero,sourcePhaseProjection,AlgEquiv.apply_symm_apply,
    sourcePhaseProjectionMatrix,Matrix.diagonal_mul_diagonal]
  rw [←Matrix.diagonal_zero]
  congr 1
  funext i
  have levels : sourcePhaseLevel a≠sourcePhaseLevel b := by
    fin_cases a <;> fin_cases b <;> norm_num [sourcePhaseLevel] at *
  split_ifs with h k k <;> simp_all

theorem sourcePhaseProjection_total :
    ∑a : Fin 3,sourcePhaseProjection a=1 := by
  apply Quantum.operatorMatrix.injective
  simp only [map_sum,map_one,sourcePhaseProjection,AlgEquiv.apply_symm_apply]
  rw [Fin.sum_univ_three]
  ext i j
  by_cases same:i=j
  · subst j
    rcases sourceWholeWeight_range i with h|h|h <;>
      norm_num [sourcePhaseProjectionMatrix,Matrix.add_apply,h,sourcePhaseLevel,Matrix.cons_val_two]
  · simp [sourcePhaseProjectionMatrix,Matrix.add_apply,same]

theorem sourcePhaseProjection_eigen (a : Fin 3) :
    sourceNativeOriginGenerator*sourcePhaseProjection a=
      ((sourcePhaseLevel a:ℂ)*Complex.I) • sourcePhaseProjection a := by
  apply Quantum.operatorMatrix.injective
  simp only [map_mul,map_smul,sourcePhaseGenerator_matrix,sourcePhaseProjection,
    AlgEquiv.apply_symm_apply,sourcePhaseProjectionMatrix,Matrix.diagonal_mul_diagonal,
    ←Matrix.diagonal_smul]
  congr 1
  funext i
  split_ifs with h <;> simp [h]

/-- The temporal insertion uses the same original gamma principal and the same X. -/
def sourcePhaseNoether : Mother :=
  Complex.I • (diracMatrixMatterAction diracGammaZero).comp sourceNativeOriginGenerator

theorem sourcePhaseNoether_canonical :
    phaseInverse.comp sourcePhaseNoether=Complex.I • sourceNativeOriginGenerator := by
  apply LinearMap.ext
  intro v
  simp only [sourcePhaseNoether,LinearMap.comp_apply,LinearMap.smul_apply,map_smul]
  rw [phase_inverse_source]

theorem sourcePhaseNoether_matrix :
    Quantum.operatorMatrix (phaseInverse.comp sourcePhaseNoether)=
      Matrix.diagonal (fun i=> -(sourceWholeWeight i:ℂ)) := by
  rw [sourcePhaseNoether_canonical,map_smul,sourcePhaseGenerator_matrix,←Matrix.diagonal_smul]
  congr 1
  funext i
  change Complex.I*((sourceWholeWeight i:ℂ)*Complex.I)=_
  calc
    _=(sourceWholeWeight i:ℂ)*(Complex.I*Complex.I) := by ring
    _=_ := by rw [Complex.I_mul_I]; ring

theorem sourcePhaseNoether_eigen (a : Fin 3) :
    (phaseInverse.comp sourcePhaseNoether)*sourcePhaseProjection a=
      (-(sourcePhaseLevel a:ℂ)) • sourcePhaseProjection a := by
  rw [sourcePhaseNoether_canonical,smul_mul_assoc,sourcePhaseProjection_eigen,smul_smul]
  congr 1
  calc
    Complex.I*((sourcePhaseLevel a:ℂ)*Complex.I)=(sourcePhaseLevel a:ℂ)*(Complex.I*Complex.I) := by ring
    _= -(sourcePhaseLevel a:ℂ) := by rw [Complex.I_mul_I]; ring

theorem sourcePhaseNoether_resolution :
    phaseInverse.comp sourcePhaseNoether=
      ∑a : Fin 3,(-(sourcePhaseLevel a:ℂ)) • sourcePhaseProjection a := by
  calc
    _=(phaseInverse.comp sourcePhaseNoether)*(∑a : Fin 3,sourcePhaseProjection a) := by
      rw [sourcePhaseProjection_total,mul_one]
    _=_ := by rw [Finset.mul_sum]; simp_rw [sourcePhaseNoether_eigen]

def sourcePhaseFiber (a : Fin 3) : FiberOperators := operator (sourcePhaseProjection a)

theorem sourcePhaseFiber_idempotent (a : Fin 3) : sourcePhaseFiber a*sourcePhaseFiber a=sourcePhaseFiber a := by
  rw [sourcePhaseFiber,←operator_mul,sourcePhaseProjection_idempotent]

theorem sourcePhaseProjection_coordinates (a : Fin 3) (v : DiracExteriorMatterCarrier) (i : Quantum.Index) :
    Quantum.coordinates (sourcePhaseProjection a v) i=
      if sourceWholeWeight i=sourcePhaseLevel a then Quantum.coordinates v i else 0 := by
  have h:=Quantum.matrix_action (sourcePhaseProjection a) v
  rw [sourcePhaseProjection,AlgEquiv.apply_symm_apply,sourcePhaseProjectionMatrix] at h
  have read:=congrFun h i
  change _=Quantum.coordinates (sourcePhaseProjection a v) i at read
  rw [←read]
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem sourcePhaseFiber_inner (a : Fin 3) (v w : Hilbert) :
    inner ℂ (sourcePhaseFiber a v) w=inner ℂ v (sourcePhaseFiber a w) := by
  obtain ⟨v,rfl⟩:=naturalCoordinates.surjective v
  obtain ⟨w,rfl⟩:=naturalCoordinates.surjective w
  simp only [sourcePhaseFiber,operator_coordinates,natural_inner,←Quantum.coordinatePair_full]
  unfold Quantum.coordinatePair
  apply Finset.sum_congr rfl
  intro i _
  rw [sourcePhaseProjection_coordinates,sourcePhaseProjection_coordinates]
  split_ifs <;> simp

theorem sourcePhaseFiber_total : ∑a : Fin 3,sourcePhaseFiber a=1 := by
  have h:=congrArg operator sourcePhaseProjection_total
  simp only [Fin.sum_univ_three,operator_add] at h ⊢
  have one : operator (1:Mother)=(1:FiberOperators) := by ext v; simp [operator]
  simpa only [sourcePhaseFiber,one] using h

theorem sourcePhaseDensity_resolution :
    Electromagnetic.CanonicalPacket.densityReader sourcePhaseNoether=
      ∑a : Fin 3,(-(sourcePhaseLevel a:ℂ)) • sourcePhaseFiber a := by
  change operator (phaseInverse.comp sourcePhaseNoether)=_
  rw [sourcePhaseNoether_resolution]
  simp only [Fin.sum_univ_three,operator_add,operator_smul,sourcePhaseFiber]

theorem sourcePhaseNoether_original (point : ProofFreeRicherAnholonomicSource.BasePoint)
    (left right : Mother) :
    Stage9C.Material.SpinPair.actual.conjugateMatter point
      (canonicalDual left (sourcePhaseNoether (right (Stage9C.Material.SpinPair.actual.matter point))))=
      4*(Stage9C.Material.SpinPair.spinScale:ℂ)*inner ℂ
        (operator left (prepared point))
        (operator ((phaseInverse.comp sourcePhaseNoether).comp right) (prepared point)) := by
  exact Electromagnetic.ExternalState.original_prepared_vertex point left right sourcePhaseNoether

end LowEnergy.PreparationPhysicalNativePhaseChargeInventory
