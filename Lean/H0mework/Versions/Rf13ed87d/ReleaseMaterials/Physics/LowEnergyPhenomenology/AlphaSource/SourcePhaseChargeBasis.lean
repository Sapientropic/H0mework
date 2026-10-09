import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginMatterPhase
import H0mework.Versions.AB.Physics.LowEnergyQuantum.Carrier

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativePhaseChargeInventory
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa DiracExteriorMatterAction DiracCliffordRepresentation
open StageNineHolonomicField StageNineResidualLimitScalarBalanceClosure StageNineExteriorMotherLieRepresentation
open StageNineP286GaugeConnectionVariation
open Stage9C.Material.SpinPair YangMills.FullPairing PreparationPhysicalNativeOriginPhaseWard
open scoped BigOperators Matrix
local instance : DecidableEq Quantum.Index:=Classical.decEq _

def sourceColorWeight (i : SU7MotherIndex) : ℚ :=
  (if i=Sum.inl (0:Fin 3) then 1/2 else 0)-(if i=Sum.inl (1:Fin 3) then 1/2 else 0)

def sourceExteriorWeight {degree : ℕ} (i : ExteriorBasisIndex degree) : ℚ :=
  ∑ j∈i.1,sourceColorWeight j

def sourcePhaseWeight {degree : ℕ} (i : ExteriorBasisIndex degree) : ℚ := -sourceExteriorWeight i-1/2

theorem sourceColorWeight_action (i : SU7MotherIndex) :
    fundamentalMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator 2)) (su7FundamentalBasis i)=
      ((sourceColorWeight i:ℂ)*Complex.I) • su7FundamentalBasis i := by
  fin_cases i <;> ext row <;> fin_cases row <;>
    norm_num [fundamentalMotherLieAction,sourceColorP286Generator,colorCartanGenerator,colorCartanRaw,
      p286LieBlockEmbed,rawP286LieBlock,weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,
      su7FundamentalBasis,Matrix.mulVecLin,Matrix.mulVec,sourceColorWeight,Matrix.diagonal,Pi.single_apply]
  all_goals simp

theorem sourceExteriorWeight_action (degree : ℕ) (i : ExteriorBasisIndex degree) :
    exteriorMotherLieAction degree (p286LieBlockEmbed (sourceColorP286Generator 2)) (su7ExteriorBasis degree i)=
      ((sourceExteriorWeight i:ℂ)*Complex.I) • su7ExteriorBasis degree i := by
  classical
  rw [exteriorMotherLieAction_basis]
  have term (position : Fin degree) :
      (exteriorPower.ιMulti ℂ degree)
        (exteriorBasisLieActionInput degree (p286LieBlockEmbed (sourceColorP286Generator 2)) i position)=
      ((sourceColorWeight (exteriorPositionEquiv i position).1:ℂ)*Complex.I) • su7ExteriorBasis degree i := by
    rw [exteriorBasisLieActionTerm_eq_update]
    have eigen:=sourceColorWeight_action (exteriorPositionEquiv i position).1
    change fundamentalMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator 2))
      (exteriorBasisInput degree i position)=
        ((sourceColorWeight (exteriorPositionEquiv i position).1:ℂ)*Complex.I) •
          exteriorBasisInput degree i position at eigen
    rw [eigen,(exteriorPower.ιMulti ℂ degree).map_update_smul,Function.update_eq_self,
      exteriorBasisInput_wedge_eq_basis]
  change (∑position : Fin degree,(exteriorPower.ιMulti ℂ degree)
    (exteriorBasisLieActionInput degree (p286LieBlockEmbed (sourceColorP286Generator 2)) i position))=_
  simp_rw [term]
  rw [←Finset.sum_smul,←Finset.sum_mul,←Rat.cast_sum]
  congr 3
  exact ((exteriorPositionEquiv i).sum_comp (fun j=>sourceColorWeight j)).trans
    (Finset.sum_subtype i.1 (by simp) sourceColorWeight).symm

theorem sourcePhaseWeight_subset {degree : ℕ} (i : ExteriorBasisIndex degree) :
    sourcePhaseWeight i= -((if Sum.inl (0:Fin 3)∈i.1 then 1/2 else 0)-
      (if Sum.inl (1:Fin 3)∈i.1 then 1/2 else 0))-1/2 := by
  classical
  simp [sourcePhaseWeight,sourceExteriorWeight,sourceColorWeight,Finset.sum_sub_distrib]

theorem sourcePhaseWeight_range {degree : ℕ} (i : ExteriorBasisIndex degree) :
    sourcePhaseWeight i= -1 ∨ sourcePhaseWeight i= -1/2 ∨ sourcePhaseWeight i=0 := by
  rw [sourcePhaseWeight_subset]
  split_ifs <;> norm_num

def sourceInternalWeight : Quantum.InternalIndex → ℚ
  | .inl i=>sourcePhaseWeight i
  | .inr (.inl i)=>sourcePhaseWeight i
  | .inr (.inr i)=>sourcePhaseWeight i

def sourceWholeWeight (i : Quantum.Index) : ℚ := sourceInternalWeight i.2

theorem sourceWholeWeight_range (i : Quantum.Index) :
    sourceWholeWeight i= -1 ∨ sourceWholeWeight i= -1/2 ∨ sourceWholeWeight i=0 := by
  rcases i with ⟨spin,i|i|i⟩ <;> exact sourcePhaseWeight_range i

theorem sourcePhaseGenerator_basis (i : Quantum.Index) :
    sourceNativeOriginGenerator (Quantum.wholeBasis i)=
      ((sourceWholeWeight i:ℂ)*Complex.I) • Quantum.wholeBasis i := by
  rcases i with ⟨spin,i|i|i⟩
  all_goals
    funext s
    simp only [sourceNativeOriginGenerator,LinearMap.sub_apply,LinearMap.neg_apply,
      LinearMap.smul_apply,LinearMap.id_apply,Pi.sub_apply,Pi.neg_apply,Pi.smul_apply,
      diracExteriorMotherLieAction,internalMatterLinearAction,Quantum.wholeBasis,Pi.basis_apply]
    by_cases h:s=spin
    · subst s
      simp [Quantum.internalBasis,Module.Basis.prod_apply,exteriorSpinorMotherLieAction,
        sourceExteriorWeight_action,sourceWholeWeight,sourceInternalWeight,sourcePhaseWeight]
      all_goals module
    · simp [h,exteriorSpinorMotherLieAction]

theorem sourcePhaseGenerator_matrix :
    Quantum.operatorMatrix sourceNativeOriginGenerator=
      Matrix.diagonal (fun i=>(sourceWholeWeight i:ℂ)*Complex.I) := by
  ext i j
  rw [Quantum.operatorMatrix,LinearMap.toMatrixAlgEquiv_apply]
  rw [sourcePhaseGenerator_basis,map_smul,Module.Basis.repr_self]
  simp [Matrix.diagonal_apply,Finsupp.single_apply]
  split_ifs <;> simp_all

def sourceWeightSubsets (degree : ℕ) (q : ℚ) : Finset (Finset SU7MotherIndex) :=
  (Finset.univ.powersetCard degree).filter (fun i=> -(∑j∈i,sourceColorWeight j)-1/2=q)

theorem sourceWeightSubsets_membership {degree : ℕ} (q : ℚ) (i : ExteriorBasisIndex degree) :
    i.1∈sourceWeightSubsets degree q ↔ sourcePhaseWeight i=q := by
  simp [sourceWeightSubsets,sourcePhaseWeight,sourceExteriorWeight]

def sourceInternalMultiplicity (q : ℚ) : ℕ :=
  (sourceWeightSubsets 6 q).card+(sourceWeightSubsets 2 q).card+(sourceWeightSubsets 4 q).card

theorem sourcePhaseMultiplicity :
    sourceInternalMultiplicity (-1)=16 ∧ sourceInternalMultiplicity (-1/2)=31 ∧
      sourceInternalMultiplicity 0=16 := by decide +kernel

theorem sourcePhase_fourPi (i : Quantum.Index) :
    Complex.exp ((sourceWholeWeight i:ℂ)*(4*Real.pi)*Complex.I)=1 := by
  rcases sourceWholeWeight_range i with h|h|h
  · rw [h]
    convert Complex.exp_int_mul_two_pi_mul_I (-2) using 1
    norm_num
    ring
  · rw [h]
    convert Complex.exp_int_mul_two_pi_mul_I (-1) using 1
    norm_num
    ring
  · simp [h]

theorem sourcePhase_half_twoPi : Complex.exp (((-1/2:ℚ):ℂ)*(2*Real.pi)*Complex.I)= -1 := by
  have exponent : (((-1/2:ℚ):ℂ)*(2*Real.pi)*Complex.I)= -(Real.pi*Complex.I) := by push_cast; ring
  rw [exponent,Complex.exp_neg,Complex.exp_pi_mul_I]
  norm_num

end LowEnergy.PreparationPhysicalNativePhaseChargeInventory
