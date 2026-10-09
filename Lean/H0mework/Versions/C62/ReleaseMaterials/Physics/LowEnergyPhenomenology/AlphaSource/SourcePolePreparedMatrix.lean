import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceCurvaturePoleReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalPoleChargeMatrix
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracCliffordRepresentation DiracExteriorMatterAction FullQuantum.CoframeResponse
open PreparationPhysicalNormalizedFullField PreparationPhysicalActualNoetherVertexReturn
open PreparationPhysicalActualPhaseChargeReturn PreparationPhysicalPhaseGaugeRealization
open PreparationVacuumPhysicalFeedback PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumNonlinearFieldCurve PreparationVacuumNativeSlowCoupling
open PreparationVacuumSourceFieldFamily GaussHistoryHilbert
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open GaussQuantumMultiplier GaussFockLift GaussCoreHilbert SourceQuantumFockGauge
open CanonicalGradedCharge CanonicalGradedSpatialSource
open scoped Matrix BigOperators InnerProductSpace Topology
attribute [local instance] SourceRealScalarFock.branchOrder
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Quantum.InternalIndex:=Classical.decEq _

/-- The original full252 basis returns the spin matrix with its independent internal index preserved. -/
theorem sourceSpinMatrix_entry (A : DiracMatrix) (i j : Quantum.Index) :
    spinCoordinates A i j=A i.1 j.1*(if i.2=j.2 then 1 else 0) := by
  classical
  change (LinearMap.toMatrix Quantum.wholeBasis Quantum.wholeBasis (diracMatrixMatterAction A)) i j=_
  rw [LinearMap.toMatrix_apply]
  simp only [Quantum.wholeBasis,Pi.basis_repr,Pi.basis_apply,diracMatrixMatterAction,
    LinearMap.coe_mk,AddHom.coe_mk]
  simp [Pi.single_apply,Finsupp.single_apply,eq_comm]

/-- Both source branches are kept before the actual external preparation restriction. -/
theorem sourceSpinBranches_entry (A : DiracMatrix) (i j : Quantum.Index) :
    SourceRealScalarFock.branches (spinCoordinates A) (Sum.inl i) (Sum.inl j)=
      A i.1 j.1*(if i.2=j.2 then 1 else 0) ∧
    SourceRealScalarFock.branches (spinCoordinates A) (Sum.inr i) (Sum.inr j)=
      -star (A i.1 j.1*(if i.2=j.2 then 1 else 0)) ∧
    SourceRealScalarFock.branches (spinCoordinates A) (Sum.inl i) (Sum.inr j)=0 ∧
    SourceRealScalarFock.branches (spinCoordinates A) (Sum.inr i) (Sum.inl j)=0 := by
  constructor
  · exact sourceSpinMatrix_entry A i j
  constructor
  · change -star (spinCoordinates A i j)=_
    rw [sourceSpinMatrix_entry]
  exact ⟨rfl,rfl⟩

/-- The complete literal energy column is read on all four actual Gauss preparations, including every cross entry. -/
def sourcePoleEnergyMatrix (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (v : Fin 4→ℂ) : Matrix ActualPreparedIndex ActualPreparedIndex ℂ :=
  fun i j=>sourceLiteralEnergyCoefficient epsilon precision p (sourceState sourcePoint.val) v 2 i.1 i.2 j.1 j.2

private theorem sourceColorIndex_eq (a b : Fin 2) :
    Stage9C.Material.SpinPair.sourceColorDoubletIndex a=Stage9C.Material.SpinPair.sourceColorDoubletIndex b ↔ a=b := by
  fin_cases a <;> fin_cases b <;> decide

private theorem sourceSpinCharged_entry (A : DiracMatrix) (s e t f : Fin 2) :
    spinCoordinates A (sourceChargedQuantumIndex s e) (sourceChargedQuantumIndex t f)=
      if e=f then A (sourceChargedBasisIndex s e).1 (sourceChargedBasisIndex t f).1 else 0 := by
  rw [sourceSpinMatrix_entry]
  simp only [sourceChargedQuantumIndex,Sum.inr.injEq,Sum.inl.injEq,sourceColorIndex_eq]
  split_ifs <;> simp

private def sourcePoleSpinSign (i : ActualPreparedIndex) : ℂ := if i.1=i.2 then 1 else -1

private theorem sourceEnergyAxis_zero :
    ((Complex.I*((Pi.single (0:Fin 4) (1:ℝ):Fin 4→ℝ) 0:ℂ)) • (1:DiracMatrix)-
      (Complex.I*(Real.sqrt 30:ℂ)/5) •
        (∑j : Fin 3,((Pi.single (0:Fin 4) (1:ℝ):Fin 4→ℝ) j.succ:ℂ) •
          (diracGammaZero*diracGamma j.succ)))=Complex.I • (1:DiracMatrix) := by
  norm_num [Pi.single_apply,Fin.sum_univ_three]

private theorem sourceEnergyAxis_succ (k : Fin 3) :
    ((Complex.I*((Pi.single k.succ (1:ℝ):Fin 4→ℝ) 0:ℂ)) • (1:DiracMatrix)-
      (Complex.I*(Real.sqrt 30:ℂ)/5) •
        (∑j : Fin 3,((Pi.single k.succ (1:ℝ):Fin 4→ℝ) j.succ:ℂ) •
          (diracGammaZero*diracGamma j.succ)))=
      -(Complex.I*(Real.sqrt 30:ℂ)/5) • (diracGammaZero*diracGamma k.succ) := by
  fin_cases k <;> simp only [Pi.single_apply,Fin.sum_univ_three,Fin.ext_iff] <;> norm_num
  all_goals rfl

private theorem sourceEnergyAxis_all (k : Fin 4) :
    ((Complex.I*((Pi.single k (1:ℝ):Fin 4→ℝ) 0:ℂ)) • (1:DiracMatrix)-
      (Complex.I*(Real.sqrt 30:ℂ)/5) •
        (∑j : Fin 3,((Pi.single k (1:ℝ):Fin 4→ℝ) j.succ:ℂ) •
          (diracGammaZero*diracGamma j.succ)))=
      if k=0 then Complex.I • (1:DiracMatrix)
      else -(Complex.I*(Real.sqrt 30:ℂ)/5) • (diracGammaZero*diracGamma k) := by
  rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨j,rfl⟩
  · simpa only [ite_true] using sourceEnergyAxis_zero
  · rw [if_neg (Fin.succ_ne_zero j)]
    exact sourceEnergyAxis_succ j

/-- All16 entries follow from the full200 column and actual source normalization, including neutral and mixed preparations. -/
theorem sourcePoleEnergyMatrix_generated (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (v : Fin 4→ℂ) :
    sourcePoleEnergyMatrix epsilon precision p v=
      Matrix.diagonal (fun i=>Complex.I*v 0-(Complex.I*(Real.sqrt 30:ℂ)/5)*sourcePoleSpinSign i*v 3) := by
  ext i j
  rcases i with ⟨side,edge⟩
  rcases j with ⟨other,opposite⟩
  simp only [sourcePoleEnergyMatrix,sourceLiteralEnergyCoefficient,sourceChargedEnergyRead_entry,
    sourceLiteralChannelTwoEnergy,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [SourceRealScalarFock.branches,Matrix.fromBlocks_apply₁₁,sourceSpinCharged_entry]
  simp only [sourceEnergyAxis_all,Fin.sum_univ_four]
  fin_cases side <;> fin_cases edge <;> fin_cases other <;> fin_cases opposite <;>
    simp only [sourceChargedBasisIndex,Matrix.diagonal_apply,Prod.mk.injEq,Fin.ext_iff] <;>
    norm_num [sourceChargedBasisIndex,sourcePoleSpinSign,
      Fin.sum_univ_four,Fin.sum_univ_three,Pi.single_apply,
      Matrix.diagonal_apply,Matrix.mul_apply,Matrix.one_apply,Matrix.sub_apply,Matrix.smul_apply,
      Matrix.sum_apply,smul_eq_mul,diracGammaZero,diracGamma,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.of_apply,Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  all_goals ring

end LowEnergy.PreparationPhysicalPoleChargeMatrix
