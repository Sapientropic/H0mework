import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliaryClockRows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMNativeRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryClockReduction
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualEMAction ActualEMCarrierOwn
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedAuxiliaryClockRows
open ActualSourcePreparedEMClockEquation ActualSourcePreparedEMJacobiRow
open ActualSourcePreparedEMNativeRow ActualSourcePreparedEMNativeRead
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMNativeAuxiliary SourcePropagationNativeActionHessian
open scoped Matrix BigOperators
attribute [local irreducible] sourceClockReducedPencil sourceEMClockForce sourceFourClockDenominator
  sourceTemporalEMForce sourceReducedClockFieldNumerator sourceReducedClockDeterminant
  Matrix.det Matrix.adjugate Matrix.mulVec

private def wholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_left (i : Fin 217) : wholeIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem whole_right (pair : Fin 6 × Fin 12) : wholeIndex (Sum.inr pair)=gaugeAuxiliaryIndex pair := by
  apply Fin.ext
  change 217+(pair.2.val+12*pair.1.val)=217+12*pair.1.val+pair.2.val
  omega

def sourceAuxiliaryClockFactor (event : DressedEvent) (n : PhysicalMomentum) : ((ℂ[X])[X]) :=
  X^3*sourceFourClockDenominator event n

def sourceAuxiliaryRowWeight (event : DressedEvent) (n : PhysicalMomentum) (i : Fin 289) : ((ℂ[X])[X]) :=
  Sum.elim (fun _ : Fin 217 => 1) (fun _ : Fin 6 × Fin 12 => sourceAuxiliaryClockFactor event n)
    (wholeIndex.symm i)

/-- All original rows and columns remain; the generated common factor is
removed only from auxiliary equations, not from the physical field. -/
def sourceAuxiliaryReducedPencil (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  fun i j => Sum.elim (fun r : Fin 217 => sourceClockReducedPencil event n (nativeRestIndex r) j)
    (fun pair : Fin 6 × Fin 12 => staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex pair) j))
      (wholeIndex.symm i)

attribute [local irreducible] sourceAuxiliaryReducedPencil sourceAuxiliaryRowWeight

theorem source_auxiliary_pencil_row_factor (event : DressedEvent) (n : PhysicalMomentum) :
    sourceClockReducedPencil event n=
      Matrix.diagonal (sourceAuxiliaryRowWeight event n)*sourceAuxiliaryReducedPencil event n := by
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul]
  obtain ⟨r,rfl⟩ := wholeIndex.surjective i
  cases r with
  | inl r =>
      simp only [sourceAuxiliaryRowWeight,sourceAuxiliaryReducedPencil,
        Equiv.symm_apply_apply,Sum.elim_inl,one_mul]
      rw [whole_left]
  | inr pair =>
      simp only [sourceAuxiliaryRowWeight,sourceAuxiliaryReducedPencil,Equiv.symm_apply_apply,
        Sum.elim_inr,sourceAuxiliaryClockFactor]
      rw [whole_right]
      exact source_auxiliary_clock_pencil_row event n pair j

private theorem weights_product (event : DressedEvent) (n : PhysicalMomentum) :
    (∏i : Fin 289, sourceAuxiliaryRowWeight event n i)=(sourceAuxiliaryClockFactor event n)^72 := by
  rw [←wholeIndex.prod_comp (sourceAuxiliaryRowWeight event n),Fintype.prod_sum_type]
  simp only [sourceAuxiliaryRowWeight,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr,
    Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,one_pow,one_mul]

private theorem diagonal_factor_det {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (K M : Matrix I I R) (w : I → R) (b : R)
    (rows : K=Matrix.diagonal w*M) (weight : (∏i,w i)=b) : K.det=b*M.det := by
  rw [rows,Matrix.det_mul,Matrix.det_diagonal,weight]

/-- Exactly seventy-two original auxiliary rows supply the common source
factor, before either physical scale is specialized. -/
theorem source_auxiliary_determinant_factor (event : DressedEvent) (n : PhysicalMomentum) :
    (sourceClockReducedPencil event n).det=
      (sourceAuxiliaryClockFactor event n)^72*(sourceAuxiliaryReducedPencil event n).det := by
  exact diagonal_factor_det (sourceClockReducedPencil event n) (sourceAuxiliaryReducedPencil event n)
    (sourceAuxiliaryRowWeight event n) ((sourceAuxiliaryClockFactor event n)^72)
    (source_auxiliary_pencil_row_factor event n) (weights_product event n)

private theorem force_auxiliary_zero (pair : Fin 6 × Fin 12) :
    sourceTemporalEMForce (gaugeAuxiliaryIndex pair)=0 := by
  unfold sourceTemporalEMForce
  have high : 217≤(gaugeAuxiliaryIndex pair).val := by
    dsimp only [gaugeAuxiliaryIndex,gaugeBSlot]
    omega
  have outside (a : Fin 289) (small : a.val<217) : gaugeAuxiliaryIndex pair≠a := by
    intro same
    have equal := congrArg Fin.val same
    omega
  have response := em_projection_coordinates (Pi.single (gaugeAuxiliaryIndex pair) (1 : ℂ)) 0
  simp only [Matrix.mulVec,Matrix.transpose_apply] at response
  simpa only [dotProduct_single,mul_one,Pi.single_eq_of_ne (outside (gaugeSlot 0 6) (by decide)).symm,
    Pi.single_eq_of_ne (outside (gaugeSlot 0 7) (by decide)).symm,
    Pi.single_eq_of_ne (outside (gaugeSlot 0 11) (by decide)).symm,
    neg_zero,add_zero,sub_zero,mul_zero] using response

private theorem weighted_force (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix.diagonal (sourceAuxiliaryRowWeight event n)*ᵥsourceEMClockForce=sourceEMClockForce := by
  funext i
  rw [Matrix.mulVec_diagonal]
  obtain ⟨r,rfl⟩ := wholeIndex.surjective i
  cases r with
  | inl r => simp only [sourceAuxiliaryRowWeight,Equiv.symm_apply_apply,Sum.elim_inl,one_mul]
  | inr pair =>
      simp only [sourceAuxiliaryRowWeight,Equiv.symm_apply_apply,Sum.elim_inr]
      rw [whole_right]
      simp only [sourceEMClockForce,force_auxiliary_zero,map_zero,mul_zero]

def sourceAuxiliaryReducedFieldNumerator (event : DressedEvent) (n : PhysicalMomentum) : Fin 289 → ((ℂ[X])[X]) :=
  sourceAuxiliaryClockFactor event n • ((sourceAuxiliaryReducedPencil event n).adjugate*ᵥsourceEMClockForce)

attribute [local irreducible] sourceAuxiliaryReducedFieldNumerator

private theorem diagonal_factor_cofactor {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (K M : Matrix I I R) (w : I → R) (e : I → R) (a b : R)
    (rows : K=Matrix.diagonal w*M) (forcing : Matrix.diagonal w*ᵥe=e)
    (weight : (∏i,w i)=b) : a • (K.adjugate*ᵥe)=b • (a • (M.adjugate*ᵥe)) := by
  have initial := congrArg (fun B : Matrix I I R => B*ᵥe) (Matrix.adjugate_mul (Matrix.diagonal w))
  rw [←Matrix.mulVec_mulVec,forcing,Matrix.smul_mulVec,Matrix.one_mulVec,
    Matrix.det_diagonal,weight] at initial
  rw [rows,Matrix.adjugate_mul_distrib,←Matrix.mulVec_mulVec,initial,Matrix.mulVec_smul]
  simp only [smul_smul]
  congr 1
  exact mul_comm a b

/-- The same common factor is generated on the entire field cofactor,
because the actual source forcing has no auxiliary component. -/
theorem source_auxiliary_field_cofactor_factor (event : DressedEvent) (n : PhysicalMomentum) :
    sourceAuxiliaryClockFactor event n • ((sourceClockReducedPencil event n).adjugate*ᵥsourceEMClockForce)=
      (sourceAuxiliaryClockFactor event n)^72 • (sourceAuxiliaryClockFactor event n •
        ((sourceAuxiliaryReducedPencil event n).adjugate*ᵥsourceEMClockForce)) := by
  exact diagonal_factor_cofactor (sourceClockReducedPencil event n) (sourceAuxiliaryReducedPencil event n)
    (sourceAuxiliaryRowWeight event n) sourceEMClockForce (sourceAuxiliaryClockFactor event n)
    ((sourceAuxiliaryClockFactor event n)^72) (source_auxiliary_pencil_row_factor event n)
    (weighted_force event n) (weights_product event n)

end LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryClockReduction
