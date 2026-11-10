import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterClockRows
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualPreparedMatterSupportNative
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliaryActualReturn

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualPreparedMatterClock
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualEMAction ActualEMCarrierOwn
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedReducedQuantumCofactor ActualSourcePreparedAuxiliaryClockRows
open ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedEMClockEquation ActualSourcePreparedEMJacobiRow
open ActualSourcePreparedEMNativeRow ActualSourcePreparedEMNativeRead
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMNativeAuxiliary ActualPreparedMatterSupport SourcePropagationNativeActionHessian
open scoped Matrix BigOperators
attribute [local irreducible] sourceAuxiliaryReducedPencil sourceEMClockForce
  sourceFourClockDenominator sourceTemporalEMForce sourceReducedClockFieldNumerator
  sourceReducedClockDeterminant Matrix.det Matrix.adjugate Matrix.mulVec

private def matterWholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem matter_whole_left (i : Fin 217) :
    matterWholeIndex (Sum.inl i)=nativeRestIndex i := rfl

private theorem matter_whole_right (pair : Fin 6 × Fin 12) :
    matterWholeIndex (Sum.inr pair)=gaugeAuxiliaryIndex pair := by
  apply Fin.ext
  change 217+(pair.2.val+12*pair.1.val)=217+12*pair.1.val+pair.2.val
  omega

/-- All original rows and columns remain; the generated common factor is now
removed from the remaining 120 source-inactive rows as well. -/
def sourceMatterClockPencil (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  fun i j => if (73 ≤ i.val ∧ i.val < 121) ∨ 145 ≤ i.val
    then staticIRClockSlice (commonJacobi n i j)
    else sourceClockReducedPencil event n i j

def sourceMatterRemainingRowWeight (event : DressedEvent) (n : PhysicalMomentum)
    (i : Fin 289) : ((ℂ[X])[X]) :=
  if (73 ≤ i.val ∧ i.val < 121) ∨ (145 ≤ i.val ∧ i.val < 217)
    then sourceAuxiliaryClockFactor event n else 1

attribute [local irreducible] sourceMatterClockPencil sourceMatterRemainingRowWeight

theorem source_matter_auxiliary_row_factor (event : DressedEvent) (n : PhysicalMomentum) :
    sourceAuxiliaryReducedPencil event n=
      Matrix.diagonal (sourceMatterRemainingRowWeight event n)*
        sourceMatterClockPencil event n := by
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul]
  obtain ⟨r,rfl⟩ := matterWholeIndex.surjective i
  cases r with
  | inl r =>
      have auxP : sourceAuxiliaryReducedPencil event n (matterWholeIndex (Sum.inl r)) j=
          sourceClockReducedPencil event n (nativeRestIndex r) j := by
        unfold sourceAuxiliaryReducedPencil
        change Sum.elim
          (fun r : Fin 217 => sourceClockReducedPencil event n (nativeRestIndex r) j)
          (fun pair : Fin 6 × Fin 12 =>
            staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex pair) j))
          (matterWholeIndex.symm (matterWholeIndex (Sum.inl r))) = _
        rw [Equiv.symm_apply_apply,Sum.elim_inl]
      rw [auxP,matter_whole_left]
      simp only [sourceMatterRemainingRowWeight,sourceMatterClockPencil]
      have hv : (nativeRestIndex r).val=r.val := rfl
      simp only [hv]
      by_cases outside : (73 ≤ r.val ∧ r.val < 121) ∨ 145 ≤ r.val
      · have mask : (73 ≤ r.val ∧ r.val < 121) ∨ (145 ≤ r.val ∧ r.val < 217) := by omega
        rw [if_pos outside,if_pos mask]
        exact source_matter_clock_pencil_row event n (nativeRestIndex r) outside j
      · have nmask : ¬((73 ≤ r.val ∧ r.val < 121) ∨ (145 ≤ r.val ∧ r.val < 217)) := by omega
        rw [if_neg outside,if_neg nmask,one_mul]
  | inr pair =>
      have auxP : sourceAuxiliaryReducedPencil event n (matterWholeIndex (Sum.inr pair)) j=
          staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex pair) j) := by
        unfold sourceAuxiliaryReducedPencil
        change Sum.elim
          (fun r : Fin 217 => sourceClockReducedPencil event n (nativeRestIndex r) j)
          (fun pair : Fin 6 × Fin 12 =>
            staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex pair) j))
          (matterWholeIndex.symm (matterWholeIndex (Sum.inr pair))) = _
        rw [Equiv.symm_apply_apply,Sum.elim_inr]
      rw [auxP,matter_whole_right]
      simp only [sourceMatterRemainingRowWeight,sourceMatterClockPencil]
      have hv : (gaugeAuxiliaryIndex pair).val=217+12*pair.1.val+pair.2.val := by
        dsimp only [gaugeAuxiliaryIndex,gaugeBSlot]
      simp only [hv]
      have nmask : ¬((73 ≤ 217+12*pair.1.val+pair.2.val ∧
          217+12*pair.1.val+pair.2.val < 121) ∨
          (145 ≤ 217+12*pair.1.val+pair.2.val ∧
          217+12*pair.1.val+pair.2.val < 217)) := by omega
      have omask : (73 ≤ 217+12*pair.1.val+pair.2.val ∧
          217+12*pair.1.val+pair.2.val < 121) ∨
          145 ≤ 217+12*pair.1.val+pair.2.val := by omega
      rw [if_neg nmask,if_pos omask,one_mul]

private theorem weights_product_matter (event : DressedEvent) (n : PhysicalMomentum) :
    (∏i : Fin 289, sourceMatterRemainingRowWeight event n i)=
      (sourceAuxiliaryClockFactor event n)^120 := by
  have split : Finset.univ.filter (fun i : Fin 289 =>
        (73 ≤ i.val ∧ i.val < 121) ∨ (145 ≤ i.val ∧ i.val < 217)) =
      Finset.Icc ⟨73,by omega⟩ ⟨120,by omega⟩ ∪
        Finset.Icc ⟨145,by omega⟩ ⟨216,by omega⟩ := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
      Finset.mem_Icc,Fin.le_def]
    omega
  have disj : Disjoint (Finset.Icc (⟨73,by omega⟩ : Fin 289) ⟨120,by omega⟩)
      (Finset.Icc (⟨145,by omega⟩ : Fin 289) ⟨216,by omega⟩) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    simp only [Finset.mem_Icc,Fin.le_def] at h1 h2
    omega
  have count : (Finset.univ.filter (fun i : Fin 289 =>
        (73 ≤ i.val ∧ i.val < 121) ∨ (145 ≤ i.val ∧ i.val < 217))).card = 120 := by
    rw [split,Finset.card_union_of_disjoint disj,Fin.card_Icc,Fin.card_Icc]
    decide
  simp only [sourceMatterRemainingRowWeight]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const,one_pow,mul_one,count]

private theorem diagonal_factor_det {R I : Type*} [CommRing R] [Fintype I] [DecidableEq I]
    (K M : Matrix I I R) (w : I → R) (b : R)
    (rows : K=Matrix.diagonal w*M) (weight : (∏i,w i)=b) : K.det=b*M.det := by
  rw [rows,Matrix.det_mul,Matrix.det_diagonal,weight]

/-- Exactly one hundred twenty remaining source-inactive rows supply the
common factor: the original determinant loses another cubic-clock power. -/
theorem source_matter_auxiliary_determinant_factor (event : DressedEvent)
    (n : PhysicalMomentum) :
    (sourceAuxiliaryReducedPencil event n).det=
      (sourceAuxiliaryClockFactor event n)^120*(sourceMatterClockPencil event n).det :=
  diagonal_factor_det (sourceAuxiliaryReducedPencil event n)
    (sourceMatterClockPencil event n) (sourceMatterRemainingRowWeight event n)
    ((sourceAuxiliaryClockFactor event n)^120)
    (source_matter_auxiliary_row_factor event n) (weights_product_matter event n)

end LowEnergy.GaussComposite.ActualPreparedMatterClock
