import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedAuxiliaryActualReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMAuxiliaryInverseMatrix
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryClockSchur
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic SourcePropagationNativeActionHessian
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualEMAction
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualDressedEMNativeAuxiliary ActualDressedEMAuxiliaryFeedback
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedFourClockCarrier
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedAuxiliaryActualReturn
open scoped Matrix BigOperators
attribute [local irreducible] sourceClockReducedPencil sourceAuxiliaryReducedPencil
  commonJacobi emOriginalJacobi nativeAuxiliaryInverseMatrix Matrix.det Matrix.mulVec

private def wholeIndex : Fin 217 ⊕ (Fin 6 × Fin 12) ≃ Fin 289 :=
  (Equiv.sumCongr (Equiv.refl (Fin 217)) finProdFinEquiv).trans finSumFinEquiv

private theorem whole_right (pair : Fin 6 × Fin 12) : wholeIndex (Sum.inr pair)=gaugeAuxiliaryIndex pair := by
  apply Fin.ext
  change 217+(pair.2.val+12*pair.1.val)=217+12*pair.1.val+pair.2.val
  omega

private theorem reduced_auxiliary_row (event : DressedEvent) (n : PhysicalMomentum)
    (pair : Fin 6 × Fin 12) (j : Fin 289) :
    sourceAuxiliaryReducedPencil event n (gaugeAuxiliaryIndex pair) j=
      staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex pair) j) := by
  have index : wholeIndex.symm (gaugeAuxiliaryIndex pair)=Sum.inr pair := by
    apply wholeIndex.injective
    rw [Equiv.apply_symm_apply,whole_right]
  unfold sourceAuxiliaryReducedPencil
  change Sum.elim (fun r : Fin 217 => sourceClockReducedPencil event n (nativeRestIndex r) j)
    (fun q : Fin 6 × Fin 12 => staticIRClockSlice (commonJacobi n (gaugeAuxiliaryIndex q) j))
    (wholeIndex.symm (gaugeAuxiliaryIndex pair))=_
  rw [index]
  rfl

private theorem positive_polynomial_zero (P : ℂ[X])
    (zero : ∀ s : ℝ, 0<s → P.eval (s : ℂ)=0) : P=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have injective : Function.Injective (fun k : ℕ => ((k+1 : ℕ) : ℂ)) := by
    intro a b same
    change ((a+1 : ℕ) : ℂ)=((b+1 : ℕ) : ℂ) at same
    have natural : a+1=b+1 := by exact_mod_cast same
    omega
  refine (Set.infinite_range_of_injective injective).mono ?_
  rintro z ⟨k,rfl⟩
  change P.eval ((k+1 : ℕ) : ℂ)=0
  have point : (((k : ℝ)+1 : ℝ) : ℂ)=((k+1 : ℕ) : ℂ) := by push_cast;rfl
  rw [←point]
  exact zero ((k : ℝ)+1) (by positivity)

private theorem clock_polynomial_zero (P : (ℂ[X])[X])
    (zero : ∀ eps sigma : ℝ, 0<sigma → sourceClockEval eps sigma P=0) : P=0 := by
  have specialized (eps : ℝ) : clockSpecialize eps P=0 :=
    positive_polynomial_zero _ (fun sigma positive => zero eps sigma positive)
  apply Polynomial.ext
  intro k
  rw [coeff_zero]
  apply positive_polynomial_zero
  intro eps _
  have coefficient := congrArg (fun Q : ℂ[X] => Q.coeff k) (specialized eps)
  simpa only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,coeff_zero,
    Polynomial.coe_evalRingHom] using coefficient

private def clockConstant : ℂ →+* (ℂ[X])[X] :=
  (Polynomial.C : ℂ[X] →+* (ℂ[X])[X]).comp (Polynomial.C : ℂ →+* ℂ[X])

private theorem clock_constant_eval (eps sigma : ℝ) (z : ℂ) :
    sourceClockEval eps sigma (clockConstant z)=z := by
  simp only [clockConstant,RingHom.comp_apply,sourceClockEval,clockSpecialize,
    Polynomial.coe_mapRingHom,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem clock_slice_eval (eps sigma : ℝ) (P : Parameters) :
    sourceClockEval eps sigma (staticIRClockSlice P)=MvPolynomial.eval (irValues eps sigma 0) P := by
  change (clockSpecialize eps (staticIRClockSlice P)).eval (sigma : ℂ)=_
  rw [ir_clock_specialize,damping_slice_eval]

def sourceAuxiliaryClockBlock (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 6 × Fin 12) (Fin 6 × Fin 12) ((ℂ[X])[X]) :=
  (sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex gaugeAuxiliaryIndex

def sourceAuxiliaryClockInverse : Matrix (Fin 6 × Fin 12) (Fin 6 × Fin 12) ((ℂ[X])[X]) :=
  nativeAuxiliaryInverseMatrix.map clockConstant

/-- The same original algebraic auxiliary block is constant before either
physical scale is specialized, including both zero-coordinate faces. -/
theorem source_auxiliary_clock_block_constant (event : DressedEvent) (n : PhysicalMomentum) :
    sourceAuxiliaryClockBlock event n=originalGaugeAuxiliaryUnit.map clockConstant := by
  apply Matrix.ext
  intro i j
  apply sub_eq_zero.mp
  apply clock_polynomial_zero
  intro eps sigma _
  simp only [sourceAuxiliaryClockBlock,Matrix.submatrix_apply,Matrix.map_apply,map_sub,
    reduced_auxiliary_row,clock_constant_eval,clock_slice_eval]
  apply sub_eq_zero.mpr
  have jacobi := congrFun (congrFun (common_jacobi_eval n eps sigma 0)
    (gaugeAuxiliaryIndex i)) (gaugeAuxiliaryIndex j)
  change MvPolynomial.eval (irValues eps sigma 0)
    (commonJacobi n (gaugeAuxiliaryIndex i) (gaugeAuxiliaryIndex j))=_ at jacobi
  have native := congrFun (congrFun (actual_native_gauge_auxiliary_unit (frequencyRay eps 0 n)) i) j
  exact jacobi.trans native

private theorem mapped_inverse {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (f : R →+* S) (A B : Matrix I I R)
    (left : A*B=1) (right : B*A=1) : A.map f*B.map f=1 ∧ B.map f*A.map f=1 := by
  constructor
  · calc
      A.map f*B.map f=(A*B).map f := Matrix.map_mul.symm
      _=(1 : Matrix I I R).map f := congrArg (fun M : Matrix I I R => M.map f) left
      _=1 := Matrix.map_one f f.map_zero f.map_one
  · calc
      B.map f*A.map f=(B*A).map f := Matrix.map_mul.symm
      _=(1 : Matrix I I R).map f := congrArg (fun M : Matrix I I R => M.map f) right
      _=1 := Matrix.map_one f f.map_zero f.map_one

/-- The original source colour/lapse inverse supplies the full polynomial
block inverse; no full Green regularity or extra inverse witness enters. -/
theorem source_auxiliary_clock_block_inverse (event : DressedEvent) (n : PhysicalMomentum) :
    sourceAuxiliaryClockInverse*sourceAuxiliaryClockBlock event n=1 ∧
      sourceAuxiliaryClockBlock event n*sourceAuxiliaryClockInverse=1 := by
  have left := actual_native_auxiliary_matrix_left (0 : Fin 4 → ℂ)
  have right := actual_native_auxiliary_matrix_right (0 : Fin 4 → ℂ)
  rw [actual_native_gauge_auxiliary_unit] at left right
  rw [source_auxiliary_clock_block_constant]
  unfold sourceAuxiliaryClockInverse
  exact mapped_inverse clockConstant nativeAuxiliaryInverseMatrix originalGaugeAuxiliaryUnit left right


private theorem whole_left (i : Fin 217) : wholeIndex (Sum.inl i)=nativeRestIndex i := rfl

-- Fix coefficient operations while keeping finite indices abstract for kernel checking.
private def genericSchurPencil {M A : Type*} [Fintype M] [Fintype A]
    (B : Matrix M M ((ℂ[X])[X])) (C : Matrix M A ((ℂ[X])[X]))
    (D : Matrix A M ((ℂ[X])[X])) (H : Matrix A A ((ℂ[X])[X])) :
    Matrix M M ((ℂ[X])[X]) := B-C*H*D

attribute [local irreducible] genericSchurPencil

/-- The remaining source matrix retains all prepared quantum cross columns. -/
def sourceAuxiliaryClockSchurPencil (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 217) (Fin 217) ((ℂ[X])[X]) :=
  genericSchurPencil
    ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex nativeRestIndex)
    ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex gaugeAuxiliaryIndex)
    ((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex)
    sourceAuxiliaryClockInverse

private theorem source_blocks (event : DressedEvent) (n : PhysicalMomentum) :
    (sourceAuxiliaryReducedPencil event n).submatrix wholeIndex wholeIndex=
      Matrix.fromBlocks
        ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex nativeRestIndex)
        ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex gaugeAuxiliaryIndex)
        ((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex)
        (sourceAuxiliaryClockBlock event n) := by
  apply Matrix.ext
  intro i j
  cases i with
  | inl i =>
      cases j with
      | inl j => simp only [Matrix.submatrix_apply,whole_left,Matrix.fromBlocks_apply₁₁]
      | inr j => simp only [Matrix.submatrix_apply,whole_left,whole_right,Matrix.fromBlocks_apply₁₂]
  | inr i =>
      cases j with
      | inl j => simp only [Matrix.submatrix_apply,whole_left,whole_right,Matrix.fromBlocks_apply₂₁]
      | inr j => simp only [Matrix.submatrix_apply,whole_right,Matrix.fromBlocks_apply₂₂,
          sourceAuxiliaryClockBlock]


private theorem schur_det_source {M A I : Type*}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (e : M ⊕ A ≃ I) (P : Matrix I I ((ℂ[X])[X])) (B : Matrix M M ((ℂ[X])[X])) (C : Matrix M A ((ℂ[X])[X]))
    (D : Matrix A M ((ℂ[X])[X])) (F H : Matrix A A ((ℂ[X])[X])) (S : Matrix M M ((ℂ[X])[X]))
    (blocks : P.submatrix e e=Matrix.fromBlocks B C D F)
    (left : H*F=1) (right : F*H=1) (schur : S=genericSchurPencil B C D H) : P.det=F.det*S.det := by
  rw [schur]
  unfold genericSchurPencil
  let : Invertible F := ⟨H,left,right⟩
  rw [←Matrix.det_submatrix_equiv_self e P,blocks,Matrix.det_fromBlocks₂₂]
  rfl


/-- Full source determinant reduction; the removed factor is the original
algebraic auxiliary block, and all quantum cross terms remain in Schur217. -/
theorem source_auxiliary_clock_schur_determinant (event : DressedEvent) (n : PhysicalMomentum) :
    (sourceAuxiliaryReducedPencil event n).det=
      (sourceAuxiliaryClockBlock event n).det*(sourceAuxiliaryClockSchurPencil event n).det := by
  exact schur_det_source wholeIndex (sourceAuxiliaryReducedPencil event n)
    ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex nativeRestIndex)
    ((sourceAuxiliaryReducedPencil event n).submatrix nativeRestIndex gaugeAuxiliaryIndex)
    ((sourceAuxiliaryReducedPencil event n).submatrix gaugeAuxiliaryIndex nativeRestIndex)
    (sourceAuxiliaryClockBlock event n) sourceAuxiliaryClockInverse
    (sourceAuxiliaryClockSchurPencil event n) (source_blocks event n)
    (source_auxiliary_clock_block_inverse event n).1 (source_auxiliary_clock_block_inverse event n).2 rfl


end LowEnergy.GaussComposite.ActualSourcePreparedAuxiliaryClockSchur
