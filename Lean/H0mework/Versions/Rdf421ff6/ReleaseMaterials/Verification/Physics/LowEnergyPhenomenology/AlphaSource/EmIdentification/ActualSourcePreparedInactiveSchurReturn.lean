import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedInactiveNativeInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedInactiveSchurReturn
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualEMAction
open ActualDressedOrderedStatic ActualDressedUniformMaterialCoefficients ActualDressedZeroDamping
open ActualPreparedMatterClock ActualPreparedMatterSupport ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedAuxiliaryClockReduction ActualSourcePreparedClockReducedPencil
open ActualSourcePreparedEMClockEquation ActualSourcePreparedMatterClockField
open ActualSourcePreparedMatterClockPrincipal ActualSourcePreparedInactiveNativeCertificate
open ActualSourcePreparedInactiveNativeInverse
open scoped Matrix BigOperators
attribute [local irreducible] commonJacobi emOriginalJacobi sourceMatterClockPencil
  sourceMatterClockActualFieldNumerator Matrix.mulVec Matrix.det

def sourceMatterNativeMatrix (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    Matrix (Fin 289) (Fin 289) ℂ := (sourceMatterClockPencil event n).map (sourceClockEval eps sigma)

def sourceMatterNativeSchur (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    Matrix NativeActive NativeActive ℂ :=
  (sourceMatterNativeMatrix event n eps sigma).submatrix Subtype.val Subtype.val-
    (sourceMatterNativeMatrix event n eps sigma).submatrix
      (Subtype.val : NativeActive → Fin 289) (Subtype.val : NativeInactive → Fin 289)*
    nativeInactiveInverse (frequencyRay eps 0 n)*
    (sourceMatterNativeMatrix event n eps sigma).submatrix
      (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289)

private theorem actual_inactive_block (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    (sourceMatterNativeMatrix event n eps sigma).submatrix
      (Subtype.val : NativeInactive → Fin 289) Subtype.val=nativeInactiveBlock (frequencyRay eps 0 n) := by
  ext i j
  have outside : (73 ≤ i.val.val ∧ i.val.val < 121) ∨ 145 ≤ i.val.val := i.property
  simp only [sourceMatterNativeMatrix,Matrix.submatrix_apply,Matrix.map_apply,
    sourceMatterClockPencil,if_pos outside,nativeInactiveBlock]
  have source := congrFun (congrFun (common_jacobi_eval n eps sigma 0) i.val) j.val
  change MvPolynomial.eval (irValues eps sigma 0) (commonJacobi n i.val j.val)=_ at source
  change (clockSpecialize eps (staticIRClockSlice (commonJacobi n i.val j.val))).eval (sigma:ℂ)=_
  rw [ir_clock_specialize,damping_slice_eval]
  exact source

private theorem mapped_force (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceEMClockForce=sourceTemporalEMForce := by
  funext i
  simp only [Function.comp_apply,sourceEMClockForce,sourceClockEval,RingHom.comp_apply,
    clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem map_field_equation {I : Type*} [Fintype I]
    (f : ((ℂ[X])[X]) →+* ℂ) (P : Matrix I I ((ℂ[X])[X]))
    (N E : I → (ℂ[X])[X]) (a : (ℂ[X])[X]) (field : P*ᵥN=a • E) :
    P.map f*ᵥ(f ∘ N)=f a • (f ∘ E) := by
  funext i
  have point := congrArg f (congrFun field i)
  change f ((P*ᵥN) i)=f (a*E i) at point
  rw [f.map_mulVec,map_mul] at point
  exact point

private theorem actual_cofactor_field (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceMatterNativeMatrix event n eps sigma*ᵥsourceMatterClockActualFieldNumerator event n eps sigma=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n*sourceMatterClockDeterminant event n) •
        sourceTemporalEMForce := by
  have point := map_field_equation (sourceClockEval eps sigma) _ _ _ _
    (source_matter_clock_field_equation event n)
  rw [source_matter_clock_field_eval,mapped_force] at point
  exact point

private theorem blocks {M A I : Type*} [Fintype M] [Fintype A]
    (e : M ⊕ A ≃ I) (P : Matrix I I ℂ) :
    P.submatrix e e=Matrix.fromBlocks
      (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
      (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
      (P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl))
      (P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  ext (i|i) (j|j) <;> rfl

private theorem block_field {M A I : Type*} [Fintype M] [Fintype A] [Fintype I]
    [DecidableEq A] (e : M ⊕ A ≃ I) (P : Matrix I I ℂ)
    (H : Matrix A A ℂ) (v E : I → ℂ) (a : ℂ)
    (inverse : H*P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)=1)
    (zero : E ∘ e ∘ Sum.inr=0) (field : P*ᵥv=a • E) :
    v ∘ e ∘ Sum.inr= -(H*ᵥ(P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)*ᵥ(v ∘ e ∘ Sum.inl))) ∧
    (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)-
      P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)*H*
        P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl))*ᵥ(v ∘ e ∘ Sum.inl)=a • (E ∘ e ∘ Sum.inl) := by
  have reindexed : P.submatrix e e*ᵥ(v ∘ e)=(P*ᵥv) ∘ e := by
    rw [Matrix.submatrix_mulVec_equiv]
    have same : (v ∘ e) ∘ e.symm=v := by funext i; simp only [Function.comp_apply,Equiv.apply_symm_apply]
    rw [same]
  rw [blocks,Matrix.fromBlocks_mulVec,field] at reindexed
  have aux := congrArg (fun z : M ⊕ A → ℂ => z ∘ Sum.inr) reindexed
  have rest := congrArg (fun z : M ⊕ A → ℂ => z ∘ Sum.inl) reindexed
  simp only [Function.comp_def,Sum.elim_inr,Pi.smul_apply,smul_eq_mul] at aux
  simp only [Function.comp_def,Sum.elim_inl,Pi.smul_apply,smul_eq_mul] at rest
  have right_zero : (fun x => a*E (e (Sum.inr x)))=0 := by
    funext i
    have point := congrFun zero i
    change E (e (Sum.inr i))=0 at point
    simp only [point,Pi.zero_apply,mul_zero]
  rw [right_zero] at aux
  have forced : P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)*ᵥ(v ∘ e ∘ Sum.inr)=
      -(P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)*ᵥ(v ∘ e ∘ Sum.inl)) :=
    eq_neg_of_add_eq_zero_right aux
  have solved := congrArg (fun z => H*ᵥz) forced
  rw [Matrix.mulVec_mulVec,inverse,Matrix.one_mulVec,Matrix.mulVec_neg] at solved
  constructor
  · exact solved
  · change P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)*ᵥ(v ∘ e ∘ Sum.inl)+
      P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)*ᵥ(v ∘ e ∘ Sum.inr)=a • (E ∘ e ∘ Sum.inl) at rest
    rw [solved,Matrix.mulVec_neg] at rest
    rw [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
    simpa only [sub_eq_add_neg] using rest

/-- The full prepared cofactor generates a97 Schur equation and restores
all192 complementary fields. Every original quantum cross column survives. -/
theorem source_matter_native_schur_cofactor_field (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    (sourceMatterClockActualFieldNumerator event n eps sigma ∘ (Subtype.val : NativeInactive → Fin 289))=
      -(nativeInactiveInverse (frequencyRay eps 0 n)*ᵥ
        ((sourceMatterNativeMatrix event n eps sigma).submatrix
          (Subtype.val : NativeInactive → Fin 289) (Subtype.val : NativeActive → Fin 289)*ᵥ
            (sourceMatterClockActualFieldNumerator event n eps sigma ∘ Subtype.val))) ∧
    sourceMatterNativeSchur event n eps sigma*ᵥ
      (sourceMatterClockActualFieldNumerator event n eps sigma ∘ Subtype.val)=
      sourceClockEval eps sigma (sourceAuxiliaryClockFactor event n*sourceMatterClockDeterminant event n) •
        (sourceTemporalEMForce ∘ Subtype.val) := by
  have right : (nativeWholeIndex ∘ Sum.inr : NativeInactive → Fin 289)=Subtype.val := rfl
  have left : (nativeWholeIndex ∘ Sum.inl : NativeActive → Fin 289)=Subtype.val := rfl
  have inverse : nativeInactiveInverse (frequencyRay eps 0 n)*
      (sourceMatterNativeMatrix event n eps sigma).submatrix (nativeWholeIndex ∘ Sum.inr) (nativeWholeIndex ∘ Sum.inr)=1 := by
    rw [right,actual_inactive_block]
    exact (source_inactive_native_physical_inverse eps n unit positive small).1
  have zero : sourceTemporalEMForce ∘ nativeWholeIndex ∘ Sum.inr=0 := by
    funext i
    change sourceTemporalEMForce i.val=0
    exact actual_em_force_inactive_zero i.val i.property
  have generated := block_field nativeWholeIndex _ _ _ _ _ inverse zero (actual_cofactor_field event n eps sigma)
  simpa only [left,right,sourceMatterNativeSchur] using generated

private theorem determinant_schur {M A I : Type*}
    [Fintype M] [DecidableEq M] [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (e : M ⊕ A ≃ I) (P : Matrix I I ℂ) (H : Matrix A A ℂ)
    (left : H*P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)=1)
    (right : P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)*H=1) :
    P.det=(P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)).det*
      (P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)-
        P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr)*H*
          P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inl)).det := by
  let : Invertible (P.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := ⟨H,left,right⟩
  rw [←Matrix.det_submatrix_equiv_self e P,blocks,Matrix.det_fromBlocks₂₂]
  rfl

/-- Full-source determinant factorization on the native source ball.
No complete97 determinant or physical Green nonzero value is supplied. -/
theorem source_matter_native_schur_determinant (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma : ℝ) (unit : spatialSquare n=1) (positive : 0<eps) (small : eps≤1/2) :
    sourceMatterClockActualDeterminant event n eps sigma=
      (nativeInactiveBlock (frequencyRay eps 0 n)).det*(sourceMatterNativeSchur event n eps sigma).det := by
  have right : (nativeWholeIndex ∘ Sum.inr : NativeInactive → Fin 289)=Subtype.val := rfl
  have left : (nativeWholeIndex ∘ Sum.inl : NativeActive → Fin 289)=Subtype.val := rfl
  have inverse := source_inactive_native_physical_inverse eps n unit positive small
  have block := actual_inactive_block event n eps sigma
  have l : nativeInactiveInverse (frequencyRay eps 0 n)*
      (sourceMatterNativeMatrix event n eps sigma).submatrix (nativeWholeIndex ∘ Sum.inr) (nativeWholeIndex ∘ Sum.inr)=1 := by
    rw [right,block];exact inverse.1
  have r : (sourceMatterNativeMatrix event n eps sigma).submatrix (nativeWholeIndex ∘ Sum.inr) (nativeWholeIndex ∘ Sum.inr)*
      nativeInactiveInverse (frequencyRay eps 0 n)=1 := by
    rw [right,block];exact inverse.2
  have generated := determinant_schur nativeWholeIndex (sourceMatterNativeMatrix event n eps sigma)
    (nativeInactiveInverse (frequencyRay eps 0 n)) l r
  rw [right,left,block] at generated
  simpa only [sourceMatterNativeSchur,sourceMatterClockActualDeterminant,sourceMatterNativeMatrix] using generated

end LowEnergy.GaussComposite.ActualSourcePreparedInactiveSchurReturn
