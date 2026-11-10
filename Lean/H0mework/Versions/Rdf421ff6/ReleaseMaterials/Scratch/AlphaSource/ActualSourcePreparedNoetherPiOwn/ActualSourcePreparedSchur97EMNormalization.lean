import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97Cofactor
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97PolynomialNormalization

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97EMNormalization
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic ActualDressedFullCoulomb ActualDressedNoetherCoulombUnit
open ActualDressedOrderedStatic ActualDressedCorrectedGreen ActualDressedUniformMaterialCoefficients
open ActualSourcePreparedSchur97PhysicalRead ActualSourcePreparedN3EMChargeRead ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedInactiveSchurReturn ActualSourcePreparedSchur97Normalization
open ActualPreparedMatterSupport ActualPreparedMatterClock
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedAuxiliaryClockReduction
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedEMClockEquation
open ActualSourcePreparedMatterClockField ActualSourcePreparedMatterClockPrincipal
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedSchur97Polynomial
open ActualSourcePreparedSchur97Cofactor ActualSourcePreparedSchur97PolynomialNormalization
open scoped Matrix BigOperators

private theorem inactive_force (i : NativeInactive) : sourceEMClockForce i.val=0 := by
  unfold sourceEMClockForce
  rw [actual_em_force_inactive_zero i.val i.property,map_zero,map_zero]

private theorem dot_restrict {M A I R : Type*}
    [Fintype M] [Fintype A] [Fintype I] [CommRing R]
    (e : M ⊕ A ≃ I) (E v : I → R) (zero : ∀ i : A,E (e (Sum.inr i))=0) :
    dotProduct E v=dotProduct (E ∘ e ∘ Sum.inl) (v ∘ e ∘ Sum.inl) := by
  unfold dotProduct
  rw [←e.sum_comp,Fintype.sum_sum_type]
  have vanished : (∑i : A,E (e (Sum.inr i))*v (e (Sum.inr i)))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [zero i,zero_mul]
  change (∑i : M,E (e (Sum.inl i))*v (e (Sum.inl i)))+
    (∑i : A,E (e (Sum.inr i))*v (e (Sum.inr i)))=_
  rw [vanished,add_zero]
  rfl

private theorem force_dot_restrict (v : Fin 289 → (ℂ[X])[X]) :
    dotProduct sourceEMClockForce v=
      dotProduct sourceSchur97Force (v ∘ (Subtype.val : NativeActive → Fin 289)) := by
  exact dot_restrict nativeWholeIndex sourceEMClockForce v inactive_force

private theorem mulVec_restrict {M A I R : Type*}
    [Fintype M] [Fintype A] [Fintype I] [CommRing R]
    (e : M ⊕ A ≃ I) (E : I → R) (P : Matrix I I R)
    (zero : ∀ i : A,E (e (Sum.inr i))=0) :
    (P*ᵥE) ∘ e ∘ Sum.inl=P.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl)*ᵥ(E ∘ e ∘ Sum.inl) := by
  funext i
  change dotProduct (P (e (Sum.inl i))) E=
    dotProduct (P (e (Sum.inl i)) ∘ e ∘ Sum.inl) (E ∘ e ∘ Sum.inl)
  exact (dotProduct_comm _ _).trans
    ((dot_restrict e E (P (e (Sum.inl i))) zero).trans (dotProduct_comm _ _))

private theorem force_mulVec_restrict (P : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X])) :
    (P*ᵥsourceEMClockForce) ∘ (Subtype.val : NativeActive → Fin 289)=
      P.submatrix Subtype.val Subtype.val*ᵥsourceSchur97Force := by
  exact mulVec_restrict nativeWholeIndex sourceEMClockForce P inactive_force

private theorem complete_contraction (P : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]))
    (c : (ℂ[X])[X]) :
    dotProduct sourceEMClockForce (c • (P*ᵥsourceEMClockForce))=
      c*dotProduct sourceSchur97Force
        (P.submatrix (Subtype.val : NativeActive → Fin 289) Subtype.val*ᵥsourceSchur97Force) := by
  rw [dotProduct_smul,smul_eq_mul,force_dot_restrict,force_mulVec_restrict]

private theorem real_polynomial_zero (P : ℂ[X])
    (zero : ∀ s : ℝ, P.eval (s:ℂ)=0) : P=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have injective : Function.Injective (fun k : ℕ => ((k+1:ℕ):ℂ)) := by
    intro a b same
    change ((a+1:ℕ):ℂ)=((b+1:ℕ):ℂ) at same
    have natural : a+1=b+1 := by exact_mod_cast same
    omega
  refine (Set.infinite_range_of_injective injective).mono ?_
  rintro z ⟨k,rfl⟩
  change P.eval ((k+1:ℕ):ℂ)=0
  have point : (((k:ℝ)+1:ℝ):ℂ)=((k+1:ℕ):ℂ) := by push_cast; rfl
  rw [←point]
  exact zero ((k:ℝ)+1)


private theorem small_polynomial_zero (P : ℂ[X])
    (zero : ∀ eps : ℝ, 0<eps → eps≤1/2 → P.eval (eps:ℂ)=0) : P=0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  have interval : Set.Infinite (Set.Ioo (0:ℝ) (1/2)) := Set.Ioo_infinite (by norm_num)
  refine (interval.image Complex.ofReal_injective.injOn).mono ?_
  rintro z ⟨eps,inside,rfl⟩
  exact zero eps inside.1 inside.2.le


private theorem source_rectangle_zero (P : (ℂ[X])[X])
    (zero : ∀ eps sigma : ℝ, 0<eps → eps≤1/2 → sourceClockEval eps sigma P=0) : P=0 := by
  have specialized (eps : ℝ) (positive : 0<eps) (small : eps≤1/2) : clockSpecialize eps P=0 :=
    real_polynomial_zero _ (fun sigma => zero eps sigma positive small)
  apply Polynomial.ext
  intro k
  rw [coeff_zero]
  apply small_polynomial_zero
  intro eps positive small
  have coefficient := congrArg (fun Q : ℂ[X] => Q.coeff k) (specialized eps positive small)
  simpa only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map,coeff_zero,
    Polynomial.coe_evalRingHom] using coefficient


private theorem map_vector {I J : Type*} [Fintype J]
    (f : ((ℂ[X])[X]) →+* ℂ) (P : Matrix I J ((ℂ[X])[X])) (v : J → (ℂ[X])[X]) :
    f ∘ (P*ᵥv)=(P.map f)*ᵥ(f ∘ v) := by
  funext i
  exact f.map_mulVec P v i

private theorem map_pairing {I : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (P : Matrix I I ((ℂ[X])[X]))
    (a : (ℂ[X])[X]) (u v : I → (ℂ[X])[X]) :
    f (a*dotProduct u (P.adjugate*ᵥv))=
      f a*dotProduct (f ∘ u) ((P.map f).adjugate*ᵥ(f ∘ v)) := by
  rw [map_mul,f.map_dotProduct,map_vector]
  have adj := f.map_adjugate P
  simp only [RingHom.mapMatrix_apply] at adj
  rw [adj]

private theorem pairing_map_submatrix {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (f : ((ℂ[X])[X]) →+* ℂ) (P : Matrix I I ((ℂ[X])[X]))
    (a : (ℂ[X])[X]) (u v : J → (ℂ[X])[X]) (r : J → I) :
    f (a*dotProduct u (P.adjugate.submatrix r r*ᵥv))=
      f a*dotProduct (f ∘ u) ((P.map f).adjugate.submatrix r r*ᵥ(f ∘ v)) := by
  rw [map_mul,f.map_dotProduct,map_vector]
  have adj := f.map_adjugate P
  simp only [RingHom.mapMatrix_apply] at adj
  have sub : (P.adjugate.submatrix r r).map f=(P.map f).adjugate.submatrix r r :=
    congrArg (fun M : Matrix I I ℂ => M.submatrix r r) adj
  rw [sub]

private theorem scalar_pairing_lift {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : Matrix I I ((ℂ[X])[X])) (Q : Matrix J J ((ℂ[X])[X]))
    (d D : (ℂ[X])[X]) (E : J → (ℂ[X])[X]) (r : J → I)
    (point : ∀ eps sigma : ℝ, 0<eps → eps≤1/2 →
      (sourceClockEval eps sigma d*sourceClockEval eps sigma D)*
        dotProduct (sourceClockEval eps sigma ∘ E)
          ((Q.map (sourceClockEval eps sigma)).adjugate*ᵥ(sourceClockEval eps sigma ∘ E))=
      (Q.map (sourceClockEval eps sigma)).det*
        dotProduct (sourceClockEval eps sigma ∘ E)
          ((P.map (sourceClockEval eps sigma)).adjugate.submatrix r r*ᵥ(sourceClockEval eps sigma ∘ E))) :
    (d*D)*dotProduct E (Q.adjugate*ᵥE)=Q.det*dotProduct E (P.adjugate.submatrix r r*ᵥE) := by
  apply sub_eq_zero.mp
  apply source_rectangle_zero
  intro eps sigma positive small
  rw [map_sub,map_pairing,pairing_map_submatrix,map_mul]
  have determinant := (sourceClockEval eps sigma).map_det Q
  simp only [RingHom.mapMatrix_apply] at determinant
  rw [determinant]
  exact sub_eq_zero.mpr (point eps sigma positive small)

private theorem force_eval (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceSchur97Force=
      sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289) := by
  funext i
  simp only [Function.comp_apply,sourceSchur97Force,sourceEMClockForce,sourceClockEval,
    RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem point_read_bridge {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : Matrix I I ℂ) (Q : Matrix J J ℂ) (r : J → I) (d D actual : ℂ)
    (E force : J → ℂ) (determinant : D=actual) (forcing : E=force)
    (cross : (d*actual)*dotProduct force (Q.adjugate*ᵥforce)=
      Q.det*dotProduct force (P.adjugate.submatrix r r*ᵥforce)) :
    (d*D)*dotProduct E (Q.adjugate*ᵥE)=Q.det*dotProduct E (P.adjugate.submatrix r r*ᵥE) := by
  rw [determinant,forcing]
  exact cross

attribute [local irreducible] Matrix.det Matrix.adjugate Matrix.mulVec sourceClockEval
  sourceMatterClockPencil sourceSchur97Polynomial sourceEMClockForce sourceSchur97Force

/-- Both EM scalar cofactors retain one source bivariate rational occurrence;
unit directions preserve epsilon/sigma independently, including singular loci. -/
theorem source_schur97_em_scalar_cofactor_cross (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    (nativeClockDenominator n*sourceMatterClockDeterminant event n)*
      dotProduct sourceSchur97Force ((sourceSchur97Polynomial event n).adjugate*ᵥsourceSchur97Force)=
    (sourceSchur97Polynomial event n).det*
      dotProduct sourceSchur97Force ((sourceMatterClockPencil event n).adjugate.submatrix
        (Subtype.val : NativeActive → Fin 289) Subtype.val*ᵥsourceSchur97Force) := by
  refine scalar_pairing_lift (sourceMatterClockPencil event n) (sourceSchur97Polynomial event n)
    (nativeClockDenominator n) (sourceMatterClockDeterminant event n) sourceSchur97Force
    (Subtype.val : NativeActive → Fin 289) ?_
  intro eps sigma positive small
  exact point_read_bridge (sourceMatterNativeMatrix event n eps sigma)
    ((sourceSchur97Polynomial event n).map (sourceClockEval eps sigma))
    (Subtype.val : NativeActive → Fin 289)
    (sourceClockEval eps sigma (nativeClockDenominator n))
    (sourceClockEval eps sigma (sourceMatterClockDeterminant event n))
    (sourceMatterClockActualDeterminant event n eps sigma)
    (sourceClockEval eps sigma ∘ sourceSchur97Force)
    (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
    (source_matter_clock_determinant_eval event n eps sigma) (force_eval eps sigma)
    (source_schur97_current_cofactor_cross event n eps sigma unit positive small
      (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289))
      (sourceTemporalEMForce ∘ (Subtype.val : NativeActive → Fin 289)))


end LowEnergy.GaussComposite.ActualSourcePreparedSchur97EMNormalization
