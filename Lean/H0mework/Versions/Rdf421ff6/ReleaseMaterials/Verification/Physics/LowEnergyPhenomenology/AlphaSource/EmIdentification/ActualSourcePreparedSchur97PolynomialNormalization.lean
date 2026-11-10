import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchur97Normalization
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchur97PolynomialNormalization
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open ActualDressedFullCoulomb PreparationVacuumPhysicalCharacteristic
open ActualDressedOrderedStatic ActualPreparedMatterClock ActualPreparedMatterSupport
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedMatterClockField
open ActualSourcePreparedInactiveNativeInverse ActualSourcePreparedInactiveSchurReturn
open ActualSourcePreparedSchur97Polynomial ActualSourcePreparedSchur97Normalization
open scoped Matrix BigOperators
attribute [local irreducible] Matrix.det Matrix.adjugate sourceMatterClockDeterminant
  sourceMatterClockPencil sourceSchur97Polynomial

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


private theorem matrix_rectangle_eq {I J : Type*}
    (M N : Matrix I J ((ℂ[X])[X]))
    (point : ∀ eps sigma : ℝ, 0<eps → eps≤1/2 →
      M.map (sourceClockEval eps sigma)=N.map (sourceClockEval eps sigma)) : M=N := by
  apply Matrix.ext
  intro i j
  apply sub_eq_zero.mp
  apply source_rectangle_zero
  intro eps sigma positive small
  rw [map_sub]
  exact sub_eq_zero.mpr (congrFun (congrFun (point eps sigma positive small) i) j)


private theorem map_scaled_adjugate {I J : Type*} [Fintype I] [DecidableEq I]
    (f : ((ℂ[X])[X]) →+* ℂ) (a : (ℂ[X])[X])
    (P : Matrix I I ((ℂ[X])[X])) (r : J → I) :
    (a • P.adjugate.submatrix r r).map f=
      f a • (P.map f).adjugate.submatrix r r := by
  have adj := f.map_adjugate P
  simp only [RingHom.mapMatrix_apply] at adj
  apply Matrix.ext
  intro i j
  change f (a*P.adjugate (r i) (r j))=f a*(P.map f).adjugate (r i) (r j)
  have entry : f (P.adjugate (r i) (r j))=(P.map f).adjugate (r i) (r j) :=
    congrFun (congrFun adj (r i)) (r j)
  exact (f.map_mul a (P.adjugate (r i) (r j))).trans
    (congrArg (fun z : ℂ => f a*z) entry)



private theorem polynomial_cross {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : Matrix I I ((ℂ[X])[X])) (Q : Matrix J J ((ℂ[X])[X]))
    (d D : (ℂ[X])[X]) (r : J → I)
    (point : ∀ eps sigma : ℝ, 0<eps → eps≤1/2 →
      (sourceClockEval eps sigma d*sourceClockEval eps sigma D) •
        (Q.map (sourceClockEval eps sigma)).adjugate=
      (Q.map (sourceClockEval eps sigma)).det •
        (P.map (sourceClockEval eps sigma)).adjugate.submatrix r r) :
    (d*D) • Q.adjugate=Q.det • P.adjugate.submatrix r r := by
  apply matrix_rectangle_eq
  intro eps sigma positive small
  let f := sourceClockEval eps sigma
  have determinant := f.map_det Q
  simp only [RingHom.mapMatrix_apply] at determinant
  have left := map_scaled_adjugate f (d*D) Q (id : J → J)
  change ((d*D) • Q.adjugate).map f=f (d*D) • (Q.map f).adjugate at left
  have right := map_scaled_adjugate f Q.det P r
  exact left.trans ((congrArg (fun a : ℂ => a • (Q.map f).adjugate) (f.map_mul d D)).trans
    ((point eps sigma positive small).trans
      ((congrArg (fun a : ℂ => a • (P.map f).adjugate.submatrix r r) determinant.symm).trans right.symm)))

private theorem point_determinant_bridge {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (P : Matrix I I ℂ) (Q : Matrix J J ℂ) (d D actual : ℂ) (r : J → I)
    (determinant : D=actual)
    (cross : (d*actual) • Q.adjugate=Q.det • P.adjugate.submatrix r r) :
    (d*D) • Q.adjugate=Q.det • P.adjugate.submatrix r r := by
  rw [determinant]
  exact cross

attribute [local irreducible] sourceClockEval

/-- The original native clearing is simultaneous in both bivariate cofactors,
for each unit direction before either epsilon or sigma evaluation, including singular loci. -/
theorem source_schur97_polynomial_adjugate_cross (event : DressedEvent) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) :
    (nativeClockDenominator n*sourceMatterClockDeterminant event n) •
      (sourceSchur97Polynomial event n).adjugate=
    (sourceSchur97Polynomial event n).det • (sourceMatterClockPencil event n).adjugate.submatrix
      (Subtype.val : NativeActive → Fin 289) Subtype.val := by
  refine polynomial_cross (sourceMatterClockPencil event n) (sourceSchur97Polynomial event n)
    (nativeClockDenominator n) (sourceMatterClockDeterminant event n)
    (Subtype.val : NativeActive → Fin 289) ?_
  intro eps sigma positive small
  exact point_determinant_bridge
    (sourceMatterNativeMatrix event n eps sigma)
    ((sourceSchur97Polynomial event n).map (sourceClockEval eps sigma))
    (sourceClockEval eps sigma (nativeClockDenominator n))
    (sourceClockEval eps sigma (sourceMatterClockDeterminant event n))
    (sourceMatterClockActualDeterminant event n eps sigma)
    (Subtype.val : NativeActive → Fin 289)
    (source_matter_clock_determinant_eval event n eps sigma)
    (source_schur97_adjugate_cross event n eps sigma unit positive small)





end LowEnergy.GaussComposite.ActualSourcePreparedSchur97PolynomialNormalization
