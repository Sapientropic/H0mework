import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.AdjoinRoot
import H0mework.Foundation.Source.AccountedUnfolding

set_option autoImplicit false

/-!
# Root-generated determinant factorization across a surjective restriction

An actual surjective restriction commuting with source and target actions
generates its invariant kernel, the quotient action and the exact
characteristic-polynomial factorization.  Reversing the monic factors gives

`det(1-XF_source) = det(1-XF_kernel) * det(1-XF_target)`.

The same calculation generates the coordinate-ring transition between the
two universal polynomial zero fibres.  The mouth accepts one local action
row, its actual surjective restriction and commuting square.  It accepts no
kernel basis, quotient equivalence, determinant factor, zero point, coverage,
cofinal table or global component.
-/

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SurjectiveRestrictionActionDeterminant

open Module.Basis

universe u v

theorem charpoly_eq_charpoly_mul_charpoly
    {R : Type u} {V : Type v} [CommRing R] [Nontrivial R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    (W : Submodule R V) [Module.Free R W] [Module.Finite R W]
    [Module.Free R (V ⧸ W)]
    (e : V →ₗ[R] V) (he : W ≤ W.comap e) :
    e.charpoly =
      (e.restrict he).charpoly * (W.mapQ W e he).charpoly := by
  let m := Module.Free.ChooseBasisIndex R W
  let bW : Module.Basis m R W := Module.Free.chooseBasis R W
  let n := Module.Free.ChooseBasisIndex R (V ⧸ W)
  let bQ : Module.Basis n R (V ⧸ W) := Module.Free.chooseBasis R (V ⧸ W)
  let b := sumQuot bW bQ
  let A : Matrix m m R := LinearMap.toMatrix bW bW (e.restrict he)
  let B : Matrix m n R := Matrix.of fun i l ↦
    ((sumQuot bW bQ).repr (e ((sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n R := LinearMap.toMatrix bQ bQ (W.mapQ W e he)
  suffices LinearMap.toMatrix b b e = Matrix.fromBlocks A B 0 D by
    rw [← LinearMap.charpoly_toMatrix e b, this,
      ← LinearMap.charpoly_toMatrix (e.restrict he) bW,
      ← LinearMap.charpoly_toMatrix (W.mapQ W e he) bQ,
      Matrix.charpoly_fromBlocks_zero₂₁]
  ext row column
  cases row with
  | inl i =>
    cases column with
    | inl k =>
      simp only [b, sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
        LinearMap.toMatrix_apply]
      apply sumQuot_repr_inl_of_mem
    | inr l =>
      simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
  | inr j =>
    cases column with
    | inl k =>
      suffices W.mkQ (e (bW k)) = 0 by
        simp [LinearMap.toMatrix_apply, b, this]
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact he (Submodule.coe_mem (bW k))
    | inr l =>
      simp only [LinearMap.toMatrix_apply, sumQuot_repr_inr,
        Matrix.fromBlocks_apply₂₂, b, D]
      rw [← sumQuot_inr bW bQ l, W.mapQ_apply]
      simp

structure SurjectiveRestrictionActionAt
    (R Source Target : Type*) [CommRing R]
    [AddCommGroup Source] [Module R Source]
    [AddCommGroup Target] [Module R Target] where
  sourceAction : Source →ₗ[R] Source
  targetAction : Target →ₗ[R] Target
  restriction : Source →ₗ[R] Target
  restriction_surjective : Function.Surjective restriction
  action_square : restriction.comp sourceAction =
    targetAction.comp restriction

namespace SurjectiveRestrictionActionAt

variable {R Source Target : Type*} [CommRing R]
variable [AddCommGroup Source] [Module R Source]
variable [AddCommGroup Target] [Module R Target]
variable (row : SurjectiveRestrictionActionAt R Source Target)

abbrev Kernel := LinearMap.ker row.restriction

theorem kernel_invariant : row.Kernel ≤ row.Kernel.comap row.sourceAction := by
  intro value value_mem
  rw [LinearMap.mem_ker] at value_mem
  change row.restriction (row.sourceAction value) = 0
  have square := LinearMap.congr_fun row.action_square value
  change row.restriction (row.sourceAction value) =
    row.targetAction (row.restriction value) at square
  rw [value_mem, map_zero] at square
  exact square

def kernelAction : row.Kernel →ₗ[R] row.Kernel :=
  row.sourceAction.restrict row.kernel_invariant

def quotientAction :
    (Source ⧸ row.Kernel) →ₗ[R] (Source ⧸ row.Kernel) :=
  row.Kernel.mapQ row.Kernel row.sourceAction row.kernel_invariant

noncomputable def quotientEquiv :
    (Source ⧸ row.Kernel) ≃ₗ[R] Target :=
  row.restriction.quotKerEquivOfSurjective row.restriction_surjective

theorem quotientAction_conj_eq_target :
    row.quotientEquiv.conj row.quotientAction = row.targetAction := by
  apply LinearMap.ext
  intro target
  obtain ⟨source, rfl⟩ := row.restriction_surjective target
  change row.quotientEquiv
      (row.quotientAction
        (row.quotientEquiv.symm (row.restriction source))) =
    row.targetAction (row.restriction source)
  unfold quotientEquiv
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  change row.quotientEquiv
      (row.Kernel.mkQ (row.sourceAction source)) = _
  unfold quotientEquiv
  change (row.restriction.quotKerEquivOfSurjective
      row.restriction_surjective)
        (Submodule.Quotient.mk (row.sourceAction source)) = _
  rw [LinearMap.quotKerEquivOfSurjective_apply_mk]
  exact LinearMap.congr_fun row.action_square source

end SurjectiveRestrictionActionAt

universe w

structure RootGeneratedSurjectiveRestrictionActionDeterminantAt
    {Root : Type w} {R Source Target : Type*}
    [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup Source] [Module R Source]
    [Module.Free R Source] [Module.Finite R Source]
    [AddCommGroup Target] [Module R Target]
    [Module.Free R Target] [Module.Finite R Target]
    (rootOccurrence : SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootedAccountedUnfolding Root)
    (dependentRowOccurrence :
      SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootedAccountedUnfolding
        (Root × SurjectiveRestrictionActionAt R Source Target))
    (projects : dependentRowOccurrence.map Prod.fst = rootOccurrence) : Type w where
  private mk ::

namespace RootGeneratedSurjectiveRestrictionActionDeterminantAt

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

variable {Root : Type w} {R Source Target : Type*}
variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable [AddCommGroup Source] [Module R Source]
variable [Module.Free R Source] [Module.Finite R Source]
variable [AddCommGroup Target] [Module R Target]
variable [Module.Free R Target] [Module.Finite R Target]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {dependentRowOccurrence : RootedAccountedUnfolding
  (Root × SurjectiveRestrictionActionAt R Source Target)}
variable {projects : dependentRowOccurrence.map Prod.fst = rootOccurrence}

def generate : RootGeneratedSurjectiveRestrictionActionDeterminantAt
    rootOccurrence dependentRowOccurrence projects :=
  ⟨⟩

def root
    (_face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :=
  dependentRowOccurrence.map Prod.fst

def actualRow
    (_face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :=
  dependentRowOccurrence.root.2

private noncomputable def kernelBasis
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    Σ rank : ℕ, Module.Basis (Fin rank) R face.actualRow.Kernel :=
  Submodule.basisOfPid (Module.finBasis R Source) face.actualRow.Kernel

noncomputable instance kernel_free
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    Module.Free R face.actualRow.Kernel :=
  Module.Free.of_basis (face.kernelBasis).2

noncomputable instance kernel_finite
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    Module.Finite R face.actualRow.Kernel :=
  Module.Finite.of_basis (face.kernelBasis).2

noncomputable instance quotient_free
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    Module.Free R (Source ⧸ face.actualRow.Kernel) :=
  Module.Free.of_equiv face.actualRow.quotientEquiv.symm

noncomputable instance quotient_finite
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    Module.Finite R (Source ⧸ face.actualRow.Kernel) :=
  Module.Finite.equiv face.actualRow.quotientEquiv.symm

noncomputable def sourceDeterminantPolynomial
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) : Polynomial R :=
  face.actualRow.sourceAction.charpoly.reverse

noncomputable def relativeKernelDeterminantPolynomial
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) : Polynomial R :=
  face.actualRow.kernelAction.charpoly.reverse

noncomputable def targetDeterminantPolynomial
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) : Polynomial R :=
  face.actualRow.targetAction.charpoly.reverse

theorem quotientAction_charpoly_eq_target
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    face.actualRow.quotientAction.charpoly =
      face.actualRow.targetAction.charpoly := by
  have conjugation := LinearEquiv.charpoly_conj
    face.actualRow.quotientEquiv face.actualRow.quotientAction
  rw [face.actualRow.quotientAction_conj_eq_target] at conjugation
  exact conjugation.symm

theorem source_charpoly_factorization
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    face.actualRow.sourceAction.charpoly =
      face.actualRow.kernelAction.charpoly *
        face.actualRow.targetAction.charpoly := by
  have factorization := charpoly_eq_charpoly_mul_charpoly
    (R := R) (V := Source) face.actualRow.Kernel
      face.actualRow.sourceAction face.actualRow.kernel_invariant
  calc
    face.actualRow.sourceAction.charpoly =
        face.actualRow.kernelAction.charpoly *
          face.actualRow.quotientAction.charpoly := by
      simpa [SurjectiveRestrictionActionAt.kernelAction,
        SurjectiveRestrictionActionAt.quotientAction] using factorization
    _ = face.actualRow.kernelAction.charpoly *
        face.actualRow.targetAction.charpoly := by
      rw [face.quotientAction_charpoly_eq_target]

theorem sourceDeterminantPolynomial_factorization
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    face.sourceDeterminantPolynomial =
      face.relativeKernelDeterminantPolynomial *
        face.targetDeterminantPolynomial := by
  unfold sourceDeterminantPolynomial relativeKernelDeterminantPolynomial
    targetDeterminantPolynomial
  rw [face.source_charpoly_factorization,
    Polynomial.reverse_mul_of_domain]

noncomputable def zeroFiberTransition
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    AdjoinRoot face.sourceDeterminantPolynomial →+*
      AdjoinRoot face.targetDeterminantPolynomial :=
  AdjoinRoot.lift (AdjoinRoot.of face.targetDeterminantPolynomial)
    (AdjoinRoot.root face.targetDeterminantPolynomial) (by
      rw [face.sourceDeterminantPolynomial_factorization,
        Polynomial.eval₂_mul, AdjoinRoot.eval₂_root, mul_zero])

@[simp] theorem zeroFiberTransition_universalPoint
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    face.zeroFiberTransition
        (AdjoinRoot.root face.sourceDeterminantPolynomial) =
      AdjoinRoot.root face.targetDeterminantPolynomial :=
  AdjoinRoot.lift_root _

theorem zeroFiberTransition_comp_universalInclusion
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    face.zeroFiberTransition.comp
        (AdjoinRoot.mk face.sourceDeterminantPolynomial) =
      AdjoinRoot.mk face.targetDeterminantPolynomial := by
  apply Polynomial.ringHom_ext
  · intro coefficient
    simp [zeroFiberTransition]
  · simp [zeroFiberTransition]

theorem preserves_root_and_actual_row
    (face : RootGeneratedSurjectiveRestrictionActionDeterminantAt
      rootOccurrence dependentRowOccurrence projects) :
    face.root = rootOccurrence ∧
      face.actualRow = dependentRowOccurrence.root.2 :=
  ⟨projects, rfl⟩

end RootGeneratedSurjectiveRestrictionActionDeterminantAt

end SurjectiveRestrictionActionDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
