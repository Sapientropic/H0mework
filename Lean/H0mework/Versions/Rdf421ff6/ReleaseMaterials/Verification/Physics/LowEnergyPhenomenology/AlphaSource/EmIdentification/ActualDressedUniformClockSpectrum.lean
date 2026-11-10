import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTwoClockNumerator
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.Smeval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalRayNumerator
open Polynomial
open scoped TensorProduct

private abbrev FreeClock (P Q : ℂ[X]) := AdjoinRoot P ⊗[ℂ] AdjoinRoot Q

private def freeClockGenerator (P Q : ℂ[X]) : FreeClock P Q :=
  Complex.I • ((AdjoinRoot.root P) ⊗ₜ[ℂ] (1:AdjoinRoot Q))+
    (-Complex.I) • ((1:AdjoinRoot P) ⊗ₜ[ℂ] (AdjoinRoot.root Q))

private def freeClockPolynomial (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) : ℂ[X] := by
  letI : Module.Finite ℂ (AdjoinRoot P) := hP.finite_adjoinRoot
  letI : Module.Finite ℂ (AdjoinRoot Q) := hQ.finite_adjoinRoot
  exact (Algebra.lmul ℂ (FreeClock P Q) (freeClockGenerator P Q)).charpoly

private theorem free_clock_monic (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    (freeClockPolynomial P Q hP hQ).Monic := by
  let : Module.Finite ℂ (AdjoinRoot P) := hP.finite_adjoinRoot
  let : Module.Finite ℂ (AdjoinRoot Q) := hQ.finite_adjoinRoot
  exact LinearMap.charpoly_monic _

private theorem free_clock_degree (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    (freeClockPolynomial P Q hP hQ).natDegree=P.natDegree*Q.natDegree := by
  let : Module.Finite ℂ (AdjoinRoot P) := hP.finite_adjoinRoot
  let : Module.Finite ℂ (AdjoinRoot Q) := hQ.finite_adjoinRoot
  unfold freeClockPolynomial
  rw [LinearMap.charpoly_natDegree,Module.finrank_tensorProduct]
  have left : Module.finrank ℂ (AdjoinRoot P)=P.natDegree := (AdjoinRoot.powerBasis' hP).finrank
  have right : Module.finrank ℂ (AdjoinRoot Q)=Q.natDegree := (AdjoinRoot.powerBasis' hQ).finrank
  rw [left,right]

private theorem free_clock_annihilates {A : Type*} [CommRing A] [Algebra ℂ A]
    (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (x y : A) (commutes : Commute x y)
    (hx : aeval x P=0) (hy : aeval y Q=0) :
    aeval (Complex.I • x+(-Complex.I) • y) (freeClockPolynomial P Q hP hQ)=0 := by
  let : Module.Finite ℂ (AdjoinRoot P) := hP.finite_adjoinRoot
  let : Module.Finite ℂ (AdjoinRoot Q) := hQ.finite_adjoinRoot
  let left : AdjoinRoot P→ₐ[ℂ]A:=AdjoinRoot.liftAlgHom P (Algebra.ofId ℂ A) x hx
  let right : AdjoinRoot Q→ₐ[ℂ]A:=AdjoinRoot.liftAlgHom Q (Algebra.ofId ℂ A) y hy
  have image : ∀a b,Commute (left a) (right b) := by
    intro a b
    obtain ⟨p,rfl⟩:=AdjoinRoot.mk_surjective a
    obtain ⟨q,rfl⟩:=AdjoinRoot.mk_surjective b
    change Commute (aeval x p) (aeval y q)
    rw [aeval_eq_smeval,aeval_eq_smeval]
    exact Polynomial.smeval_commute ℂ p q commutes
  let source : FreeClock P Q→ₐ[ℂ]A:=Algebra.TensorProduct.lift left right image
  have generator : source (freeClockGenerator P Q)=Complex.I • x+(-Complex.I) • y := by
    simp [source,freeClockGenerator,left,right]
  have closed:=congrArg source (Algebra.aeval_self_charpoly_lmul (R:=ℂ) (M:=FreeClock P Q) (freeClockGenerator P Q))
  rw [map_zero,←aeval_algHom_apply,generator] at closed
  exact closed

private theorem free_clock_annihilates_commuting {A : Type*} [Ring A] [Algebra ℂ A]
    (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) (x y : A) (commutes : Commute x y)
    (hx : aeval x P=0) (hy : aeval y Q=0) :
    aeval (Complex.I • x+(-Complex.I) • y) (freeClockPolynomial P Q hP hQ)=0 := by
  let S : Subalgebra ℂ A:=Algebra.adjoin ℂ {x,y}
  have : IsMulCommutative S := by
    apply Algebra.isMulCommutative_adjoin
    intro a ha b hb
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · rfl
    · exact commutes.eq
    · exact commutes.eq.symm
    · rfl
  let : CommRing S:={ Subalgebra.toRing S with mul_comm:=fun a b=>mul_comm' a b }
  let sx : S:=⟨x,Algebra.subset_adjoin (by simp)⟩
  let sy : S:=⟨y,Algebra.subset_adjoin (by simp)⟩
  have left : aeval sx P=0 := by
    apply (show Function.Injective S.val from Subtype.val_injective)
    rw [←aeval_algHom_apply,map_zero]
    exact hx
  have right : aeval sy Q=0 := by
    apply (show Function.Injective S.val from Subtype.val_injective)
    rw [←aeval_algHom_apply,map_zero]
    exact hy
  have generated:=free_clock_annihilates P Q hP hQ sx sy (Commute.all _ _) left right
  have mapped:=congrArg S.val generated
  have vx : S.val sx=x := rfl
  have vy : S.val sy=y := rfl
  rw [←aeval_algHom_apply,map_add,map_smul,map_smul,vx,vy,map_zero] at mapped
  exact mapped

open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse SourcePropagationAlgebraicResponse SourcePropagationResolvent
open PreparationVacuumPropagationPencil
open scoped BigOperators
attribute [local irreducible] jointGenerator sourceLeft sourceRight evolutionGenerator

private def leftHom {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] : R→ₐ[ℂ](R→L[ℂ]R) where
  toFun:=ContinuousLinearMap.mul ℂ R
  map_zero':=by apply ContinuousLinearMap.ext;intro a;exact zero_mul a
  map_one':=by apply ContinuousLinearMap.ext;intro a;exact one_mul a
  map_add':=by intro x y;apply ContinuousLinearMap.ext;intro a;exact add_mul x y a
  map_mul':=by intro x y;apply ContinuousLinearMap.ext;intro a;exact mul_assoc x y a
  commutes':=by
    intro c
    apply ContinuousLinearMap.ext
    intro a
    simp only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.mul_apply',smul_mul_assoc,
      one_mul,smul_apply,one_apply_eq_self]

private theorem right_polynomial {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    (A : R) (P : ℂ[X]) :
    aeval ((ContinuousLinearMap.mul ℂ R).flip A) P=
      (ContinuousLinearMap.mul ℂ R).flip (aeval A P) := by
  have power (n : ℕ) : ((ContinuousLinearMap.mul ℂ R).flip A)^n=
      (ContinuousLinearMap.mul ℂ R).flip (A^n) := by
    induction n with
    | zero=>
      apply ContinuousLinearMap.ext
      intro B
      simp only [pow_zero,one_apply_eq_self,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply',mul_one]
    | succ n ih=>
      rw [pow_succ',ih,pow_succ]
      apply ContinuousLinearMap.ext
      intro B
      simp only [mul_apply_eq_comp,ContinuousLinearMap.flip_apply,ContinuousLinearMap.mul_apply']
      exact mul_assoc B (A^n) A
  rw [aeval_eq_sum_range,aeval_eq_sum_range,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_smul,power]

private theorem left_annihilated (q : PhysicalResponsePoint) :
    aeval (sourceLeft q) (jointPolynomial (q.p+q.k) q.F)=0 := by
  have same : sourceLeft q=leftHom (R:=H→L[ℂ]H) (jointGenerator (q.p+q.k) q.F 0 0) := by
    unfold sourceLeft
    rfl
  have zero : leftHom (R:=H→L[ℂ]H) (0:H→L[ℂ]H)=(0:SourcePropagationResolvent.TransferOp) := by
    apply ContinuousLinearMap.ext
    intro A
    exact zero_mul A
  refine (congrArg (fun T : SourcePropagationResolvent.TransferOp=>aeval T (jointPolynomial (q.p+q.k) q.F)) same).trans ?_
  exact (aeval_algHom_apply (leftHom (R:=H→L[ℂ]H)) (jointGenerator (q.p+q.k) q.F 0 0) (jointPolynomial (q.p+q.k) q.F)).trans
    ((congrArg (leftHom (R:=H→L[ℂ]H)) (actualJoint_annihilated (q.p+q.k) q.F)).trans zero)

private theorem right_annihilated (q : PhysicalResponsePoint) :
    aeval (sourceRight q) (jointPolynomial q.p q.F)=0 := by
  have same : sourceRight q=(ContinuousLinearMap.mul ℂ (H→L[ℂ]H)).flip (jointGenerator q.p q.F 0 0) := by
    unfold sourceRight
    rfl
  have zero : (ContinuousLinearMap.mul ℂ (H→L[ℂ]H)).flip (0:H→L[ℂ]H)=(0:SourcePropagationResolvent.TransferOp) := by
    apply ContinuousLinearMap.ext
    intro A
    exact mul_zero A
  refine (congrArg (fun T : SourcePropagationResolvent.TransferOp=>aeval T (jointPolynomial q.p q.F)) same).trans ?_
  exact (right_polynomial (jointGenerator q.p q.F 0 0) (jointPolynomial q.p q.F)).trans
    ((congrArg (ContinuousLinearMap.mul ℂ (H→L[ℂ]H)).flip (actualJoint_annihilated q.p q.F)).trans zero)

/-- A fixed-degree free completion of both original joint annihilators, retaining the actual generator. -/
def uniformClockPolynomial (q : PhysicalResponsePoint) : ℂ[X] :=
  freeClockPolynomial (jointPolynomial (q.p+q.k) q.F) (jointPolynomial q.p q.F)
    (jointPolynomial_monic _ _) (jointPolynomial_monic _ _)

theorem uniform_clock_monic (q : PhysicalResponsePoint) : (uniformClockPolynomial q).Monic :=
  free_clock_monic _ _ _ _

theorem actual_evolution_uniform_annihilated (q : PhysicalResponsePoint) :
    aeval (evolutionGenerator q) (uniformClockPolynomial q)=0 := by
  refine (congrArg (fun T : SourcePropagationResolvent.TransferOp=>aeval T (uniformClockPolynomial q))
    (sourceEvolution_multiplications q)).trans ?_
  exact free_clock_annihilates_commuting (A:=SourcePropagationResolvent.TransferOp)
    (jointPolynomial (q.p+q.k) q.F) (jointPolynomial q.p q.F) (jointPolynomial_monic _ _)
    (jointPolynomial_monic _ _) (sourceLeft q) (sourceRight q) (sourceLeftRight_commute q)
    (left_annihilated q) (right_annihilated q)

theorem uniform_clock_degree (q : PhysicalResponsePoint) :
    (uniformClockPolynomial q).natDegree=
      (jointPolynomial (q.p+q.k) q.F).natDegree*(jointPolynomial q.p q.F).natDegree :=
  free_clock_degree _ _ _ _

private theorem joint_fixed_degree (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (jointPolynomial p F).natDegree=57*(Module.finrank ℂ (compressionCarrier F)+1) := by
  rw [jointPolynomial,natDegree_pow,compressionPolynomial,natDegree_mul_X (LinearMap.charpoly_monic _).ne_zero,
    LinearMap.charpoly_natDegree]

theorem uniform_clock_fixed_degree (q : PhysicalResponsePoint) :
    (uniformClockPolynomial q).natDegree=(57*(Module.finrank ℂ (compressionCarrier q.F)+1))^2 := by
  rw [uniform_clock_degree,joint_fixed_degree,joint_fixed_degree,pow_two]

end LowEnergy.GaussComposite.ActualDressedPhysicalRayNumerator
