import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRResponse
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Maximal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformClockNonzero
open Polynomial
open scoped TensorProduct
private theorem character_of_nonunit {A : Type*} [CommRing A] [Algebra ℂ A]
    [Module.Finite ℂ A] (x : A) (lambda : ℂ) (bad : ¬IsUnit (x-algebraMap ℂ A lambda)) :
    ∃phi : A→ₐ[ℂ]ℂ,phi x=lambda := by
  have proper : Ideal.span ({x-algebraMap ℂ A lambda} : Set A)≠⊤ :=
    fun top=>bad (Ideal.span_singleton_eq_top.mp top)
  obtain ⟨M,hM,contained⟩:=Ideal.exists_le_maximal _ proper
  let : M.IsMaximal:=hM
  let K:=A⧸M
  let equiv : K≃ₐ[ℂ]ℂ := (AlgEquiv.ofBijective (Algebra.ofId ℂ K)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k:=ℂ) (K:=K))).symm
  let phi : A→ₐ[ℂ]ℂ:=equiv.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M)
  have killed : (Ideal.Quotient.mkₐ ℂ M) (x-algebraMap ℂ A lambda)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (contained (Ideal.subset_span (by simp)))
  have read : phi (x-algebraMap ℂ A lambda)=0 := by
    change equiv ((Ideal.Quotient.mkₐ ℂ M) (x-algebraMap ℂ A lambda))=0
    rw [killed,map_zero]
  exact ⟨phi,sub_eq_zero.mp (by simpa only [map_sub,AlgHom.commutes,Algebra.algebraMap_self,RingHom.id_apply] using read)⟩
private theorem lmul_charpoly_nonzero {A : Type*} [CommRing A] [Algebra ℂ A]
    [Module.Finite ℂ A] (x : A) (lambda : ℂ)
    (characters : ∀phi : A→ₐ[ℂ]ℂ,phi x≠lambda) :
    (Algebra.lmul ℂ A x).charpoly.eval lambda≠0 := by
  intro root
  obtain ⟨v,hv⟩:=((Module.End.hasEigenvalue_iff_isRoot_charpoly _ lambda).mpr root).exists_hasEigenvector
  have unit : IsUnit (x-algebraMap ℂ A lambda) := by
    by_contra bad
    obtain ⟨phi,hphi⟩:=character_of_nonunit x lambda bad
    exact characters phi hphi
  have killed : (x-algebraMap ℂ A lambda)*v=0 := by
    rw [sub_mul,←Algebra.smul_def]
    exact sub_eq_zero.mpr hv.apply_eq_smul
  exact hv.2 (unit.mul_left_cancel (by simpa only [mul_zero] using killed))
private theorem free_clock_nonzero (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic)
    (leftReal : ∀z : ℂ,P.eval z=0→z.im=0) (rightReal : ∀z : ℂ,Q.eval z=0→z.im=0)
    (lambda : ℂ) (offAxis : lambda.re≠0) :
    let : Module.Finite ℂ (AdjoinRoot P):=hP.finite_adjoinRoot
    let : Module.Finite ℂ (AdjoinRoot Q):=hQ.finite_adjoinRoot
    (Algebra.lmul ℂ (AdjoinRoot P⊗[ℂ]AdjoinRoot Q)
      (ActualDressedUniformRayCoefficients.canonicalClockGenerator P Q)).charpoly.eval lambda≠0 := by
  let : Module.Finite ℂ (AdjoinRoot P):=hP.finite_adjoinRoot
  let : Module.Finite ℂ (AdjoinRoot Q):=hQ.finite_adjoinRoot
  apply lmul_charpoly_nonzero
  intro phi equal
  let left : AdjoinRoot P→ₐ[ℂ]ℂ:=phi.comp Algebra.TensorProduct.includeLeft
  let right : AdjoinRoot Q→ₐ[ℂ]ℂ:=phi.comp Algebra.TensorProduct.includeRight
  have leftRoot : P.eval (left (AdjoinRoot.root P))=0 := by
    simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using AdjoinRoot.aeval_algHom_eq_zero P left
  have rightRoot : Q.eval (right (AdjoinRoot.root Q))=0 := by
    simpa only [aeval_def,Algebra.algebraMap_self,eval₂_id] using AdjoinRoot.aeval_algHom_eq_zero Q right
  have image : phi (ActualDressedUniformRayCoefficients.canonicalClockGenerator P Q)=
      Complex.I*left (AdjoinRoot.root P)+(-Complex.I)*right (AdjoinRoot.root Q) := by
    simp only [ActualDressedUniformRayCoefficients.canonicalClockGenerator,map_add,map_smul,smul_eq_mul]
    rfl
  have pure : (phi (ActualDressedUniformRayCoefficients.canonicalClockGenerator P Q)).re=0 := by
    rw [image]
    simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
      leftReal _ leftRoot,rightReal _ rightRoot]
    ring
  exact offAxis (equal.symm ▸ pure)
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback SourcePropagationAlgebraicResponse
open ActualDressedPhysicalRayNumerator ActualDressedUniformRayCoefficients ActualDressedUniformMaterialCoefficients
attribute [local irreducible] jointPolynomial
/-- The free completion itself has imaginary spectrum; no actual-evolution inverse is used. -/
theorem actual_uniform_clock_off_axis (q : PhysicalResponsePoint) (lambda : ℂ) (offAxis : lambda.re≠0) :
    (uniformClockPolynomial q).eval lambda≠0 := by
  have realRoots (p : PhysicalMomentum) (z : ℂ) (root : (jointPolynomial p q.F).eval z=0) : z.im=0 := by
    by_contra nonreal
    exact source_joint_polynomial_nonreal p q.F z nonreal root
  let P:=jointPolynomial (q.p+q.k) q.F
  let Q:=jointPolynomial q.p q.F
  let hP:=jointPolynomial_monic (q.p+q.k) q.F
  let hQ:=jointPolynomial_monic q.p q.F
  let : Module.Finite ℂ (AdjoinRoot P):=hP.finite_adjoinRoot
  let : Module.Finite ℂ (AdjoinRoot Q):=hQ.finite_adjoinRoot
  change (Algebra.lmul ℂ (AdjoinRoot P⊗[ℂ]AdjoinRoot Q) (canonicalClockGenerator P Q)).charpoly.eval lambda≠0
  exact free_clock_nonzero P Q hP hQ (realRoots (q.p+q.k)) (realRoots q.p) lambda offAxis
end LowEnergy.GaussComposite.ActualDressedUniformClockNonzero
