import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUniformClockSpectrum
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformRayCoefficients
open Polynomial
open scoped TensorProduct Matrix

/-- Multiplication by the canonical root in its prescribed power basis. -/
def canonicalCompanion (P : ℂ[X]) : Matrix (Fin P.natDegree) (Fin P.natDegree) ℂ :=
  fun i j=>(X^(j.val+1)%ₘP).coeff i.val

def canonicalClockMatrix (P Q : ℂ[X]) :
    Matrix (Fin P.natDegree×Fin Q.natDegree) (Fin P.natDegree×Fin Q.natDegree) ℂ :=
  fun i j=>Complex.I*canonicalCompanion P i.1 j.1*(if i.2=j.2 then 1 else 0)+
    (-Complex.I)*(if i.1=j.1 then 1 else 0)*canonicalCompanion Q i.2 j.2

def canonicalClockBasis (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    Module.Basis (Fin P.natDegree×Fin Q.natDegree) ℂ (AdjoinRoot P⊗[ℂ]AdjoinRoot Q) :=
  (AdjoinRoot.powerBasisAux' hP).tensorProduct (AdjoinRoot.powerBasisAux' hQ)

def canonicalClockGenerator (P Q : ℂ[X]) : AdjoinRoot P⊗[ℂ]AdjoinRoot Q :=
  Complex.I • ((AdjoinRoot.root P)⊗ₜ[ℂ](1:AdjoinRoot Q))+
    (-Complex.I) • ((1:AdjoinRoot P)⊗ₜ[ℂ](AdjoinRoot.root Q))

theorem canonical_companion_matrix (P : ℂ[X]) (hP : P.Monic) :
    LinearMap.toMatrix (AdjoinRoot.powerBasisAux' hP) (AdjoinRoot.powerBasisAux' hP)
      (Algebra.lmul ℂ (AdjoinRoot P) (AdjoinRoot.root P))=canonicalCompanion P := by
  funext i j
  have rootBasis : AdjoinRoot.powerBasisAux' hP j=AdjoinRoot.root P^j.val := (AdjoinRoot.powerBasis' hP).basis_eq_pow j
  rw [LinearMap.toMatrix_apply,Algebra.coe_lmul_eq_mul,rootBasis]
  change (AdjoinRoot.powerBasisAux' hP).repr (AdjoinRoot.root P*AdjoinRoot.root P^j.val) i=_
  rw [←pow_succ']
  have original : AdjoinRoot.root P^(j.val+1)=AdjoinRoot.mk P (X^(j.val+1)) := by
    rw [map_pow,AdjoinRoot.mk_X]
  rw [original,AdjoinRoot.powerBasisAux'_repr_apply_to_fun,AdjoinRoot.modByMonicHom_mk]
  rfl

theorem canonical_clock_tensor_matrix (P Q : ℂ[X]) (hP : P.Monic) (hQ : Q.Monic) :
    LinearMap.toMatrix (canonicalClockBasis P Q hP hQ) (canonicalClockBasis P Q hP hQ)
      (Algebra.lmul ℂ (AdjoinRoot P⊗[ℂ]AdjoinRoot Q) (canonicalClockGenerator P Q))=
      canonicalClockMatrix P Q := by
  funext i j
  have left:=congrFun (congrFun (canonical_companion_matrix P hP) i.1) j.1
  have right:=congrFun (congrFun (canonical_companion_matrix Q hQ) i.2) j.2
  rw [LinearMap.toMatrix_apply] at left right
  change (AdjoinRoot.powerBasisAux' hP).repr (AdjoinRoot.root P*(AdjoinRoot.powerBasisAux' hP) j.1) i.1=_ at left
  change (AdjoinRoot.powerBasisAux' hQ).repr (AdjoinRoot.root Q*(AdjoinRoot.powerBasisAux' hQ) j.2) i.2=_ at right
  rw [LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul]
  unfold canonicalClockBasis
  rw [Module.Basis.tensorProduct_apply']
  change ((AdjoinRoot.powerBasisAux' hP).tensorProduct (AdjoinRoot.powerBasisAux' hQ)).repr
    (canonicalClockGenerator P Q * ((AdjoinRoot.powerBasisAux' hP) j.1 ⊗ₜ[ℂ]
      (AdjoinRoot.powerBasisAux' hQ) j.2)) i = _
  simp only [canonicalClockGenerator, add_mul, smul_mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_add, map_smul,
    Finsupp.add_apply, Finsupp.smul_apply]
  obtain ⟨i₁,i₂⟩ := i
  rw [Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.tensorProduct_repr_tmul_apply]
  change Complex.I * (_ * _) + (-Complex.I) * (_ * _) = _
  unfold canonicalClockMatrix
  rw [left,right]
  simp only [Module.Basis.repr_self_apply,eq_comm]

  ring

open GaussCoreHilbert PreparationVacuumPhysicalFeedback SourcePropagationAlgebraicResponse
open ActualDressedPhysicalRayNumerator

/-- The original uniform polynomial is now in the two canonical power bases, with no selected momentum basis. -/
theorem actual_uniform_clock_canonical_matrix (q : PhysicalResponsePoint) :
    uniformClockPolynomial q=
      (canonicalClockMatrix (jointPolynomial (q.p+q.k) q.F) (jointPolynomial q.p q.F)).charpoly := by
  let P:=jointPolynomial (q.p+q.k) q.F
  let Q:=jointPolynomial q.p q.F
  let hP:=jointPolynomial_monic (q.p+q.k) q.F
  let hQ:=jointPolynomial_monic q.p q.F
  let : Module.Finite ℂ (AdjoinRoot P):=hP.finite_adjoinRoot
  let : Module.Finite ℂ (AdjoinRoot Q):=hQ.finite_adjoinRoot
  change (Algebra.lmul ℂ (AdjoinRoot P⊗[ℂ]AdjoinRoot Q) (canonicalClockGenerator P Q)).charpoly=_
  rw [←LinearMap.charpoly_toMatrix _ (canonicalClockBasis P Q hP hQ),canonical_clock_tensor_matrix]

end LowEnergy.GaussComposite.ActualDressedUniformRayCoefficients
