import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMeromorphicResponse
import Mathlib.Algebra.Polynomial.Roots

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationConstrainedPoleReturn
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationSpectralAxis
open SourcePropagationAlgebraicResponse
open Polynomial
open scoped BigOperators
abbrev Op:=SourcePropagationResolvent.Op
abbrev TransferOp:=SourcePropagationResolvent.TransferOp
local instance : IsScalarTower ℂ TransferOp TransferOp:=⟨by
  intro c A B;apply ContinuousLinearMap.ext;intro X;rfl⟩
local instance : SMulCommClass ℂ TransferOp TransferOp:=⟨by
  intro c A B;apply ContinuousLinearMap.ext;intro X;exact (map_smul A c (B X)).symm⟩
attribute [local irreducible] evolutionGenerator propagationPencil propagationPolynomial propagationNumerator polynomialResolvent

private theorem polynomial_evaluations_commute {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P Q : ℂ[X]) : Commute (aeval T P) (aeval T Q):=by
  change aeval T P*aeval T Q=aeval T Q*aeval T P
  rw [←map_mul,←map_mul,mul_comm]

theorem sourceNumerator_commute (q : PhysicalResponsePoint) (lambda : ℂ) :
    Commute (propagationNumerator q lambda) (propagationPencil q lambda):=by
  have actual:=polynomial_evaluations_commute (A:=TransferOp) (evolutionGenerator q)
    ((propagationPolynomial q)/ₘ(X-C lambda)) (C lambda-X)
  simp only [map_sub,aeval_C,aeval_X,Algebra.algebraMap_eq_smul_one] at actual
  unfold propagationNumerator propagationPencil
  convert! actual using 1

private theorem inverse_scalar_right {A : Type*} [Ring A] [Algebra ℂ A]
    (P N : A) (d : ℂ) (relation : P*N=d • (1:A)) (commutes : Commute N P) (nonzero : d≠0) :
    (d⁻¹ • N)*P=1:=by
  rw [smul_mul_assoc,commutes.eq,relation,smul_smul,inv_mul_cancel₀ nonzero,one_smul]

theorem polynomialResolvent_right (q : PhysicalResponsePoint) (lambda : ℂ)
    (regular : (propagationPolynomial q).eval lambda≠0) :
    polynomialResolvent q lambda*propagationPencil q lambda=1:=by
  unfold polynomialResolvent
  exact inverse_scalar_right (A:=TransferOp) (propagationPencil q lambda)
    (propagationNumerator q lambda) ((propagationPolynomial q).eval lambda)
    (sourceNumerator_pencil q lambda) (sourceNumerator_commute q lambda) regular

theorem sourcePencilUnit (q : PhysicalResponsePoint) (lambda : ℂ)
    (regular : (propagationPolynomial q).eval lambda≠0) : IsUnit (propagationPencil q lambda):=
  ⟨⟨propagationPencil q lambda,polynomialResolvent q lambda,
    polynomialResolvent_left q lambda regular,polynomialResolvent_right q lambda regular⟩,rfl⟩

def sourcePoleSet (q : PhysicalResponsePoint) : Set ℂ:=
  {a | (propagationPolynomial q).eval a=0}

theorem sourceSpectrum_sub_poles (q : PhysicalResponsePoint) :
    spectrum ℂ (evolutionGenerator q)⊆sourcePoleSet q:=by
  intro a member
  by_contra notRoot
  have unit:=sourcePencilUnit q a notRoot
  apply spectrum.notMem_iff.mpr _ member
  convert! unit using 1
  unfold propagationPencil
  simp only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def]

theorem sourcePoleSet_finite (q : PhysicalResponsePoint) : (sourcePoleSet q).Finite:=
  finite_setOfPred_isRoot (propagationPolynomial_monic q).ne_zero

theorem zero_transfer_sourcePole (q : PhysicalResponsePoint) (zeroTransfer : q.k=0) :
    (0:ℂ)∈sourcePoleSet q:=
  sourceSpectrum_sub_poles q (zero_transfer_actual_spectral_point q zeroTransfer)

theorem zero_transfer_sourcePoleOrder (q : PhysicalResponsePoint) (zeroTransfer : q.k=0) :
    0<sourcePoleOrder q 0:=
  (rootMultiplicity_pos (propagationPolynomial_monic q).ne_zero).mpr (zero_transfer_sourcePole q zeroTransfer)

end LowEnergy.SourcePropagationConstrainedPoleReturn
