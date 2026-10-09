import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationActualMomentumPencil
import Mathlib.LinearAlgebra.Charpoly.Basic

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.SourcePropagationAlgebraicResponse
open GaussCoreHilbert CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open PreparationVacuumGradedTransport SourcePropagationCommonMomentum PreparationVacuumMixedFieldReturn
open NativeHistoryGrade (Label projection)
open scoped BigOperators InnerProductSpace
open Polynomial
local instance : Fintype Label:=Fintype.ofFinite _
attribute [local irreducible] physicalBasis physicalFrame GaussCoreHilbert.coreEquiv

def compressionCarrier (F : GaussUnitaryHistory.Index) : Submodule ℂ H:=
  Submodule.span ℂ (Set.range (physicalFrame 0 F))

instance compressionCarrier_finite (F : GaussUnitaryHistory.Index) :
    FiniteDimensional ℂ (compressionCarrier F):=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range (physicalFrame 0 F))

theorem sourceFrame_mem (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (i : Label×PhysicalBasisIndex p F) : physicalFrame p F i∈compressionCarrier F:=by
  obtain ⟨j,hj⟩:=(sourceIndexCast p F).surjective i.2
  have same:=physicalFrame_common p F (i.1,j)
  simp only [hj] at same
  rw [same]
  exact Submodule.subset_span ⟨(i.1,j),rfl⟩

theorem sourceCompression_mem (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (x : H) :
    compression p F x∈compressionCarrier F:=by
  rw [←gradedForm_zero (0:Field289) p F]
  simp only [gradedForm,sum_apply,smul_apply,InnerProductSpace.rankOne_apply]
  apply Submodule.sum_mem
  intro g _
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  exact (compressionCarrier F).smul_mem _
    ((compressionCarrier F).smul_mem _ (sourceFrame_mem p F (g,i)))

def sourceCompressionEnd (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Module.End ℂ (compressionCarrier F):=
  (compression p F).toLinearMap.restrict (fun x _=>sourceCompression_mem p F x)

def compressionPolynomial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ℂ[X]:=
  (sourceCompressionEnd p F).charpoly*X

theorem compressionPolynomial_monic (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (compressionPolynomial p F).Monic:=
  (LinearMap.charpoly_monic _).mul monic_X

private theorem restriction_pow {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : Module.End ℂ E) (W : Submodule ℂ E) (closed : ∀x∈W,T x∈W)
    (n : ℕ) (x : W) : (((T.restrict closed)^n) x : E)=(T^n) x:=by
  rw [Module.End.pow_restrict]
  rfl

private theorem restriction_polynomial {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : Module.End ℂ E) (W : Submodule ℂ E) (closed : ∀x∈W,T x∈W)
    (P : ℂ[X]) (x : W) : (aeval (T.restrict closed) P x : E)=aeval T P x:=by
  rw [aeval_eq_sum_range,aeval_eq_sum_range]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,Submodule.coe_sum,Submodule.coe_smul]
  apply Finset.sum_congr rfl
  intro n _
  rw [restriction_pow T W closed n x]

theorem sourceCompression_annihilated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    aeval (compression p F).toLinearMap (compressionPolynomial p F)=0:=by
  unfold compressionPolynomial
  rw [map_mul,aeval_X]
  apply LinearMap.ext
  intro x
  change aeval (compression p F).toLinearMap (sourceCompressionEnd p F).charpoly
    (compression p F x)=0
  have actual:=restriction_polynomial (compression p F).toLinearMap (compressionCarrier F)
    (fun x _=>sourceCompression_mem p F x) (sourceCompressionEnd p F).charpoly
    ⟨compression p F x,sourceCompression_mem p F x⟩
  rw [←actual]
  change (((aeval (sourceCompressionEnd p F) (sourceCompressionEnd p F).charpoly)
    ⟨compression p F x,sourceCompression_mem p F x⟩ : compressionCarrier F) : H)=0
  rw [LinearMap.aeval_self_charpoly]
  rfl

private def operatorToEnd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (E→L[ℂ] E)→ₐ[ℂ] Module.End ℂ E where
  toRingHom:=ContinuousLinearMap.toLinearMapRingHom
  commutes':=fun _=>rfl

theorem actualCompression_annihilated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    aeval (compression p F) (compressionPolynomial p F)=0:=by
  have actual:=sourceCompression_annihilated p F
  have mapped:=aeval_algHom_apply (operatorToEnd (E:=H)) (compression p F) (compressionPolynomial p F)
  apply ContinuousLinearMap.ext
  intro x
  have value:=LinearMap.congr_fun (mapped.symm.trans actual) x
  exact value

end LowEnergy.SourcePropagationAlgebraicResponse
