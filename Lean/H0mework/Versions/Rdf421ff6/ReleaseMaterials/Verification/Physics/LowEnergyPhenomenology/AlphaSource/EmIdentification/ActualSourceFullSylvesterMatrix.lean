import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherSylvester
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMeromorphicResponse
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationAlgebraicResponse
open ActualDressedSylvester Polynomial PreparationVacuumPhysicalFeedback
open scoped BigOperators Matrix
abbrev ActualOperator := H →L[ℂ] H
abbrev ActualTransfer := SourcePropagationResolvent.TransferOp
local instance : IsScalarTower ℂ ActualTransfer ActualTransfer := ⟨by
  intro c A B; apply ContinuousLinearMap.ext; intro X; rfl⟩
local instance : SMulCommClass ℂ ActualTransfer ActualTransfer := ⟨by
  intro c A B; apply ContinuousLinearMap.ext; intro X; exact (map_smul A c (B X)).symm⟩

/-- The finite source algebra represents the whole original evolution, including uncut-Y outside words. -/
abbrev SourceCarrier (q : PhysicalResponsePoint) := AdjoinRoot (propagationPolynomial q)

abbrev sourcePowerBasis (q : PhysicalResponsePoint) : PowerBasis ℂ (SourceCarrier q) :=
  AdjoinRoot.powerBasis' (propagationPolynomial_monic q)

abbrev SourceIndex (q : PhysicalResponsePoint) := Fin (sourcePowerBasis q).dim

def sourcePencil (q : PhysicalResponsePoint) (lambda : ℂ) : SourceCarrier q :=
  algebraMap ℂ (SourceCarrier q) lambda - AdjoinRoot.root (propagationPolynomial q)

def sourceGreen (q : PhysicalResponsePoint) (lambda : ℂ) : SourceCarrier q :=
  ((propagationPolynomial q).eval lambda)⁻¹ •
    AdjoinRoot.mk (propagationPolynomial q) ((propagationPolynomial q) /ₘ (X-C lambda))

/-- The original annihilator generates the inverse identity; no unit certificate is an input. -/
theorem source_green_inverse (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re) :
    sourcePencil q lambda * sourceGreen q lambda = 1 := by
  have divide := congrArg (AdjoinRoot.mk (propagationPolynomial q))
    (modByMonic_add_div (propagationPolynomial q) (X-C lambda))
  rw [modByMonic_X_sub_C_eq_C_eval, map_add, map_mul, map_sub, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_self] at divide
  have relation : sourcePencil q lambda *
      AdjoinRoot.mk (propagationPolynomial q) ((propagationPolynomial q) /ₘ (X-C lambda)) =
        algebraMap ℂ (SourceCarrier q) ((propagationPolynomial q).eval lambda) := by
    unfold sourcePencil
    rw [AdjoinRoot.algebraMap_eq]
    change _ = AdjoinRoot.of _ _
    linear_combination -divide
  unfold sourceGreen
  rw [mul_smul_comm, relation, Algebra.algebraMap_eq_smul_one, smul_smul,
    inv_mul_cancel₀ (propagationPolynomial_offAxis q lambda positive.ne'), one_smul]

def sourcePencilMatrix (q : PhysicalResponsePoint) (lambda : ℂ) :
    Matrix (SourceIndex q) (SourceIndex q) ℂ :=
  Algebra.leftMulMatrix (sourcePowerBasis q).basis (sourcePencil q lambda)

def sourceGreenMatrix (q : PhysicalResponsePoint) (lambda : ℂ) :
    Matrix (SourceIndex q) (SourceIndex q) ℂ := (sourcePencilMatrix q lambda)⁻¹

theorem source_matrix_inverse (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re) :
    sourceGreenMatrix q lambda = Algebra.leftMulMatrix (sourcePowerBasis q).basis (sourceGreen q lambda) := by
  have inverse : sourcePencilMatrix q lambda *
      Algebra.leftMulMatrix (sourcePowerBasis q).basis (sourceGreen q lambda) = 1 := by
    rw [sourcePencilMatrix, ← map_mul, source_green_inverse q lambda positive, map_one]
  unfold sourceGreenMatrix
  exact Matrix.inv_eq_right_inv inverse

def sourceInverseWeights (q : PhysicalResponsePoint) (lambda : ℂ) : SourceIndex q → ℂ :=
  sourceGreenMatrix q lambda *ᵥ (sourcePowerBasis q).basis.repr (1 : SourceCarrier q)

theorem source_inverse_weights (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re) :
    sourceInverseWeights q lambda = (sourcePowerBasis q).basis.repr (sourceGreen q lambda) := by
  rw [sourceInverseWeights, source_matrix_inverse q lambda positive, Algebra.leftMulMatrix_mulVec_repr, mul_one]

attribute [local irreducible] evolutionGenerator propagationPolynomial sourceInverse

private def powerAction {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) : AdjoinRoot P →ₗ[ℂ] A :=
  (aeval T).toLinearMap.comp (AdjoinRoot.modByMonicHom monic)

private theorem power_action_mk {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0) (Q : ℂ[X]) :
    powerAction P monic T (AdjoinRoot.mk P Q) = aeval T Q := by
  have relation := congrArg (aeval T) (modByMonic_add_div Q P)
  rw [map_add, map_mul, annihilated, zero_mul, add_zero] at relation
  change aeval T (AdjoinRoot.modByMonicHom monic (AdjoinRoot.mk P Q)) = _
  rw [AdjoinRoot.modByMonicHom_mk]
  exact relation

private theorem power_action_basis {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0)
    (i : Fin (AdjoinRoot.powerBasis' monic).dim) :
    powerAction P monic T ((AdjoinRoot.powerBasis' monic).basis i) = T^i.val := by
  rw [(AdjoinRoot.powerBasis' monic).basis_eq_pow]
  change powerAction P monic T ((AdjoinRoot.root P)^i.val) = _
  rw [← AdjoinRoot.mk_X, ← map_pow, power_action_mk P monic T annihilated, map_pow, aeval_X]

private theorem power_action_scaled_mk {A : Type*} [Semiring A] [Algebra ℂ A]
    (P : ℂ[X]) (monic : P.Monic) (T : A) (annihilated : aeval T P = 0) (c : ℂ) (Q : ℂ[X]) :
    powerAction P monic T (c • AdjoinRoot.mk P Q) = c • aeval T Q := by
  rw [map_smul, power_action_mk P monic T annihilated]

private theorem basis_action_apply {B E ι : Type*} [AddCommGroup B] [Module ℂ B]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype ι]
    (b : Module.Basis ι ℂ B) (L : B →ₗ[ℂ] (E →L[ℂ] E)) (x : B) (v : E) :
    L x v = ∑ i : ι, b.repr x i • (L (b i) v) := by
  have expanded := congrArg (fun y : B => L y v) (b.sum_repr x)
  simpa only [map_sum, map_smul, sum_apply, smul_apply] using expanded.symm

def sourceWholeAction (q : PhysicalResponsePoint) : SourceCarrier q →ₗ[ℂ] ActualTransfer :=
  powerAction (propagationPolynomial q) (propagationPolynomial_monic q) (evolutionGenerator q)

theorem source_whole_action_mk (q : PhysicalResponsePoint) (P : ℂ[X]) :
    sourceWholeAction q (AdjoinRoot.mk (propagationPolynomial q) P) = aeval (evolutionGenerator q) P :=
  power_action_mk (propagationPolynomial q) (propagationPolynomial_monic q)
    (evolutionGenerator q) (sourceEvolution_annihilated q) P

theorem source_whole_action_basis (q : PhysicalResponsePoint) (i : SourceIndex q) :
    sourceWholeAction q ((sourcePowerBasis q).basis i) = (evolutionGenerator q)^i.val :=
  power_action_basis (propagationPolynomial q) (propagationPolynomial_monic q)
    (evolutionGenerator q) (sourceEvolution_annihilated q) i

/-- Original source Green is evaluated by this source-generated finite matrix inverse. -/
theorem source_inverse_matrix_return (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re)
    (A : ActualOperator) : sourceInverse q lambda A =
      ∑ i : SourceIndex q, sourceInverseWeights q lambda i • (((evolutionGenerator q)^i.val) A) := by
  have same : sourceWholeAction q (sourceGreen q lambda) = sourceInverse q lambda := by
    calc
      _ = ((propagationPolynomial q).eval lambda)⁻¹ •
          aeval (evolutionGenerator q) ((propagationPolynomial q) /ₘ (X-C lambda)) :=
        power_action_scaled_mk (propagationPolynomial q) (propagationPolynomial_monic q)
          (evolutionGenerator q) (sourceEvolution_annihilated q) ((propagationPolynomial q).eval lambda)⁻¹
          ((propagationPolynomial q) /ₘ (X-C lambda))
      _ = sourceInverse q lambda := polynomialResolvent_future q lambda positive
  have actual := basis_action_apply (sourcePowerBasis q).basis (sourceWholeAction q) (sourceGreen q lambda) A
  calc
    _ = sourceWholeAction q (sourceGreen q lambda) A := congrArg (fun T : ActualTransfer => T A) same.symm
    _ = ∑ i : SourceIndex q, (sourcePowerBasis q).basis.repr (sourceGreen q lambda) i •
        (sourceWholeAction q ((sourcePowerBasis q).basis i) A) := actual
    _ = _ := Finset.sum_congr rfl (fun i _ => by
      exact congrArg₂ (fun (c : ℂ) (T : ActualTransfer) => c • T A)
        (congrFun (source_inverse_weights q lambda positive).symm i)
        (source_whole_action_basis q i))

end LowEnergy.GaussComposite.ActualSourceFullSylvesterMatrix
