import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ExplicitPhaseSemiringRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.NativePreparedActionAPI
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullSylvesterMatrix

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPropagationPencil SourcePropagationResolvent SourcePropagationAlgebraicResponse
open Polynomial
open scoped BigOperators
abbrev WholeOp := H →L[ℂ] H
abbrev WholeTransfer := SourcePropagationResolvent.TransferOp
local instance : IsScalarTower ℂ WholeTransfer WholeTransfer :=
  ActualSourceFullSylvesterMatrix.instIsScalarTowerComplexActualTransfer
local instance : SMulCommClass ℂ WholeTransfer WholeTransfer :=
  ActualSourceFullSylvesterMatrix.instSMulCommClassComplexActualTransfer
attribute [local irreducible] jointGenerator evolutionGenerator jointPolynomial compressionPolynomial sourceCompressionEnd

def actualLeftPolynomial (q : PhysicalResponsePoint) : ℂ[X] := jointPolynomial (q.p+q.k) q.F
def actualRightPolynomial (q : PhysicalResponsePoint) : ℂ[X] := jointPolynomial q.p q.F
attribute [local irreducible] actualLeftPolynomial actualRightPolynomial

private abbrev leftAssembly : WholeOp →ₐ[ℂ] WholeTransfer :=
  originalLeftAssembly

theorem actual_left_polynomial_annihilated (q : PhysicalResponsePoint) :
    aeval (sourceLeft q) (actualLeftPolynomial q) = 0 := by
  unfold sourceLeft actualLeftPolynomial
  have generated := congrArg leftAssembly (actualJoint_annihilated (q.p+q.k) q.F)
  exact (Polynomial.aeval_algHom_apply leftAssembly (jointGenerator (q.p+q.k) q.F 0 0)
    (jointPolynomial (q.p+q.k) q.F)).trans (generated.trans (map_zero leftAssembly))

theorem actual_right_polynomial_annihilated (q : PhysicalResponsePoint) :
    aeval (sourceRight q) (actualRightPolynomial q) = 0 := by
  unfold sourceRight actualRightPolynomial
  have generated := congrArg ((ContinuousLinearMap.mul ℂ WholeOp).flip) (actualJoint_annihilated q.p q.F)
  have same := originalRightPolynomial (R := WholeOp) (jointGenerator q.p q.F 0 0) (jointPolynomial q.p q.F)
  exact same.trans (generated.trans (map_zero _))

/-- A finite algorithm over the two original charpoly*X polynomials powered57. -/
def actualExplicitEvolutionPolynomial (q : PhysicalResponsePoint) : ℂ[X] :=
  explicitPhasePolynomial (actualLeftPolynomial q) (actualRightPolynomial q)

attribute [local irreducible] actualExplicitEvolutionPolynomial

theorem actual_explicit_evolution_monic (q : PhysicalResponsePoint) :
    (actualExplicitEvolutionPolynomial q).Monic := by
  unfold actualExplicitEvolutionPolynomial
  exact explicit_phase_monic _ _

theorem actual_explicit_evolution_degree (q : PhysicalResponsePoint) :
    (actualExplicitEvolutionPolynomial q).natDegree =
      (actualLeftPolynomial q).natDegree * (actualRightPolynomial q).natDegree := by
  unfold actualExplicitEvolutionPolynomial
  exact explicit_phase_degree _ _

private theorem actual_left_monic (q : PhysicalResponsePoint) : (actualLeftPolynomial q).Monic := by
  unfold actualLeftPolynomial
  exact jointPolynomial_monic _ _
private theorem actual_right_monic (q : PhysicalResponsePoint) : (actualRightPolynomial q).Monic := by
  unfold actualRightPolynomial
  exact jointPolynomial_monic _ _

/-- Explicit source coefficients annihilate the whole original evolution, including outside uncutY words. -/
theorem actual_explicit_evolution_annihilated (q : PhysicalResponsePoint) :
    aeval (evolutionGenerator q) (actualExplicitEvolutionPolynomial q) = 0 := by
  unfold actualExplicitEvolutionPolynomial
  have native := explicit_commuting_phase_annihilated
    (actualLeftPolynomial q) (actualRightPolynomial q) (actual_left_monic q) (actual_right_monic q)
    (sourceLeft q) (sourceRight q) (actual_left_polynomial_annihilated q)
    (actual_right_polynomial_annihilated q) (sourceLeftRight_commute q)
  exact (congrArg (fun T : WholeTransfer => aeval T
    (explicitPhasePolynomial (actualLeftPolynomial q) (actualRightPolynomial q)))
      (sourceEvolution_multiplications q)).trans native


def actualPoleFreePolynomial (q : PhysicalResponsePoint) (lambda : ℂ) : ℂ[X] :=
  poleFreePolynomial (actualExplicitEvolutionPolynomial q) lambda

attribute [local irreducible] actualPoleFreePolynomial

theorem actual_pole_free_monic (q : PhysicalResponsePoint) (lambda : ℂ) :
    (actualPoleFreePolynomial q lambda).Monic := by
  unfold actualPoleFreePolynomial
  exact pole_free_monic _ (actual_explicit_evolution_monic q) lambda

theorem actual_pole_free_denominator (q : PhysicalResponsePoint) (lambda : ℂ) :
    (actualPoleFreePolynomial q lambda).eval lambda ≠ 0 := by
  unfold actualPoleFreePolynomial
  exact pole_free_denominator _ (actual_explicit_evolution_monic q) lambda

theorem actual_pole_free_annihilated (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re) :
    aeval (evolutionGenerator q) (actualPoleFreePolynomial q lambda) = 0 := by
  have factor : aeval (evolutionGenerator q) (X-C lambda) = -propagationPencil q lambda := by
    have linear := semiring_linear_factor (evolutionGenerator q) lambda
    have algebra : evolutionGenerator q + (-lambda) • (1 : WholeTransfer) = -propagationPencil q lambda := by
      exact scalar_pencil_neg (evolutionGenerator q) (1 : WholeTransfer) lambda
    exact linear.trans algebra
  unfold actualPoleFreePolynomial
  refine pole_free_annihilated (A := WholeTransfer)
    (T := evolutionGenerator q) (P := actualExplicitEvolutionPolynomial q)
    (lambda := lambda) (actual_explicit_evolution_annihilated q) ?_
  rw [factor]
  refine ⟨⟨-propagationPencil q lambda, -sourceInverse q lambda, ?_, ?_⟩, rfl⟩
  · apply ContinuousLinearMap.ext
    intro A
    change -(propagationPencil q lambda (-(sourceInverse q lambda A))) = A
    rw [map_neg, neg_neg]
    exact congrArg (fun L : WholeTransfer => L A) (sourceInverse_left q lambda positive)
  · apply ContinuousLinearMap.ext
    intro A
    change -(sourceInverse q lambda (-(propagationPencil q lambda A))) = A
    rw [map_neg, neg_neg]
    exact congrArg (fun L : WholeTransfer => L A) (sourceInverse_right q lambda positive)

/-- This generated polynomial Green uses finite coefficients and never the old minpoly choice. -/
def actualExplicitGreen (q : PhysicalResponsePoint) (lambda : ℂ) : WholeTransfer :=
  ((actualPoleFreePolynomial q lambda).eval lambda)⁻¹ •
    aeval (evolutionGenerator q) ((actualPoleFreePolynomial q lambda) /ₘ (X-C lambda))

private theorem normalized_transfer_inverse (T N : WholeTransfer) (c : ℂ)
    (relation : T * N = c • (1 : WholeTransfer)) (nonzero : c ≠ 0) :
    T * (c⁻¹ • N) = 1 := by
  rw [mul_smul_comm, relation, smul_smul, inv_mul_cancel₀ nonzero, one_smul]

/-- Original full source Green returns the explicit two-source coefficient algorithm. -/
theorem actual_explicit_green_return (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re) :
    actualExplicitGreen q lambda = sourceInverse q lambda := by
  have pencil : propagationPencil q lambda = lambda • (1 : WholeTransfer) + (-1 : ℂ) • evolutionGenerator q := by
    exact scalar_pencil_add (evolutionGenerator q) (1 : WholeTransfer) lambda
  have numerator : propagationPencil q lambda *
      aeval (evolutionGenerator q) ((actualPoleFreePolynomial q lambda) /ₘ (X-C lambda)) =
        (actualPoleFreePolynomial q lambda).eval lambda • (1 : WholeTransfer) :=
    (congrArg (fun T : WholeTransfer => T * aeval (evolutionGenerator q)
      ((actualPoleFreePolynomial q lambda) /ₘ (X-C lambda))) pencil).trans
        (semiring_polynomial_pencil (evolutionGenerator q) (actualPoleFreePolynomial q lambda) lambda
          (actual_pole_free_annihilated q lambda positive))
  have generated : propagationPencil q lambda * actualExplicitGreen q lambda = 1 := by
    unfold actualExplicitGreen
    exact normalized_transfer_inverse _ _ _ numerator (actual_pole_free_denominator q lambda)
  calc
    _ = 1 * actualExplicitGreen q lambda := (one_mul _).symm
    _ = (sourceInverse q lambda * propagationPencil q lambda) * actualExplicitGreen q lambda :=
      congrArg (fun T : WholeTransfer => T * actualExplicitGreen q lambda) (sourceInverse_right q lambda positive).symm
    _ = sourceInverse q lambda * (propagationPencil q lambda * actualExplicitGreen q lambda) := mul_assoc _ _ _
    _ = sourceInverse q lambda := by rw [generated, mul_one]

end LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
