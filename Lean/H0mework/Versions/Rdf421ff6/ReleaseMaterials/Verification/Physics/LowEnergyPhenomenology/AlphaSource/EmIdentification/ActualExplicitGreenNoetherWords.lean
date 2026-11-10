import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualExplicitEvolutionPolynomial
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticPolarization

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPropagationPencil SourcePropagationResolvent
open ActualDressedSylvester ActualDressedNoether ActualDressedFullCoulomb PreparationVacuumActionFieldLift
open scoped BigOperators Matrix
open Polynomial
attribute [local irreducible] evolutionGenerator sourceInverse actualPoleFreePolynomial actualExplicitEvolutionPolynomial

def actualExplicitNumerator (q : PhysicalResponsePoint) (lambda : ℂ) : ℂ[X] :=
  (actualPoleFreePolynomial q lambda) /ₘ (X-C lambda)
abbrev ExplicitWordIndex (q : PhysicalResponsePoint) (lambda : ℂ) :=
  Fin ((actualExplicitNumerator q lambda).natDegree + 1)
def actualExplicitWeights (q : PhysicalResponsePoint) (lambda : ℂ) : ExplicitWordIndex q lambda → ℂ :=
  fun i => ((actualPoleFreePolynomial q lambda).eval lambda)⁻¹ * (actualExplicitNumerator q lambda).coeff i.val

private theorem polynomial_word_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (P : ℂ[X]) (A : E) :
    aeval T P A = ∑ i : Fin (P.natDegree+1), P.coeff i.val • ((T^i.val) A) := by
  rw [aeval_eq_sum_range]
  simp only [sum_apply, smul_apply]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => P.coeff i • ((T^i) A)) (P.natDegree+1)).symm

/-- Explicit finite coefficients return the old whole-source Green on any original bounded insertion. -/
theorem explicit_source_inverse_words (q : PhysicalResponsePoint) (lambda : ℂ) (positive : 0 < lambda.re)
    (A : WholeOp) : sourceInverse q lambda A =
      ∑ i : ExplicitWordIndex q lambda, actualExplicitWeights q lambda i • (((evolutionGenerator q)^i.val) A) := by
  calc
    _ = actualExplicitGreen q lambda A :=
      congrArg (fun T : WholeTransfer => T A) (actual_explicit_green_return q lambda positive).symm
    _ = _ := by
      unfold actualExplicitGreen
      rw [smul_apply]
      have word := polynomial_word_apply (T := evolutionGenerator q)
        (P := (actualPoleFreePolynomial q lambda) /ₘ (X - C lambda)) (A := A)
      calc
        _ = ((actualPoleFreePolynomial q lambda).eval lambda)⁻¹ •
            (∑ i : Fin (((actualPoleFreePolynomial q lambda) /ₘ (X - C lambda)).natDegree + 1),
              ((actualPoleFreePolynomial q lambda) /ₘ (X - C lambda)).coeff i.val •
                (((evolutionGenerator q)^i.val) A)) :=
          by
            exact congrArg
              (fun B : WholeOp => ((actualPoleFreePolynomial q lambda).eval lambda)⁻¹ • B) word
        _ = _ := by
          simp only [Finset.smul_sum, smul_smul, actualExplicitWeights,
            actualExplicitNumerator, ExplicitWordIndex]

attribute [local irreducible] noetherStaticHalf noetherStaticInitial rawInitial dressedEulerObserver dressedStaticPolarization
  actualExplicitWeights driveOperator leftCurrent rightCurrent dressedKinematicPoint fieldUnit

/-- Both driven legs act on the original raw inverse before the complete source inverse is read. -/
theorem explicit_noether_half_words (q : PhysicalResponsePoint) (reader force : Field289)
    (lambda : ℂ) (positive : 0 < lambda.re) :
    noetherStaticHalf q reader force lambda =
      (∑ i : ExplicitWordIndex q lambda, actualExplicitWeights q lambda i •
        (((evolutionGenerator q)^i.val) (noetherStaticInitial q reader force))) +
      ∑ i : ExplicitWordIndex q lambda, ∑ j : ExplicitWordIndex q lambda,
        (actualExplicitWeights q lambda i * actualExplicitWeights q lambda j) •
          (((evolutionGenerator q)^i.val) (driveOperator q force
            (((evolutionGenerator q)^j.val) (rawInitial q reader)))) := by
  have source : noetherStaticInitial q reader force -
      leftCurrent q force * sourceInverse q lambda (rawInitial q reader) +
        sourceInverse q lambda (rawInitial q reader) * rightCurrent q force =
      noetherStaticInitial q reader force + driveOperator q force (sourceInverse q lambda (rawInitial q reader)) := by
    rw [driveOperator_apply]
    abel
  have inner (i : ExplicitWordIndex q lambda) :
      ((evolutionGenerator q)^i.val) (driveOperator q force (sourceInverse q lambda (rawInitial q reader))) =
      ∑ j : ExplicitWordIndex q lambda, actualExplicitWeights q lambda j •
        (((evolutionGenerator q)^i.val) (driveOperator q force (((evolutionGenerator q)^j.val) (rawInitial q reader)))) := by
    have actual := congrArg (fun B : WholeOp =>
      ((evolutionGenerator q)^i.val) (driveOperator q force B))
      (explicit_source_inverse_words q lambda positive (rawInitial q reader))
    simpa only [map_sum, map_smul] using actual
  calc
    _ = sourceInverse q lambda (noetherStaticInitial q reader force -
        leftCurrent q force * sourceInverse q lambda (rawInitial q reader) +
          sourceInverse q lambda (rawInitial q reader) * rightCurrent q force) :=
      noether_static_half_inverse q reader force lambda positive
    _ = sourceInverse q lambda (noetherStaticInitial q reader force +
        driveOperator q force (sourceInverse q lambda (rawInitial q reader))) :=
      congrArg (sourceInverse q lambda) source
    _ = sourceInverse q lambda (noetherStaticInitial q reader force) +
        sourceInverse q lambda (driveOperator q force (sourceInverse q lambda (rawInitial q reader))) := map_add _ _ _
    _ = (∑ i : ExplicitWordIndex q lambda, actualExplicitWeights q lambda i •
        (((evolutionGenerator q)^i.val) (noetherStaticInitial q reader force))) +
        ∑ i : ExplicitWordIndex q lambda, actualExplicitWeights q lambda i •
          (((evolutionGenerator q)^i.val) (driveOperator q force (sourceInverse q lambda (rawInitial q reader)))) :=
      congrArg₂ (fun (A B : WholeOp) => A+B)
        (explicit_source_inverse_words q lambda positive (noetherStaticInitial q reader force))
        (explicit_source_inverse_words q lambda positive (driveOperator q force (sourceInverse q lambda (rawInitial q reader))))
    _ = _ := by
      apply congrArg (fun B : WholeOp => _+B)
      apply Finset.sum_congr rfl
      intro i _
      exact (congrArg (fun B : WholeOp => actualExplicitWeights q lambda i • B) (inner i)).trans
        (by simp only [Finset.smul_sum, smul_smul])

/-- These are actual source words, not entries of a supplied realization or a replacement rest frame. -/
def explicitDirectMoments (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (i j : Fin 289) :
    ExplicitWordIndex (dressedKinematicPoint event transfer) lambda → ℂ := fun a =>
  dressedEulerObserver event (((evolutionGenerator (dressedKinematicPoint event transfer))^a.val)
    (noetherStaticInitial (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j)))

def explicitDrivenMoments (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (i j : Fin 289) :
    Matrix (ExplicitWordIndex (dressedKinematicPoint event transfer) lambda)
      (ExplicitWordIndex (dressedKinematicPoint event transfer) lambda) ℂ := fun a b =>
  dressedEulerObserver event (((evolutionGenerator (dressedKinematicPoint event transfer))^a.val)
    (driveOperator (dressedKinematicPoint event transfer) (fieldUnit j)
      (((evolutionGenerator (dressedKinematicPoint event transfer))^b.val)
        (rawInitial (dressedKinematicPoint event transfer) (fieldUnit i)))))

def explicitFullNoetherEntry (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (i j : Fin 289) : ℂ :=
  let weights := actualExplicitWeights (dressedKinematicPoint event transfer) lambda
  dotProduct weights (explicitDirectMoments event transfer lambda i j) +
    dotProduct weights (explicitDrivenMoments event transfer lambda i j *ᵥ weights)

/-- Full original Π consumes the generated finite source coefficients and original prepared observer. -/
theorem explicit_full_noether_polarization (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (i j : Fin 289) :
    dressedStaticPolarization event transfer lambda i j = explicitFullNoetherEntry event transfer lambda i j := by
  unfold dressedStaticPolarization
  rw [explicit_noether_half_words _ _ _ lambda positive]
  simp only [map_add, map_sum, map_smul, smul_eq_mul]
  unfold explicitFullNoetherEntry explicitDirectMoments explicitDrivenMoments Matrix.mulVec dotProduct
  simp only [Finset.mul_sum, mul_assoc]
  apply congrArg (fun c : ℂ => _+c)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end LowEnergy.GaussComposite.ActualSourceExplicitEvolutionPolynomial
