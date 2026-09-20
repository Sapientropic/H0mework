import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Data.Finset.Order
import H0mework.Realization.FiniteCell.ActionDeterminant

/-!
# Derived transport of an actual action to a canonical perfect frontier

Once the canonical frontier is adequate, its bounded finite-free candidate
is K-projective and its map to the actual complex is an isomorphism in the
derived category.  Consequently an actual endomorphism of the actual complex
generates, without a caller lift, a chain representative on the candidate.
The representative is then consumed by the canonical action-determinant fold.

The only domain datum is one same-root occurrence of the actual complex
endomorphism.  No candidate action, degreewise lift, homotopy, inverse,
quasi-isomorphism, basis, matrix or determinant is accepted.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalFrontierDerivedAction

open CategoryTheory
open CategoryTheory.Localization
open CanonicalFiniteFrontierCompression
open CanonicalFiniteFrontierCompression.RootGeneratedCanonicalFiniteFrontierCompressionAt
open CanonicalFrontierDeterminant
open CanonicalFrontierActionDeterminant

noncomputable section

universe w

attribute [local instance] HasDerivedCategory.standard

private noncomputable def candidateUpperBound
    {complex : DerivedAdicCofiber.IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex) : ℤ :=
  Classical.choose (Finset.exists_le (candidateDegreeSupport frontier))

private theorem candidate_degree_le_upperBound
    {complex : DerivedAdicCofiber.IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (degree : ℤ) (membership : degree ∈ candidateDegreeSupport frontier) :
    degree ≤ candidateUpperBound frontier :=
  Classical.choose_spec
    (Finset.exists_le (candidateDegreeSupport frontier)) degree membership

private theorem candidateIsStrictlyLE
    {complex : DerivedAdicCofiber.IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (coverage : GeneratedDifferentialCoverageAt frontier) :
    (finitePerfectCandidate frontier coverage).IsStrictlyLE
      (candidateUpperBound frontier) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro degree above
  apply candidateTerm_isZero_outside_support frontier coverage degree
  intro membership
  exact (not_lt_of_ge
    (candidate_degree_le_upperBound frontier degree membership)) above

private theorem candidateIsKProjective
    {complex : DerivedAdicCofiber.IntegralCochainComplex ℤ}
    (frontier : CanonicalFiniteFrontierAt complex)
    (coverage : GeneratedDifferentialCoverageAt frontier) :
    CochainComplex.IsKProjective
      (finitePerfectCandidate frontier coverage) := by
  letI : (finitePerfectCandidate frontier coverage).IsStrictlyLE
      (candidateUpperBound frontier) :=
    candidateIsStrictlyLE frontier coverage
  letI (degree : ℤ) : Module.Free ℤ
      ((finitePerfectCandidate frontier coverage).X degree) :=
    candidateTermFree frontier coverage degree
  letI (degree : ℤ) : CategoryTheory.Projective
      ((finitePerfectCandidate frontier coverage).X degree) :=
    inferInstance
  exact CochainComplex.isKProjective_of_projective
    (finitePerfectCandidate frontier coverage)
      (candidateUpperBound frontier)

/-- A positive determinant settlement together with one actual-complex
endomorphism occurrence on the identical root. -/
structure RootGeneratedCanonicalFrontierDerivedActionAt
    {Root : Type w}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {actualComplexOccurrence : RootedAccountedUnfolding
      (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
    {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
      rootOccurrence actualComplexOccurrence}
    {settlement : ClassifiedAdequateFrontierAt compression}
    (determinantFace : RootGeneratedCanonicalFrontierDeterminantAt
      compression settlement)
    (dependentActualActionOccurrence : RootedAccountedUnfolding
      (Root × (compression.actualComplex ⟶ compression.actualComplex)))
    (projects : dependentActualActionOccurrence.map Prod.fst =
      determinantFace.root) : Type w where
  private mk ::

namespace RootGeneratedCanonicalFrontierDerivedActionAt

variable {Root : Type w}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {actualComplexOccurrence : RootedAccountedUnfolding
  (DerivedAdicCofiber.IntegralCochainComplex ℤ)}
variable {compression : RootGeneratedCanonicalFiniteFrontierCompressionAt
  rootOccurrence actualComplexOccurrence}
variable {settlement : ClassifiedAdequateFrontierAt compression}
variable {determinantFace : RootGeneratedCanonicalFrontierDeterminantAt
  compression settlement}
variable {dependentActualActionOccurrence : RootedAccountedUnfolding
  (Root × (compression.actualComplex ⟶ compression.actualComplex))}
variable {projects : dependentActualActionOccurrence.map Prod.fst =
  determinantFace.root}

def generate : RootGeneratedCanonicalFrontierDerivedActionAt
    determinantFace dependentActualActionOccurrence projects :=
  ⟨⟩

def actualActionOccurrence
    (_face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :=
  dependentActualActionOccurrence.map Prod.snd

def actualAction
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    compression.actualComplex ⟶ compression.actualComplex :=
  face.actualActionOccurrence.root

noncomputable def derivedCandidateAction
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    DerivedCategory.Q.obj determinantFace.candidate ⟶
      DerivedCategory.Q.obj determinantFace.candidate :=
  by
    let transition :=
      finitePerfectCandidateMap settlement.frontier settlement.coverage
    exact DerivedCategory.Q.map transition ≫
      DerivedCategory.Q.map face.actualAction ≫
      CategoryTheory.inv (DerivedCategory.Q.map transition)
        (I := compression.candidateDerivedIsIso settlement)

private noncomputable def homotopyCandidateAction
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    (HomotopyCategory.quotient (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).obj
          determinantFace.candidate ⟶
      (HomotopyCategory.quotient (ModuleCat.{0} ℤ) (ComplexShape.up ℤ)).obj
          determinantFace.candidate := by
  letI : CochainComplex.IsKProjective determinantFace.candidate :=
    candidateIsKProjective settlement.frontier settlement.coverage
  let comparison := DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)
  let target := comparison.hom.app determinantFace.candidate ≫
    face.derivedCandidateAction ≫
    comparison.inv.app determinantFace.candidate
  exact Classical.choose
    ((CochainComplex.IsKProjective.Qh_map_bijective
      determinantFace.candidate
      ((HomotopyCategory.quotient (ModuleCat.{0} ℤ)
        (ComplexShape.up ℤ)).obj determinantFace.candidate)).2 target)

private theorem homotopyCandidateAction_spec
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    DerivedCategory.Qh.map face.homotopyCandidateAction =
      let comparison := DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)
      comparison.hom.app determinantFace.candidate ≫
        face.derivedCandidateAction ≫
        comparison.inv.app determinantFace.candidate := by
  letI : CochainComplex.IsKProjective determinantFace.candidate :=
    candidateIsKProjective settlement.frontier settlement.coverage
  exact Classical.choose_spec
    ((CochainComplex.IsKProjective.Qh_map_bijective
      determinantFace.candidate
      ((HomotopyCategory.quotient (ModuleCat.{0} ℤ)
        (ComplexShape.up ℤ)).obj determinantFace.candidate)).2 _)

/-- Framework-generated chain representative of the conjugated derived
action. -/
noncomputable def candidateAction
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    determinantFace.candidate ⟶ determinantFace.candidate :=
  (HomotopyCategory.quotient (ModuleCat.{0} ℤ)
    (ComplexShape.up ℤ)).preimage face.homotopyCandidateAction

theorem candidateAction_maps_to_derivedAction
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    DerivedCategory.Q.map face.candidateAction =
      face.derivedCandidateAction := by
  let comparison := DerivedCategory.quotientCompQhIso (ModuleCat.{0} ℤ)
  have specification := face.homotopyCandidateAction_spec
  have naturality := comparison.hom.naturality face.candidateAction
  change DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (ModuleCat.{0} ℤ)
        (ComplexShape.up ℤ)).map face.candidateAction) ≫
        comparison.hom.app determinantFace.candidate =
      comparison.hom.app determinantFace.candidate ≫
        DerivedCategory.Q.map face.candidateAction at naturality
  have map_preimage :
      (HomotopyCategory.quotient (ModuleCat.{0} ℤ)
        (ComplexShape.up ℤ)).map face.candidateAction =
        face.homotopyCandidateAction := by
    unfold candidateAction
    exact Functor.map_preimage _ _
  rw [map_preimage, specification] at naturality
  have reduced :
      comparison.hom.app determinantFace.candidate ≫
          face.derivedCandidateAction =
        comparison.hom.app determinantFace.candidate ≫
          DerivedCategory.Q.map face.candidateAction := by
    calc
      comparison.hom.app determinantFace.candidate ≫
          face.derivedCandidateAction =
          (comparison.hom.app determinantFace.candidate ≫
            face.derivedCandidateAction ≫
              comparison.inv.app determinantFace.candidate) ≫
                comparison.hom.app determinantFace.candidate := by
            simp [Category.assoc]
      _ = comparison.hom.app determinantFace.candidate ≫
          DerivedCategory.Q.map face.candidateAction := naturality
  exact ((cancel_epi
    (comparison.hom.app determinantFace.candidate)).1 reduced).symm

/-- The generated chain action is put back on the exact action occurrence
before entering the determinant fold. -/
noncomputable def candidateActionOccurrence
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    RootedAccountedUnfolding
      (Root × (determinantFace.candidate ⟶ determinantFace.candidate)) :=
  dependentActualActionOccurrence.map fun payload ↦
    (payload.1, face.candidateAction)

theorem candidateActionOccurrence_projects
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    face.candidateActionOccurrence.map Prod.fst = determinantFace.root := by
  unfold candidateActionOccurrence
  rw [RootedAccountedUnfolding.map_map]
  change dependentActualActionOccurrence.map Prod.fst = _
  exact projects

/-- Canonical determinant fold of the generated candidate action. -/
noncomputable def actionDeterminant
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    RootGeneratedCanonicalFrontierActionDeterminantAt determinantFace
      face.candidateActionOccurrence face.candidateActionOccurrence_projects :=
  RootGeneratedCanonicalFrontierActionDeterminantAt.generate

theorem preserves_actual_action_and_derived_conjugation
    (face : RootGeneratedCanonicalFrontierDerivedActionAt
      determinantFace dependentActualActionOccurrence projects) :
    face.actualAction = dependentActualActionOccurrence.root.2 ∧
      DerivedCategory.Q.map face.candidateAction =
        face.derivedCandidateAction ∧
      face.actionDeterminant.actualAction = face.candidateAction := by
  exact ⟨by simp [actualAction, actualActionOccurrence],
    face.candidateAction_maps_to_derivedAction,
    by simp [
      CanonicalFrontierActionDeterminant.RootGeneratedCanonicalFrontierActionDeterminantAt.actualAction,
      CanonicalFrontierActionDeterminant.RootGeneratedCanonicalFrontierActionDeterminantAt.actionOccurrence,
      candidateActionOccurrence]⟩

end RootGeneratedCanonicalFrontierDerivedActionAt

end

end CanonicalFrontierDerivedAction
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
