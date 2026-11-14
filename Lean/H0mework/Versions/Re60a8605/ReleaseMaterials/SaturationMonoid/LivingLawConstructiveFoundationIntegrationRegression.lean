import Mathlib.Algebra.Module.Presentation.Finite
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.Tracks.LivingLawConstructiveCore

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ConstructiveFoundationIntegrationRegression

open CofinalPerfectCompression
open CofinalPerfectCompressionNoGo
open CofinalPerfectCompressionAxiomFreeCore

noncomputable section

/- The constructive foundation must not acquire a domain-named BSD determinant
   namespace through a transitive import. -/
/-- error: Unknown identifier `SaturationMonoid.BSDDeterminantLineKernel.FourTermDeterminantLine` -/
#guard_msgs in
#check SaturationMonoid.BSDDeterminantLineKernel.FourTermDeterminantLine

/-! A rank-one relation history is enough to exercise the constructive
compression producer: the relation is absent at stage zero and generated
fully at every later stage.  No finite model, basis, or determinant frame is
provided by the test source. -/

abbrev Generator := Fin 1

def rootOccurrence : RootedAccountedUnfolding Unit :=
  RootedAccountedUnfolding.zero ()

def generatorOccurrences (generator : Generator) :
    RootedAccountedUnfolding Generator :=
  RootedAccountedUnfolding.zero generator

def relationStages : ℕ →o Submodule ℤ (Generator →₀ ℤ) where
  toFun stage := if stage = 0 then ⊥ else ⊤
  monotone' := by
    intro first later order
    by_cases first_zero : first = 0
    · simp [first_zero]
    · have later_ne : later ≠ 0 := by omega
      simp [first_zero, later_ne]

def diagram : CofinalSourceGeneratedRelationDiagramAt Generator where
  relationStages := relationStages

def diagramOccurrence :
    RootedAccountedUnfolding (CofinalSourceGeneratedRelationDiagramAt Generator) :=
  RootedAccountedUnfolding.zero diagram

def face : RootGeneratedCofinalPerfectCompressionAt rootOccurrence
    generatorOccurrences diagramOccurrence :=
  RootGeneratedCofinalPerfectCompressionAt.generate (fun _ => rfl)

theorem finite_positive_branch :
    face.stabilizationTrace.index = 1 ∧
      face.quasiIsomorphism.IsQuasiIsomorphism ∧
      Nonempty
        (GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
          face.determinantState.integralLine) := by
  refine ⟨?_, face.quasiIsomorphism.isQuasiIsomorphism,
    face.determinantState_has_unitTorsor⟩
  apply le_antisymm
  · apply face.stabilizationTrace.least
    intro later _
    have later_ne : later ≠ 0 := by omega
    change
      (if (1 : ℕ) = 0 then ⊥ else ⊤) =
        (if later = 0 then ⊥ else ⊤)
    simp [later_ne]
  · by_contra not_one_le
    have index_zero : face.stabilizationTrace.index = 0 := by omega
    have stable := face.stabilizationTrace.stabilizes 1 (by omega)
    rw [index_zero] at stable
    change
      (if (0 : ℕ) = 0 then ⊥ else ⊤) =
        (if (1 : ℕ) = 0 then ⊥ else ⊤) at stable
    have impossible :
        (⊥ : Submodule ℤ (Generator →₀ ℤ)) = ⊤ := by
      simp only [if_neg Nat.one_ne_zero] at stable
      exact stable
    exact (bot_ne_top :
      (⊥ : Submodule ℤ (Generator →₀ ℤ)) ≠ ⊤) impossible

/-! The opposite branch is a genuine type-level obstruction: a countable
free integral module cannot be the image of any finite free compression.
This prevents the positive compression producer from being generalized to
all additive carriers by a presentation marker alone. -/

theorem infinite_rank_negative_branch :
    ¬ Module.Finite ℤ (ℕ →₀ ℤ) ∧
      ¬ Nonempty (FiniteFreeSurjectiveCompressionAt (ℕ →₀ ℤ)) ∧
      ¬ (∀ (module : Type) [AddCommGroup module],
        Nonempty (FiniteFreeSurjectiveCompressionAt module)) :=
  ⟨natFinsupp_not_moduleFinite,
    natFinsupp_no_finiteFreeSurjectiveCompression,
    no_uniform_finiteFreeSurjectiveCompression⟩

#print axioms finite_positive_branch
#print axioms infinite_rank_negative_branch
#print axioms CofinalPerfectCompressionAxiomFreeCore.RootGeneratedCofinalCompressionIncidenceAt.generate
#print axioms RootGeneratedExteriorDeterminantLine.topExteriorLine_finrank

/-! ## An actual persistent-residual witness

The negative branch is not only the abstract finite-generation no-go above.
For a zero evaluator on a constant infinite-rank carrier, the residual tower
has a concrete nonzero compatible point.  The generic settlement classifier
therefore exposes a finite residual coordinate and a carrier representative
outside the source range. -/

namespace InfiniteRankResidualExample

open CategoryTheory
open CategoryTheory.Limits
open CofinalKernelCompletion
open CofinalKernelCompletion.RootGeneratedCofinalKernelCompletionAt
open CofinalCoverageResidualTower
open CofinalCoverageResidualTower.RootGeneratedCofinalCoverageResidualTowerAt

abbrev ResidualGenerator := Unit
abbrev ResidualCarrier (_stage : Nat) : Type := Finsupp Nat Int

def zeroEvaluator (_stage : Nat) : ResidualGenerator →+ ResidualCarrier _stage := 0

def identityTransition (_stage : Nat) :
    ResidualCarrier (_stage + 1) →+ ResidualCarrier _stage :=
  AddMonoidHom.id _

def residualData : AdditiveCofinalEvaluatorData ResidualGenerator
    ResidualCarrier where
  evaluator := zeroEvaluator
  transition := identityTransition

def residualDependentOccurrence : RootedAccountedUnfolding
    (Unit × AdditiveCofinalEvaluatorData ResidualGenerator ResidualCarrier) :=
  RootedAccountedUnfolding.zero ((), residualData)

def residualCompletionFace : RootGeneratedCofinalKernelCompletionAt
    residualDependentOccurrence :=
  RootGeneratedCofinalKernelCompletionAt.generate

theorem residualCompatibility :
    GeneratedCompatibilityCalculationAt residualCompletionFace := by
  apply RootGeneratedCofinalKernelCompletionAt.generateCompatibility
  intro stage
  ext generator
  rfl

def residualFace : RootGeneratedCofinalCoverageResidualTowerAt
    residualCompletionFace residualCompatibility :=
  RootGeneratedCofinalCoverageResidualTowerAt.generate

private def scalarHom {Group : Type} [AddCommGroup Group]
    (value : Group) : ULift.{0, 0} Int →+ Group where
  toFun integer := integer.down • value
  map_zero' := by simp
  map_add' left right := by simp [add_zsmul]

def residualValues (x : Finsupp Nat Int) (stage : Nat) :
    residualFace.StageCoverageResidual stage :=
  QuotientAddGroup.mk' (residualCompletionFace.evaluator stage).range x

theorem residualValues_transition (x : Finsupp Nat Int) (stage : Nat) :
    residualFace.residualTransition stage
        (residualValues x (stage + 1)) = residualValues x stage := by
  change QuotientAddGroup.map _ _ (identityTransition stage) _
      (QuotientAddGroup.mk' _ x) = QuotientAddGroup.mk' _ x
  rfl

def residualElementCone (x : Finsupp Nat Int) :
    Cone residualFace.residualTower where
  pt := AddCommGrpCat.of (ULift.{0, 0} Int)
  π := NatTrans.ofOpSequence
    (fun stage => AddCommGrpCat.ofHom
      (scalarHom (residualValues x stage)))
    (fun stage => by
      simp only [residualTower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply AddCommGrpCat.ext
      intro integer
      change integer.down • residualValues x stage =
        residualFace.residualTransition stage
          (integer.down • residualValues x (stage + 1))
      rw [map_zsmul, residualValues_transition])

def residualElement (x : Finsupp Nat Int) : residualFace.residualLimit :=
  (limit.lift residualFace.residualTower (residualElementCone x)).hom
    (ULift.up 1)

theorem residualElement_projection (x : Finsupp Nat Int) (stage : Nat) :
    (residualFace.residualRestriction stage).hom
        (residualElement x) = residualValues x stage := by
  change (limit.π residualFace.residualTower (Opposite.op stage)).hom
      ((limit.lift residualFace.residualTower (residualElementCone x)).hom
        (ULift.up 1)) = residualValues x stage
  have h := congrArg
    (fun arrow : AddCommGrpCat.of (ULift.{0, 0} Int) ⟶
        AddCommGrpCat.of (residualFace.StageCoverageResidual stage) =>
      arrow.hom (ULift.up 1))
    (limit.lift_π (residualElementCone x) (Opposite.op stage))
  change
    (limit.π residualFace.residualTower (Opposite.op stage)).hom
        ((limit.lift residualFace.residualTower
          (residualElementCone x)).hom (ULift.up 1)) =
      (scalarHom (residualValues x stage)) (ULift.up 1) at h
  simpa [scalarHom] using h

theorem residualElement_one_ne_zero :
    residualElement (Finsupp.single 0 1) ≠ 0 := by
  intro equality
  have projection := congrArg
    (fun value => (residualFace.residualRestriction 0).hom value)
    equality
  rw [map_zero, residualElement_projection] at projection
  have class_ne_zero : residualValues (Finsupp.single 0 1) 0 ≠ 0 := by
    intro zero
    have membership := (QuotientAddGroup.eq_zero_iff
      (Finsupp.single 0 1)).mp zero
    rcases membership with ⟨generator, generator_eq⟩
    have single_zero :
        (Finsupp.single (0 : Nat) (1 : Int) : Finsupp Nat Int) = 0 := by
      symm
      have evaluator_zero :
          residualCompletionFace.evaluator 0 generator = 0 := by
        rfl
      rw [evaluator_zero] at generator_eq
      exact generator_eq
    exact (by simp :
      (Finsupp.single (0 : Nat) (1 : Int) : Finsupp Nat Int) ≠ 0)
      single_zero
  exact class_ne_zero projection

theorem residualLimit_not_subsingleton :
    ¬ Subsingleton residualFace.residualLimit := by
  intro rigid
  exact residualElement_one_ne_zero
    (rigid.elim (residualElement (Finsupp.single 0 1)) 0)

theorem infinite_rank_persistent_residual_branch :
    ¬ Module.Finite Int (Finsupp Nat Int) ∧
      ∃ obstruction : GeneratedFiniteResidualCoordinateObstructionAt
          residualFace,
        obstruction.residualCoordinate ≠ 0 ∧
        obstruction.representative ∉
          (residualCompletionFace.evaluator obstruction.stage).range := by
  refine ⟨?_, ?_⟩
  · exact natFinsupp_not_moduleFinite
  · let outcome := residualFace.settleResidualHistory
    cases outcome with
    | rigid historyRigid =>
        exact False.elim (residualLimit_not_subsingleton historyRigid)
    | finiteCoordinateObstruction obstruction =>
        exact ⟨obstruction, obstruction.residualCoordinate_ne_zero,
          obstruction.representative_not_mem_sourceRange⟩

#print axioms residualElement_projection
#print axioms residualElement_one_ne_zero
#print axioms infinite_rank_persistent_residual_branch

end InfiniteRankResidualExample

end

end ConstructiveFoundationIntegrationRegression
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
