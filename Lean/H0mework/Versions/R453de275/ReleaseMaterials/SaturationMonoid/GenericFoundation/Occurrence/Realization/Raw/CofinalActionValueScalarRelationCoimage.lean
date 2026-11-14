import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValueScalarRelation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
open SourceGeneratedScalarPerfectification

noncomputable section
variable {D : Dynamics.{0}} {Carrier : Type} [CommRing Carrier]

/-- The already generated coimage can pass through the scalar relation
quotient precisely when the old source evaluator kills every old relation. -/
theorem valueRelationCoimage_descent_iff [IsReduced Carrier]
    (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    (∃ factor : valueRelationCompletion law occurrence →ₗ[Carrier]
        valueWordCoimage law occurrence,
      factor.comp (valueRelationProjection law occurrence) =
        canonicalMap (valueWordPairing law occurrence)) ↔
    ∀ relation : ((historyLaw law).historyAt occurrence).relationClosure,
      ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
        (installedRelationAction law occurrence relation).1 = 0 := by
  rw [valueRelation_descend_iff]
  constructor
  · intro killed relation
    have coimageZero := killed relation
    have pairingZero : integerToValueWords law
        (installedRelationAction law occurrence relation).1 ∈
        LinearMap.ker (valueWordPairing law occurrence) :=
      (Submodule.Quotient.mk_eq_zero _).1 coimageZero
    rw [valueWordPairing_kernel_eq_evaluation_kernel law occurrence] at pairingZero
    exact (valueWordEvaluation_integer_square law occurrence _).symm.trans pairingZero
  · intro killed relation
    have evaluationZero : valueWordEvaluation law occurrence
        (integerToValueWords law
          (installedRelationAction law occurrence relation).1) = 0 :=
      (valueWordEvaluation_integer_square law occurrence _).trans (killed relation)
    have pairingZero : integerToValueWords law
        (installedRelationAction law occurrence relation).1 ∈
        LinearMap.ker (valueWordPairing law occurrence) := by
      rw [valueWordPairing_kernel_eq_evaluation_kernel law occurrence]
      exact evaluationZero
    exact (Submodule.Quotient.mk_eq_zero _).2 pairingZero

/-- The old generated disposition governs the new scalar relation/coimage
square. On an unsound branch the same boundary is zero in the relation
quotient but nonzero in the full coimage, retaining the precise residual. -/
theorem valueRelationCoimage_generated_disposition [IsReduced Carrier]
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    let face := (faithfulLaw law).faithfulAt occurrence
    let compatible := ∃ factor : valueRelationCompletion law occurrence →ₗ[Carrier]
        valueWordCoimage law occurrence,
      factor.comp (valueRelationProjection law occurrence) =
        canonicalMap (valueWordPairing law occurrence)
    match face.settleWithResidual with
    | .faithful _ _ _ => compatible
    | .unsound _ _ =>
        ∃ relation : history.relationClosure,
          valueRelationProjection law occurrence
            (integerToValueWords law
              (installedRelationAction law occurrence relation).1) = 0 ∧
          canonicalMap (valueWordPairing law occurrence)
            (integerToValueWords law
              (installedRelationAction law occurrence relation).1) ≠ 0
    | .kernelResidual _ _ _ => compatible
    | .coverageResidual _ _ _ => compatible := by
  dsimp only
  let occurrence := emitted D state
  let history := (historyLaw law).historyAt occurrence
  let face := (faithfulLaw law).faithfulAt occurrence
  have soundCompatible (soundness : GeneratedRelationSoundnessAt face) :
      ∃ factor : valueRelationCompletion law occurrence →ₗ[Carrier]
          valueWordCoimage law occurrence,
        factor.comp (valueRelationProjection law occurrence) =
          canonicalMap (valueWordPairing law occurrence) := by
    apply (valueRelationCoimage_descent_iff law occurrence).mpr
    intro relation
    exact soundness.sound relation.2
  have unsoundResidual (obstruction : GeneratedUnsoundRelationObstructionAt face) :
      ∃ relation : history.relationClosure,
        valueRelationProjection law occurrence
          (integerToValueWords law
            (installedRelationAction law occurrence relation).1) = 0 ∧
        canonicalMap (valueWordPairing law occurrence)
          (integerToValueWords law
            (installedRelationAction law occurrence relation).1) ≠ 0 := by
    obtain ⟨word, belongs, nonzero⟩ := face.unsoundRelationWitness obstruction
    let relation : history.relationClosure := ⟨word, belongs⟩
    refine ⟨relation, valueRelationProjection_old_boundary law occurrence relation, ?_⟩
    intro coimageZero
    have pairingZero : integerToValueWords law
        (installedRelationAction law occurrence relation).1 ∈
        LinearMap.ker (valueWordPairing law occurrence) :=
      (Submodule.Quotient.mk_eq_zero _).1 coimageZero
    rw [valueWordPairing_kernel_eq_evaluation_kernel law occurrence] at pairingZero
    have readZero := (valueWordEvaluation_integer_square law occurrence _).symm.trans
      pairingZero
    exact nonzero readZero
  cases outcome : face.settleWithResidual with
  | faithful soundness _ _ => exact soundCompatible soundness
  | unsound obstruction _ => exact unsoundResidual obstruction
  | kernelResidual soundness _ _ => exact soundCompatible soundness
  | coverageResidual soundness _ _ => exact soundCompatible soundness

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
