import H0mework.Versions.R453de275.ReleaseMaterials.SaturationMonoid.GenericFoundation.Occurrence.Realization.Raw.CofinalActionValuePairing

/-! The original relation differential and full value pairing determine exact quotient descent. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RawGeneratedRoot.CofinalAction

open CofinalRelationGeneratedComplex
open CofinalFaithfulRealization
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt

noncomputable section
variable {D : Dynamics.{0}} {Carrier : Type} [CommRing Carrier]

def valuePairingOnClosure (law : Law D Carrier) {state : D.State}
    (occurrence : (source D).toRootSource.actual.OccurrenceAt state) :
    ((historyLaw law).historyAt occurrence).generatorClosure →ₗ[ℤ]
      ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier) :=
  (valuePairing law occurrence).comp
    (((historyLaw law).historyAt occurrence).generatorClosure.subtype)

theorem valuePairing_descent_iff_boundary_zero
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    (∃ factor : history.CompletionCarrier →ₗ[ℤ]
        ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier),
      factor.comp history.completionProjection =
        valuePairingOnClosure law occurrence) ↔
      ∀ relation : history.relationClosure,
        valuePairingOnClosure law occurrence
          (installedRelationAction law occurrence relation) = 0 := by
  dsimp only
  let occurrence := emitted D state
  let history := (historyLaw law).historyAt occurrence
  let pairing := valuePairingOnClosure law occurrence
  constructor
  · rintro ⟨factor, same⟩ relation
    have zero : history.completionProjection
        (installedRelationAction law occurrence relation) = 0 :=
      ((generated_cochain_kernel_exact law state).2 _).2 ⟨relation, rfl⟩
    have atRelation := LinearMap.congr_fun same
      (installedRelationAction law occurrence relation)
    change factor (history.completionProjection
      (installedRelationAction law occurrence relation)) =
        pairing (installedRelationAction law occurrence relation) at atRelation
    rw [zero, map_zero] at atRelation
    exact atRelation.symm
  · intro killed
    have compatible : history.relationInGeneratorClosure ≤
        LinearMap.ker pairing := by
      intro value belongs
      have zero : history.completionProjection value = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 belongs
      obtain ⟨relation, same⟩ :=
        ((generated_cochain_kernel_exact law state).2 value).1 zero
      change pairing value = 0
      rw [← same]
      exact killed relation
    refine ⟨history.relationInGeneratorClosure.liftQ pairing compatible, ?_⟩
    apply LinearMap.ext
    intro value
    rfl

theorem valuePairing_boundary_zero_iff_annihilator
    (law : Law D Carrier) (state : D.State)
    (relation : ((historyLaw law).historyAt (emitted D state)).relationClosure) :
    valuePairingOnClosure law (emitted D state)
        (installedRelationAction law (emitted D state) relation) = 0 ↔
      ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation
        (installedRelationAction law (emitted D state) relation).1 ∈
          valuePairingAnnihilator law (emitted D state) := by
  constructor
  · intro zero
    change ∀ right : law.Generator →₀ ℤ,
      ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation
          (installedRelationAction law (emitted D state) relation).1 *
        ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation right = 0
    intro right
    have atRight := LinearMap.congr_fun zero right
    change ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation
        (installedRelationAction law (emitted D state) relation).1 *
      ((faithfulLaw law).faithfulAt (emitted D state)).freeEvaluation right = 0
      at atRight
    exact atRight
  · intro annihilates
    apply LinearMap.ext
    intro right
    exact annihilates right

theorem valuePairing_descent_iff_annihilator
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    (∃ factor : history.CompletionCarrier →ₗ[ℤ]
        ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier),
      factor.comp history.completionProjection =
        valuePairingOnClosure law occurrence) ↔
      ∀ relation : history.relationClosure,
        ((faithfulLaw law).faithfulAt occurrence).freeEvaluation
          (installedRelationAction law occurrence relation).1 ∈
            valuePairingAnnihilator law occurrence := by
  constructor
  · intro factor relation
    exact (valuePairing_boundary_zero_iff_annihilator law state relation).mp
      ((valuePairing_descent_iff_boundary_zero law state).mp factor relation)
  · intro annihilates
    apply (valuePairing_descent_iff_boundary_zero law state).mpr
    intro relation
    exact (valuePairing_boundary_zero_iff_annihilator law state relation).mpr
      (annihilates relation)

theorem valuePairing_descent_iff_evaluator_descent [IsReduced Carrier]
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    (∃ factor : history.CompletionCarrier →ₗ[ℤ]
        ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier),
      factor.comp history.completionProjection =
        valuePairingOnClosure law occurrence) ↔
      ∃ factor : history.CompletionCarrier →ₗ[ℤ] Carrier,
        ∀ value : history.generatorClosure,
          factor (history.completionProjection value) =
            ((faithfulLaw law).faithfulAt occurrence).freeEvaluation value.1 := by
  constructor
  · intro pairing
    apply (generated_differential_descent_iff law state).mp
    intro relation
    exact (valuePairingAnnihilator_source_value_iff_zero law (emitted D state)
      (installedRelationAction law (emitted D state) relation).1).mp
        ((valuePairing_descent_iff_annihilator law state).mp pairing relation)
  · intro evaluator
    apply (valuePairing_descent_iff_annihilator law state).mpr
    intro relation
    exact (valuePairingAnnihilator_source_value_iff_zero law (emitted D state)
      (installedRelationAction law (emitted D state) relation).1).mpr
        ((generated_differential_descent_iff law state).mpr evaluator relation)

/-- The existing faithful disposition decides quotient pairing availability
from the actual relation values. No disposition branch is supplied by a caller. -/
theorem valuePairing_generated_disposition [IsReduced Carrier]
    (law : Law D Carrier) (state : D.State) :
    let occurrence := emitted D state
    let history := (historyLaw law).historyAt occurrence
    let face := (faithfulLaw law).faithfulAt occurrence
    let canDescend := ∃ factor : history.CompletionCarrier →ₗ[ℤ]
        ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier),
      factor.comp history.completionProjection =
        valuePairingOnClosure law occurrence
    match face.settleWithResidual with
    | .faithful _ _ _ => canDescend
    | .unsound _ _ => ¬ canDescend
    | .kernelResidual _ _ _ => canDescend
    | .coverageResidual _ _ _ => canDescend := by
  dsimp only
  let occurrence := emitted D state
  let history := (historyLaw law).historyAt occurrence
  let face := (faithfulLaw law).faithfulAt occurrence
  have soundDescent (soundness : GeneratedRelationSoundnessAt face) :
      ∃ factor : history.CompletionCarrier →ₗ[ℤ]
          ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier),
        factor.comp history.completionProjection =
          valuePairingOnClosure law occurrence := by
    apply (valuePairing_descent_iff_evaluator_descent law state).mpr
    exact ⟨face.completionEvaluation soundness, fun _ => rfl⟩
  have unsoundNoDescent (obstruction : GeneratedUnsoundRelationObstructionAt face) :
      ¬ ∃ factor : history.CompletionCarrier →ₗ[ℤ]
          ((law.Generator →₀ ℤ) →ₗ[ℤ] Carrier),
        factor.comp history.completionProjection =
          valuePairingOnClosure law occurrence := by
    intro pairingFactor
    have evaluatorFactor := (valuePairing_descent_iff_evaluator_descent law state).mp
      pairingFactor
    have killed := (generated_differential_descent_iff law state).mpr evaluatorFactor
    obtain ⟨relation, belongs, nonzero⟩ := face.unsoundRelationWitness obstruction
    have zero := killed (show history.relationClosure from ⟨relation, belongs⟩)
    change face.freeEvaluation relation = 0 at zero
    exact nonzero zero
  cases outcome : face.settleWithResidual with
  | faithful soundness _ _ => exact soundDescent soundness
  | unsound obstruction _ => exact unsoundNoDescent obstruction
  | kernelResidual soundness _ _ => exact soundDescent soundness
  | coverageResidual soundness _ _ => exact soundDescent soundness

end
end RawGeneratedRoot.CofinalAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
