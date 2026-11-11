import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarExteriorLocalizationKernel

/-!
# Scalar projective exterior localization

A finite projective module is a source-generated retract of a finite free
presentation.  The free exterior/localization comparison and its naturality
descend across that retract, producing the same comparison for every finite
projective carrier.  The splitting is internal and no basis or frame escapes
the constructor.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarProjectiveExteriorLocalization

open Module Set
open SourceGeneratedScalarExteriorLocalization

noncomputable section

universe r m

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]

/-- An actual split embedding into a free carrier generates the exterior
localization comparison. -/
noncomputable def splitExteriorLocalizationEquiv
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    (sectionMap : M →ₗ[R] F) (projection : F →ₗ[R] M)
    (split : projection ∘ₗ sectionMap = LinearMap.id)
    (S : Submonoid R) (degree : ℕ) :
    LocalizedModule S (⋀[R]^degree M) ≃ₗ[Localization S]
      ⋀[Localization S]^degree (LocalizedModule S M) := by
  let localSection :
      LocalizedModule S M →ₗ[Localization S] LocalizedModule S F :=
    LocalizedModule.map S sectionMap
  let localProjection :
      LocalizedModule S F →ₗ[Localization S] LocalizedModule S M :=
    LocalizedModule.map S projection
  let localizedExteriorSection :
      LocalizedModule S (⋀[R]^degree M) →ₗ[Localization S]
        LocalizedModule S (⋀[R]^degree F) :=
    LocalizedModule.map S (exteriorPower.map degree sectionMap)
  let localizedExteriorProjection :
      LocalizedModule S (⋀[R]^degree F) →ₗ[Localization S]
        LocalizedModule S (⋀[R]^degree M) :=
    LocalizedModule.map S (exteriorPower.map degree projection)
  let exteriorLocalSection :
      (⋀[Localization S]^degree (LocalizedModule S M)) →ₗ[Localization S]
        ⋀[Localization S]^degree (LocalizedModule S F) :=
    exteriorPower.map degree localSection
  let exteriorLocalProjection :
      (⋀[Localization S]^degree (LocalizedModule S F)) →ₗ[Localization S]
        ⋀[Localization S]^degree (LocalizedModule S M) :=
    exteriorPower.map degree localProjection
  let freeComparison :=
    freeExteriorLocalizationEquiv (F := F) S degree

  have localSplit : localProjection ∘ₗ localSection = LinearMap.id := by
    rw [← localizedMap_comp, split, localizedMap_id]
  have localizedExteriorSplit :
      localizedExteriorProjection ∘ₗ localizedExteriorSection = LinearMap.id := by
    rw [← localizedMap_comp, ← exteriorPower.map_comp, split,
      exteriorPower.map_id, localizedMap_id]
  have exteriorLocalSplit :
      exteriorLocalProjection ∘ₗ exteriorLocalSection = LinearMap.id := by
    rw [← exteriorPower.map_comp, localSplit, exteriorPower.map_id]
  have localizedIdempotent :
      localizedExteriorSection ∘ₗ localizedExteriorProjection =
        LocalizedModule.map S
          (exteriorPower.map degree (sectionMap ∘ₗ projection)) := by
    rw [← localizedMap_comp, ← exteriorPower.map_comp]
  have exteriorLocalIdempotent :
      exteriorLocalSection ∘ₗ exteriorLocalProjection =
        exteriorPower.map degree (localSection ∘ₗ localProjection) := by
    rw [← exteriorPower.map_comp]
  have localIdempotent :
      localSection ∘ₗ localProjection =
        LocalizedModule.map S (sectionMap ∘ₗ projection) := by
    rw [localizedMap_comp]
  have intertwines :
      freeComparison.toLinearMap ∘ₗ
          (localizedExteriorSection ∘ₗ localizedExteriorProjection) =
        (exteriorLocalSection ∘ₗ exteriorLocalProjection) ∘ₗ
          freeComparison.toLinearMap := by
    rw [localizedIdempotent, exteriorLocalIdempotent, localIdempotent]
    exact freeExteriorLocalizationEquiv_naturality
      (F := F) S degree (sectionMap ∘ₗ projection)

  let forward := exteriorLocalProjection ∘ₗ
    freeComparison.toLinearMap ∘ₗ localizedExteriorSection
  let backward := localizedExteriorProjection ∘ₗ
    freeComparison.symm.toLinearMap ∘ₗ exteriorLocalSection
  refine LinearEquiv.ofLinearMap forward backward ?_ ?_
  · apply LinearMap.ext
    intro value
    change exteriorLocalProjection
        (freeComparison
          (localizedExteriorSection
            (localizedExteriorProjection
              (freeComparison.symm (exteriorLocalSection value))))) = value
    have commute := LinearMap.congr_fun intertwines
      (freeComparison.symm (exteriorLocalSection value))
    simp only [LinearMap.comp_apply] at commute
    have cancelForward :
        freeComparison (freeComparison.symm (exteriorLocalSection value)) =
          exteriorLocalSection value :=
      freeComparison.apply_symm_apply _
    change freeComparison
        (localizedExteriorSection
          (localizedExteriorProjection
            (freeComparison.symm (exteriorLocalSection value)))) =
      exteriorLocalSection
        (exteriorLocalProjection
          (freeComparison (freeComparison.symm (exteriorLocalSection value)))) at commute
    rw [cancelForward] at commute
    have targetSplit := LinearMap.congr_fun exteriorLocalSplit
    have targetOnce : exteriorLocalProjection (exteriorLocalSection value) = value :=
      targetSplit value
    calc
      exteriorLocalProjection
          (freeComparison
            (localizedExteriorSection
              (localizedExteriorProjection
                (freeComparison.symm (exteriorLocalSection value))))) =
          exteriorLocalProjection
            (exteriorLocalSection
              (exteriorLocalProjection (exteriorLocalSection value))) :=
        congrArg exteriorLocalProjection commute
      _ = value := by rw [targetOnce, targetOnce]
  · apply LinearMap.ext
    intro value
    change localizedExteriorProjection
        (freeComparison.symm
          (exteriorLocalSection
            (exteriorLocalProjection
              (freeComparison (localizedExteriorSection value))))) = value
    have commute := LinearMap.congr_fun intertwines
      (localizedExteriorSection value)
    simp only [LinearMap.comp_apply] at commute
    have inverseCommute := congrArg freeComparison.symm commute
    have cancelBackward :
        freeComparison.symm
            (freeComparison
              (localizedExteriorSection
                (localizedExteriorProjection (localizedExteriorSection value)))) =
          localizedExteriorSection
            (localizedExteriorProjection (localizedExteriorSection value)) :=
      freeComparison.symm_apply_apply _
    change freeComparison.symm
        (freeComparison
          (localizedExteriorSection
            (localizedExteriorProjection (localizedExteriorSection value)))) =
      freeComparison.symm
        (exteriorLocalSection
          (exteriorLocalProjection
            (freeComparison (localizedExteriorSection value)))) at inverseCommute
    rw [cancelBackward] at inverseCommute
    rw [← inverseCommute]
    have sourceSplit := LinearMap.congr_fun localizedExteriorSplit
    have sourceOnce :
        localizedExteriorProjection (localizedExteriorSection value) = value :=
      sourceSplit value
    rw [sourceOnce, sourceOnce]

/-- The split comparison is the canonical pure-wedge comparison. -/
theorem splitExteriorLocalizationEquiv_ιMulti
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Free R F]
    (sectionMap : M →ₗ[R] F) (projection : F →ₗ[R] M)
    (split : projection ∘ₗ sectionMap = LinearMap.id)
    (S : Submonoid R) (degree : ℕ) (vectors : Fin degree → M) :
    splitExteriorLocalizationEquiv sectionMap projection split S degree
        (LocalizedModule.mkLinearMap S (⋀[R]^degree M)
          (exteriorPower.ιMulti R degree vectors)) =
      exteriorPower.ιMulti (Localization S) degree
        (LocalizedModule.mkLinearMap S M ∘ vectors) := by
  unfold splitExteriorLocalizationEquiv
  simp only [LinearEquiv.coe_ofLinearMap, LinearMap.comp_apply]
  have inner :
      LocalizedModule.map S (exteriorPower.map degree sectionMap)
          (LocalizedModule.mkLinearMap S (⋀[R]^degree M)
            (exteriorPower.ιMulti R degree vectors)) =
        LocalizedModule.mkLinearMap S (⋀[R]^degree F)
          (exteriorPower.ιMulti R degree (sectionMap ∘ vectors)) := by
    change LocalizedModule.map S (exteriorPower.map degree sectionMap)
        (LocalizedModule.mk (exteriorPower.ιMulti R degree vectors) 1) =
      LocalizedModule.mk
        (exteriorPower.ιMulti R degree (sectionMap ∘ vectors)) 1
    rw [LocalizedModule.map_mk, exteriorPower.map_apply_ιMulti]
  rw [inner]
  change exteriorPower.map degree (LocalizedModule.map S projection)
      (freeExteriorLocalizationEquiv (F := F) S degree
        (LocalizedModule.mkLinearMap S (⋀[R]^degree F)
          (exteriorPower.ιMulti R degree (sectionMap ∘ vectors)))) = _
  rw [freeExteriorLocalizationEquiv_ιMulti]
  rw [exteriorPower.map_apply_ιMulti]
  apply congrArg (exteriorPower.ιMulti (Localization S) degree)
  funext index
  simp only [Function.comp_apply]
  change LocalizedModule.map S projection
      (LocalizedModule.mk (sectionMap (vectors index)) 1) =
    LocalizedModule.mk (vectors index) 1
  rw [LocalizedModule.map_mk]
  have splitAt := LinearMap.congr_fun split (vectors index)
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using
    congrArg (fun value => LocalizedModule.mk value 1) splitAt

/-- Every projective carrier obtains the split comparison from an internally
generated free-module retraction. -/
noncomputable def projectiveExteriorLocalizationEquiv
    (projective : Module.Projective R M)
    (S : Submonoid R) (degree : ℕ) :
    LocalizedModule S (⋀[R]^degree M) ≃ₗ[Localization S]
      ⋀[Localization S]^degree (LocalizedModule S M) := by
  letI : Module.Projective R M := projective
  let FreeCarrier := M →₀ R
  let projection : FreeCarrier →ₗ[R] M := Finsupp.linearCombination R id
  have projectionSurjective : Function.Surjective projection := by
    intro value
    refine ⟨Finsupp.single value 1, ?_⟩
    change Finsupp.linearCombination R id (Finsupp.single value 1) = value
    rw [Finsupp.linearCombination_single]
    simp
  have sectionExists := Module.projective_lifting_property
    projection (LinearMap.id : M →ₗ[R] M) projectionSurjective
  let sectionMap : M →ₗ[R] FreeCarrier := Classical.choose sectionExists
  have split : projection ∘ₗ sectionMap = LinearMap.id :=
    Classical.choose_spec sectionExists
  exact splitExteriorLocalizationEquiv sectionMap projection split S degree

/-- The projective comparison is independent of its internal retraction:
its value on every pure wedge is canonical. -/
theorem projectiveExteriorLocalizationEquiv_ιMulti
    (projective : Module.Projective R M)
    (S : Submonoid R) (degree : ℕ) (vectors : Fin degree → M) :
    projectiveExteriorLocalizationEquiv projective S degree
        (LocalizedModule.mkLinearMap S (⋀[R]^degree M)
          (exteriorPower.ιMulti R degree vectors)) =
      exteriorPower.ιMulti (Localization S) degree
        (LocalizedModule.mkLinearMap S M ∘ vectors) := by
  unfold projectiveExteriorLocalizationEquiv
  apply splitExteriorLocalizationEquiv_ιMulti

end
end SourceGeneratedScalarProjectiveExteriorLocalization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
