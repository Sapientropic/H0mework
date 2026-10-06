import H0mework.Realization.Perfectification.Integral.Completion.LivingLawRootGeneratedPrimePowerSeparationKernel

/-!
# Naturality of prime-power residual completion

Every integral-linear source morphism preserves every `p^(n+1)` range.  It
therefore induces maps of the actual quotient tower, inverse limit, and
faithful coimage.  The source and coimage squares commute without any
finite-generation or localization premise.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {L M N : Type u}
variable [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]

theorem powerRange_maps
    (prime : Nat.Primes) (stage : Nat) (map : L →ₗ[ℤ] M) :
    powerRange (L := L) prime stage ≤
      (powerRange (L := M) prime stage).comap map := by
  rintro _ ⟨value, rfl⟩
  refine ⟨map value, ?_⟩
  simp only [powerMultiplication_apply, map_smul]

def stageMap (prime : Nat.Primes) (stage : Nat) (map : L →ₗ[ℤ] M) :
    StageResidual (L := L) prime stage →ₗ[ℤ]
      StageResidual (L := M) prime stage :=
  Submodule.mapQ
    (powerRange (L := L) prime stage)
    (powerRange (L := M) prime stage)
    map (powerRange_maps prime stage map)

@[simp] theorem stageMap_projection
    (prime : Nat.Primes) (stage : Nat) (map : L →ₗ[ℤ] M) :
    (stageMap prime stage map).comp
        (stageProjection (L := L) prime stage) =
      (stageProjection (L := M) prime stage).comp map := by
  rfl

theorem stageMap_transition
    (prime : Nat.Primes) (stage : Nat) (map : L →ₗ[ℤ] M) :
    (stageMap prime stage map).comp (transition (L := L) prime stage) =
      (transition (L := M) prime stage).comp
        (stageMap prime (stage + 1) map) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective
      (powerRange (L := L) prime (stage + 1)) quotient
  rfl

noncomputable def towerMap (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    tower (L := L) prime ⟶ tower (L := M) prime :=
  NatTrans.ofOpSequence
    (fun stage ↦ ModuleCat.ofHom (stageMap prime stage map))
    (fun stage ↦ by
      simp only [tower, Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact stageMap_transition prime stage map)

noncomputable def inducedCompletionMap
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    Completion (L := L) prime ⟶ Completion (L := M) prime :=
  limMap (towerMap prime map)

theorem inducedCompletionMap_restriction
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) (stage : Nat) :
    inducedCompletionMap prime map ≫ restriction (L := M) prime stage =
      restriction (L := L) prime stage ≫
        ModuleCat.ofHom (stageMap prime stage map) :=
  limMap_π (towerMap prime map) (Opposite.op stage)

theorem canonicalMap_naturality
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    canonicalMap (L := L) prime ≫ inducedCompletionMap prime map =
      ModuleCat.ofHom map ≫ canonicalMap (L := M) prime := by
  apply (limit.isLimit (tower (L := M) prime)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  calc
    (canonicalMap (L := L) prime ≫ inducedCompletionMap prime map) ≫
          restriction (L := M) prime stage =
        canonicalMap (L := L) prime ≫
          (inducedCompletionMap prime map ≫
            restriction (L := M) prime stage) := by rw [Category.assoc]
    _ = canonicalMap (L := L) prime ≫
          (restriction (L := L) prime stage ≫
            ModuleCat.ofHom (stageMap prime stage map)) := by
      rw [inducedCompletionMap_restriction]
    _ = ModuleCat.ofHom map ≫
          (canonicalMap (L := M) prime ≫
            restriction (L := M) prime stage) := by
      simp only [← Category.assoc, canonicalMap_restriction]
      apply ModuleCat.hom_ext
      exact stageMap_projection prime stage map
    _ = (ModuleCat.ofHom map ≫ canonicalMap (L := M) prime) ≫
          restriction (L := M) prime stage := by rw [Category.assoc]

def inducedCompletionLinearMap
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    Completion (L := L) prime →ₗ[ℤ] Completion (L := M) prime :=
  (inducedCompletionMap prime map).hom

theorem separationKernel_maps
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    SeparationKernel (L := L) prime ≤
      (SeparationKernel (L := M) prime).comap map := by
  intro value sourceKernel
  rw [LinearMap.mem_ker] at sourceKernel
  change canonicalLinearMap (L := M) prime (map value) = 0
  have naturality := ConcreteCategory.congr_hom
    (canonicalMap_naturality prime map) value
  change inducedCompletionLinearMap prime map
        (canonicalLinearMap (L := L) prime value) =
      canonicalLinearMap (L := M) prime (map value) at naturality
  rw [sourceKernel, map_zero] at naturality
  exact naturality.symm

def coimageMap (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    FaithfulCoimage (L := L) prime →ₗ[ℤ]
      FaithfulCoimage (L := M) prime :=
  Submodule.mapQ
    (SeparationKernel (L := L) prime)
    (SeparationKernel (L := M) prime)
    map (separationKernel_maps prime map)

@[simp] theorem coimageMap_projection
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    (coimageMap prime map).comp (coimageProjection (L := L) prime) =
      (coimageProjection (L := M) prime).comp map := by
  rfl

theorem coimageRealization_naturality
    (prime : Nat.Primes) (map : L →ₗ[ℤ] M) :
    (coimageRealization (L := M) prime).comp (coimageMap prime map) =
      (inducedCompletionLinearMap prime map).comp
        (coimageRealization (L := L) prime) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (SeparationKernel (L := L) prime) quotient
  have naturality := ConcreteCategory.congr_hom
    (canonicalMap_naturality prime map) value
  change inducedCompletionLinearMap prime map
        (canonicalLinearMap (L := L) prime value) =
      canonicalLinearMap (L := M) prime (map value) at naturality
  exact naturality.symm

theorem stageMap_id (prime : Nat.Primes) (stage : Nat) :
    stageMap prime stage (LinearMap.id : L →ₗ[ℤ] L) = LinearMap.id := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (powerRange (L := L) prime stage) quotient
  rfl

theorem stageMap_comp
    (prime : Nat.Primes) (stage : Nat)
    (second : M →ₗ[ℤ] N) (first : L →ₗ[ℤ] M) :
    stageMap prime stage (second.comp first) =
      (stageMap prime stage second).comp (stageMap prime stage first) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (powerRange (L := L) prime stage) quotient
  rfl

theorem coimageMap_id (prime : Nat.Primes) :
    coimageMap prime (LinearMap.id : L →ₗ[ℤ] L) = LinearMap.id := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (SeparationKernel (L := L) prime) quotient
  rfl

theorem coimageMap_comp
    (prime : Nat.Primes)
    (second : M →ₗ[ℤ] N) (first : L →ₗ[ℤ] M) :
    coimageMap prime (second.comp first) =
      (coimageMap prime second).comp (coimageMap prime first) := by
  apply LinearMap.ext
  intro quotient
  obtain ⟨value, rfl⟩ :=
    Submodule.mkQ_surjective (SeparationKernel (L := L) prime) quotient
  rfl

theorem inducedCompletionMap_id (prime : Nat.Primes) :
    inducedCompletionMap prime (LinearMap.id : L →ₗ[ℤ] L) =
      𝟙 (Completion (L := L) prime) := by
  apply (limit.isLimit (tower (L := L) prime)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  change inducedCompletionMap prime (LinearMap.id : L →ₗ[ℤ] L) ≫
      restriction (L := L) prime stage =
    𝟙 (Completion (L := L) prime) ≫ restriction (L := L) prime stage
  rw [inducedCompletionMap_restriction, stageMap_id]
  simp

theorem inducedCompletionMap_comp
    (prime : Nat.Primes)
    (second : M →ₗ[ℤ] N) (first : L →ₗ[ℤ] M) :
    inducedCompletionMap prime (second.comp first) =
      inducedCompletionMap prime first ≫ inducedCompletionMap prime second := by
  apply (limit.isLimit (tower (L := N) prime)).hom_ext
  intro index
  rcases index with ⟨stage⟩
  calc
    inducedCompletionMap prime (second.comp first) ≫
          restriction (L := N) prime stage =
        restriction (L := L) prime stage ≫
          ModuleCat.ofHom (stageMap prime stage (second.comp first)) :=
      inducedCompletionMap_restriction prime (second.comp first) stage
    _ = restriction (L := L) prime stage ≫
          (ModuleCat.ofHom (stageMap prime stage first) ≫
            ModuleCat.ofHom (stageMap prime stage second)) := by
      rw [stageMap_comp]
      apply congrArg
      apply ModuleCat.hom_ext
      rfl
    _ = (inducedCompletionMap prime first ≫
          inducedCompletionMap prime second) ≫
            restriction (L := N) prime stage := by
      calc
        (restriction (L := L) prime stage ≫
              ModuleCat.ofHom (stageMap prime stage first)) ≫
              ModuleCat.ofHom (stageMap prime stage second) =
            (inducedCompletionMap prime first ≫
              restriction (L := M) prime stage) ≫
                ModuleCat.ofHom (stageMap prime stage second) := by
          rw [inducedCompletionMap_restriction]
        _ = inducedCompletionMap prime first ≫
              (restriction (L := M) prime stage ≫
                ModuleCat.ofHom (stageMap prime stage second)) := by
          rw [Category.assoc]
        _ = inducedCompletionMap prime first ≫
              (inducedCompletionMap prime second ≫
                restriction (L := N) prime stage) := by
          rw [inducedCompletionMap_restriction]
        _ = (inducedCompletionMap prime first ≫
              inducedCompletionMap prime second) ≫
                restriction (L := N) prime stage := by
          rw [Category.assoc]

end
end SourceGeneratedPrimePowerCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
