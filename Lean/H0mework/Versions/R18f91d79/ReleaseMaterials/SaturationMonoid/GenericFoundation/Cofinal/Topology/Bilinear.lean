import H0mework.Realization.Perfectification.Integral.Completion.LivingLawRootGeneratedPrimePowerCompletionNaturalityKernel
import Mathlib.LinearAlgebra.Quotient.Bilinear

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedPrimePowerCompletion

variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]

/-- An actual bilinear operation consumes both original prime-power observations. -/
def stageBilinear (act : L →ₗ[ℤ] M →ₗ[ℤ] N) (p : Nat.Primes) (j : Nat) :
    StageResidual (L := L) p j →ₗ[ℤ] StageResidual (L := M) p j →ₗ[ℤ] StageResidual (L := N) p j :=
  (act.compr₂ (stageProjection p j)).liftQ₂ (powerRange p j) (powerRange p j)
    (by
      rintro _ ⟨left, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro right
      change stageProjection p j (act ((p.1 : ℤ)^(j+1) • left) right) = 0
      rw [map_smul, LinearMap.smul_apply]
      exact (stageProjection_eq_zero_iff p j _).mpr ⟨act left right, rfl⟩)
    (by
      rintro _ ⟨right, rfl⟩
      apply LinearMap.mem_ker.mpr
      apply LinearMap.ext
      intro left
      change stageProjection p j (act left ((p.1 : ℤ)^(j+1) • right)) = 0
      rw [map_smul]
      exact (stageProjection_eq_zero_iff p j _).mpr ⟨act left right, rfl⟩)

theorem stage_bilinear_projection (act : L →ₗ[ℤ] M →ₗ[ℤ] N) (p : Nat.Primes) (j : Nat)
    (left : L) (right : M) :
    stageBilinear act p j (stageProjection p j left) (stageProjection p j right) =
      stageProjection p j (act left right) := rfl

theorem stage_bilinear_transition (act : L →ₗ[ℤ] M →ₗ[ℤ] N) (p : Nat.Primes) (j : Nat)
    (left : StageResidual (L := L) p (j+1)) (right : StageResidual (L := M) p (j+1)) :
    transition p j (stageBilinear act p (j+1) left right) =
      stageBilinear act p j (transition p j left) (transition p j right) := by
  obtain ⟨left, rfl⟩ := (powerRange (L := L) p (j+1)).mkQ_surjective left
  obtain ⟨right, rfl⟩ := (powerRange (L := M) p (j+1)).mkQ_surjective right
  change transition p j (stageBilinear act p (j+1) (stageProjection p (j+1) left) (stageProjection p (j+1) right)) =
    stageBilinear act p j (transition p j (stageProjection p (j+1) left))
      (transition p j (stageProjection p (j+1) right))
  have leftRead : transition p j (stageProjection p (j+1) left) = stageProjection p j left :=
    LinearMap.congr_fun (transition_projection (L := L) p j) left
  have rightRead : transition p j (stageProjection p (j+1) right) = stageProjection p j right :=
    LinearMap.congr_fun (transition_projection (L := M) p j) right
  rw [stage_bilinear_projection, leftRead, rightRead, stage_bilinear_projection]
  exact LinearMap.congr_fun (transition_projection (L := N) p j) (act left right)

/-- The joint increment is divisible by the product of the two actual source depths. -/
theorem stage_bilinear_joint_vanish (act : L →ₗ[ℤ] M →ₗ[ℤ] N) (p : Nat.Primes) (j k : Nat)
    (left : L) (right : M) (leftZero : stageProjection p j left = 0)
    (rightZero : stageProjection p k right = 0) : stageProjection p (j+k+1) (act left right) = 0 := by
  obtain ⟨oldLeft, rfl⟩ := (stageProjection_eq_zero_iff p j left).mp leftZero
  obtain ⟨oldRight, rfl⟩ := (stageProjection_eq_zero_iff p k right).mp rightZero
  let leftDepth := (p.1 : ℤ)^(j+1)
  let rightDepth := (p.1 : ℤ)^(k+1)
  have acrossLeft : act (leftDepth • oldLeft) (rightDepth • oldRight) =
      leftDepth • act oldLeft (rightDepth • oldRight) :=
    LinearMap.congr_fun (map_smul act leftDepth oldLeft) _
  have acrossRight : act oldLeft (rightDepth • oldRight) = rightDepth • act oldLeft oldRight :=
    map_smul (act oldLeft) rightDepth oldRight
  refine (stageProjection_eq_zero_iff p (j+k+1) _).mpr ⟨act oldLeft oldRight, ?_⟩
  calc
    _ = leftDepth • (rightDepth • act oldLeft oldRight) := by
      dsimp only [leftDepth, rightDepth]
      rw [smul_smul, ← pow_add, show j+k+1+1 = j+1+(k+1) by omega]
    _ = _ := (acrossLeft.trans (congrArg (fun value => leftDepth • value) acrossRight)).symm

end SourceGeneratedPrimePowerCompletion
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
