import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.LinearAlgebra.Quotient.Basic
import H0mework.Realization.Integral.PrimeResidual

/-!
# Source-generated prime-power residual completion

For an additive source carrier and a rational prime, the actual multiplication
maps by `p^(n+1)` generate the quotient tower `L / p^(n+1)L`, its inverse
limit, and the canonical source map.  No finite, projective, determinant, or
adic-identification premise enters the construction.
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

variable {L : Type u} [AddCommGroup L]

/-- Multiplication by the positive power `p^(stage+1)`. -/
def powerMultiplication (prime : Nat.Primes) (stage : Nat) : L →ₗ[ℤ] L :=
  { toFun := fun value ↦ (prime.1 : ℤ) ^ (stage + 1) • value
    map_add' := fun left right ↦ smul_add _ left right
    map_smul' := by
      intro scalar value
      simp only [RingHom.id_apply, smul_smul]
      rw [mul_comm] }

@[simp] theorem powerMultiplication_apply
    (prime : Nat.Primes) (stage : Nat) (value : L) :
    powerMultiplication (L := L) prime stage value =
      (prime.1 : ℤ) ^ (stage + 1) • value := by
  rfl

def powerRange (prime : Nat.Primes) (stage : Nat) : Submodule ℤ L :=
  LinearMap.range (powerMultiplication (L := L) prime stage)

/-- The actual finite observation `L / p^(stage+1)L`. -/
abbrev StageResidual (prime : Nat.Primes) (stage : Nat) :=
  L ⧸ powerRange (L := L) prime stage

def stageProjection (prime : Nat.Primes) (stage : Nat) :
    L →ₗ[ℤ] StageResidual (L := L) prime stage :=
  Submodule.mkQ (powerRange (L := L) prime stage)

theorem powerRange_succ_le (prime : Nat.Primes) (stage : Nat) :
    powerRange (L := L) prime (stage + 1) ≤
      powerRange (L := L) prime stage := by
  rintro _ ⟨value, rfl⟩
  refine ⟨(prime.1 : ℤ) • value, ?_⟩
  simp only [powerMultiplication_apply]
  rw [smul_smul]
  conv_rhs => rw [pow_succ]

/-- The actual restriction from the `p^(n+2)` quotient to the `p^(n+1)`
quotient. -/
def transition (prime : Nat.Primes) (stage : Nat) :
    StageResidual (L := L) prime (stage + 1) →ₗ[ℤ]
      StageResidual (L := L) prime stage :=
  (powerRange (L := L) prime (stage + 1)).liftQ
    (stageProjection (L := L) prime stage) (by
      intro value membership
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact powerRange_succ_le prime stage membership)

@[simp] theorem transition_projection
    (prime : Nat.Primes) (stage : Nat) :
    (transition (L := L) prime stage).comp
        (stageProjection (L := L) prime (stage + 1)) =
      stageProjection (L := L) prime stage := by
  unfold transition stageProjection
  exact Submodule.liftQ_mkQ _ _ _

@[reducible] noncomputable def tower (prime : Nat.Primes) :
    Functor ℕᵒᵖ (ModuleCat.{u} ℤ) :=
  Functor.ofOpSequence
    (X := fun stage ↦ ModuleCat.of ℤ (StageResidual (L := L) prime stage))
    (fun stage ↦ ModuleCat.ofHom (transition (L := L) prime stage))

noncomputable def sourceState (prime : Nat.Primes) :
    (Functor.const ℕᵒᵖ).obj (ModuleCat.of ℤ L) ⟶ tower (L := L) prime :=
  NatTrans.ofOpSequence
    (fun stage ↦ ModuleCat.ofHom (stageProjection (L := L) prime stage))
    (fun stage ↦ by
      simp only [Functor.const_obj_map, tower,
        Functor.ofOpSequence_map_homOfLE_succ]
      apply ModuleCat.hom_ext
      exact transition_projection prime stage)

noncomputable def sourceCone (prime : Nat.Primes) :
    Cone (tower (L := L) prime) :=
  Cone.mk (ModuleCat.of ℤ L) (sourceState (L := L) prime)

/-- The canonical inverse limit of the complete prime-power residual
history. -/
noncomputable def Completion (prime : Nat.Primes) : ModuleCat.{u} ℤ :=
  limit (tower (L := L) prime)

noncomputable def canonicalMap (prime : Nat.Primes) :
    ModuleCat.of ℤ L ⟶ Completion (L := L) prime :=
  limit.lift (tower (L := L) prime) (sourceCone (L := L) prime)

noncomputable def restriction (prime : Nat.Primes) (stage : Nat) :
    Completion (L := L) prime ⟶
      ModuleCat.of ℤ (StageResidual (L := L) prime stage) :=
  limit.π (tower (L := L) prime) (Opposite.op stage)

@[reassoc (attr := simp)] theorem canonicalMap_restriction
    (prime : Nat.Primes) (stage : Nat) :
    canonicalMap (L := L) prime ≫ restriction (L := L) prime stage =
      ModuleCat.ofHom (stageProjection (L := L) prime stage) :=
  limit.lift_π (sourceCone (L := L) prime) (Opposite.op stage)

theorem stageProjection_eq_zero_iff
    (prime : Nat.Primes) (stage : Nat) (value : L) :
    stageProjection (L := L) prime stage value = 0 ↔
      ∃ divided : L,
        (prime.1 : ℤ) ^ (stage + 1) • divided = value := by
  rw [stageProjection, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨divided, equality⟩
    refine ⟨divided, ?_⟩
    simpa only [powerMultiplication_apply] using equality
  · rintro ⟨divided, equality⟩
    refine ⟨divided, ?_⟩
    simpa only [powerMultiplication_apply] using equality

theorem canonicalMap_eq_zero_iff
    (prime : Nat.Primes) (value : L) :
    canonicalMap (L := L) prime value = 0 ↔
      ∀ stage, ∃ divided : L,
        (prime.1 : ℤ) ^ (stage + 1) • divided = value := by
  constructor
  · intro completionZero stage
    have atStage := congrArg
      (fun completed ↦ (restriction (L := L) prime stage).hom completed)
      completionZero
    simp only [map_zero] at atStage
    have projection := ConcreteCategory.congr_hom
      (canonicalMap_restriction (L := L) prime stage) value
    apply (stageProjection_eq_zero_iff prime stage value).1
    exact projection.symm.trans atStage
  · intro divided
    apply Concrete.limit_ext (tower (L := L) prime)
    intro index
    rcases index with ⟨stage⟩
    change restriction (L := L) prime stage
        (canonicalMap (L := L) prime value) =
      restriction (L := L) prime stage 0
    have projection := ConcreteCategory.congr_hom
      (canonicalMap_restriction (L := L) prime stage) value
    have projected :
        restriction (L := L) prime stage
            (canonicalMap (L := L) prime value) =
          stageProjection (L := L) prime stage value := by
      change restriction (L := L) prime stage
          (canonicalMap (L := L) prime value) =
        stageProjection (L := L) prime stage value at projection
      exact projection
    rw [map_zero, projected]
    exact (stageProjection_eq_zero_iff prime stage value).2 (divided stage)

end
end SourceGeneratedPrimePowerCompletion
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
