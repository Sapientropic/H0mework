import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.EssentialAccessRelationFixture

/-!
# Source-generated essential-access relation renewal

The next relation identity is generated from the target role of the current
exact relation.  The local law is cyclic, but it stores no time index or
future table:

```text
tenure role → health
health role → platform
platform role → tenure
```

This is a subordinate fold algebra.  It becomes authority only when the
existing cross-current producer consumes it.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedEssentialAccessRelationRenewal

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Lifecycle Universal Relations
open M14EssentialAccessRelationFixture

/-- Local successor read from a relation-generated target role. -/
def essentialAccessRenewalEventOfRole : EssentialAccessRole →
    EssentialAccessEvent
  | .provider => .tenure
  | .tenureProvider => .health
  | .healthProvider => .platform
  | .platformProvider => .tenure

/-- The same local law on the exact relation seed's event coordinate. -/
def essentialAccessRenewalEvent : EssentialAccessEvent → EssentialAccessEvent
  | .tenure => .health
  | .health => .platform
  | .platform => .tenure

theorem essentialAccessRenewalEvent_eq_role
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    essentialAccessRenewalEvent seed.1 =
      essentialAccessRenewalEventOfRole
        (essentialAccessRelationCompiler.roleAt
          (essentialAccessRelationCompiler.relationOf seed) .target) := by
  rcases seed with ⟨event, witness⟩
  cases event <;> rfl

/-- The exact next seed is rebuilt at the existing source occurrence from the
current relation's generated target role. -/
def sourceGeneratedEssentialAccessRenewalSeed
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    essentialAccessRelationCompiler.ExactRelationSeed :=
  exactEssentialAccessSeed
    (essentialAccessRenewalEvent seed.1)

@[simp] theorem renewalSeed_tenure :
    sourceGeneratedEssentialAccessRenewalSeed
      (exactEssentialAccessSeed .tenure) =
        exactEssentialAccessSeed .health :=
  rfl

@[simp] theorem renewalSeed_health :
    sourceGeneratedEssentialAccessRenewalSeed
      (exactEssentialAccessSeed .health) =
        exactEssentialAccessSeed .platform :=
  rfl

@[simp] theorem renewalSeed_platform :
    sourceGeneratedEssentialAccessRenewalSeed
      (exactEssentialAccessSeed .platform) =
        exactEssentialAccessSeed .tenure :=
  rfl

/-- One renewal always changes exact relation identity. -/
theorem renewalSeed_ne
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    sourceGeneratedEssentialAccessRenewalSeed seed ≠ seed := by
  intro equality
  have values := congrArg Subtype.val equality
  rcases seed with ⟨event, witness⟩
  cases event <;> cases values

/-- Three generated renewals return to the same relation-lineage identity.
This is identity closure across later occurrences, not occurrence equality. -/
theorem renewalSeed_three
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    sourceGeneratedEssentialAccessRenewalSeed
        (sourceGeneratedEssentialAccessRenewalSeed
          (sourceGeneratedEssentialAccessRenewalSeed seed)) =
      seed := by
  apply Subtype.ext
  rcases seed with ⟨event, witness⟩
  cases event <;> rfl

theorem renewalSeed_actor_three
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    (sourceGeneratedEssentialAccessRenewalSeed
        (sourceGeneratedEssentialAccessRenewalSeed
          (sourceGeneratedEssentialAccessRenewalSeed seed))).actor
          essentialAccessRelationCompiler =
      seed.actor essentialAccessRelationCompiler := by
  rw [renewalSeed_three]

theorem renewalSeed_actor_ne
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    (sourceGeneratedEssentialAccessRenewalSeed seed).actor
        essentialAccessRelationCompiler ≠
      seed.actor essentialAccessRelationCompiler := by
  intro equality
  have values := congrArg Subtype.val equality
  rcases seed with ⟨event, witness⟩
  cases event <;> cases values

/-- Direct provenance: the successor is a function of the current generated
target role, and its third iterate renews the same lineage/actor identity. -/
theorem essentialAccessRelationRenewal_directConsumer
    (seed : essentialAccessRelationCompiler.ExactRelationSeed) :
    (sourceGeneratedEssentialAccessRenewalSeed seed).1 =
        essentialAccessRenewalEventOfRole
          (essentialAccessRelationCompiler.roleAt
            (essentialAccessRelationCompiler.relationOf seed) .target) ∧
      sourceGeneratedEssentialAccessRenewalSeed seed ≠ seed ∧
      (sourceGeneratedEssentialAccessRenewalSeed seed).actor
          essentialAccessRelationCompiler ≠
        seed.actor essentialAccessRelationCompiler ∧
      sourceGeneratedEssentialAccessRenewalSeed
          (sourceGeneratedEssentialAccessRenewalSeed
            (sourceGeneratedEssentialAccessRenewalSeed seed)) =
        seed ∧
      (sourceGeneratedEssentialAccessRenewalSeed
          (sourceGeneratedEssentialAccessRenewalSeed
            (sourceGeneratedEssentialAccessRenewalSeed seed))).actor
            essentialAccessRelationCompiler =
        seed.actor essentialAccessRelationCompiler :=
  ⟨essentialAccessRenewalEvent_eq_role seed,
    renewalSeed_ne seed, renewalSeed_actor_ne seed,
    renewalSeed_three seed,
    renewalSeed_actor_three seed⟩

end
end M14SourceGeneratedEssentialAccessRelationRenewal
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessRelationRenewal.sourceGeneratedEssentialAccessRenewalSeed
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessRelationRenewal.renewalSeed_ne
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessRelationRenewal.renewalSeed_three
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessRelationRenewal.renewalSeed_actor_ne
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedEssentialAccessRelationRenewal.essentialAccessRelationRenewal_directConsumer
