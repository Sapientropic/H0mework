import H0mework.Physics.Admission.StandingPullback
import H0mework.Realization.Claims.P8

/-!
# Raw authority standing for claims

Authority monotonicity is claim metadata, not physical energy.  A raw state
stores only the current authority level and its ceiling.  A legal move carries
an authority transform proved `NonIncreasing` in the sense of Proposition 8.
The move is defined only while the source claim is authorized; P8 then proves
that the transformed claim remains under the same ceiling.

No final audit truth field, physical Noether quantity, or seven-facet package
is stored here.
-/

namespace SaturationMonoid
namespace PhysicsCore

structure RawAuthorityStanding where
  level : Nat
  ceiling : Nat
  deriving DecidableEq, Repr

namespace RawAuthorityStanding

def StandingAuthorized (S : RawAuthorityStanding) : Prop :=
  S.level ≤ S.ceiling

instance standingAuthorizedDecidable (S : RawAuthorityStanding) :
    Decidable S.StandingAuthorized := by
  unfold StandingAuthorized
  infer_instance

/-- A legal authority transformation is non-increasing by construction. -/
structure Move where
  transform : Nat → Nat
  nonIncreasing : NonIncreasing transform

def transformed (move : Move) (S : RawAuthorityStanding) :
    RawAuthorityStanding where
  level := move.transform S.level
  ceiling := S.ceiling

theorem transformed_authorized
    (move : Move) (S : RawAuthorityStanding)
    (hauthorized : S.StandingAuthorized) :
    (S.transformed move).StandingAuthorized := by
  exact authority_conserved move.nonIncreasing S.level S.ceiling hauthorized

/-- Authority change is an identity-preserving standing move only while the
source claim is already authorized. -/
def apply (move : Move) (S : RawAuthorityStanding) :
    Option RawAuthorityStanding :=
  if S.StandingAuthorized then some (S.transformed move) else none

def standingOperations :
    NativeStandingOperations RawAuthorityStanding Move where
  apply := apply

def anchoredStandingOperations :
    AnchoredStandingOperations RawAuthorityStanding Move Nat where
  toNativeStandingOperations := standingOperations
  anchor := fun standing => standing.ceiling
  anchor_preserved := by
    intro move source result happlies
    simp only [standingOperations, apply] at happlies
    split at happlies
    · simp only [Option.some.injEq] at happlies
      subst result
      rfl
    · simp at happlies

theorem authorized_nativeMoveInvariant :
    NativeMoveInvariant standingOperations StandingAuthorized := by
  intro move source result happlies
  simp only [standingOperations, apply] at happlies
  split at happlies
  · rename_i hauthorized
    simp only [Option.some.injEq] at happlies
    subst result
    exact iff_of_true hauthorized
      (transformed_authorized move source hauthorized)
  · simp at happlies

theorem authorized_standingInvariant :
    StandingInvariant (generatedStandingIdentity standingOperations)
      StandingAuthorized :=
  (standingInvariant_generatedStandingIdentity_iff_nativeMoveInvariant
    standingOperations StandingAuthorized).mpr
      authorized_nativeMoveInvariant

def identityMove : Move where
  transform := id
  nonIncreasing := by
    intro level
    rfl

def weakenOneMove : Move where
  transform := Nat.pred
  nonIncreasing := Nat.pred_le

namespace Toy

def authorized : RawAuthorityStanding where
  level := 2
  ceiling := 3

def unauthorized : RawAuthorityStanding where
  level := 3
  ceiling := 2

theorem authorized_valid : authorized.StandingAuthorized := by
  norm_num [StandingAuthorized, authorized]

theorem unauthorized_invalid : ¬ unauthorized.StandingAuthorized := by
  norm_num [StandingAuthorized, unauthorized]

theorem weakenOne_applies :
    apply weakenOneMove authorized =
      some { level := 1, ceiling := 3 } := by
  rfl

end Toy
end RawAuthorityStanding
end PhysicsCore
end SaturationMonoid
