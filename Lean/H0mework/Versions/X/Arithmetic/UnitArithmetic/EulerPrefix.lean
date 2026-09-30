import H0mework.Versions.X.Arithmetic.UnitArithmetic.CommonCarrier

/-!
# Cofinal Euler prefixes generated from the coordinate-free common occurrence

These are finite observations of repeated canonical root updates.  No future
table is stored: stage `n` recursively applies the root's actual `next` law
`n` times to the history carried by one common source point.  The Euler fold
therefore acquires exactly one next prime-local factor at each transition.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticCofinalEulerPrefix

open ArithmeticGeneration
open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticPrimePowerIncidence
open CanonicalUnitArithmeticRoot

noncomputable section

/-- Finite observation of repeated generated-next histories. -/
def cofinalHistory (source : CoordinateFreeRelationSource) : Nat → UnitHistory
  | 0 => source.history
  | stage + 1 => CanonicalUnitArithmeticRoot.next
      (cofinalHistory source stage)

@[simp] theorem cofinalHistory_zero
    (source : CoordinateFreeRelationSource) :
    cofinalHistory source 0 = source.history :=
  rfl

@[simp] theorem cofinalHistory_succ
    (source : CoordinateFreeRelationSource) (stage : Nat) :
    cofinalHistory source (stage + 1) =
      CanonicalUnitArithmeticRoot.next (cofinalHistory source stage) :=
  rfl

theorem cofinalHistory_cardinalShadow
    (source : CoordinateFreeRelationSource) (stage : Nat) :
    (cofinalHistory source stage).cardinalShadow =
      source.history.cardinalShadow + stage := by
  induction stage with
  | zero => simp
  | succ stage inductionHypothesis =>
      rw [cofinalHistory_succ,
        CanonicalUnitArithmeticRoot.next_eq_next]
      change Nat.succ (cofinalHistory source stage).cardinalShadow =
        source.history.cardinalShadow + Nat.succ stage
      rw [inductionHypothesis, Nat.add_succ]

/-- Euler prefix at one finite observation of the same source. -/
def cofinalPrefix
    (source : CoordinateFreeRelationSource) (stage : Nat) :
    ArithmeticFunction ℤ :=
  finiteEulerPrefix (cofinalHistory source stage)

@[simp] theorem cofinalPrefix_zero
    (source : CoordinateFreeRelationSource) :
    cofinalPrefix source 0 = source.eulerPrefix := by
  exact source.eulerPrefix_eq_finiteEulerPrefix.symm

/-- The actual transition multiplies by exactly the next unit-generated
prime-local factor. -/
theorem cofinalPrefix_succ
    (source : CoordinateFreeRelationSource) (stage : Nat) :
    cofinalPrefix source (stage + 1) =
      sourceLocalFormalEulerFactor
          (primeAtStage
            (cofinalHistory source stage).cardinalShadow) *
        cofinalPrefix source stage := by
  rw [cofinalPrefix, cofinalHistory_succ,
    CanonicalUnitArithmeticRoot.next_eq_next,
    finiteEulerPrefix_next]
  rfl

/-- One finite prefix readout remains attached to the common occurrence. -/
def prefixOccurrence (stage : Nat) :
    RootedAccountedUnfolding
      ((DomainPoint × CoordinateFreeRelationSource) × ArithmeticFunction ℤ) :=
  commonOccurrence.map fun point =>
    (point, cofinalPrefix point.2 stage)

theorem prefixOccurrence_projects_to_commonOccurrence (stage : Nat) :
    (prefixOccurrence stage).map Prod.fst = commonOccurrence := by
  rw [prefixOccurrence, RootedAccountedUnfolding.map_map]
  change commonOccurrence.map id = commonOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem prefixOccurrence_projects_to_exact_unit_root (stage : Nat) :
    (prefixOccurrence stage).map (fun point => point.1.1) = rootOccurrence := by
  rw [prefixOccurrence, RootedAccountedUnfolding.map_map]
  exact commonOccurrence_projects_to_exact_unit_root

def PrimeGeneratedByPrefixAt
    (source : CoordinateFreeRelationSource) (stage : Nat)
    (prime : Nat.Primes) : Prop :=
  ∃ localStage < (cofinalHistory source stage).cardinalShadow,
    primeAtStage localStage = prime

/-- Every rational prime is born at a finite observation of any actual common
source history. -/
theorem everyPrime_generated_at_finite_stage
    (source : CoordinateFreeRelationSource) (prime : Nat.Primes) :
    PrimeGeneratedByPrefixAt source (stageOfPrime prime + 1) prime := by
  refine ⟨stageOfPrime prime, ?_, primeAtStage_stageOfPrime prime⟩
  rw [cofinalHistory_cardinalShadow]
  omega

/-- Transition equation retained at the exact common occurrence root. -/
theorem prefixOccurrence_transition (stage : Nat) :
    (prefixOccurrence (stage + 1)).root.2 =
      sourceLocalFormalEulerFactor
          (primeAtStage
            (cofinalHistory commonOccurrence.root.2 stage).cardinalShadow) *
        (prefixOccurrence stage).root.2 := by
  exact cofinalPrefix_succ commonOccurrence.root.2 stage

end
end CanonicalUnitArithmeticCofinalEulerPrefix
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
