import H0mework.Versions.Y.Arithmetic.RiemannRuntime.PairedOmegaEffectRuntimeFacade

/-!
# Accounted finite fold of the A1c paired-Omega effect history

One private successor on the fixed installed-effect process generates a
`RootedAccountedUnfolding` of exact runtime stages.  Every stage computes its
material tick, rooted effect authority and effect value from its depth; no
payload or future table is stored.  The unique occurrence fold accumulates
phase, retained incidence and centered trace while preserving their exact
conservation equation.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace CenteredGram
namespace IntegralGraphJointAction

noncomputable section

/-- A stage stores only its generated finite depth.  All authority and effect
coordinates below are dependent readouts of that depth in the fixed process. -/
structure AccountedRuntimeEffectStageAt
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) where
  private mk ::
  depth : Nat

namespace AccountedRuntimeEffectStageAt

def generate
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) : AccountedRuntimeEffectStageAt observation nontrivial :=
  ⟨depth⟩

def runtime
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :=
  runtimeEffectRuntimeAt observation nontrivial stage.depth

def material
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    SourceGeneratedRuntimeMaterialStageAt stage.runtime :=
  .generate _

def rootedActive
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :=
  runtimeEffectRootedActiveAt observation nontrivial stage.depth

def effect
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) : RuntimeEffect :=
  installedRuntimeEffectValueAt observation nontrivial stage.depth

def next
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    AccountedRuntimeEffectStageAt observation nontrivial :=
  generate observation nontrivial (stage.depth + 1)

@[simp] theorem generate_depth
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (generate observation nontrivial depth).depth = depth :=
  rfl

@[simp] theorem next_depth
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    stage.next.depth = stage.depth + 1 :=
  rfl

theorem material_factorizes
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    type_of% stage.material.factorizes :=
  stage.material.factorizes

theorem installedEffect_factorizes
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    type_of% (installedRuntimeEffectAt_factorizes
      observation nontrivial stage.depth) :=
  installedRuntimeEffectAt_factorizes observation nontrivial stage.depth

theorem effect_conservation
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    stage.effect.phase =
      stage.effect.retained + stage.effect.centeredTrace :=
  installedRuntimeEffectValueAt_conservation
    observation nontrivial stage.depth

end AccountedRuntimeEffectStageAt

private def accountedRuntimeEffectContinuation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    RootedAccountedUnfolding
      (AccountedRuntimeEffectStageAt observation nontrivial) :=
  RootedAccountedUnfolding.zero stage.next

/-- Finite prefix generated only by repeated ticks of the fixed process. -/
def accountedRuntimeEffectOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    RootedAccountedUnfolding
      (AccountedRuntimeEffectStageAt observation nontrivial) :=
  RootedAccountedUnfolding.observe
    (accountedRuntimeEffectContinuation observation nontrivial)
    (AccountedRuntimeEffectStageAt.generate observation nontrivial 0) depth

@[simp] theorem accountedRuntimeEffectOccurrence_zero
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    accountedRuntimeEffectOccurrence observation nontrivial 0 =
      RootedAccountedUnfolding.zero
        (AccountedRuntimeEffectStageAt.generate observation nontrivial 0) :=
  rfl

@[simp] theorem accountedRuntimeEffectOccurrence_succ
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    accountedRuntimeEffectOccurrence observation nontrivial (depth + 1) =
      (accountedRuntimeEffectOccurrence observation nontrivial depth).advance
        (accountedRuntimeEffectContinuation observation nontrivial) :=
  rfl

theorem accountedRuntimeEffectOccurrence_frontier
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (accountedRuntimeEffectOccurrence observation nontrivial depth).frontier =
      [AccountedRuntimeEffectStageAt.generate observation nontrivial depth] := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [accountedRuntimeEffectOccurrence_succ,
        RootedAccountedUnfolding.frontier_advance,
        inductionHypothesis]
      simp [accountedRuntimeEffectContinuation,
        AccountedRuntimeEffectStageAt.next]
      rfl

/-- Complete effect-valued face of the same accounted history. -/
def accountedRuntimeEffectValueOccurrence
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) : RootedAccountedUnfolding RuntimeEffect :=
  (accountedRuntimeEffectOccurrence observation nontrivial depth).map
    AccountedRuntimeEffectStageAt.effect

structure RuntimeEffectBalance where
  retained : QRich.ClozelJPair
  phase : QRich.ClozelJPair
  centeredTrace : QRich.ClozelJPair

namespace RuntimeEffectBalance

def valid (balance : RuntimeEffectBalance) : Prop :=
  balance.phase = balance.retained + balance.centeredTrace

def ofEffect (effect : RuntimeEffect) : RuntimeEffectBalance where
  retained := effect.retained
  phase := effect.phase
  centeredTrace := effect.centeredTrace

def zero : RuntimeEffectBalance where
  retained := 0
  phase := 0
  centeredTrace := 0

def add (left right : RuntimeEffectBalance) : RuntimeEffectBalance where
  retained := left.retained + right.retained
  phase := left.phase + right.phase
  centeredTrace := left.centeredTrace + right.centeredTrace

theorem zero_valid : zero.valid := by
  simp [valid, zero]

theorem add_valid
    {left right : RuntimeEffectBalance}
    (leftValid : left.valid) (rightValid : right.valid) :
    (add left right).valid := by
  unfold valid add
  rw [leftValid, rightValid]
  ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

end RuntimeEffectBalance

abbrev BalancedRuntimeEffect :=
  { balance : RuntimeEffectBalance // balance.valid }

def balancedRuntimeEffectZero : BalancedRuntimeEffect :=
  ⟨RuntimeEffectBalance.zero, RuntimeEffectBalance.zero_valid⟩

def balancedRuntimeEffectAdd
    (left right : BalancedRuntimeEffect) : BalancedRuntimeEffect :=
  ⟨RuntimeEffectBalance.add left.1 right.1,
    RuntimeEffectBalance.add_valid left.2 right.2⟩

def balancedRuntimeEffectChildren
    (children : List BalancedRuntimeEffect) : BalancedRuntimeEffect :=
  children.foldl balancedRuntimeEffectAdd balancedRuntimeEffectZero

def accountedRuntimeEffectStageBalance
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial) :
    BalancedRuntimeEffect :=
  ⟨RuntimeEffectBalance.ofEffect stage.effect, stage.effect_conservation⟩

def accountedRuntimeEffectFoldAt
    {observation : GeneratedRiemannZeroObservation}
    {nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)}
    (stage : AccountedRuntimeEffectStageAt observation nontrivial)
    (children : List BalancedRuntimeEffect) : BalancedRuntimeEffect :=
  balancedRuntimeEffectAdd (accountedRuntimeEffectStageBalance stage)
    (balancedRuntimeEffectChildren children)

/-- The canonical finite effect fold.  Its codomain contains the conservation
proof, so no later classifier can choose whether the accumulated relation
holds. -/
def accountedRuntimeEffectFold
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) : BalancedRuntimeEffect :=
  (accountedRuntimeEffectOccurrence observation nontrivial depth).fold
    accountedRuntimeEffectFoldAt

theorem accountedRuntimeEffectFold_conservation
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (depth : Nat) :
    (accountedRuntimeEffectFold observation nontrivial depth).1.phase =
      (accountedRuntimeEffectFold observation nontrivial depth).1.retained +
        (accountedRuntimeEffectFold observation nontrivial depth
          ).1.centeredTrace :=
  (accountedRuntimeEffectFold observation nontrivial depth).2

/-- Any evaluator respecting the single occurrence constructor is the same
finite effect fold. -/
theorem accountedRuntimeEffectFold_unique
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (candidate :
      RootedAccountedUnfolding
        (AccountedRuntimeEffectStageAt observation nontrivial) →
          BalancedRuntimeEffect)
    (commutes : ∀
      (origin : AccountedRuntimeEffectStageAt observation nontrivial)
      (childBranches : AccountedBranches
        (AccountedRuntimeEffectStageAt observation nontrivial)),
      candidate (RootedAccountedUnfolding.occur origin childBranches) =
        accountedRuntimeEffectFoldAt origin
          (RootedAccountedUnfolding.candidateValues candidate childBranches))
    (depth : Nat) :
    candidate (accountedRuntimeEffectOccurrence observation nontrivial depth) =
      accountedRuntimeEffectFold observation nontrivial depth :=
  RootedAccountedUnfolding.fold_unique
    accountedRuntimeEffectFoldAt candidate commutes _

end

end IntegralGraphJointAction
end CenteredGram
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
