import H0mework.Foundation.Runtime.EffectDynamics

/-!
# Source-native temporal action coupling

Physical time is an operational extent, not automatically a consumable
budget.  This axiom-free kernel records the stronger source-native relation
carried by one exact material edge:

```text
scale -> barrier -> horizon -> actual clock
potential drop = material action = clock-density coupling.
```

The kernel does not choose an ordered field or interpret a zero density.
Concrete scalar arithmetic belongs to an explicit domain adapter; root
authority only retains the same-source occurrence and its generated laws.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

universe u

/-- Domain-independent grammar for temporal/material arithmetic.  Its
relations are fixed before an occurrence is read; a coupling cannot replace
them after seeing a desired clock or branch. -/
structure SourceNativeTemporalActionCalculus : Type (u + 1) where
  Scalar : Type u
  Scale : Type u
  barrierFromScale : Scale -> Scalar
  horizonFromBarrier : Scalar -> Scalar
  actionFromClockDensity : Scalar -> Scalar -> Scalar
  potentialDrop : Scalar -> Scalar -> Scalar
  ScaleAdmissible : Scale -> Prop
  Nonnegative : Scalar -> Prop
  Positive : Scalar -> Prop
  LateClockAt : Scalar -> Scalar -> Prop
  ClockWithinAt : Scalar -> Scalar -> Prop

/-- One exact temporal/material edge in a fixed temporal calculus. -/
structure SourceNativeTemporalActionCouplingAt
    (calculus : SourceNativeTemporalActionCalculus.{u}) : Type u where
  scale : calculus.Scale
  barrier : calculus.Scalar
  horizon : calculus.Scalar
  clock : calculus.Scalar
  sourcePotential : calculus.Scalar
  targetPotential : calculus.Scalar
  action : calculus.Scalar
  density : calculus.Scalar
  scale_admissible : calculus.ScaleAdmissible scale
  barrier_positive : calculus.Positive barrier
  horizon_positive : calculus.Positive horizon
  clock_positive : calculus.Positive clock
  barrier_eq_scale : barrier = calculus.barrierFromScale scale
  horizon_eq : horizon = calculus.horizonFromBarrier barrier
  late_clock : calculus.LateClockAt horizon clock
  clock_within : calculus.ClockWithinAt clock horizon
  sourcePotential_nonnegative : calculus.Nonnegative sourcePotential
  targetPotential_nonnegative : calculus.Nonnegative targetPotential
  action_nonnegative : calculus.Nonnegative action
  density_nonnegative : calculus.Nonnegative density
  action_eq_potential_drop :
    action = calculus.potentialDrop sourcePotential targetPotential
  action_eq_clock_density :
    action = calculus.actionFromClockDensity clock density

/-- A temporal coupling indexed by exact occurrences of one fixed ledger
source.  `TemporalAt` restricts the law to occurrences which actually carry
physical time; no clock, scale, action or branch is accepted from callers. -/
structure SourceNativeTemporalActionCouplingLaw
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (source : SourceNativeLedgerSource N V)
    (calculus : SourceNativeTemporalActionCalculus.{u}) : Type (u + 1) where
  TemporalAt : {current : V.Current} ->
    source.source.toRootSource.actual.OccurrenceAt current -> Type u
  couplingAt : {current : V.Current} ->
    (occurrence : source.source.toRootSource.actual.OccurrenceAt current) ->
    TemporalAt occurrence -> SourceNativeTemporalActionCouplingAt calculus

end ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end SaturationMonoid
