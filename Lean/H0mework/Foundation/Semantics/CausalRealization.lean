/-!
# Field-free causal realization core

This module is the constructive No-Free Causal Difference spine.  It knows
nothing about fields, quotients, `Equiv`, or the concrete living-law branch
grammar.  Its parameter is one already fixed causal law surface: changing the
lawful graph is a source/law change, not another proof of the same world.

At one exact occurrence, every authoritative evolution must inhabit the
world-owned lawful graph.  A no-suspended-causal-magic witness proves that
graph pointwise single-valued.  Hence any observable difference must leave a
source/event, residual, or law-revision account; a difference with no such
account has no authority.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace CausalCore

universe u

structure World : Type (u + 1) where
  Current : Type u
  OccurrenceAt : Current → Type u
  EvolutionAt : Current → Type u
  emitted : (current : Current) → OccurrenceAt current
  LawfulEvolutionAt : {current : Current} →
    OccurrenceAt current → EvolutionAt current → Type u

/-- A constructive realization selects a lawful graph member and proves that
every lawful member at the same exact occurrence is that member. -/
structure NoSuspendedCausalMagic (W : World.{u}) : Type (u + 1) where
  realize : {current : W.Current} → W.OccurrenceAt current →
    W.EvolutionAt current
  lawful : {current : W.Current} →
    (occurrence : W.OccurrenceAt current) →
    W.LawfulEvolutionAt occurrence (realize occurrence)
  lawful_unique : {current : W.Current} →
    (occurrence : W.OccurrenceAt current) →
    (evolution : W.EvolutionAt current) →
    W.LawfulEvolutionAt occurrence evolution →
    evolution = realize occurrence

/-- Whole-evolution causal quotient: all lawful outputs of one exact
occurrence collapse to one generated reality, not merely one branch tag. -/
theorem NoSuspendedCausalMagic.lawful_evolution_eq
    {W : World.{u}} (law : NoSuspendedCausalMagic W)
    {current : W.Current} {occurrence : W.OccurrenceAt current}
    {left right : W.EvolutionAt current}
    (leftLawful : W.LawfulEvolutionAt occurrence left)
    (rightLawful : W.LawfulEvolutionAt occurrence right) :
    left = right := by
  exact (law.lawful_unique occurrence left leftLawful).trans
    (law.lawful_unique occurrence right rightLawful).symm

/-- No-Free Causal Difference: a distinguishable difference at the same
registered occurrence cannot inhabit the same fixed lawful graph twice. -/
theorem NoSuspendedCausalMagic.no_free_causal_difference
    {W : World.{u}} (law : NoSuspendedCausalMagic W)
    {current : W.Current} {occurrence : W.OccurrenceAt current}
    {left right : W.EvolutionAt current} (different : left ≠ right) :
    W.LawfulEvolutionAt occurrence left →
      W.LawfulEvolutionAt occurrence right → False := by
  intro leftLawful rightLawful
  exact different (law.lawful_evolution_eq leftLawful rightLawful)

theorem NoSuspendedCausalMagic.realize_eq
    {W : World.{u}} (left right : NoSuspendedCausalMagic W)
    {current : W.Current} (occurrence : W.OccurrenceAt current) :
    left.realize occurrence = right.realize occurrence := by
  exact (left.lawful_unique occurrence _ (right.lawful occurrence)).symm

/-- Minimal process presentation of the field-free causal world. -/
structure Process (W : World.{u}) : Type (u + 1) where
  EventAt : W.Current → Type u
  emitted : (current : W.Current) → EventAt current
  compile : {current : W.Current} → EventAt current → W.EvolutionAt current

def Process.generate {W : World.{u}} (process : Process W)
    (current : W.Current) : W.EvolutionAt current :=
  process.compile (process.emitted current)

def NoSuspendedCausalMagic.toProcess
    {W : World.{u}} (law : NoSuspendedCausalMagic W) : Process W where
  EventAt := W.OccurrenceAt
  emitted := W.emitted
  compile := law.realize

theorem NoSuspendedCausalMagic.process_generate_eq
    {W : World.{u}} (left right : NoSuspendedCausalMagic W)
    (current : W.Current) :
    left.toProcess.generate current = right.toProcess.generate current :=
  left.realize_eq right (W.emitted current)

/-- Constructive two-sided presentation, kept local so the causal core does
not depend on Mathlib's general `Equiv` machinery. -/
structure Presentation (A B : Type u) : Type u where
  toFun : A → B
  invFun : B → A
  left_inv : (value : A) → invFun (toFun value) = value
  right_inv : (value : B) → toFun (invFun value) = value

/-- A process faithfully presents exact world occurrences and compiles each
presented occurrence to a member of the world-owned lawful graph. -/
structure FaithfulRealization (W : World.{u})
    (process : Process W) : Type (u + 1) where
  occurrencePresentation : (current : W.Current) →
    Presentation (W.OccurrenceAt current) (process.EventAt current)
  emitted_commutes : (current : W.Current) →
    (occurrencePresentation current).toFun (W.emitted current) =
      process.emitted current
  compile_lawful : {current : W.Current} →
    (occurrence : W.OccurrenceAt current) →
    W.LawfulEvolutionAt occurrence
      (process.compile ((occurrencePresentation current).toFun occurrence))

/-- Any two faithful process presentations commute at the same exact
occurrence. -/
theorem FaithfulRealization.compile_eq_at_occurrence
    {W : World.{u}} (law : NoSuspendedCausalMagic W)
    {left right : Process W}
    (leftFaithful : FaithfulRealization W left)
    (rightFaithful : FaithfulRealization W right)
    {current : W.Current} (occurrence : W.OccurrenceAt current) :
    left.compile
        ((leftFaithful.occurrencePresentation current).toFun occurrence) =
      right.compile
        ((rightFaithful.occurrencePresentation current).toFun occurrence) :=
  law.lawful_evolution_eq
    (leftFaithful.compile_lawful occurrence)
    (rightFaithful.compile_lawful occurrence)

/-- Consequently the two processes generate the same evolution at every
reachable current. -/
theorem FaithfulRealization.generate_eq
    {W : World.{u}} (law : NoSuspendedCausalMagic W)
    {left right : Process W}
    (leftFaithful : FaithfulRealization W left)
    (rightFaithful : FaithfulRealization W right)
    (current : W.Current) :
    left.generate current = right.generate current := by
  calc
    left.generate current = left.compile
        ((leftFaithful.occurrencePresentation current).toFun
          (W.emitted current)) := by
      change left.compile (left.emitted current) = _
      rw [← leftFaithful.emitted_commutes current]
    _ = right.compile
        ((rightFaithful.occurrencePresentation current).toFun
          (W.emitted current)) :=
      leftFaithful.compile_eq_at_occurrence law rightFaithful
        (W.emitted current)
    _ = right.generate current := by
      change _ = right.compile (right.emitted current)
      rw [rightFaithful.emitted_commutes current]

/-- Constructive commuting presentation between two process realizations of
one fixed causal world.

This is stronger than equality of their generated outputs: it identifies the
event carriers through the exact world occurrence and proves that both the
source emitter and the whole compiler commute.  Consequently a grounded field
of one process cannot lend authority to an unrelated field of another process;
every authoritative event must cross this occurrence-level presentation. -/
structure ProcessCommutingPresentation
    {W : World.{u}} (left right : Process W) : Type (u + 1) where
  eventPresentation : (current : W.Current) →
    Presentation (left.EventAt current) (right.EventAt current)
  emitted_commutes : (current : W.Current) →
    (eventPresentation current).toFun (left.emitted current) =
      right.emitted current
  compile_commutes : {current : W.Current} →
    (event : left.EventAt current) →
    right.compile ((eventPresentation current).toFun event) =
      left.compile event

/-- Any two faithful realizations of one no-suspended-magic world differ at
most by a constructive event presentation commuting with the source emitter
and compiler.  No `Equiv`, quotient, choice, or extra comparison law is
installed by the consumer. -/
def FaithfulRealization.commutingPresentation
    {W : World.{u}} (law : NoSuspendedCausalMagic W)
    {left right : Process W}
    (leftFaithful : FaithfulRealization W left)
    (rightFaithful : FaithfulRealization W right) :
    ProcessCommutingPresentation left right where
  eventPresentation := fun current =>
    let leftPresentation := leftFaithful.occurrencePresentation current
    let rightPresentation := rightFaithful.occurrencePresentation current
    { toFun := fun event =>
        rightPresentation.toFun (leftPresentation.invFun event)
      invFun := fun event =>
        leftPresentation.toFun (rightPresentation.invFun event)
      left_inv := by
        intro event
        rw [rightPresentation.left_inv]
        exact leftPresentation.right_inv event
      right_inv := by
        intro event
        rw [leftPresentation.left_inv]
        exact rightPresentation.right_inv event }
  emitted_commutes := by
    intro current
    dsimp only
    rw [← leftFaithful.emitted_commutes current]
    rw [(leftFaithful.occurrencePresentation current).left_inv]
    exact rightFaithful.emitted_commutes current
  compile_commutes := by
    intro current event
    dsimp only
    let occurrence :=
      (leftFaithful.occurrencePresentation current).invFun event
    calc
      right.compile
          ((rightFaithful.occurrencePresentation current).toFun occurrence) =
          left.compile
            ((leftFaithful.occurrencePresentation current).toFun occurrence) :=
        (leftFaithful.compile_eq_at_occurrence law rightFaithful occurrence).symm
      _ = left.compile event := by
        rw [(leftFaithful.occurrencePresentation current).right_inv]

/-! ## Operational equivalence core -/

/-- A causal world whose observable equality is itself fixed by the world.

`EquivalentAt` is deliberately not a field of a realization witness.  A
realizer may present an already registered operational equivalence, but it
cannot decide after seeing its output which differences count as invisible. -/
structure OperationalWorld : Type (u + 1) where
  Current : Type u
  OccurrenceAt : Current → Type u
  EvolutionAt : Current → Type u
  emitted : (current : Current) → OccurrenceAt current
  EquivalentAt : {current : Current} →
    EvolutionAt current → EvolutionAt current → Type u
  equivalent_refl : {current : Current} →
    (evolution : EvolutionAt current) → EquivalentAt evolution evolution
  equivalent_symm : {current : Current} →
    {left right : EvolutionAt current} →
    EquivalentAt left right → EquivalentAt right left
  equivalent_trans : {current : Current} →
    {left middle right : EvolutionAt current} →
    EquivalentAt left middle → EquivalentAt middle right →
      EquivalentAt left right
  LawfulEvolutionAt : {current : Current} →
    OccurrenceAt current → EvolutionAt current → Type u

/-- Operational no-suspended-magic does not collapse harmless presentation
differences to literal equality.  It proves instead that every lawful output
belongs to the one world-owned operational class generated at the exact
occurrence. -/
structure NoSuspendedOperationalMagic
    (W : OperationalWorld.{u}) : Type (u + 1) where
  realize : {current : W.Current} → W.OccurrenceAt current →
    W.EvolutionAt current
  lawful : {current : W.Current} →
    (occurrence : W.OccurrenceAt current) →
    W.LawfulEvolutionAt occurrence (realize occurrence)
  lawful_unique_up_to_equivalence : {current : W.Current} →
    (occurrence : W.OccurrenceAt current) →
    (evolution : W.EvolutionAt current) →
    W.LawfulEvolutionAt occurrence evolution →
    W.EquivalentAt evolution (realize occurrence)

/-- Any two lawful outputs at one exact occurrence are operationally the same
according to the equivalence fixed by the world. -/
def NoSuspendedOperationalMagic.lawful_evolution_equivalent
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    {current : W.Current} {occurrence : W.OccurrenceAt current}
    {left right : W.EvolutionAt current}
    (leftLawful : W.LawfulEvolutionAt occurrence left)
    (rightLawful : W.LawfulEvolutionAt occurrence right) :
    W.EquivalentAt left right :=
  W.equivalent_trans
    (law.lawful_unique_up_to_equivalence occurrence left leftLawful)
    (W.equivalent_symm
      (law.lawful_unique_up_to_equivalence occurrence right rightLawful))

/-- A substantive difference is a world-owned proof that the two evolutions
do not lie in the same operational class. -/
structure DistinguishableAt (W : OperationalWorld.{u})
    {current : W.Current} (left right : W.EvolutionAt current) : Type u where
  rulesOutEquivalence : W.EquivalentAt left right → False

/-- One already registered operational observation of the fixed world.

This is a derived consumer contract, not another source of authority.  A
domain adapter may expose an observation only after proving that the world's
pre-existing operational equivalence commutes with it.  Consequently a
post-hoc observer cannot declare an equivalent pair distinguishable, while a
genuine observed difference cannot be hidden by an over-coarse equivalence. -/
structure OperationalObservationLaw (W : OperationalWorld.{u}) : Type (u + 1) where
  ObservationAt : W.Current → Type u
  observe : {current : W.Current} →
    W.EvolutionAt current → ObservationAt current
  equivalent_observation_eq : {current : W.Current} →
    {left right : W.EvolutionAt current} →
    W.EquivalentAt left right → observe left = observe right

/-- A complete registered operational signature.

Besides preserving every equivalence receipt, equality of the signature is
sufficient to reconstruct one.  A domain should expose this stronger
contract only for an exhaustive source-fixed observation inventory.  It
formalizes the converse half of the magic-detector rule: a presentation bit
that never changes the complete registered signature has no operationally
distinct standing. -/
structure CompleteOperationalObservationLaw
    (W : OperationalWorld.{u}) extends OperationalObservationLaw W where
  equivalent_of_observation_eq : {current : W.Current} →
    {left right : W.EvolutionAt current} →
    toOperationalObservationLaw.observe left =
        toOperationalObservationLaw.observe right →
      W.EquivalentAt left right

/-- Equality of a complete operational signature produces the world's own
equivalence receipt. -/
def CompleteOperationalObservationLaw.equivalentAt
    {W : OperationalWorld.{u}}
    (observation : CompleteOperationalObservationLaw W)
    {current : W.Current} {left right : W.EvolutionAt current}
    (same : observation.observe left = observation.observe right) :
    W.EquivalentAt left right :=
  observation.equivalent_of_observation_eq same

/-- No source-backed distinction can survive equality of a complete
operational signature. -/
theorem CompleteOperationalObservationLaw.no_distinguishable_of_observation_eq
    {W : OperationalWorld.{u}}
    (observation : CompleteOperationalObservationLaw W)
    {current : W.Current} {left right : W.EvolutionAt current}
    (same : observation.observe left = observation.observe right) :
    DistinguishableAt W left right → False := by
  intro different
  exact different.rulesOutEquivalence (observation.equivalentAt same)

/-- A difference detected by one commuting registered observation is a
substantive operational difference. -/
def OperationalObservationLaw.distinguishableAt
    {W : OperationalWorld.{u}} (observation : OperationalObservationLaw W)
    {current : W.Current} {left right : W.EvolutionAt current}
    (different : observation.observe left ≠ observation.observe right) :
    DistinguishableAt W left right where
  rulesOutEquivalence := fun equivalent =>
    different (observation.equivalent_observation_eq equivalent)

/-- No-Free Operational Difference: a genuinely distinguishable difference
cannot be introduced by two realizers of the same exact occurrence. -/
theorem NoSuspendedOperationalMagic.no_free_operational_difference
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    {current : W.Current} {occurrence : W.OccurrenceAt current}
    {left right : W.EvolutionAt current}
    (different : DistinguishableAt W left right)
    (leftLawful : W.LawfulEvolutionAt occurrence left)
    (rightLawful : W.LawfulEvolutionAt occurrence right) : False :=
  different.rulesOutEquivalence
    (law.lawful_evolution_equivalent leftLawful rightLawful)

/-- A distinguishable lawful difference inside one fixed world and current
must be paid by a different exact occurrence.  This is the positive readout
of No-Free Operational Difference: if the occurrences were equal, both
outputs would be realizations of the same event and the existing hard gate
would reject the distinction.

The theorem does not classify cross-world changes.  There the differing
source or law-world index is already the registered difference. -/
theorem NoSuspendedOperationalMagic.occurrence_ne_of_distinguishable
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    {current : W.Current}
    {leftOccurrence rightOccurrence : W.OccurrenceAt current}
    {left right : W.EvolutionAt current}
    (different : DistinguishableAt W left right)
    (leftLawful : W.LawfulEvolutionAt leftOccurrence left)
    (rightLawful : W.LawfulEvolutionAt rightOccurrence right) :
    leftOccurrence ≠ rightOccurrence := by
  intro occurrence_eq
  cases occurrence_eq
  exact law.no_free_operational_difference
    different leftLawful rightLawful

/-- No-Free Observed Difference: if a registered observation distinguishes
two outputs, they cannot both be lawful realizations of one exact occurrence.
The theorem reuses the existing no-free operational law; it does not add a
second notion of causality or equality. -/
theorem NoSuspendedOperationalMagic.no_free_observed_difference
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    (observation : OperationalObservationLaw W)
    {current : W.Current} {occurrence : W.OccurrenceAt current}
    {left right : W.EvolutionAt current}
    (different : observation.observe left ≠ observation.observe right)
    (leftLawful : W.LawfulEvolutionAt occurrence left)
    (rightLawful : W.LawfulEvolutionAt occurrence right) : False :=
  law.no_free_operational_difference
    (observation.distinguishableAt different) leftLawful rightLawful

/-- Two constructive realizers of the same operational world may return
different presentations, but never different operational realities. -/
def NoSuspendedOperationalMagic.realize_equivalent
    {W : OperationalWorld.{u}}
    (left right : NoSuspendedOperationalMagic W)
    {current : W.Current} (occurrence : W.OccurrenceAt current) :
    W.EquivalentAt (left.realize occurrence) (right.realize occurrence) :=
  left.lawful_evolution_equivalent
    (left.lawful occurrence) (right.lawful occurrence)

/-- Minimal process presentation of an operational causal world. -/
structure OperationalProcess (W : OperationalWorld.{u}) : Type (u + 1) where
  EventAt : W.Current → Type u
  emitted : (current : W.Current) → EventAt current
  compile : {current : W.Current} → EventAt current → W.EvolutionAt current

def OperationalProcess.generate
    {W : OperationalWorld.{u}} (process : OperationalProcess W)
    (current : W.Current) : W.EvolutionAt current :=
  process.compile (process.emitted current)

def NoSuspendedOperationalMagic.toProcess
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W) :
    OperationalProcess W where
  EventAt := W.OccurrenceAt
  emitted := W.emitted
  compile := law.realize

def NoSuspendedOperationalMagic.process_generate_equivalent
    {W : OperationalWorld.{u}}
    (left right : NoSuspendedOperationalMagic W)
    (current : W.Current) :
    W.EquivalentAt (left.toProcess.generate current)
      (right.toProcess.generate current) :=
  left.realize_equivalent right (W.emitted current)

/-- A process faithfully presents exact occurrences and lands in the lawful
operational class fixed by the world. -/
structure OperationalFaithfulRealization (W : OperationalWorld.{u})
    (process : OperationalProcess W) : Type (u + 1) where
  occurrencePresentation : (current : W.Current) →
    Presentation (W.OccurrenceAt current) (process.EventAt current)
  emitted_commutes : (current : W.Current) →
    (occurrencePresentation current).toFun (W.emitted current) =
      process.emitted current
  compile_lawful : {current : W.Current} →
    (occurrence : W.OccurrenceAt current) →
    W.LawfulEvolutionAt occurrence
      (process.compile ((occurrencePresentation current).toFun occurrence))

/-- Faithful presentations commute up to the operational equivalence fixed
before either presentation is supplied. -/
def OperationalFaithfulRealization.compile_equivalent_at_occurrence
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    {left right : OperationalProcess W}
    (leftFaithful : OperationalFaithfulRealization W left)
    (rightFaithful : OperationalFaithfulRealization W right)
    {current : W.Current} (occurrence : W.OccurrenceAt current) :
    W.EquivalentAt
      (left.compile
        ((leftFaithful.occurrencePresentation current).toFun occurrence))
      (right.compile
        ((rightFaithful.occurrencePresentation current).toFun occurrence)) :=
  law.lawful_evolution_equivalent
    (leftFaithful.compile_lawful occurrence)
    (rightFaithful.compile_lawful occurrence)

def OperationalFaithfulRealization.generate_equivalent
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    {left right : OperationalProcess W}
    (leftFaithful : OperationalFaithfulRealization W left)
    (rightFaithful : OperationalFaithfulRealization W right)
    (current : W.Current) :
    W.EquivalentAt (left.generate current) (right.generate current) := by
  change W.EquivalentAt
    (left.compile (left.emitted current))
    (right.compile (right.emitted current))
  rw [← leftFaithful.emitted_commutes current,
    ← rightFaithful.emitted_commutes current]
  exact leftFaithful.compile_equivalent_at_occurrence law rightFaithful
    (W.emitted current)

/-- Constructive event presentation between two faithful processes of one
fixed operational world.  Compiler commutation is measured by the
world-owned equivalence relation rather than literal equality. -/
structure OperationalProcessCommutingPresentation
    {W : OperationalWorld.{u}}
    (left right : OperationalProcess W) : Type (u + 1) where
  eventPresentation : (current : W.Current) →
    Presentation (left.EventAt current) (right.EventAt current)
  emitted_commutes : (current : W.Current) →
    (eventPresentation current).toFun (left.emitted current) =
      right.emitted current
  compile_equivalent : {current : W.Current} →
    (event : left.EventAt current) →
    W.EquivalentAt
      (left.compile event)
      (right.compile ((eventPresentation current).toFun event))

/-- Any two faithful realizations of one operational world differ at most by
an exact event presentation whose compiler images lie in the equivalence
class fixed by that world.  The comparison law is not supplied by either
process or by the consumer. -/
def OperationalFaithfulRealization.commutingPresentation
    {W : OperationalWorld.{u}} (law : NoSuspendedOperationalMagic W)
    {left right : OperationalProcess W}
    (leftFaithful : OperationalFaithfulRealization W left)
    (rightFaithful : OperationalFaithfulRealization W right) :
    OperationalProcessCommutingPresentation left right where
  eventPresentation := fun current =>
    let leftPresentation := leftFaithful.occurrencePresentation current
    let rightPresentation := rightFaithful.occurrencePresentation current
    { toFun := fun event =>
        rightPresentation.toFun (leftPresentation.invFun event)
      invFun := fun event =>
        leftPresentation.toFun (rightPresentation.invFun event)
      left_inv := by
        intro event
        rw [rightPresentation.left_inv]
        exact leftPresentation.right_inv event
      right_inv := by
        intro event
        rw [leftPresentation.left_inv]
        exact rightPresentation.right_inv event }
  emitted_commutes := by
    intro current
    dsimp only
    rw [← leftFaithful.emitted_commutes current]
    rw [(leftFaithful.occurrencePresentation current).left_inv]
    exact rightFaithful.emitted_commutes current
  compile_equivalent := by
    intro current event
    dsimp only
    let occurrence :=
      (leftFaithful.occurrencePresentation current).invFun event
    have equivalent := leftFaithful.compile_equivalent_at_occurrence
      law rightFaithful occurrence
    rw [(leftFaithful.occurrencePresentation current).right_inv event] at equivalent
    exact equivalent

/-- Type-valued witness for literal equality.  Keeping the witness explicit
lets the constructive core use equality as one operational relation without
turning every operational receipt into a proposition or quotient. -/
structure EqualityReceipt {A : Type u} (left right : A) : Type u where
  eq : left = right

/-- Literal causal uniqueness is the special operational world whose
equivalence relation is equality. -/
def World.toOperationalWorld (W : World.{u}) : OperationalWorld.{u} where
  Current := W.Current
  OccurrenceAt := W.OccurrenceAt
  EvolutionAt := W.EvolutionAt
  emitted := W.emitted
  EquivalentAt := EqualityReceipt
  equivalent_refl := fun _ => ⟨rfl⟩
  equivalent_symm := fun receipt => ⟨receipt.eq.symm⟩
  equivalent_trans := fun leftToMiddle middleToRight =>
    ⟨leftToMiddle.eq.trans middleToRight.eq⟩
  LawfulEvolutionAt := W.LawfulEvolutionAt

/-- Equality-based no-suspended-magic canonically realizes the operational
law; no new comparator or outcome choice is introduced. -/
def NoSuspendedCausalMagic.toOperational
    {W : World.{u}} (law : NoSuspendedCausalMagic W) :
    NoSuspendedOperationalMagic W.toOperationalWorld where
  realize := fun occurrence => law.realize occurrence
  lawful := fun occurrence => law.lawful occurrence
  lawful_unique_up_to_equivalence := fun occurrence evolution lawful =>
    ⟨law.lawful_unique occurrence evolution lawful⟩

end CausalCore
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
