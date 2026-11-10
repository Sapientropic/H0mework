import H0mework.Physics.Admission.StandingAuditBasis
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.PhysicsCore.SU7GeneratedCenterCoverPath

/-!
# Generated residual standing boundary

The generated endpoint repair graph exposes two different identities that
must not be conflated:

* exact endpoint identity remembers the full endpoint/source lineage;
* residual identity remembers only the raw residual-energy level.

This module packages residual equality as a *candidate* native standing
identity and packages the predicates that factor through residual energy as a
candidate standing-relevance family.  It does not select that candidate as the
physical standing contract, and it does not add an eighth audit primitive.

The `n=5`, bound-seven fork makes the boundary concrete.  Its two terminal
endpoints have the same zero residual, so every residual-relevant predicate
agrees on them.  They nevertheless have different exact endpoint lineages,
and a signed reference-relative lineage residual separates them.  Thus a
residual quotient can support a standing-level convergence claim without
erasing the lineage responsibility retained by relation, trace, and residual.
-/

namespace SaturationMonoid
namespace PhysicsCore
namespace SU7GeneratedResidualStandingBoundary

open Relation
open SU7GeneratedCurrentSourceClosure
open SU7GeneratedCenterCoverPath

noncomputable section

/-! ## Two identity layers -/

/-- Exact endpoint identity.  This is the finest identity considered here and
retains the full ordered endpoint pair. -/
def endpointExactIdentity : NativeStandingIdentity (Nat × Nat) where
  sameStanding := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans

/-- Equality of raw residual energy, packaged as a candidate standing
identity.  The word `Candidate` is substantive: selecting this quotient for a
physical standing contract remains a separate source/relevance obligation. -/
def endpointResidualIdentityCandidate (n : Nat) :
    NativeStandingIdentity (Nat × Nat) where
  sameStanding := EndpointResidualEquivalent n
  refl := endpointResidualEquivalent_refl n
  symm := endpointResidualEquivalent_symm
  trans := endpointResidualEquivalent_trans

/-- A residual-level predicate saying that endpoint repair has reached the
zero-energy class. -/
def EndpointResidualZero (n : Nat) (state : Nat × Nat) : Prop :=
  endpointEnergy n state = 0

theorem endpointResidualZero_standingInvariant (n : Nat) :
    StandingInvariant
      (endpointResidualIdentityCandidate n) (EndpointResidualZero n) := by
  intro source target hsame
  change EndpointResidualEquivalent n source target at hsame
  change endpointEnergy n source = 0 ↔ endpointEnergy n target = 0
  rw [hsame]

/-- Candidate relevance family consisting exactly of predicates that factor
through the generated residual-energy readout.  This family is derived from
the residual map, not from expressibility by the seven audit atoms. -/
def endpointResidualRelevanceCandidate (n : Nat) :
    StandingRelevance (endpointResidualIdentityCandidate n) where
  relevant := fun target =>
    ∃ residualPredicate : Nat → Prop,
      ∀ state, target state ↔ residualPredicate (endpointEnergy n state)
  invariant := by
    intro target htarget source result hsame
    rcases htarget with ⟨residualPredicate, htarget⟩
    change EndpointResidualEquivalent n source result at hsame
    calc
      target source ↔
          residualPredicate (endpointEnergy n source) := htarget source
      _ ↔ residualPredicate (endpointEnergy n result) := by rw [hsame]
      _ ↔ target result := (htarget result).symm

theorem endpointResidualZero_relevant (n : Nat) :
    (endpointResidualRelevanceCandidate n).relevant
      (EndpointResidualZero n) := by
  refine ⟨fun residual => residual = 0, ?_⟩
  intro state
  rfl

theorem sameResidualStanding_of_zero
    {n : Nat} {left right : Nat × Nat}
    (hleft : EndpointResidualZero n left)
    (hright : EndpointResidualZero n right) :
    (endpointResidualIdentityCandidate n).sameStanding left right := by
  change EndpointResidualEquivalent n left right
  exact hleft.trans hright.symm

/-- The existing global source-closure theorem reaches the zero class of the
candidate residual identity.  No unique terminal endpoint is claimed. -/
theorem generatedEndpointPair_reaches_residualStandingZero_of_closure
    {n bound : Nat}
    (Hclosure : GeneratedSourceClosure n bound)
    {pair : Nat × Nat}
    (Hpair : GeneratedEndpointPair n bound pair) :
    ∃ terminal : Nat × Nat,
      RewriteStar (GeneratedEndpointRepairStep n bound) pair terminal ∧
        GeneratedEndpointPair n bound terminal ∧
          EndpointResidualZero n terminal := by
  simpa [EndpointResidualZero] using
    generatedEndpointPair_reaches_residualZero_of_closure Hclosure Hpair

/-! ## Reference-relative exact lineage residual -/

/-- Exact endpoint lineage is a reference-relative relation, not another
Boolean standing primitive. -/
def EndpointLineageMatches
    (reference state : Nat × Nat) : Prop :=
  state = reference

/-- Signed endpoint displacement relative to an exact lineage reference.  It
retains direction and magnitude even when the scalar endpoint energy agrees. -/
abbrev EndpointLineageResidual := Int × Int

def endpointLineageResidual
    (reference state : Nat × Nat) : EndpointLineageResidual :=
  ((state.1 : Int) - (reference.1 : Int),
    (state.2 : Int) - (reference.2 : Int))

/-- The reference-relative residual vanishes exactly at an exact endpoint
lineage match. -/
theorem endpointLineageResidual_eq_zero_iff
    (reference state : Nat × Nat) :
    endpointLineageResidual reference state = 0 ↔
      EndpointLineageMatches reference state := by
  constructor
  · intro hzero
    have hleft := congrArg Prod.fst hzero
    have hright := congrArg Prod.snd hzero
    change
      (state.1 : Int) - (reference.1 : Int) = 0 at hleft
    change
      (state.2 : Int) - (reference.2 : Int) = 0 at hright
    change state = reference
    apply Prod.ext
    · exact_mod_cast (sub_eq_zero.mp hleft)
    · exact_mod_cast (sub_eq_zero.mp hright)
  · intro hmatch
    change state = reference at hmatch
    subst state
    simp [endpointLineageResidual]

theorem endpointLineageMatches_exactStandingInvariant
    (reference : Nat × Nat) :
    StandingInvariant endpointExactIdentity
      (EndpointLineageMatches reference) := by
  intro source target hsame
  change source = target at hsame
  subst target
  rfl

/-- Exact standing transport preserves the complete signed lineage residual. -/
theorem endpointLineageResidual_eq_of_exactStanding
    (reference : Nat × Nat) {source target : Nat × Nat}
    (hsame : endpointExactIdentity.sameStanding source target) :
    endpointLineageResidual reference source =
      endpointLineageResidual reference target := by
  change source = target at hsame
  subst target
  rfl

theorem endpointLineageResidual_separates
    {reference source target : Nat × Nat}
    (hsource : EndpointLineageMatches reference source)
    (htarget : ¬ EndpointLineageMatches reference target) :
    endpointLineageResidual reference source ≠
      endpointLineageResidual reference target := by
  intro hequal
  have hsourceZero : endpointLineageResidual reference source = 0 :=
    (endpointLineageResidual_eq_zero_iff reference source).2 hsource
  have htargetZero : endpointLineageResidual reference target = 0 := by
    rw [← hequal]
    exact hsourceZero
  exact htarget
    ((endpointLineageResidual_eq_zero_iff reference target).1 htargetZero)

/-! ## Repair-path responsibility transport -/

/-- A generated repair path indexed by its exact number of unit-energy
steps.  Unlike a scalar residual readout, this proposition retains every
intermediate generated endpoint and edge in its constructor chain. -/
inductive GeneratedEndpointRepairSteps (n bound : Nat) :
    (Nat × Nat) → (Nat × Nat) → Nat → Prop
  | refl (state : Nat × Nat) :
      GeneratedEndpointRepairSteps n bound state state 0
  | tail {source middle target : Nat × Nat} {stepCount : Nat}
      (pathPrefix : GeneratedEndpointRepairSteps n bound source middle stepCount)
      (step : GeneratedEndpointRepairStep n bound middle target) :
      GeneratedEndpointRepairSteps n bound source target (stepCount + 1)

namespace GeneratedEndpointRepairSteps

variable {n bound stepCount : Nat}
variable {source target : Nat × Nat}

theorem to_rewriteStar
    (H : GeneratedEndpointRepairSteps n bound source target stepCount) :
    RewriteStar (GeneratedEndpointRepairStep n bound) source target := by
  induction H with
  | refl => exact ReflTransGen.refl
  | tail _ step ih => exact ReflTransGen.tail ih step

/-- The step index is exactly the scalar residual-energy loss. -/
theorem energy_balance
    (H : GeneratedEndpointRepairSteps n bound source target stepCount) :
    endpointEnergy n target + stepCount = endpointEnergy n source := by
  induction H with
  | refl => simp
  | tail _ step ih =>
      have hunit := step.energy_unit
      omega

end GeneratedEndpointRepairSteps

/-- Every ordinary generated rewrite path admits an exact unit-step index. -/
theorem exists_generatedEndpointRepairSteps_of_rewriteStar
    {n bound : Nat} {source target : Nat × Nat}
    (H : RewriteStar (GeneratedEndpointRepairStep n bound) source target) :
    ∃ stepCount : Nat,
      GeneratedEndpointRepairSteps n bound source target stepCount := by
  induction H with
  | refl => exact ⟨0, .refl _⟩
  | tail _ step ih =>
      rcases ih with ⟨stepCount, pathPrefix⟩
      exact ⟨stepCount + 1, .tail pathPrefix step⟩

theorem rewriteStar_iff_exists_generatedEndpointRepairSteps
    {n bound : Nat} {source target : Nat × Nat} :
    RewriteStar (GeneratedEndpointRepairStep n bound) source target ↔
      ∃ stepCount : Nat,
        GeneratedEndpointRepairSteps n bound source target stepCount := by
  constructor
  · exact exists_generatedEndpointRepairSteps_of_rewriteStar
  · rintro ⟨_stepCount, H⟩
    exact H.to_rewriteStar

/-- Reference-relative signed endpoint displacements compose additively.
This identity is the exact-lineage account that the scalar residual quotient
does not retain. -/
theorem endpointLineageResidual_transport
    (reference source target : Nat × Nat) :
    endpointLineageResidual reference target =
      endpointLineageResidual reference source +
        endpointLineageResidual source target := by
  apply Prod.ext
  · change
      (target.1 : Int) - (reference.1 : Int) =
        ((source.1 : Int) - (reference.1 : Int)) +
          ((target.1 : Int) - (source.1 : Int))
    ring
  · change
      (target.2 : Int) - (reference.2 : Int) =
        ((source.2 : Int) - (reference.2 : Int)) +
          ((target.2 : Int) - (source.2 : Int))
    ring

/-- A proof-level responsibility chain couples the exact generated path with
its scalar energy ledger and its signed exact-lineage displacement. -/
def EndpointRepairResponsibilityTrace
    (n bound : Nat) (reference source target : Nat × Nat) : Prop :=
  ∃ stepCount : Nat,
    GeneratedEndpointRepairSteps n bound source target stepCount ∧
      endpointEnergy n target + stepCount = endpointEnergy n source ∧
        endpointLineageResidual reference target =
          endpointLineageResidual reference source +
            endpointLineageResidual source target

/-- Native generated rewrite paths therefore preserve an explicit
responsibility account without requiring exact-state confluence. -/
theorem endpointRepairResponsibilityTrace_of_rewriteStar
    {n bound : Nat} (reference : Nat × Nat)
    {source target : Nat × Nat}
    (H : RewriteStar (GeneratedEndpointRepairStep n bound) source target) :
    EndpointRepairResponsibilityTrace n bound reference source target := by
  rcases exists_generatedEndpointRepairSteps_of_rewriteStar H with
    ⟨stepCount, Hsteps⟩
  exact
    ⟨stepCount, Hsteps, Hsteps.energy_balance,
      endpointLineageResidual_transport reference source target⟩

/-! ## The zero-residual fork separates the two responsibilities -/

theorem five_seven_zero_pairs_sameResidualStanding :
    (endpointResidualIdentityCandidate 5).sameStanding
      (3, 7) (5, 5) :=
  five_seven_zero_pairs_distinct_but_residualEquivalent.2

theorem five_seven_reference_lineageResiduals :
    endpointLineageResidual (3, 7) (3, 7) = (0, 0) ∧
      endpointLineageResidual (3, 7) (5, 5) =
        ((2 : Int), (-2 : Int)) := by
  norm_num [endpointLineageResidual]

theorem five_seven_zero_pairs_lineageResidual_distinct :
    endpointLineageResidual (3, 7) (3, 7) ≠
      endpointLineageResidual (3, 7) (5, 5) := by
  rw [five_seven_reference_lineageResiduals.1,
    five_seven_reference_lineageResiduals.2]
  norm_num

theorem five_seven_left_responsibilityTrace :
    EndpointRepairResponsibilityTrace
      5 7 (2, 7) (2, 7) (3, 7) :=
  endpointRepairResponsibilityTrace_of_rewriteStar (2, 7)
    (ReflTransGen.single step_five_seven_two_seven_to_three_seven)

theorem five_seven_right_responsibilityTrace :
    EndpointRepairResponsibilityTrace
      5 7 (2, 7) (2, 7) (5, 5) :=
  endpointRepairResponsibilityTrace_of_rewriteStar (2, 7)
    (ReflTransGen.single step_five_seven_two_seven_to_five_five)

theorem five_seven_fork_sourceLineageResiduals :
    endpointLineageResidual (2, 7) (3, 7) = ((1 : Int), 0) ∧
      endpointLineageResidual (2, 7) (5, 5) =
        ((3 : Int), (-2 : Int)) := by
  norm_num [endpointLineageResidual]

theorem five_seven_fork_responsibilityDisplacements_distinct :
    endpointLineageResidual (2, 7) (3, 7) ≠
      endpointLineageResidual (2, 7) (5, 5) := by
  rw [five_seven_fork_sourceLineageResiduals.1,
    five_seven_fork_sourceLineageResiduals.2]
  norm_num

/-- Exact lineage match is stable for exact endpoint identity but not for the
coarser residual-identity candidate. -/
theorem five_seven_lineageMatches_not_residualStandingInvariant :
    ¬ StandingInvariant (endpointResidualIdentityCandidate 5)
        (EndpointLineageMatches (3, 7)) := by
  intro hinvariant
  have hmatch : EndpointLineageMatches (3, 7) (3, 7) := rfl
  have hwrong : EndpointLineageMatches (3, 7) (5, 5) :=
    (hinvariant five_seven_zero_pairs_sameResidualStanding).mp hmatch
  norm_num [EndpointLineageMatches] at hwrong

/-- Consequently exact lineage is outside the residual-factorizing candidate
relevance family.  Its information remains available in the signed residual. -/
theorem five_seven_lineageMatches_not_residualRelevant :
    ¬ (endpointResidualRelevanceCandidate 5).relevant
        (EndpointLineageMatches (3, 7)) := by
  intro hrelevant
  exact five_seven_lineageMatches_not_residualStandingInvariant
    ((endpointResidualRelevanceCandidate 5).invariant
      (EndpointLineageMatches (3, 7)) hrelevant)

/-- Final concrete layer statement: the two terminal repairs agree at the
residual standing candidate while a reference-relative exact-lineage residual
still distinguishes them. -/
theorem five_seven_sameResidualStanding_but_lineageTrace_distinct :
    (endpointResidualIdentityCandidate 5).sameStanding (3, 7) (5, 5) ∧
      endpointLineageResidual (3, 7) (3, 7) ≠
        endpointLineageResidual (3, 7) (5, 5) :=
  ⟨five_seven_zero_pairs_sameResidualStanding,
    five_seven_zero_pairs_lineageResidual_distinct⟩

/-- Both nonconfluent legs carry generated responsibility traces with the same
scalar terminal residual but different exact signed displacements. -/
theorem five_seven_residualJoin_but_responsibilityTraces_distinct :
    EndpointRepairResponsibilityTrace 5 7 (2, 7) (2, 7) (3, 7) ∧
      EndpointRepairResponsibilityTrace 5 7 (2, 7) (2, 7) (5, 5) ∧
        EndpointResidualEquivalent 5 (3, 7) (5, 5) ∧
          endpointLineageResidual (2, 7) (3, 7) ≠
            endpointLineageResidual (2, 7) (5, 5) :=
  ⟨five_seven_left_responsibilityTrace,
    five_seven_right_responsibilityTrace,
    five_seven_zero_pairs_distinct_but_residualEquivalent.2,
    five_seven_fork_responsibilityDisplacements_distinct⟩

end
end SU7GeneratedResidualStandingBoundary
end PhysicsCore
end SaturationMonoid
