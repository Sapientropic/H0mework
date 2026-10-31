import H0mework.Versions.Rfde5c14d.ReleaseMaterials.SaturationMonoid.ProcessGame.Regression.Society.M14.Fixture.Economy.Credit.Risk.Merge.Capacity.Renewal.Settlement.Joint.Renewal.Submission.Action.Transport.Renewal.Recurrence.Iteration.Lifecycle.Constitution.RootLaw.Cofinality.Recognition.Archive.Revision.Gain.Explosion.Fair.Pro.Noncompact.Local.Threshold.Fibre.Flux.Cumulative.Adaptive.Terminating.ActionableExit.Acceptance.Enactment.Cascade.Fold.Consumer.ProofCarryingCanonicalSocietyAcceptedLegislationFiniteFoldUniversal

/-!
# Source-generated finite proposal acceptance compiler

An arbitrary finite external Payment-proposal program is classified as
accepted at every physical node or refused for the first time at one unique
node.  The program is theorem input only; it carries no verdict, acceptance,
effect, next, root authority or stored future.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ProcessGame
namespace Society
namespace M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler

noncomputable section

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open M14UBIPeriodicRootHistory
open M14SourceGeneratedContributionMergeActionSource
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation
open M14SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislation.SourceGeneratedPostSettlementObserverSubmissionExternalPaymentLegislationAt
open M14SourceGeneratedPostSettlementObserverFinitePaidSelfU8Iteration
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal
open M14SourceGeneratedCanonicalSocietyExternalPaymentLegislationAcceptanceSeal.SourceAcceptedExternalPaymentLegislationAt
open M14SourceGeneratedCanonicalSocietyPointwiseRecognizedExternalPaymentLegislationAcceptance
open M14SourceGeneratedCanonicalSocietyFiniteAcceptedLegislationEnactmentCascade
open M14SourceGeneratedCanonicalSocietyAcceptedLegislationEnactmentStep

/-- A finite external proposal program.  It submits only heterogeneous
Payment occurrences and owns no acceptance or world-writing authority. -/
abbrev FiniteProposalProgramAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (_initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :=
  Fin (fuel + 1) → AnySourceBackedPaymentOccurrence

/-- Source acceptance of one program proposal at the literal physical cycle
span and its already existing target PCL. -/
abbrev FiniteProposalAcceptedAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) :=
  SourceAcceptedExternalPaymentLegislationAt
    (cycleLegislationSpanAt initial node.1)
    (program node)
    (targetLegislation (cycleLegislationSpanAt initial node.1))

abbrev EveryFiniteProposalAcceptedAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel) :=
  ∀ node, Nonempty (FiniteProposalAcceptedAt initial program node)

/-- Acceptance is exactly equality with the source-recognized Payment at the
same physical node. -/
theorem finiteProposalAccepted_nonempty_iff_sourceProposal
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) :
    Nonempty (FiniteProposalAcceptedAt initial program node) ↔
      program node =
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + node.1) := by
  exact
    sourceAcceptance_nonempty_iff_pointwiseProposal_exactPCL
      (cycleLegislationSpanAt initial node.1) (program node)
      (targetLegislation (cycleLegislationSpanAt initial node.1))
      |>.trans (and_iff_left HEq.rfl)

/-- Least-failure certificate.  This is proof-only classification data, not
a rejection occurrence, ledger row or authority token. -/
structure FirstSourceAcceptanceRefusalAt
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1)) : Prop where
  earlierAccepted : ∀ earlier : Fin (fuel + 1),
    earlier.1 < node.1 →
      Nonempty (FiniteProposalAcceptedAt initial program earlier)
  refused : IsEmpty (FiniteProposalAcceptedAt initial program node)

/-- A mismatched external proposal cannot inhabit the source acceptance
fibre at that node. -/
theorem finiteProposalAccepted_isEmpty_of_ne_sourceProposal
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary)
    (program : FiniteProposalProgramAt initial fuel)
    (node : Fin (fuel + 1))
    (different : program node ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + node.1)) :
    IsEmpty (FiniteProposalAcceptedAt initial program node) :=
  ⟨fun acceptance => different
    ((finiteProposalAccepted_nonempty_iff_sourceProposal initial program node
      ).mp ⟨acceptance⟩)⟩

theorem FirstSourceAcceptanceRefusalAt.proposal_ne_source
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    {node : Fin (fuel + 1)}
    (refusal : FirstSourceAcceptanceRefusalAt initial program node) :
    program node ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + node.1) := by
  intro exactProposal
  exact refusal.refused.false
    (Classical.choice
      ((finiteProposalAccepted_nonempty_iff_sourceProposal initial program node
        ).mpr exactProposal))

/-- Exhaustive compiler: it chooses the least refusal internally whenever
not every node is accepted. -/
def compileFiniteProposalProgram
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (program : FiniteProposalProgramAt initial fuel) :
    Sum (PLift (EveryFiniteProposalAcceptedAt initial program))
      (Σ node, PLift
        (FirstSourceAcceptanceRefusalAt initial program node)) := by
  classical
  let refusedNodes : Finset (Fin (fuel + 1)) :=
    Finset.univ.filter fun node =>
      program node ≠
        pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
          (boundary + node.1)
  by_cases refusedNonempty : refusedNodes.Nonempty
  · let firstNode : Fin (fuel + 1) :=
      refusedNodes.min' refusedNonempty
    have firstMem : firstNode ∈ refusedNodes :=
      Finset.min'_mem refusedNodes refusedNonempty
    have firstMismatch :
        program firstNode ≠
          pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
            (boundary + firstNode.1) :=
      (Finset.mem_filter.mp firstMem).2
    refine .inr ⟨firstNode, ⟨?_⟩⟩
    exact
      { earlierAccepted := by
          intro earlier earlierLt
          apply
            (finiteProposalAccepted_nonempty_iff_sourceProposal initial
              program earlier).mpr
          by_contra earlierMismatch
          have earlierMem : earlier ∈ refusedNodes :=
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ earlier, earlierMismatch⟩
          have firstLeEarlier : firstNode ≤ earlier :=
            Finset.min'_le refusedNodes earlier earlierMem
          exact (not_lt_of_ge firstLeEarlier) earlierLt
        refused :=
          finiteProposalAccepted_isEmpty_of_ne_sourceProposal initial
            program firstNode firstMismatch }
  · refine .inl ⟨?_⟩
    intro node
    apply
      (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
        node).mpr
    by_contra mismatch
    apply refusedNonempty
    exact ⟨node, Finset.mem_filter.mpr
      ⟨Finset.mem_univ node, mismatch⟩⟩

/-- The least refusal is propositionally unique. -/
theorem firstSourceAcceptanceRefusal_unique
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel}
    {left right : Fin (fuel + 1)}
    (leftRefusal :
      FirstSourceAcceptanceRefusalAt initial program left)
    (rightRefusal :
      FirstSourceAcceptanceRefusalAt initial program right) :
    left = right := by
  apply Fin.ext
  by_contra different
  by_cases leftEarlier : left.1 < right.1
  · exact leftRefusal.refused.false
      (Classical.choice
        (rightRefusal.earlierAccepted left leftEarlier))
  · have rightEarlier : right.1 < left.1 := by omega
    exact rightRefusal.refused.false
      (Classical.choice
        (leftRefusal.earlierAccepted right rightEarlier))

/-- Exhaustive branches cannot both hold. -/
theorem everyAccepted_and_firstRefusal_isEmpty
    {oldVisit : OldVisit} {sourceIndex boundary fuel : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {program : FiniteProposalProgramAt initial fuel} :
    IsEmpty
      (PLift (EveryFiniteProposalAcceptedAt initial program) ×
        (Σ node, PLift
          (FirstSourceAcceptanceRefusalAt initial program node))) :=
  ⟨fun both =>
    both.2.2.down.refused.false
      (Classical.choice (both.1.down both.2.1))⟩

/-- Exact semantic classification of the compiler's all-accepted branch. -/
theorem compileFiniteProposalProgram_allBranch_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (program : FiniteProposalProgramAt initial fuel) :
    (∃ every : PLift (EveryFiniteProposalAcceptedAt initial program),
        compileFiniteProposalProgram initial fuel program = .inl every) ↔
      EveryFiniteProposalAcceptedAt initial program := by
  constructor
  · rintro ⟨every, _⟩
    exact every.down
  · intro every
    cases resultExact :
        compileFiniteProposalProgram initial fuel program with
    | inl compiledEvery =>
        exact ⟨compiledEvery, rfl⟩
    | inr compiledRefusal =>
        exact False.elim
          (compiledRefusal.2.down.refused.false
            (Classical.choice (every compiledRefusal.1)))

/-- Exact semantic classification of the compiler's refusal branch. -/
theorem compileFiniteProposalProgram_refusalBranch_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (program : FiniteProposalProgramAt initial fuel) :
    (∃ (node : Fin (fuel + 1))
        (refusal : PLift
          (FirstSourceAcceptanceRefusalAt initial program node)),
        compileFiniteProposalProgram initial fuel program =
          .inr ⟨node, refusal⟩) ↔
      ¬ EveryFiniteProposalAcceptedAt initial program := by
  constructor
  · rintro ⟨node, refusal, _⟩ every
    exact refusal.down.refused.false
      (Classical.choice (every node))
  · intro notEvery
    cases resultExact :
        compileFiniteProposalProgram initial fuel program with
    | inl compiledEvery =>
        exact False.elim (notEvery compiledEvery.down)
    | inr compiledRefusal =>
        exact ⟨compiledRefusal.1, compiledRefusal.2, rfl⟩

/-- Restriction of theorem-input proposals to a shorter finite audit. -/
def restrictFiniteProposalProgramAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {shortFuel longFuel : Nat} (within : shortFuel ≤ longFuel)
    (program : FiniteProposalProgramAt initial longFuel) :
    FiniteProposalProgramAt initial shortFuel := fun node =>
  program ⟨node.1, by omega⟩

theorem everyFiniteProposalAccepted_restrict
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {shortFuel longFuel : Nat} (within : shortFuel ≤ longFuel)
    {program : FiniteProposalProgramAt initial longFuel}
    (every : EveryFiniteProposalAcceptedAt initial program) :
    EveryFiniteProposalAcceptedAt initial
      (restrictFiniteProposalProgramAt within program) := by
  intro node
  let lifted : Fin (longFuel + 1) := ⟨node.1, by omega⟩
  apply
    (finiteProposalAccepted_nonempty_iff_sourceProposal initial
      (restrictFiniteProposalProgramAt within program) node).mpr
  have liftedExact :=
    (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
      lifted).mp (every lifted)
  simpa only [restrictFiniteProposalProgramAt, lifted] using liftedExact

/-- A first refusal inside a shorter prefix remains the same first refusal
after restriction. -/
theorem firstSourceAcceptanceRefusal_restrict
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {shortFuel longFuel : Nat} (within : shortFuel ≤ longFuel)
    {program : FiniteProposalProgramAt initial longFuel}
    {node : Fin (longFuel + 1)}
    (refusal : FirstSourceAcceptanceRefusalAt initial program node)
    (inside : node.1 < shortFuel + 1) :
    FirstSourceAcceptanceRefusalAt initial
      (restrictFiniteProposalProgramAt within program)
      ⟨node.1, inside⟩ := by
  constructor
  · intro earlier earlierLt
    let lifted : Fin (longFuel + 1) := ⟨earlier.1, by omega⟩
    apply
      (finiteProposalAccepted_nonempty_iff_sourceProposal initial
        (restrictFiniteProposalProgramAt within program) earlier).mpr
    have liftedExact :=
      (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
        lifted).mp
        (refusal.earlierAccepted lifted (by simpa only [lifted] using earlierLt))
    simpa only [restrictFiniteProposalProgramAt, lifted] using liftedExact
  · apply finiteProposalAccepted_isEmpty_of_ne_sourceProposal
    simpa only [restrictFiniteProposalProgramAt] using
      refusal.proposal_ne_source

/-- A first refusal in a shorter prefix remains the first refusal after the
program is extended to a longer finite audit. -/
theorem firstSourceAcceptanceRefusal_extend
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {shortFuel longFuel : Nat} (within : shortFuel ≤ longFuel)
    (program : FiniteProposalProgramAt initial longFuel)
    (node : Fin (shortFuel + 1))
    (refusal : FirstSourceAcceptanceRefusalAt initial
      (restrictFiniteProposalProgramAt within program) node) :
    FirstSourceAcceptanceRefusalAt initial program
      ⟨node.1, by omega⟩ := by
  constructor
  · intro earlier earlierLt
    have earlierNodeLt : earlier.1 < node.1 := by
      simpa only using earlierLt
    let shortEarlier : Fin (shortFuel + 1) :=
      ⟨earlier.1, lt_trans earlierNodeLt node.2⟩
    apply
      (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
        earlier).mpr
    have shortExact :=
      (finiteProposalAccepted_nonempty_iff_sourceProposal initial
        (restrictFiniteProposalProgramAt within program) shortEarlier).mp
        (refusal.earlierAccepted shortEarlier (by
          simpa only [shortEarlier] using earlierNodeLt))
    simpa only [restrictFiniteProposalProgramAt, shortEarlier] using shortExact
  · apply finiteProposalAccepted_isEmpty_of_ne_sourceProposal
    simpa only [restrictFiniteProposalProgramAt] using
      refusal.proposal_ne_source

/-- Once a prefix has refused, compiling any extension returns that same
first refusal node. -/
theorem compileFiniteProposalProgram_prefixRefusal_node
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    {shortFuel longFuel : Nat} (within : shortFuel ≤ longFuel)
    (program : FiniteProposalProgramAt initial longFuel)
    (node : Fin (shortFuel + 1))
    (prefixRefusal : FirstSourceAcceptanceRefusalAt initial
      (restrictFiniteProposalProgramAt within program) node) :
    match compileFiniteProposalProgram initial longFuel program with
    | .inl _ => False
    | .inr compiledRefusal =>
        compiledRefusal.1 = (⟨node.1, by omega⟩ : Fin (longFuel + 1)) := by
  let extendedRefusal :=
    firstSourceAcceptanceRefusal_extend within program node prefixRefusal
  cases resultExact :
      compileFiniteProposalProgram initial longFuel program with
  | inl compiledEvery =>
      exact extendedRefusal.refused.false
        (Classical.choice (compiledEvery.down ⟨node.1, by omega⟩))
  | inr compiledRefusal =>
      exact firstSourceAcceptanceRefusal_unique
        compiledRefusal.2.down extendedRefusal

/-- Zero-fuel classification is exactly acceptance of its sole node. -/
theorem everyFiniteProposalAccepted_zero_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (program : FiniteProposalProgramAt initial 0) :
    EveryFiniteProposalAcceptedAt initial program ↔
      Nonempty
        (FiniteProposalAcceptedAt initial program ⟨0, by omega⟩) := by
  constructor
  · intro every
    exact every ⟨0, by omega⟩
  · intro accepted node
    have nodeExact : node = ⟨0, by omega⟩ := Fin.ext (by omega)
    rw [nodeExact]
    exact accepted

/-- Successor-fuel coherence: a program is accepted through the new horizon
exactly when its prefix is accepted and its new last node is accepted. -/
theorem everyFiniteProposalAccepted_succ_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (fuel : Nat)
    (program : FiniteProposalProgramAt initial (fuel + 1)) :
    EveryFiniteProposalAcceptedAt initial program ↔
      EveryFiniteProposalAcceptedAt initial
          (restrictFiniteProposalProgramAt (Nat.le_succ fuel) program) ∧
        Nonempty
          (FiniteProposalAcceptedAt initial program
            ⟨fuel + 1, by omega⟩) := by
  constructor
  · intro every
    exact ⟨everyFiniteProposalAccepted_restrict (Nat.le_succ fuel) every,
      every ⟨fuel + 1, by omega⟩⟩
  · rintro ⟨prefixAccepted, lastAccepted⟩
    intro node
    by_cases inside : node.1 < fuel + 1
    · let prefixNode : Fin (fuel + 1) := ⟨node.1, inside⟩
      apply
        (finiteProposalAccepted_nonempty_iff_sourceProposal initial program
          node).mpr
      have prefixExact :=
        (finiteProposalAccepted_nonempty_iff_sourceProposal initial
          (restrictFiniteProposalProgramAt (Nat.le_succ fuel) program)
          prefixNode).mp (prefixAccepted prefixNode)
      simpa only [restrictFiniteProposalProgramAt, prefixNode] using prefixExact
    · have nodeBound := node.2
      have nodeValue : node.1 = fuel + 1 := by omega
      have nodeExact : node = ⟨fuel + 1, by omega⟩ := Fin.ext nodeValue
      rw [nodeExact]
      exact lastAccepted

/-- Exact zero-fuel compiler regression. -/
theorem compileFiniteProposalProgram_zero_all_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (program : FiniteProposalProgramAt initial 0) :
    (∃ every : PLift (EveryFiniteProposalAcceptedAt initial program),
        compileFiniteProposalProgram initial 0 program = .inl every) ↔
      Nonempty
        (FiniteProposalAcceptedAt initial program ⟨0, by omega⟩) :=
  (compileFiniteProposalProgram_allBranch_iff initial 0 program).trans
    (everyFiniteProposalAccepted_zero_iff program)

/-- Exact successor-fuel compiler regression. -/
theorem compileFiniteProposalProgram_succ_all_iff
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    {initial : CycleAt oldVisit sourceIndex boundary}
    (fuel : Nat)
    (program : FiniteProposalProgramAt initial (fuel + 1)) :
    (∃ every : PLift (EveryFiniteProposalAcceptedAt initial program),
        compileFiniteProposalProgram initial (fuel + 1) program =
          .inl every) ↔
      EveryFiniteProposalAcceptedAt initial
          (restrictFiniteProposalProgramAt (Nat.le_succ fuel) program) ∧
        Nonempty
          (FiniteProposalAcceptedAt initial program
            ⟨fuel + 1, by omega⟩) :=
  (compileFiniteProposalProgram_allBranch_iff initial (fuel + 1)
    program).trans (everyFiniteProposalAccepted_succ_iff fuel program)

/-- Source-owned proposal program. -/
def canonicalFiniteProposalProgramAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    FiniteProposalProgramAt initial fuel := fun node =>
  pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
    (boundary + node.1)

theorem canonicalFiniteProposalProgram_everyAccepted
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    EveryFiniteProposalAcceptedAt initial
      (canonicalFiniteProposalProgramAt initial fuel) := by
  intro node
  exact
    (finiteProposalAccepted_nonempty_iff_sourceProposal initial
      (canonicalFiniteProposalProgramAt initial fuel) node).mpr rfl

/-- A concrete external program that deviates at exactly one requested node.
It is a counterexample input, not an installed future. -/
def finiteProposalProgramRefusingAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (refusalNode : Fin (fuel + 1))
    (alternative : AnySourceBackedPaymentOccurrence) :
    FiniteProposalProgramAt initial fuel := fun node =>
  if node.1 = refusalNode.1 then alternative
  else pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
    (boundary + node.1)

/-- The one-node deviation is refused first at the requested node while all
strictly earlier canonical proposals remain accepted. -/
theorem finiteProposalProgramRefusingAt_first
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat)
    (refusalNode : Fin (fuel + 1))
    (alternative : AnySourceBackedPaymentOccurrence)
    (different : alternative ≠
      pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
        (boundary + refusalNode.1)) :
    FirstSourceAcceptanceRefusalAt initial
      (finiteProposalProgramRefusingAt initial fuel refusalNode alternative)
      refusalNode := by
  constructor
  · intro earlier earlierLt
    have differentNode : earlier.1 ≠ refusalNode.1 := by omega
    apply
      (finiteProposalAccepted_nonempty_iff_sourceProposal initial
        (finiteProposalProgramRefusingAt initial fuel refusalNode alternative)
        earlier).mpr
    simp only [finiteProposalProgramRefusingAt, differentNode, if_false]
  · apply finiteProposalAccepted_isEmpty_of_ne_sourceProposal
    simpa [finiteProposalProgramRefusingAt] using different

/-- Premise-free negative-control program: at node zero it submits the next
physical node's distinct, source-backed Payment proposal. -/
def adjacentMismatchFiniteProposalProgramAt
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    FiniteProposalProgramAt initial fuel :=
  finiteProposalProgramRefusingAt initial fuel ⟨0, by omega⟩
    (pointwiseRecognizedPaymentProposalAt oldVisit sourceIndex
      (boundary + 1))

theorem adjacentMismatchFiniteProposalProgram_firstRefusal
    {oldVisit : OldVisit} {sourceIndex boundary : Nat}
    (initial : CycleAt oldVisit sourceIndex boundary) (fuel : Nat) :
    FirstSourceAcceptanceRefusalAt initial
      (adjacentMismatchFiniteProposalProgramAt initial fuel)
      ⟨0, by omega⟩ := by
  apply finiteProposalProgramRefusingAt_first
  simpa only [Nat.add_zero, zero_add] using
    (cyclePointwiseProposal_succ_ne initial 0).symm

end
end M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler
end Society
end ProcessGame
end SaturationMonoid

#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.finiteProposalAccepted_nonempty_iff_sourceProposal
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.compileFiniteProposalProgram
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.firstSourceAcceptanceRefusal_unique
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.compileFiniteProposalProgram_prefixRefusal_node
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.compileFiniteProposalProgram_zero_all_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.compileFiniteProposalProgram_succ_all_iff
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.finiteProposalProgramRefusingAt_first
#print axioms SaturationMonoid.ProcessGame.Society.M14SourceGeneratedCanonicalSocietyFiniteProposalAcceptanceCompiler.adjacentMismatchFiniteProposalProgram_firstRefusal
