import H0mework.Foundation.Authority.Representation

/-!
# Total disposition of a registered causal entry

An exact causal entry may not disappear merely because the next finite patch
does not select it.  At every generated root visit the complete source ledger
therefore exposes one of two outcomes:

* a whole-ledger successor, which carries the existing causal authority to
  the compiler-generated target visit; or
* the root's exact terminal discharge for that entry.

Sparse patches remain local processing readouts.  Their `none` branch cannot
revoke an entry already admitted into the complete live ledger.  The kernel
is constructive and adds no fairness, total-row, terminal, or target premise.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot

universe u

/-- Zero-information witness that the fixed root evolution is nonterminal at
this visit. -/
def CausalEntryNonterminalAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root) : Type u :=
  match (root.toRoot.evolutionAt visit.current).nextCurrent? with
  | some _ => PUnit
  | none => PEmpty

namespace CausalEntryNonterminalAt

/-- The successor current selected by the fixed root evolution. -/
def next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (branch : CausalEntryNonterminalAt root visit) : V.Current := by
  match next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? with
  | some next => exact next
  | none =>
      unfold CausalEntryNonterminalAt at branch
      rw [next_eq] at branch
      exact PEmpty.elim branch

/-- The branch token contains no target payload; this equation is recovered
from the fixed root evolution. -/
theorem next_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    (branch : CausalEntryNonterminalAt root visit) :
    (root.toRoot.evolutionAt visit.current).nextCurrent? = some branch.next := by
  unfold next
  split
  · assumption
  · rename_i root_eq
    unfold CausalEntryNonterminalAt at branch
    rw [root_eq] at branch
    exact PEmpty.elim branch

end CausalEntryNonterminalAt

/-- Entry-indexed spelling of the exact nonterminal root branch.  The same
whole-ledger branch transports every live entry, so no second successor
constructor is issued per row. -/
abbrev CausalEntrySuccessorAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root)
    (_entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) : Type u :=
  CausalEntryNonterminalAt root visit

namespace CausalEntrySuccessorAt

/-- Successor current read from the fixed root evolution. -/
def next
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (successor : CausalEntrySuccessorAt root visit entry) : V.Current :=
  CausalEntryNonterminalAt.next successor

/-- The continuing token stores no target equation. -/
theorem next_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (successor : CausalEntrySuccessorAt root visit entry) :
    (root.toRoot.evolutionAt visit.current).nextCurrent? = some successor.next :=
  CausalEntryNonterminalAt.next_eq successor

/-- Canonical constructor from the root's own nonterminal branch equation. -/
def ofNonterminal
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {next : V.Current}
    (next_eq : (root.toRoot.evolutionAt visit.current).nextCurrent? = some next) :
    CausalEntrySuccessorAt root visit entry := by
  unfold CausalEntrySuccessorAt
  unfold CausalEntryNonterminalAt
  rw [next_eq]
  exact PUnit.unit

/-- The exact target visit belongs to the existing root history. -/
def targetVisit
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (successor : CausalEntrySuccessorAt root visit entry) :
    SourceNativeTemporalVisitAt root :=
  visit.next successor.next_eq

/-- The target entry is computed by the same whole-ledger fold. -/
def targetEntry
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (successor : CausalEntrySuccessorAt root visit entry) :
    OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted successor.next)) :=
  root.canonicalTargetEntryAtNext successor.next_eq entry

/-- The same whole-ledger fold that computes `targetEntry` also owns the
dependent row relating the source entry to that target.  Exposing the pair
prevents downstream lifecycle adapters from reconstructing a receipt from a
coarser target or branch label. -/
def entryDestination
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (successor : CausalEntrySuccessorAt root visit entry) :
    Sigma fun targetEntry : OpenResponsibilityAt N
        (root.source.source.toRootSource.account.supportOf
          (root.emitted successor.next)) =>
      LedgerEntryEvolutionAt N entry targetEntry := by
  have next_eq := successor.next_eq
  cases generated_eq : root.generatedLedgerAt visit.current with
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.nativeTarget write = successor.next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted visit.current)).nextCurrent? = some successor.next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.nativeTarget write) := by
        have commutes := root.compiler_commutes visit.current
        rw [show root.source.ledgerCompiler.compile
          (root.emitted visit.current) =
            .nativeWrite write structural_eq targetOccurrence ledgerEvolution
          from generated_eq] at commutes
        exact commutes
      rw [← target_eq, ← occurrence_eq]
      exact ledgerEvolution.destination entry
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.relationTarget write = successor.next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted visit.current)).nextCurrent? = some successor.next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.relationTarget write) := by
        have commutes := root.compiler_commutes visit.current
        rw [show root.source.ledgerCompiler.compile
          (root.emitted visit.current) =
            .relationWrite write structural_eq targetOccurrence ledgerEvolution
          from generated_eq] at commutes
        exact commutes
      rw [← target_eq, ← occurrence_eq]
      exact ledgerEvolution.destination entry
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.continuedTarget write = successor.next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted visit.current)).nextCurrent? = some successor.next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.continuedTarget write) := by
        have commutes := root.compiler_commutes visit.current
        rw [show root.source.ledgerCompiler.compile
          (root.emitted visit.current) =
            .continuedTransport write structural_eq targetOccurrence
              ledgerEvolution
          from generated_eq] at commutes
        exact commutes
      rw [← target_eq, ← occurrence_eq]
      exact ledgerEvolution.destination entry
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      have target_eq : V.redirectTarget write = successor.next := by
        change
          (root.source.source.toRootSource.actual.compile
            (root.emitted visit.current)).nextCurrent? = some successor.next at next_eq
        rw [structural_eq] at next_eq
        exact Option.some.inj next_eq
      have occurrence_eq :
          targetOccurrence = root.emitted (V.redirectTarget write) := by
        have commutes := root.compiler_commutes visit.current
        rw [show root.source.ledgerCompiler.compile
          (root.emitted visit.current) =
            .borromeanRedirect write structural_eq targetOccurrence
              ledgerEvolution
          from generated_eq] at commutes
        exact commutes
      rw [← target_eq, ← occurrence_eq]
      exact ledgerEvolution.destination entry
  | faithfulTerminal terminal structural_eq ledgerEvolution =>
      change
        (root.source.source.toRootSource.actual.compile
          (root.emitted visit.current)).nextCurrent? = some successor.next at next_eq
      rw [structural_eq] at next_eq
      contradiction

/-- A successor carries the prior causal ledger history; target-side visibility
cannot create a fresh admission or upgrade this readout into authority. -/
def targetReadout
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (successor : CausalEntrySuccessorAt root visit entry)
    (sourceReadout : SourceNativeTemporalCausalEntryLedgerReadoutAt root visit entry) :
    SourceNativeTemporalCausalEntryLedgerReadoutAt root successor.targetVisit
      successor.targetEntry :=
  sourceReadout.next successor.next_eq

end CausalEntrySuccessorAt

/-- Zero-information witness that the fixed root ledger compiler selected its
faithful-terminal branch at this visit.  A world-level terminal receipt alone
cannot inhabit this type. -/
private def CausalEntryTerminalDispositionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root)
    (_entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) : Type u :=
  match root.generatedLedgerAt visit.current with
  | .faithfulTerminal .. => PUnit
  | .nativeWrite ..
  | .relationWrite ..
  | .continuedTransport ..
  | .borromeanRedirect .. => PEmpty

namespace CausalEntryTerminalDispositionAt

/-- A terminal compiler branch and a continuing branch cannot classify the
same exact temporal visit. -/
private def noNonterminal
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (terminal : CausalEntryTerminalDispositionAt root visit entry)
    (branch : CausalEntryNonterminalAt root visit) : PEmpty := by
  cases generated_eq : root.generatedLedgerAt visit.current with
  | nativeWrite =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact terminal
  | relationWrite =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact terminal
  | continuedTransport =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact terminal
  | borromeanRedirect =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact terminal
  | faithfulTerminal payload structural_eq ledgerEvolution =>
      unfold CausalEntryNonterminalAt at branch
      rw [show root.toRoot.evolutionAt visit.current = .faithfulTerminal payload
        from structural_eq] at branch
      exact branch

/-- The exact discharge receipt is read from the fixed terminal compiler
branch; it is not a constructor argument of the public disposition. -/
private def receipt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLedgerRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root}
    {entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    (terminal : CausalEntryTerminalDispositionAt root visit entry) :
    LedgerEntryTerminalAt N entry := by
  cases generated_eq : root.generatedLedgerAt visit.current with
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact PEmpty.elim terminal
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact PEmpty.elim terminal
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact PEmpty.elim terminal
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      unfold CausalEntryTerminalDispositionAt at terminal
      rw [generated_eq] at terminal
      exact PEmpty.elim terminal
  | faithfulTerminal payload structural_eq ledgerEvolution =>
      exact ledgerEvolution.discharge entry

end CausalEntryTerminalDispositionAt

/-- Exhaustive syntax at one exact causal entry.  Every constructor requires
branch evidence indexed by the fixed root compiler; no world receipt by itself
can select a disposition. -/
private inductive CausalEntryDispositionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root)
    (entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) : Type u
  | successor (step : CausalEntrySuccessorAt root visit entry)
  | terminal (terminal : CausalEntryTerminalDispositionAt root visit entry)

/-- Authority-independent raw classifier.  Every continuing branch transports
the entry through the complete source-native ledger; terminal reads its exact
discharge from that same root occurrence.  Sparse patch membership cannot
become an outcome selector. -/
private def SourceNativeLedgerRootClosure.causalEntryDispositionAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root)
    (entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))) :
    CausalEntryDispositionAt root visit entry := by
  cases generated_eq : root.generatedLedgerAt visit.current with
  | nativeWrite write structural_eq targetOccurrence ledgerEvolution =>
      have next_eq :
          (root.toRoot.evolutionAt visit.current).nextCurrent? =
            some (V.nativeTarget write) := by
        rw [show root.toRoot.evolutionAt visit.current = .nativeWrite write from
          structural_eq]
        rfl
      exact .successor (CausalEntrySuccessorAt.ofNonterminal next_eq)
  | relationWrite write structural_eq targetOccurrence ledgerEvolution =>
      have next_eq :
          (root.toRoot.evolutionAt visit.current).nextCurrent? =
            some (V.relationTarget write) := by
        rw [show root.toRoot.evolutionAt visit.current = .relationWrite write from
          structural_eq]
        rfl
      exact .successor (CausalEntrySuccessorAt.ofNonterminal next_eq)
  | continuedTransport write structural_eq targetOccurrence ledgerEvolution =>
      have next_eq :
          (root.toRoot.evolutionAt visit.current).nextCurrent? =
            some (V.continuedTarget write) := by
        rw [show root.toRoot.evolutionAt visit.current =
          .continuedTransport write from structural_eq]
        rfl
      exact .successor (CausalEntrySuccessorAt.ofNonterminal next_eq)
  | borromeanRedirect write structural_eq targetOccurrence ledgerEvolution =>
      have next_eq :
          (root.toRoot.evolutionAt visit.current).nextCurrent? =
            some (V.redirectTarget write) := by
        rw [show root.toRoot.evolutionAt visit.current =
          .borromeanRedirect write from structural_eq]
        rfl
      exact .successor (CausalEntrySuccessorAt.ofNonterminal next_eq)
  | faithfulTerminal terminal structural_eq ledgerEvolution =>
      refine CausalEntryDispositionAt.terminal ?_
      unfold CausalEntryTerminalDispositionAt
      rw [generated_eq]
      exact PUnit.unit

/-! ## Authority-facing answer-and-next

The internal root classifier directly exposes its dependent answer payload.
Every continuing root carries the admitted authority through the complete
ledger; sparse-patch omission creates neither a parallel demand grammar nor a
second answer token. -/

/-- Dependent payload selected by the canonical root disposition. -/
private def SourceNativeCausalEntryAnswerPayloadAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLedgerRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root)
    (entry : OpenResponsibilityAt N
      (root.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (_authority : SourceNativeTemporalCausalEntryLedgerReadoutAt root visit entry) :
    Type (u + 1) :=
  match root.causalEntryDispositionAt visit entry with
  | .successor successor =>
      SourceNativeTemporalCausalEntryLedgerReadoutAt root successor.targetVisit
        successor.targetEntry
  | .terminal _terminal => ULift.{u + 1, u} (LedgerEntryTerminalAt N entry)

/-- One root entry has one public answer-and-next shape.  The entry answer is
read directly from the private classifier; the world successor is the living
root compiler's canonical next current. -/
structure SourceNativeLivingCausalEntryAnswerAndNextAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry) : Type (u + 3) where
  private mk ::

/-- Public dependent answer vocabulary.  Its index includes the complete
admitted living root; the raw ledger classifier remains internal. -/
def SourceNativeLivingCausalEntryAnswerPayloadAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry) : Type (u + 1) :=
  SourceNativeCausalEntryAnswerPayloadAt
    root.toAuthoritativeRoot.toLedgerRoot visit entry authority.toLedgerReadout

namespace SourceNativeLivingCausalEntryAnswerAndNextAt

/-- Living answer-and-next likewise has no presentation bit. -/
theorem eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry}
    (left right : SourceNativeLivingCausalEntryAnswerAndNextAt
      root visit entry authority) : left = right := by
  cases left
  cases right
  rfl

/-- The entry answer is the fixed root classifier's dependent payload.  No
ledger-only answer token is constructed between living authority and result. -/
def answer
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry}
    (_generated : SourceNativeLivingCausalEntryAnswerAndNextAt
      root visit entry authority) :
    SourceNativeLivingCausalEntryAnswerPayloadAt
      root visit entry authority := by
  unfold SourceNativeLivingCausalEntryAnswerPayloadAt
  unfold SourceNativeCausalEntryAnswerPayloadAt
  cases disposition_eq : root.toAuthoritativeRoot.toLedgerRoot
      |>.causalEntryDispositionAt visit entry with
  | successor successor =>
      exact successor.targetReadout authority.toLedgerReadout
  | terminal terminal =>
      exact ULift.up terminal.receipt

/-- The next current is a readout, not a field of the entry answer. -/
def nextCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry}
    (_generated : SourceNativeLivingCausalEntryAnswerAndNextAt
      root visit entry authority) : SourceNativeAuthoritativeRootCurrentAt N :=
  root.generatedNextCurrentAt visit

theorem nextCurrent_eq
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current))}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry}
    (generated : SourceNativeLivingCausalEntryAnswerAndNextAt
      root visit entry authority) :
    generated.nextCurrent = root.generatedNextCurrentAt visit := rfl

end SourceNativeLivingCausalEntryAnswerAndNextAt

/-- Canonical living answer-and-next for an already-authoritative entry. -/
def SourceNativeLivingRootClosure.generatedCausalEntryAnswerAndNextAt
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
    (entry : OpenResponsibilityAt N
      (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
        (root.emitted visit.current)))
    (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
      root visit entry) :
    SourceNativeLivingCausalEntryAnswerAndNextAt root visit entry authority :=
  ⟨⟩

end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
