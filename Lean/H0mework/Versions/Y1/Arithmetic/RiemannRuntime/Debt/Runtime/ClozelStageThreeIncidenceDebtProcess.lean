import H0mework.Versions.Y1.Arithmetic.RiemannRuntime.Debt.Runtime.ClozelStageThreeIncidenceDebtTerminalHandoff

/-!
# Living process for the stage-three incidence debt

The process has two active states (`pending`, `installed`) followed by the
ordinary debt-inactive arithmetic continuation.  Its state presentation is
injective, so the terminal handoff cannot hide a future-selection bit.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
namespace IntegralGraphJointAction.BranchNeutralDebtGate.DebtProcess

open ArithmeticGeneration
open BranchNeutralDebtGate

noncomputable section

variable {observation : GeneratedRiemannZeroObservation}
variable {nontrivial : ¬ ∃ n : Nat,
  observation.coordinate = -2 * (n + 1)}

local notation "W" =>
  StageThreeIncidenceProjectionDebtNetwork observation nontrivial

def inactiveLivingRoot
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLivingRootClosure W
      (InactiveRoot.vocabulary
        (observation := observation) (nontrivial := nontrivial)) where
  source :=
    { base := InactiveRoot.authoritySource receipt
      terminalHandoff :=
        (InactiveRoot.authoritySource receipt).emptyFaithfulTerminalHandoff
          (fun _ => ⟨fun terminal => nomatch terminal⟩) }
  emitted := InactiveRoot.emitted receipt
  compiler_commutes := InactiveRoot.authoritativeRoot receipt |>.compiler_commutes

def inactiveFiniteVisit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    Nat → RootVisit (inactiveLivingRoot receipt).toAuthoritativeRoot.toRoot
  | 0 => (inactiveLivingRoot receipt).toAuthoritativeRoot.toRoot.initialVisit
  | depth + 1 => (inactiveFiniteVisit receipt depth).next rfl

def inactiveTemporalVisit
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (depth : Nat) :
    SourceNativeTemporalVisitAt
      (inactiveLivingRoot receipt).toAuthoritativeRoot.toLedgerRoot :=
  .finite (inactiveFiniteVisit receipt depth)

def temporalDepth?
    (current : SourceNativeLivingRootCurrentAt W) : Option Nat :=
  match current.visit.history with
  | .finite history => some (ProductiveFiniteRootHistoryAt.causalDepth history)
  | .postCofinal _ => none

theorem inactiveTemporalVisit_depth
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial)
    (depth : Nat) :
    temporalDepth?
      ⟨InactiveRoot.vocabulary
          (observation := observation) (nontrivial := nontrivial),
        inactiveLivingRoot receipt, inactiveTemporalVisit receipt depth⟩ =
      some depth := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      change
        some (ProductiveFiniteRootHistoryAt.causalDepth
          (inactiveFiniteVisit receipt depth).history + 1) = some (depth + 1)
      have priorDepth :
          ProductiveFiniteRootHistoryAt.causalDepth
              (inactiveFiniteVisit receipt depth).history = depth := by
        change some (ProductiveFiniteRootHistoryAt.causalDepth
          (inactiveFiniteVisit receipt depth).history) = some depth at inductionHypothesis
        exact Option.some.inj inductionHypothesis
      rw [priorDepth]

def activePendingCurrent
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLivingRootCurrentAt W :=
  ⟨ActiveRoot.vocabulary
      (observation := observation) (nontrivial := nontrivial),
    TerminalHandoff.livingActiveRoot receipt,
    .finite (TerminalHandoff.livingActiveRoot receipt
      |>.toAuthoritativeRoot.toRoot.initialVisit)⟩

def activeInstalledCurrent
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLivingRootCurrentAt W :=
  ⟨ActiveRoot.vocabulary
      (observation := observation) (nontrivial := nontrivial),
    TerminalHandoff.livingActiveRoot receipt,
    .finite (TerminalHandoff.installedVisit receipt)⟩

@[simp] theorem activePendingCurrent_depth
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    temporalDepth? (activePendingCurrent receipt) = some 0 :=
  rfl

@[simp] theorem activeInstalledCurrent_depth
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    temporalDepth? (activeInstalledCurrent receipt) = some 1 :=
  rfl

set_option linter.style.haveILetI false in
theorem activeCurrentType_ne_inactiveCurrentType :
    ActiveRoot.Phase ≠ CanonicalUnitArithmeticRoot.Current := by
  intro type_eq
  let phaseEquivBool : ActiveRoot.Phase ≃ Bool :=
    { toFun := fun phase => match phase with
        | .pending => false
        | .installed => true
      invFun := fun value => if value then .installed else .pending
      left_inv := by intro phase; cases phase <;> rfl
      right_inv := by intro value; cases value <;> rfl }
  letI : Fintype ActiveRoot.Phase :=
    Fintype.ofEquiv Bool phaseEquivBool.symm
  let equivalence : ActiveRoot.Phase ≃ CanonicalUnitArithmeticRoot.Current :=
    Equiv.cast type_eq
  letI : Fintype CanonicalUnitArithmeticRoot.Current :=
    Fintype.ofEquiv ActiveRoot.Phase equivalence
  have three_le : 3 ≤ Fintype.card CanonicalUnitArithmeticRoot.Current := by
    let embed : Fin 3 → CanonicalUnitArithmeticRoot.Current :=
      fun index => UnitHistory.generate index.1
    have injective : Function.Injective embed := by
      intro left right equality
      apply Fin.ext
      have shadow_eq := congrArg UnitHistory.cardinalShadow equality
      simpa [embed] using shadow_eq
    exact Fintype.card_le_of_injective embed injective
  have card_eq :
      Fintype.card CanonicalUnitArithmeticRoot.Current =
        Fintype.card ActiveRoot.Phase :=
    Fintype.card_congr equivalence.symm
  have phase_card : Fintype.card ActiveRoot.Phase = 2 := by decide
  omega

def State := Option (Option Nat)

def stateAt
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    State → SourceNativeLivingRootCurrentAt W
  | none => activePendingCurrent receipt
  | some none => activeInstalledCurrent receipt
  | some (some depth) =>
      ⟨InactiveRoot.vocabulary
          (observation := observation) (nontrivial := nontrivial),
        inactiveLivingRoot receipt, inactiveTemporalVisit receipt depth⟩

theorem stateAt_injective
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    Function.Injective (stateAt receipt) := by
  intro left right equality
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some right =>
          cases right with
          | none =>
              have depth_eq := congrArg temporalDepth? equality
              simp [stateAt] at depth_eq
          | some right =>
              have vocabulary_eq :=
                congrArg SourceNativeLivingRootCurrentAt.V equality
              have current_eq := congrArg Vocabulary.Current vocabulary_eq
              exact False.elim (activeCurrentType_ne_inactiveCurrentType current_eq)
  | some left =>
      cases left with
      | none =>
          cases right with
          | none =>
              have depth_eq := congrArg temporalDepth? equality
              simp [stateAt] at depth_eq
          | some right =>
              cases right with
              | none => rfl
              | some right =>
                  have vocabulary_eq :=
                    congrArg SourceNativeLivingRootCurrentAt.V equality
                  have current_eq := congrArg Vocabulary.Current vocabulary_eq
                  exact False.elim
                    (activeCurrentType_ne_inactiveCurrentType current_eq)
      | some left =>
          cases right with
          | none =>
              have vocabulary_eq :=
                congrArg SourceNativeLivingRootCurrentAt.V equality
              have current_eq := congrArg Vocabulary.Current vocabulary_eq
              exact False.elim
                (activeCurrentType_ne_inactiveCurrentType current_eq.symm)
          | some right =>
              cases right with
              | none =>
                  have vocabulary_eq :=
                    congrArg SourceNativeLivingRootCurrentAt.V equality
                  have current_eq := congrArg Vocabulary.Current vocabulary_eq
                  exact False.elim
                    (activeCurrentType_ne_inactiveCurrentType current_eq.symm)
              | some right =>
                  have depth_eq := congrArg temporalDepth? equality
                  change temporalDepth?
                      ⟨InactiveRoot.vocabulary,
                        inactiveLivingRoot receipt,
                        inactiveTemporalVisit receipt left⟩ =
                    temporalDepth?
                      ⟨InactiveRoot.vocabulary,
                        inactiveLivingRoot receipt,
                        inactiveTemporalVisit receipt right⟩ at depth_eq
                  rw [inactiveTemporalVisit_depth receipt left,
                    inactiveTemporalVisit_depth receipt right] at depth_eq
                  cases Option.some.inj depth_eq
                  rfl

def successor : State → State
  | none => some none
  | some none => some (some 0)
  | some (some depth) => some (some (depth + 1))

def process
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    SourceNativeLivingRootProcess W where
  State := State
  stateAt := stateAt receipt
  stateAt_injective := stateAt_injective receipt
  initial := none
  successorAt := by
    intro state
    refine ⟨successor state, ?_⟩
    cases state with
    | none => exact ⟨rfl, HEq.rfl⟩
    | some state =>
        cases state with
        | none => exact ⟨rfl, trivial⟩
        | some depth => exact ⟨rfl, HEq.rfl⟩

theorem pending_successor_is_installed
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    (process receipt).stateAt ((process receipt).successor none) =
      activeInstalledCurrent receipt :=
  rfl

theorem installed_successor_is_exact_inactive_handoff
    (receipt : StageThreeIncidencePaymentReceiptAt observation nontrivial) :
    ((process receipt).stateAt ((process receipt).successor (some none))).erase =
      (TerminalHandoff.livingActiveRoot receipt).generatedNextCurrentAt
        (.finite (TerminalHandoff.installedVisit receipt)) :=
  rfl

end
end IntegralGraphJointAction.BranchNeutralDebtGate.DebtProcess
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.BranchNeutralDebtGate.DebtProcess.installed_successor_is_exact_inactive_handoff
