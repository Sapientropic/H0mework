import H0mework.Foundation.Responsibility.DebtLedgerReadback
import H0mework.Versions.R2.Arithmetic.FockState.FactorDecay

/-!
# Finite structural-channel observer debt

The complete repair/emission structural-key type embeds injectively in a
finite coordinate code, so its remaining observer inventory carries an exact
cardinal budget.  A step consumes one present key, retains the channel receipt
and Fock-kernel trace, strictly decreases that observer budget, and evolves
the whole activated ledger while preserving the canonical base row.  It does
not classify occurrence-sensitive recurrence.

An empty inventory settles only the added sector debt.  The canonical base
has no support-settlement receipt, so debt exhaustion cannot mint a terminal.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockSectorDebt

open CanonicalUnitArithmeticOperationalFactorDecayProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticFullFactorRepairProducer
open DebtActivationWorld DebtActivationLedger
open ParticleWaveFock

noncomputable section

abbrev ChannelCode (index : Nat) :=
  EffectiveSplitAt index × Bool × Fin (repairTargetValue index + 1) × Bool

def alternativeSide {index : Nat} {source : EffectiveSplitAt index} :
    FactorRepairAlternativeAt source → Bool
  | .left _ _ => false
  | .right _ _ => true

def alternativeFactorCode {index : Nat} {source : EffectiveSplitAt index}
    (alternative : FactorRepairAlternativeAt source) :
    Fin (repairTargetValue index + 1) :=
  ⟨alternative.factor, by
    cases alternative with
    | left leftNotPrime factor =>
        have factorLt : factor.1 < splitLeft source :=
          FactorRepairAlternativeAt.factorProper
            (.left leftNotPrime factor)
        have endpointLe := splitLeft_le_target source
        exact factorLt.trans_le (Nat.le_succ_of_le endpointLe)
    | right rightNotPrime factor =>
        have factorLt : factor.1 < splitRight source :=
          FactorRepairAlternativeAt.factorProper
            (.right rightNotPrime factor)
        have landing := split_landing source
        have endpointLe : splitRight source ≤ repairTargetValue index := by
          omega
        exact factorLt.trans_le (Nat.le_succ_of_le endpointLe)⟩

def encodeStructuralKey {index : Nat} :
    FactorDecayStructuralChannelKeyAt index → ChannelCode index
  | ⟨source, .repair alternative⟩ =>
      (source, alternativeSide alternative,
        alternativeFactorCode alternative, false)
  | ⟨source, .emission alternative⟩ =>
      (source, alternativeSide alternative,
        alternativeFactorCode alternative, true)

theorem encodeStructuralKey_injective {index : Nat} :
    Function.Injective (encodeStructuralKey (index := index)) := by
  rintro ⟨source, channel⟩ ⟨target, targetChannel⟩ equality
  cases channel <;> cases targetChannel <;>
    rename_i left right <;>
    cases left <;> cases right <;>
    simp_all [encodeStructuralKey, alternativeSide, alternativeFactorCode]
  all_goals
    rcases equality with ⟨source_eq, factor_eq⟩
    subst target
    have factor_subtype_eq := Subtype.ext factor_eq
    cases factor_subtype_eq
    rfl

noncomputable instance factorDecayStructuralKeyFinite (index : Nat) :
    Finite (FactorDecayStructuralChannelKeyAt index) :=
  Finite.of_injective (encodeStructuralKey (index := index))
    encodeStructuralKey_injective

noncomputable instance factorDecayStructuralKeyFintype (index : Nat) :
    Fintype (FactorDecayStructuralChannelKeyAt index) := Fintype.ofFinite _

noncomputable local instance factorDecayStructuralKeyDecidableEq (index : Nat) :
    DecidableEq (FactorDecayStructuralChannelKeyAt index) := Classical.decEq _

abbrev State (index : Nat) := Finset (FactorDecayStructuralChannelKeyAt index)

def initialState (index : Nat) : State index := Finset.univ

theorem initialState_complete {index : Nat}
    (key : FactorDecayStructuralChannelKeyAt index) :
    key ∈ initialState index :=
  Finset.mem_univ key

def budget {index : Nat} (state : State index) : Nat := state.card

def target {index : Nat} (source : State index)
    (key : FactorDecayStructuralChannelKeyAt index) : State index :=
  source.erase key

@[simp] theorem consumed_not_mem_target {index : Nat}
    (source : State index) (key : FactorDecayStructuralChannelKeyAt index) :
    key ∉ target source key := by
  simp [target]

structure StepAt {index : Nat} (source targetState : State index) : Type where
  private mk ::
  structuralKey : FactorDecayStructuralChannelKeyAt index
  present : structuralKey ∈ source
  target_eq : targetState = target source structuralKey
  receipt : OperationalFactorDecayChannelReceiptAt structuralKey.2
  receipt_eq : receipt = generateChannelReceipt structuralKey.2
  fockTrace : GeneratedFactorDecayFockTraceAt structuralKey.2 receipt
  fockTrace_eq : fockTrace = generateFactorDecayFockTrace structuralKey.2 receipt

def generateStep {index : Nat} (source : State index)
    (structuralKey : FactorDecayStructuralChannelKeyAt index)
    (present : structuralKey ∈ source) :
    StepAt source (target source structuralKey) :=
  { structuralKey := structuralKey
    present := present
    target_eq := rfl
    receipt := generateChannelReceipt structuralKey.2
    receipt_eq := rfl
    fockTrace := generateFactorDecayFockTrace structuralKey.2
      (generateChannelReceipt structuralKey.2)
    fockTrace_eq := rfl }

theorem step_budget_lt {index : Nat} {source targetState : State index}
    (step : StepAt source targetState) :
    budget targetState < budget source := by
  rw [step.target_eq]
  exact Finset.card_erase_lt_of_mem step.present

inductive DebtId
  | sector

inductive DebtClaim
  | accountStructuralChannelObserver

def activationLaw (index : Nat) : DebtActivationLaw where
  DebtState := State index
  DebtId := DebtId
  DebtClaim := DebtClaim
  debtId := .sector
  debtClaim := .accountStructuralChannelObserver
  budget := budget
  StepAt := StepAt
  step_budget_lt := step_budget_lt
  SettlementAt := fun state => PLift (state = ∅)
  settlement_budget_zero := by
    intro state settlement
    exact Finset.card_eq_zero.mpr settlement.down
  ObstructionAt := fun _ => PEmpty

def ledgerStep {index : Nat} (support : CanonicalUnitArithmeticRoot.Current)
    {source targetState : State index}
    (step : StepAt source targetState) :=
  stepLedgerEvolution (N := CanonicalUnitArithmeticRoot.N)
    (law := activationLaw index) support step

abbrev ActivatedN (index : Nat) :=
  ExtendedNetwork CanonicalUnitArithmeticRoot.N (activationLaw index)

def activeLedgerAt (index : Nat)
    (support : CanonicalUnitArithmeticRoot.Current) (state : State index) :=
  activeLedger (N := CanonicalUnitArithmeticRoot.N)
    (law := activationLaw index) support state

def emptySettlement (index : Nat) :
    (activationLaw index).SettlementAt (∅ : State index) :=
  ⟨rfl⟩

theorem generatedStep_trace_mem_kernel {index : Nat}
    (source : State index) (key : FactorDecayStructuralChannelKeyAt index)
    (present : key ∈ source) :
    (((generateStep source key present).fockTrace.trace :
      JointMeasurementKernel) : ParentCarrier) ∈ JointMeasurementKernel :=
  (generateStep source key present).fockTrace.trace.2

theorem generatedStep_debt_budget_strict {index : Nat}
    (support : CanonicalUnitArithmeticRoot.Current)
    (source : State index) (key : FactorDecayStructuralChannelKeyAt index)
    (present : key ∈ source) :
    (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := activationLaw index) support (target source key)
      ).progressBudget <
      (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := activationLaw index) support source).progressBudget :=
  DebtActivationWorld.debtStep_budget_lt
    (N := CanonicalUnitArithmeticRoot.N) (law := activationLaw index)
    support (generateStep source key present)

theorem generatedStep_transfers_canonical_root_row {index : Nat}
    (support : CanonicalUnitArithmeticRoot.Current)
    (source : State index) (key : FactorDecayStructuralChannelKeyAt index)
    (present : key ∈ source) :
    ((ledgerStep support (generateStep source key present)).destination
      (oldEntry (law := activationLaw index) (state? := some source)
        (CanonicalUnitArithmeticRoot.rootLedgerEntry support))).1 =
      oldEntry (law := activationLaw index)
        (state? := some (target source key))
        (CanonicalUnitArithmeticRoot.rootLedgerEntry support) :=
  stepLedgerEvolution_destination_old
    (N := CanonicalUnitArithmeticRoot.N) (law := activationLaw index)
    support (generateStep source key present)
    (CanonicalUnitArithmeticRoot.rootLedgerEntry support)

/-- Debt exhaustion alone cannot manufacture the canonical base terminal,
whose support-settlement disposition is empty. -/
theorem emptyDebt_cannot_terminal_canonicalBase (index : Nat)
    (support : CanonicalUnitArithmeticRoot.Current) :
    IsEmpty
      (LedgerTerminalEvolutionAt (ActivatedN index)
        (activeLedgerAt index support ∅)) := by
  constructor
  intro terminal
  have discharged := terminal.discharge
    (oldEntry (law := activationLaw index)
      (state? := some (∅ : State index))
      (CanonicalUnitArithmeticRoot.rootLedgerEntry support))
  have receipt := discharged.receipt
  change CanonicalUnitArithmeticRoot.N.DispositionAt
    support .supportSettlement at receipt
  exact nomatch receipt

end

end ParticleWaveFockSectorDebt
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
