import H0mework.Versions.R2.Arithmetic.FockUnitAction.Inventory.LivingLawCanonicalParticleWaveFockFullInventoryAction
import H0mework.Versions.R2.Arithmetic.FockUnitAction.Scan
import H0mework.Versions.R2.Arithmetic.FockUnitAction.ActionHistory

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace GoldbachUnitSelectedActor

open ArithmeticGeneration
open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open CanonicalUnitArithmeticExactOccurrenceAdditiveProducer
open ParticleWaveFockAtomicProcess
open ParticleWaveFockFullInventoryAction
open ParticleWaveFockUnitChargeAction
open ParticleWaveFockUnitChargeScan
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

/-- A selected unit event retains the entire old factor inventory and the
literal source-generated unit receipt.  The existing classifier has already
reported a nonterminal state before this event is constructed. -/
structure SelectedUnitEventAt {index : Nat} (source : EffectiveSplitAt index) : Type where
  private mk ::
  room : 3 ≤ splitRight source
  factorInventory : Finset (FactorDecayChannelAt source)
  factorInventory_eq : factorInventory = completeApplicableInventory source
  classifiedFactor : FactorDecayChannelAt source
  classifier_eq : (fullFactorDecayLaw index).classify source = .inr classifiedFactor
  inventoryNone : completeInventoryTerminalAction source = none
  unit : UnitChargeActionAt source
  unit_eq : unit = generateUnitChargeAction source room

def generateSelectedUnitEvent {index : Nat} (source : EffectiveSplitAt index)
    (room : 3 ≤ splitRight source)
    (classifiedFactor : FactorDecayChannelAt source)
    (classifier_eq : (fullFactorDecayLaw index).classify source = .inr classifiedFactor)
    (inventoryNone : completeInventoryTerminalAction source = none) :
    SelectedUnitEventAt source :=
  { room := room
    factorInventory := completeApplicableInventory source
    factorInventory_eq := rfl
    classifiedFactor := classifiedFactor
    classifier_eq := classifier_eq
    inventoryNone := inventoryNone
    unit := generateUnitChargeAction source room
    unit_eq := rfl }

/-- A positive history keeps the first actual terminal read, or the original
factor-channel edge and its generated operational/Fock receipt. -/
inductive ReachedAt {index : Nat} : EffectiveSplitAt index → Type
  | current {source} (terminal : PrimePairTerminalAt source)
      (classifier_eq : (fullFactorDecayLaw index).classify source = .inl terminal) :
      ReachedAt source
  | factor {source} (selected : InventoryTerminalActionAt source)
      (inventory_eq : completeInventoryTerminalAction source = some selected)
      (sourcePath : GeneratedPathAt (fullFactorDecayLaw index) source selected.1.target)
      (factorReceipt : ParticleWaveFockPrimePairActualityActionHistory.GeneratedFactorActionAt selected.1)
      (factorReceipt_eq : factorReceipt =
        ParticleWaveFockPrimePairActualityActionHistory.generateFactorAction selected.1) :
      ReachedAt source
  | advance {source} (event : SelectedUnitEventAt source)
      (tail : ReachedAt event.unit.target) : ReachedAt source

/-- Exhaustion retains *every* classified nonterminal state and every actual
unit action on the entire source-computed suffix. -/
inductive ExhaustedAt {index : Nat} : EffectiveSplitAt index → Type
  | final {source} (right_eq_two : splitRight source = 2)
      (classifiedFactor : FactorDecayChannelAt source)
      (classifier_eq : (fullFactorDecayLaw index).classify source = .inr classifiedFactor)
      (inventoryNone : completeInventoryTerminalAction source = none) : ExhaustedAt source
  | advance {source} (event : SelectedUnitEventAt source)
      (tail : ExhaustedAt event.unit.target) : ExhaustedAt source

abbrev OutcomeAt {index : Nat} (source : EffectiveSplitAt index) :=
  ReachedAt source ⊕ ExhaustedAt source

namespace ExhaustedAt

def steps {index : Nat} {source : EffectiveSplitAt index} : ExhaustedAt source → Nat
  | .final .. => 0
  | .advance _ tail => tail.steps + 1

theorem steps_pay_full_suffix {index : Nat} {source : EffectiveSplitAt index}
    (history : ExhaustedAt source) : history.steps + 2 = splitRight source := by
  induction history with
  | final right_eq_two _ _ _ =>
      simp only [steps, zero_add]
      exact right_eq_two.symm
  | advance event tail inductionHypothesis =>
      have rightWrite := event.unit.rightWriteEquation
      simp only [steps]
      omega

def VisitedAt {index : Nat} {source : EffectiveSplitAt index} :
    (history : ExhaustedAt source) → EffectiveSplitAt index → Prop
  | .final .., state => state = source
  | .advance _ tail, state => state = source ∨ VisitedAt tail state

theorem visited_no_terminal {index : Nat} {source state : EffectiveSplitAt index}
    (history : ExhaustedAt source) (visited : VisitedAt history state) :
    ¬ Nonempty (PrimePairTerminalAt state) := by
  induction history with
  | final _ factor classifier_eq inventoryNone =>
      change state = _ at visited
      subst state
      intro ⟨terminal⟩
      obtain ⟨generated, positive⟩ :=
        fullFactorDecayClassify_isTerminal_of_terminal terminal
      rw [classifier_eq] at positive
      contradiction
  | advance event tail inductionHypothesis =>
      change state = _ ∨ VisitedAt tail state at visited
      rcases visited with here | later
      · subst state
        intro ⟨terminal⟩
        obtain ⟨generated, positive⟩ :=
          fullFactorDecayClassify_isTerminal_of_terminal terminal
        rw [event.classifier_eq] at positive
        contradiction
      · exact inductionHypothesis later

theorem visits_complete_forward_suffix {index : Nat}
    {source : EffectiveSplitAt index}
    (history : ExhaustedAt source) :
    ∀ target : EffectiveSplitAt index,
      splitLeft source ≤ splitLeft target → VisitedAt history target := by
  induction history with
  | @final current right_eq_two _ _ _ =>
      intro target left_bound
      have targetFloor := splitRight_atLeastTwo target
      have sourceLanding := split_landing current
      have targetLanding := split_landing target
      have left_eq : splitLeft target = splitLeft current := by omega
      have state_eq : target = current := by
        apply Subtype.ext
        apply Fin.ext
        exact left_eq
      change target = current
      exact state_eq
  | @advance current event tail inductionHypothesis =>
      intro target left_bound
      by_cases left_eq : splitLeft target = splitLeft current
      · have state_eq : target = current := by
          apply Subtype.ext
          apply Fin.ext
          exact left_eq
        change target = current ∨ VisitedAt tail target
        exact .inl state_eq
      · have next_left : splitLeft event.unit.target = splitLeft current + 1 := by
          rw [event.unit.target_eq, unitChargeTarget_left]
        change target = current ∨ VisitedAt tail target
        right
        apply inductionHypothesis
        omega

theorem canonical_exhausted_no_terminal
    (index : Nat) (indexInRange : 1 ≤ index)
    (history : ExhaustedAt (canonicalSplit index indexInRange))
    (target : EffectiveSplitAt index) :
    ¬ Nonempty (PrimePairTerminalAt target) := by
  apply visited_no_terminal history
  apply visits_complete_forward_suffix history
  rw [canonicalSplit_left]
  exact splitLeft_atLeastTwo target

end ExhaustedAt

private def runWithSourceFuel {index : Nat} :
    (fuel : Nat) → (source : EffectiveSplitAt index) →
      fuel + 2 = splitRight source → OutcomeAt source
  | 0, source, right_eq_two => by
      generalize classifier_eq : (fullFactorDecayLaw index).classify source = outcome
      cases outcome with
      | inl terminal => exact .inl (.current terminal classifier_eq)
      | inr factor =>
          generalize inventory_eq : completeInventoryTerminalAction source = inventory
          cases inventory with
          | some selected =>
              exact .inl (.factor selected inventory_eq
                ((GeneratedPathAt.nil : GeneratedPathAt
                  (fullFactorDecayLaw index) source source).snoc selected.1)
                (ParticleWaveFockPrimePairActualityActionHistory.generateFactorAction selected.1)
                rfl)
          | none =>
              exact .inr (.final
                (by simpa only [zero_add] using right_eq_two.symm)
                factor classifier_eq inventory_eq)
  | fuel + 1, source, fuel_eq => by
      generalize classifier_eq : (fullFactorDecayLaw index).classify source = outcome
      cases outcome with
      | inl terminal => exact .inl (.current terminal classifier_eq)
      | inr factor =>
          generalize inventory_eq : completeInventoryTerminalAction source = inventory
          cases inventory with
          | some selected =>
              exact .inl (.factor selected inventory_eq
                ((GeneratedPathAt.nil : GeneratedPathAt
                  (fullFactorDecayLaw index) source source).snoc selected.1)
                (ParticleWaveFockPrimePairActualityActionHistory.generateFactorAction selected.1)
                rfl)
          | none =>
              have room : 3 ≤ splitRight source := by omega
              let event := generateSelectedUnitEvent source room factor classifier_eq inventory_eq
              have next_fuel : fuel + 2 = splitRight event.unit.target := by
                rw [event.unit_eq, (generateUnitChargeAction source room).target_eq,
                  unitChargeTarget_right]
                omega
              cases tail : runWithSourceFuel fuel event.unit.target next_fuel with
              | inl reached => exact .inl (.advance event reached)
              | inr exhausted => exact .inr (.advance event exhausted)

/-- The public actor derives its full fuel from the fixed source split. -/
def generate {index : Nat} (source : EffectiveSplitAt index) : OutcomeAt source :=
  runWithSourceFuel (splitRight source - 2) source (by
    have floor := splitRight_atLeastTwo source
    omega)
end
end GoldbachUnitSelectedActor
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
