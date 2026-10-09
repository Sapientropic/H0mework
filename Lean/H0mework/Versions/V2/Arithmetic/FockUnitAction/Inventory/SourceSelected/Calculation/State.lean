import H0mework.Versions.V2.Arithmetic.FockUnitAction.Inventory.SourceSelected.Actor

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation

open CanonicalUnitArithmeticEffectiveAdditiveProducer
open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticExactOccurrenceOperationalFactorDecayProducer
open ParticleWaveFockFullInventoryAction
open ParticleWaveFockUnitChargeAction
open SourceGeneratedFiniteEffectiveBranchingReachability

noncomputable section

/-- Every intermediate cursor retains its ordered, source-generated unit receipts. -/
inductive PrefixAt {index : Nat} (source : EffectiveSplitAt index) :
    EffectiveSplitAt index → Type
  | nil : PrefixAt source source
  | advance {current : EffectiveSplitAt index} (trail : PrefixAt source current)
      (event : SelectedUnitEventAt current) : PrefixAt source event.unit.target

namespace PrefixAt

def steps {index : Nat} {source current : EffectiveSplitAt index} :
    PrefixAt source current → Nat
  | .nil => 0
  | .advance trail _ => trail.steps + 1

theorem right_accounting {index : Nat} {source current : EffectiveSplitAt index}
    (trail : PrefixAt source current) :
    trail.steps + splitRight current = splitRight source := by
  induction trail with
  | nil => simp only [steps, Nat.zero_add]
  | advance trail event previous =>
      have actualWrite := event.unit.rightWriteEquation
      simp only [steps]
      omega

def appendOutcome {index : Nat} {source current : EffectiveSplitAt index} :
    PrefixAt source current → OutcomeAt current → OutcomeAt source
  | .nil, outcome => outcome
  | .advance trail event, .inl reached =>
      trail.appendOutcome (.inl (.advance event reached))
  | .advance trail event, .inr exhausted =>
      trail.appendOutcome (.inr (.advance event exhausted))

end PrefixAt

inductive StateAt {index : Nat} (source : EffectiveSplitAt index) : Type
  | active {current : EffectiveSplitAt index} (trail : PrefixAt source current)
  | completed (outcome : OutcomeAt source)

def initial {index : Nat} (source : EffectiveSplitAt index) : StateAt source :=
  .active .nil

/-- Only the original classifier, complete inventory, and literal unit action
select the next state. The actor's completed future is absent from this map. -/
def next {index : Nat} {source : EffectiveSplitAt index} : StateAt source → StateAt source
  | .completed outcome => .completed outcome
  | .active (current := current) trail =>
      match pulse current with
      | .current terminal classified =>
          .completed (trail.appendOutcome (.inl (.current terminal classified)))
      | .factor _ _ selected inventory =>
          .completed (trail.appendOutcome (.inl (.factor selected inventory
            ((GeneratedPathAt.nil : GeneratedPathAt
              (fullFactorDecayLaw index) current current).snoc selected.1)
            (ParticleWaveFockPrimePairActualityActionHistory.generateFactorAction selected.1) rfl)))
      | .advance event => .active (.advance trail event)
      | .final right factor classified inventory =>
          .completed (trail.appendOutcome (.inr (.final right factor classified inventory)))

def remaining {index : Nat} {source : EffectiveSplitAt index} : StateAt source → Nat
  | .active (current := current) _ => splitRight current - 1
  | .completed _ => 0

theorem remaining_next_le {index : Nat} {source : EffectiveSplitAt index}
    (state : StateAt source) : remaining (next state) ≤ remaining state - 1 := by
  cases state with
  | completed outcome => simp only [next, remaining, Nat.zero_sub, Nat.le_refl]
  | @active current trail =>
      cases generated : pulse current with
      | current terminal classified => simp only [next, generated, remaining, Nat.zero_le]
      | factor factor classified selected inventory =>
          simp only [next, generated, remaining, Nat.zero_le]
      | advance event =>
          have actualWrite := event.unit.rightWriteEquation
          simp only [next, generated, remaining]
          omega
      | final right factor classified inventory =>
          simp only [next, generated, remaining, Nat.zero_le]

def run {index : Nat} {source : EffectiveSplitAt index} : Nat → StateAt source → StateAt source
  | 0, state => state
  | count + 1, state => run count (next state)

theorem remaining_run_le {index : Nat} {source : EffectiveSplitAt index}
    (count : Nat) (state : StateAt source) :
    remaining (run count state) ≤ remaining state - count := by
  induction count generalizing state with
  | zero => simp only [run, Nat.sub_zero, Nat.le_refl]
  | succ count previous =>
      calc
        remaining (run (count + 1) state) ≤ remaining (next state) - count := previous _
        _ ≤ (remaining state - 1) - count := Nat.sub_le_sub_right (remaining_next_le state) count
        _ = remaining state - (count + 1) := by omega

def sourceFuel {index : Nat} (source : EffectiveSplitAt index) : Nat :=
  splitRight source - 1

private def originalOutcome {index : Nat} {source : EffectiveSplitAt index} :
    StateAt source → OutcomeAt source
  | .active (current := current) trail => trail.appendOutcome (generate current)
  | .completed outcome => outcome

private theorem originalOutcome_next {index : Nat} {source : EffectiveSplitAt index}
    (state : StateAt source) : originalOutcome (next state) = originalOutcome state := by
  cases state with
  | completed outcome => rfl
  | @active current trail =>
      change originalOutcome (next (.active trail)) = trail.appendOutcome (generate current)
      rw [generate_eq_assemblePulse current]
      cases generated : pulse current with
      | current terminal classified => simp only [next, generated, originalOutcome, assemblePulse]
      | factor factor classified selected inventory =>
          simp only [next, generated, originalOutcome, assemblePulse]
      | advance event =>
          simp only [next, generated, originalOutcome, assemblePulse]
          cases generate event.unit.target <;> rfl
      | final right factor classified inventory =>
          simp only [next, generated, originalOutcome, assemblePulse]

private theorem originalOutcome_run {index : Nat} {source : EffectiveSplitAt index}
    (count : Nat) (state : StateAt source) :
    originalOutcome (run count state) = originalOutcome state := by
  induction count generalizing state with
  | zero => rfl
  | succ count previous =>
      exact (previous (next state)).trans (originalOutcome_next state)

/-- The source-derived number of actual pulses recognizes the original full
actor outcome, including either complete chronological branch. -/
theorem run_source {index : Nat} (source : EffectiveSplitAt index) :
    run (sourceFuel source) (initial source) = .completed (generate source) := by
  have finished : remaining (run (sourceFuel source) (initial source)) = 0 := by
    have bound := remaining_run_le (sourceFuel source) (initial source)
    simp only [sourceFuel, initial, remaining, Nat.sub_self] at bound
    exact Nat.eq_zero_of_le_zero bound
  have recognized := originalOutcome_run (sourceFuel source) (initial source)
  cases generated : run (sourceFuel source) (initial source) with
  | @active current trail =>
      rw [generated] at finished
      have floor := splitRight_atLeastTwo current
      simp only [remaining] at finished
      omega
  | completed outcome =>
      rw [generated] at recognized
      change outcome = generate source at recognized
      rw [recognized]

end
end NoIslandNoMagic.CanonicalArithmeticState.GoldbachUnitSelectedActor.Calculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
