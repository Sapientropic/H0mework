import H0mework.Versions.R2.Arithmetic.FockDynamics.AtomicDynamics
import H0mework.Versions.R2.Arithmetic.FockResponsibility.SectorDebt

/-!
# Structural-channel observation debt driven by the physical dynamics

The debt current couples the physical particle projection to the finite
inventory of still-unaccounted structural channel keys.  Its emitted event is
always `generateDynamics current` itself:

* a generated terminal settles immediately;
* a generated nonzero physical step whose structural key remains performs the
  physical update and erases exactly that observer key;
* a generated step whose key is absent exposes projection loss.  It does not
  assert that the actual occurrence was already consumed.

The caller supplies no channel, branch, terminal, or target.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockAtomicSectorDebt

open CanonicalUnitArithmeticEffectiveFactorRepairOrbitProducer
open CanonicalUnitArithmeticFullFactorEmissionProducer
open CanonicalUnitArithmeticOperationalFactorDecayProducer
open DebtActivationWorld
open ParticleWaveFock
open ParticleWaveFockAtomicProcess

noncomputable section

noncomputable local instance factorDecayStructuralKeyDecidableEq (index : Nat) :
    DecidableEq (FactorDecayStructuralChannelKeyAt index) := Classical.decEq _

/-- The projected physical current and remaining structural-key inventory. -/
abbrev State (index : Nat) :=
  PhysicalCurrentAt index × Finset (FactorDecayStructuralChannelKeyAt index)

def initialState (index : Nat) (indexInRange : 1 ≤ index) : State index :=
  (canonicalCurrent index indexInRange, Finset.univ)

@[simp] theorem initialState_physical (index : Nat)
    (indexInRange : 1 ≤ index) :
    (initialState index indexInRange).1 = canonicalCurrent index indexInRange :=
  rfl

@[simp] theorem initialState_contains_every_key (index : Nat)
    (indexInRange : 1 ≤ index)
    (key : FactorDecayStructuralChannelKeyAt index) :
    key ∈ (initialState index indexInRange).2 :=
  Finset.mem_univ key

/-- Finite observer key of a generated physical step. -/
def stepStructuralKey {index : Nat} {current : PhysicalCurrentAt index}
    {event : SourceEventAt current}
    (generated : GeneratedStepAt current event) :
    FactorDecayStructuralChannelKeyAt index :=
  ⟨current.current, generated.channel⟩

/-- A terminal dynamics branch is the settlement witness.  Its constructor is
private, so only the source-emitted dynamics can install it below. -/
structure SettlementAt {index : Nat} (state : State index) : Type where
  private mk ::
  generated : GeneratedTerminalAt state.1 (generateEvent state.1)
  species : GeneratedTerminalSpeciesAt state.1 generated.terminal
  dynamics_eq : generateDynamics state.1 = .terminal generated species

/-- A source-emitted physical step pays one still-present observer key. -/
structure StepAt {index : Nat} (source target : State index) : Type where
  private mk ::
  generated : GeneratedStepAt source.1 (generateEvent source.1)
  effect : GeneratedStepEffectAt source.1 (generateEvent source.1) generated
  dynamics_eq : generateDynamics source.1 = .step generated effect
  structuralKey : FactorDecayStructuralChannelKeyAt index
  structuralKey_eq : structuralKey = stepStructuralKey generated
  present : structuralKey ∈ source.2
  physicalProgress :
    PhysicalFactorDecayProgressAt generated.channel
  target_eq : target = (generated.target, source.2.erase structuralKey)

/-- The actual dynamics generated a step whose finite observer key is absent.
The missing provenance coordinate must decide whether this is recurrence or a
same-occurrence replay; this projected layer does not decide that question. -/
structure ObstructionAt {index : Nat} (state : State index) : Type where
  private mk ::
  generated : GeneratedStepAt state.1 (generateEvent state.1)
  effect : GeneratedStepEffectAt state.1 (generateEvent state.1) generated
  dynamics_eq : generateDynamics state.1 = .step generated effect
  structuralKey : FactorDecayStructuralChannelKeyAt index
  structuralKey_eq : structuralKey = stepStructuralKey generated
  physicalProgress :
    PhysicalFactorDecayProgressAt generated.channel
  keyNotRemaining : structuralKey ∉ state.2

/-- Terminal currents have no live debt budget.  A continuing physical
current owns exactly the cardinality of its remaining structural-key inventory. -/
def budget {index : Nat} (state : State index) : Nat :=
  match generateDynamics state.1 with
  | .terminal _generated _species => 0
  | .step _generated _effect => state.2.card

theorem settlement_budget_zero {index : Nat} {state : State index}
    (settlement : SettlementAt state) : budget state = 0 := by
  unfold budget
  rw [settlement.dynamics_eq]

theorem step_budget_lt {index : Nat} {source target : State index}
    (step : StepAt source target) : budget target < budget source := by
  rw [step.target_eq]
  unfold budget
  rw [step.dynamics_eq]
  cases targetDynamics : generateDynamics step.generated.target with
  | terminal generated species =>
      exact Finset.card_pos.mpr ⟨step.structuralKey, step.present⟩
  | step generated effect =>
      exact Finset.card_erase_lt_of_mem step.present

inductive DebtId
  | structuralChannelObserver

inductive DebtClaim
  | accountStructuralChannelObservation

/-- Structural observer debt driven by the actual physical dynamics. -/
def activationLaw (index : Nat) : DebtActivationLaw where
  DebtState := State index
  DebtId := DebtId
  DebtClaim := DebtClaim
  debtId := .structuralChannelObserver
  debtClaim := .accountStructuralChannelObservation
  budget := budget
  StepAt := StepAt
  step_budget_lt := step_budget_lt
  SettlementAt := SettlementAt
  settlement_budget_zero := settlement_budget_zero
  ObstructionAt := ObstructionAt

/-- Total source-emitted debt disposition.  The step target is existentially
owned by the generated dynamics branch. -/
inductive GeneratedDispositionAt {index : Nat} (state : State index) : Type
  | settlement (settled : SettlementAt state)
  | step {target : State index} (generated : StepAt state target)
  | obstruction (blocked : ObstructionAt state)

/-- Consume `generateDynamics` once, then decide whether its finite structural
key remains available for a strict observer debit. -/
def generateDisposition {index : Nat}
    (state : State index) : GeneratedDispositionAt state := by
  generalize dynamics_eq : generateDynamics state.1 = dynamics
  cases dynamics with
  | terminal generated species =>
      exact .settlement
        { generated := generated
          species := species
          dynamics_eq := dynamics_eq }
  | step generated effect =>
      let structuralKey := stepStructuralKey generated
      by_cases present : structuralKey ∈ state.2
      · exact .step
          { generated := generated
            effect := effect
            dynamics_eq := dynamics_eq
            structuralKey := structuralKey
            structuralKey_eq := rfl
            present := present
            physicalProgress := generated.physicalProgress
            target_eq := rfl }
      · exact .obstruction
          { generated := generated
            effect := effect
            dynamics_eq := dynamics_eq
            structuralKey := structuralKey
            structuralKey_eq := rfl
            physicalProgress := generated.physicalProgress
            keyNotRemaining := present }

theorem generatedDisposition_is_source_total {index : Nat}
    (state : State index) : Nonempty (GeneratedDispositionAt state) :=
  ⟨generateDisposition state⟩

def generatedInitialDisposition (index : Nat) (indexInRange : 1 ≤ index) :
    GeneratedDispositionAt (initialState index indexInRange) :=
  generateDisposition (initialState index indexInRange)

end

end ParticleWaveFockAtomicSectorDebt
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
