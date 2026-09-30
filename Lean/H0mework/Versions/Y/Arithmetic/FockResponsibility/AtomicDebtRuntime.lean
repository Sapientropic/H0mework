import H0mework.Versions.Y.Arithmetic.FockResponsibility.AtomicSectorDebt
import H0mework.Versions.Y.Arithmetic.FockResponsibility.AtomicRuntime

/-!
# Physical atomic debt compiled at the exact Goldbach runtime current

The already emitted atomic runtime payload supplies the physical current.
Its complete structural-key inventory is activated as a finite observer debt.
The source debt disposition is compiled without choosing a new event:

* settlement retains the local classifier-generated terminal;
* a step runs the generic strict whole-ledger evolution at the exact runtime
  support;
* a missing structural key produces a typed projection obstruction.

The existing runtime occurrence, base whole-ledger write-back, and generated
next pointers are retained explicitly.  This file does not install the
activated ledger as a new authoritative root.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalArithmeticState
namespace ParticleWaveFockAtomicDebtRuntime

open DebtActivationLedger DebtActivationWorld
open ParticleWaveFockAtomicDynamicsRuntime

noncomputable section

abbrev RuntimeIndex (depth : Nat) :=
  scanIndex (runtimeAt depth).current.visit.current

abbrev RuntimeSupport (depth : Nat) :=
  (runtimeAt depth).current.visit.current

abbrev RuntimeDebtState (depth : Nat) :=
  ParticleWaveFockAtomicSectorDebt.State (RuntimeIndex depth)

abbrev RuntimeActivationLaw (depth : Nat) :=
  ParticleWaveFockAtomicSectorDebt.activationLaw (RuntimeIndex depth)

abbrev RuntimeActivatedNetwork (depth : Nat) :=
  ExtendedNetwork CanonicalUnitArithmeticRoot.N (RuntimeActivationLaw depth)

/-- The exact runtime physical current together with the complete structural-key
inventory. -/
def runtimeDebtState (depth : Nat) : RuntimeDebtState depth :=
  ((runtimeAtomicPayload depth).physicalCurrent, Finset.univ)

/-- The runtime state is definitionally the physical debt's canonical initial
state after reading back the payload's generated current. -/
theorem runtimeDebtState_eq_initial (depth : Nat) :
    runtimeDebtState depth =
      ParticleWaveFockAtomicSectorDebt.initialState
        (RuntimeIndex depth) (runtimeActive depth).down := by
  apply Prod.ext
  · exact (runtimeAtomicPayload depth).physicalCurrent_eq
  · rfl

@[simp] theorem runtimeDebtState_physical (depth : Nat) :
    (runtimeDebtState depth).1 =
      (runtimeAtomicPayload depth).physicalCurrent :=
  rfl

@[simp] theorem runtimeDebtState_contains_every_structuralKey
    (depth : Nat) (structuralKey :
      CanonicalUnitArithmeticOperationalFactorDecayProducer.FactorDecayStructuralChannelKeyAt
        (RuntimeIndex depth)) :
    structuralKey ∈ (runtimeDebtState depth).2 :=
  Finset.mem_univ structuralKey

/-- The three existing runtime pointers which compilation must not replace.
They certify only a dependent readout of the emitted runtime root. -/
structure RuntimeReadbackAt (depth : Nat) : Type where
  emitted :
    runtimeFacade.process.toAnswerNextCausalWorld.emitted
          (ULift.up (runtimeAt depth).state) =
      ULift.up (runtimeAt depth).tick.generated
  occurrence :
    (runtimeAt depth).tick.generated.occurrence =
      (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt depth).current.visit.current
  payloadOccurrence :
    (runtimeAtomicPayload depth).sourceOccurrence =
      (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (runtimeAt depth).current.visit.current
  wholeLedger :
    HEq (runtimeAt depth).tick.generated.wholeLedgerWriteBack
      ((runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (runtimeAt depth).current.visit.current)
  nextCurrent :
    (runtimeAt depth).tick.nextCurrent =
      runtimeFacade.process.stateAt
        (runtimeFacade.process.successor (runtimeAt depth).state)

def runtimeReadback (depth : Nat) : RuntimeReadbackAt depth := by
  have factorization := coversAt_factorizes
    (runtimeAt depth) FaceAt.atomicDynamics
  exact
    { emitted := factorization.1
      occurrence := factorization.2.1
      payloadOccurrence := (runtimeAtomicPayload_same_occurrence depth).1
      wholeLedger := factorization.2.2.1
      nextCurrent := factorization.2.2.2.2 }

/-- Local settlement is retained verbatim.  No base terminal receipt is
invented, so this branch does not manufacture authoritative root closure. -/
structure CompiledSettlementAt (depth : Nat) : Type where
  settlement : ParticleWaveFockAtomicSectorDebt.SettlementAt
    (runtimeDebtState depth)
  source_eq :
    ParticleWaveFockAtomicSectorDebt.generateDisposition
        (runtimeDebtState depth) =
      .settlement settlement
  runtime : RuntimeReadbackAt depth

/-- One exact physical step and the generic strict evolution of the entire
activated ledger at the already emitted runtime support. -/
structure CompiledStepAt (depth : Nat) : Type where
  target : RuntimeDebtState depth
  step : ParticleWaveFockAtomicSectorDebt.StepAt
    (runtimeDebtState depth) target
  source_eq :
    ParticleWaveFockAtomicSectorDebt.generateDisposition
        (runtimeDebtState depth) = .step step
  wholeLedgerUpdate :
    LedgerWriteEvolutionAt (RuntimeActivatedNetwork depth)
      (activeLedger (N := CanonicalUnitArithmeticRoot.N)
        (law := RuntimeActivationLaw depth)
        (RuntimeSupport depth) (runtimeDebtState depth))
      (activeLedger (N := CanonicalUnitArithmeticRoot.N)
        (law := RuntimeActivationLaw depth)
        (RuntimeSupport depth) target)
  wholeLedgerUpdate_eq : wholeLedgerUpdate =
    stepLedgerEvolution (N := CanonicalUnitArithmeticRoot.N)
      (law := RuntimeActivationLaw depth) (RuntimeSupport depth) step
  runtime : RuntimeReadbackAt depth

/-- A missing observer key becomes the generic activated-world obstruction
and its law-surface receipt at the same runtime support.  This does not assert
that the occurrence-sensitive physical incidence repeated. -/
structure CompiledObstructionAt (depth : Nat) : Type where
  blocked : ParticleWaveFockAtomicSectorDebt.ObstructionAt
    (runtimeDebtState depth)
  source_eq :
    ParticleWaveFockAtomicSectorDebt.generateDisposition
        (runtimeDebtState depth) =
      .obstruction blocked
  obstruction :
    (RuntimeActivatedNetwork depth).ObstructionAt
      ⟨RuntimeSupport depth, some (runtimeDebtState depth)⟩
  obstruction_eq : obstruction =
    debtObstruction (N := CanonicalUnitArithmeticRoot.N)
      (law := RuntimeActivationLaw depth) (RuntimeSupport depth) blocked
  receipt :
    (RuntimeActivatedNetwork depth).DispositionAt
      ⟨RuntimeSupport depth, some (runtimeDebtState depth)⟩
      .lawSurfaceExtension
  receipt_eq : receipt =
    debtObstructionReceipt (N := CanonicalUnitArithmeticRoot.N)
      (law := RuntimeActivationLaw depth) (RuntimeSupport depth) blocked
  runtime : RuntimeReadbackAt depth

inductive CompiledDispositionAt (depth : Nat) : Type
  | settlement (compiled : CompiledSettlementAt depth)
  | step (compiled : CompiledStepAt depth)
  | obstruction (compiled : CompiledObstructionAt depth)

/-- Compile exactly the source-generated physical debt disposition. -/
def compileDisposition (depth : Nat) : CompiledDispositionAt depth := by
  generalize source_eq :
    ParticleWaveFockAtomicSectorDebt.generateDisposition
      (runtimeDebtState depth) = disposition
  cases disposition with
  | settlement settled =>
      exact .settlement
        { settlement := settled
          source_eq := source_eq
          runtime := runtimeReadback depth }
  | step generated =>
      exact .step
        { target := _
          step := generated
          source_eq := source_eq
          wholeLedgerUpdate :=
            stepLedgerEvolution (N := CanonicalUnitArithmeticRoot.N)
              (law := RuntimeActivationLaw depth)
              (RuntimeSupport depth) generated
          wholeLedgerUpdate_eq := rfl
          runtime := runtimeReadback depth }
  | obstruction blocked =>
      exact .obstruction
        { blocked := blocked
          source_eq := source_eq
          obstruction :=
            debtObstruction (N := CanonicalUnitArithmeticRoot.N)
              (law := RuntimeActivationLaw depth)
              (RuntimeSupport depth) blocked
          obstruction_eq := rfl
          receipt :=
            debtObstructionReceipt (N := CanonicalUnitArithmeticRoot.N)
              (law := RuntimeActivationLaw depth)
              (RuntimeSupport depth) blocked
          receipt_eq := rfl
          runtime := runtimeReadback depth }

def CompiledDispositionAt.source {depth : Nat} :
    CompiledDispositionAt depth →
      ParticleWaveFockAtomicSectorDebt.GeneratedDispositionAt
        (runtimeDebtState depth)
  | .settlement compiled => .settlement compiled.settlement
  | .step compiled => .step compiled.step
  | .obstruction compiled => .obstruction compiled.blocked

def CompiledDispositionAt.runtime {depth : Nat} :
    CompiledDispositionAt depth → RuntimeReadbackAt depth
  | .settlement compiled => compiled.runtime
  | .step compiled => compiled.runtime
  | .obstruction compiled => compiled.runtime

/-- Exact source-disposition readback: compilation neither reclassifies nor
accepts a caller-selected branch. -/
theorem compileDisposition_source (depth : Nat) :
    (compileDisposition depth).source =
      ParticleWaveFockAtomicSectorDebt.generateDisposition
        (runtimeDebtState depth) := by
  cases compiled_eq : compileDisposition depth with
  | settlement compiled => exact compiled.source_eq.symm
  | step compiled => exact compiled.source_eq.symm
  | obstruction compiled => exact compiled.source_eq.symm

theorem compileDisposition_keeps_runtime (depth : Nat) :
    (runtimeAtomicPayload depth).sourceOccurrence =
        (runtimeAt depth).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt depth).current.visit.current ∧
      HEq (compileDisposition depth).runtime.wholeLedger
        (runtimeReadback depth).wholeLedger ∧
      (compileDisposition depth).runtime.nextCurrent =
        (runtimeReadback depth).nextCurrent :=
  ⟨(compileDisposition depth).runtime.payloadOccurrence, HEq.rfl, rfl⟩

theorem CompiledStepAt.debtBudget_strict {depth : Nat}
    (compiled : CompiledStepAt depth) :
    (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := RuntimeActivationLaw depth)
        (RuntimeSupport depth) compiled.target).progressBudget <
      (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := RuntimeActivationLaw depth)
        (RuntimeSupport depth) (runtimeDebtState depth)).progressBudget :=
  debtStep_budget_lt (N := CanonicalUnitArithmeticRoot.N)
    (law := RuntimeActivationLaw depth)
    (RuntimeSupport depth) compiled.step

theorem CompiledStepAt.destination_debt {depth : Nat}
    (compiled : CompiledStepAt depth) :
    (compiled.wholeLedgerUpdate.destination
      (debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := RuntimeActivationLaw depth)
        (RuntimeSupport depth) (runtimeDebtState depth))).1 =
      debtEntry (N := CanonicalUnitArithmeticRoot.N)
        (law := RuntimeActivationLaw depth)
        (RuntimeSupport depth) compiled.target := by
  rw [compiled.wholeLedgerUpdate_eq]
  exact stepLedgerEvolution_destination_debt
    (N := CanonicalUnitArithmeticRoot.N)
    (law := RuntimeActivationLaw depth)
    (RuntimeSupport depth) compiled.step

@[simp] theorem CompiledObstructionAt.claim {depth : Nat}
    (compiled : CompiledObstructionAt depth) :
    (RuntimeActivatedNetwork depth).obstructionClaim compiled.obstruction =
      .inr (RuntimeActivationLaw depth).debtClaim := by
  rw [compiled.obstruction_eq]
  exact debtObstruction_claim (N := CanonicalUnitArithmeticRoot.N)
    (law := RuntimeActivationLaw depth)
    (RuntimeSupport depth) compiled.blocked

end

end ParticleWaveFockAtomicDebtRuntime
end CanonicalArithmeticState
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
