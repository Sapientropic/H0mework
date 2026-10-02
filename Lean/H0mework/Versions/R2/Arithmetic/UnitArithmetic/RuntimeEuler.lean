import H0mework.Versions.R2.Arithmetic.UnitArithmetic.EulerLimit

/-!
# Runtime-generated cofinal Euler authority

The cofinal arithmetic stages are now read from repeated canonical runtime
activations, not from a standalone recursion on `UnitHistory`.  Every stage
contains the exact reachable runtime, its unique tick, emitted occurrence,
whole-ledger row and generated next.  The earlier pure `cofinalHistory` is
retained only through a theorem identifying its mathematical readout with
this runtime-generated sequence.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CanonicalUnitArithmeticRuntimeCofinalEuler

open ArithmeticGeneration
open CanonicalUnitArithmeticCofinalEulerLimit
open CanonicalUnitArithmeticCofinalEulerPrefix
open CanonicalUnitArithmeticCommonCarrier
open CanonicalUnitArithmeticRoot
open RootArithmeticIncidence

noncomputable section

abbrev Runtime := LivingRuntimeState runtimeFacade.process

def runtimeAt (stage : Nat) : Runtime :=
  runtimeSeed.advance stage

@[simp] theorem runtimeAt_zero : runtimeAt 0 = runtimeSeed :=
  rfl

@[simp] theorem runtimeAt_succ (stage : Nat) :
    runtimeAt (stage + 1) = (runtimeAt stage).tick.next :=
  rfl

/-- One exact runtime activation; the second component cannot be replaced by
an unrelated occurrence at the same numeric stage. -/
abbrev RuntimeAuthority :=
  Σ runtime : Runtime, ExactActivatedRootOccurrenceAt runtime

def runtimeAuthorityAt (stage : Nat) : RuntimeAuthority :=
  ⟨runtimeAt stage, (runtimeAt stage).tick⟩

def runtimeStep (stage : Nat) :
    RootArithmeticIncidenceStepAt recognition
      (runtimeAt stage).current.visit :=
  recognition.generateStepAt (runtimeAt stage).current.visit

def runtimeWholeHistory (stage : Nat) : UnitHistory :=
  (runtimeStep stage).material.whole

@[simp] theorem runtimeWholeHistory_zero :
    runtimeWholeHistory 0 = initialStep.material.whole :=
  rfl

@[simp] theorem runtimeWholeHistory_succ (stage : Nat) :
    runtimeWholeHistory (stage + 1) = next (runtimeWholeHistory stage) :=
  rfl

theorem runtimeWholeHistory_eq_cofinalHistory (stage : Nat) :
    runtimeWholeHistory stage =
      cofinalHistory commonOccurrence.root.2 stage := by
  induction stage with
  | zero => rfl
  | succ stage inductionHypothesis =>
      rw [runtimeWholeHistory_succ, cofinalHistory_succ,
        inductionHypothesis]

def runtimeEulerPrefix (stage : Nat) : ArithmeticFunction ℤ :=
  finiteEulerPrefix (runtimeWholeHistory stage)

def runtimeStageOccurrence (stage : Nat) :
    RootedAccountedUnfolding RuntimeAuthority :=
  RootedAccountedUnfolding.zero (runtimeAuthorityAt stage)

/-- Each finite Euler prefix is attached to the exact activation that
generated its whole history. -/
def runtimeEulerPrefixOccurrence (stage : Nat) : RootedAccountedUnfolding
    (RuntimeAuthority × ArithmeticFunction ℤ) :=
  (runtimeStageOccurrence stage).map fun authority =>
    (authority, runtimeEulerPrefix stage)

theorem runtimeEulerPrefix_eq_cofinalPrefix (stage : Nat) :
    runtimeEulerPrefix stage =
      cofinalPrefix commonOccurrence.root.2 stage := by
  rw [runtimeEulerPrefix, cofinalPrefix,
    runtimeWholeHistory_eq_cofinalHistory]

theorem runtimeEulerPrefix_eventually_eq_formalEulerCoefficients
    (coefficient : Nat) :
    ∀ᶠ stage : Nat in Filter.atTop,
      runtimeEulerPrefix stage coefficient =
        CanonicalUnitArithmeticDualReadouts.formalEulerCoefficients
          coefficient := by
  simpa only [runtimeEulerPrefix_eq_cofinalPrefix] using
    cofinalPrefix_eventually_eq_formalEulerCoefficients
      commonOccurrence.root.2 coefficient

def authorityWholeHistory (authority : RuntimeAuthority) : UnitHistory :=
  (recognition.generateStepAt authority.1.current.visit).material.whole

def authoritySource (authority : RuntimeAuthority) :
    CoordinateFreeRelationSource :=
  CoordinateFreeRelationSource.generate (authorityWholeHistory authority)

def runtimeAuthorityOccurrence :
    RootedAccountedUnfolding RuntimeAuthority :=
  RootedAccountedUnfolding.zero (runtimeAuthorityAt 0)

/-- The generated Euler limit is calculated from the exact runtime
authority carried by the occurrence. -/
def runtimeCofinalLimitOccurrence : RootedAccountedUnfolding
    (RuntimeAuthority × GeneratedCofinalEulerLimit) :=
  runtimeAuthorityOccurrence.map fun authority =>
    (authority, GeneratedCofinalEulerLimit.generate
      (authoritySource authority))

theorem runtimeCofinalLimitOccurrence_projects :
    runtimeCofinalLimitOccurrence.map Prod.fst =
      runtimeAuthorityOccurrence := by
  rw [runtimeCofinalLimitOccurrence, RootedAccountedUnfolding.map_map]
  change runtimeAuthorityOccurrence.map id = runtimeAuthorityOccurrence
  exact RootedAccountedUnfolding.map_id _

theorem runtimeAuthority_factorizes (stage : Nat) :
    (runtimeAt stage).tick.generated.occurrence =
        (runtimeAt stage).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
          (runtimeAt stage).current.visit.current ∧
      HEq (runtimeAt stage).tick.generated.wholeLedgerWriteBack
        ((runtimeAt stage).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
          (runtimeAt stage).current.visit.current) ∧
      (runtimeAt stage).tick.nextCurrent =
        runtimeFacade.process.stateAt
          (runtimeFacade.process.successor (runtimeAt stage).state) := by
  have factorization := coversAt_factorizes (runtimeAt stage) FacadeFace.material
  exact ⟨factorization.2.1, factorization.2.2.1,
    factorization.2.2.2.2⟩

end
end CanonicalUnitArithmeticRuntimeCofinalEuler
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
