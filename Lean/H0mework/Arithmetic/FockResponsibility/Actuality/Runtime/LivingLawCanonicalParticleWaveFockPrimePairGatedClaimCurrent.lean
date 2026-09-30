import H0mework.Foundation.Runtime.GatedClaimProcess
import H0mework.Foundation.Inquiry.EmptyObstruction
import H0mework.Arithmetic.FockResponsibility.Actuality.Admission.LivingLawCanonicalParticleWaveFockPrimePairPendingClaimBirth

/-!
# Prime-pair actuality in the gated claim pre-process

For every exact even occurrence, the source-generated effective-fibre
classifier now acts on the pending terminal claim itself.  The positive branch
generates its strict advance; the faithful residual enters the existing debt
U7 audit and has no next.  The old factor-scanning successor is absent from
this disposition.
-/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalArithmeticState
namespace ParticleWaveFockPrimePairGatedClaimCurrent

open GatedClaimPreProcess
open ParticleWaveFockOccurrenceResponsibilityRuntime
open ParticleWaveFockPrimePairActuality
open ParticleWaveFockPrimePairActualityDebt
open ParticleWaveFockPrimePairPendingClaimBirth
open RootGeneratedEmptyObstructionU7

noncomputable section

def gatedCurrent (depth : Nat) :
    SourceNativeGatedClaimCurrentAt (pendingClaimBirth depth)
      (pendingClaimBirth depth).initial :=
  SourceNativeGatedClaimCurrentAt.initial (pendingClaimBirth depth)

theorem gatedCurrent_ledger_eq_birth (depth : Nat) :
    (gatedCurrent depth).ledger = (pendingClaimBirth depth).targetLedger :=
  SourceNativeGatedClaimCurrentAt.initial_ledger_eq_birth
    (pendingClaimBirth depth)

theorem gatedCurrent_claim (depth : Nat) :
    (gatedCurrent depth).entry.claim =
      .inr (runtimeActualityPayload depth).claim :=
  rfl

/-- Exact source classifier compiled into the gated claim grammar. -/
inductive GeneratedGatedDispositionAt (depth : Nat) : Type 8
  | paid (advance : SourceNativeGatedClaimAdvanceAt (gatedCurrent depth))
  | obstructed
      (obstruction : SourceNativeGatedClaimObstructionAt (gatedCurrent depth))

def generateGatedDisposition (depth : Nat) :
    GeneratedGatedDispositionAt depth := by
  let actuality := runtimeActualityPayload depth
  generalize disposition_eq :
    ParticleWaveFockPrimePairActualityDebt.generateDisposition
      (StateAt.pending : StateAt actuality) = disposition
  cases disposition with
  | settlement settlement => exact nomatch settlement
  | payment payment =>
      exact .paid
        (SourceNativeGatedClaimAdvanceAt.generate (gatedCurrent depth) payment)
  | obstruction obstruction =>
      exact .obstructed
        (SourceNativeGatedClaimObstructionAt.generate
          (gatedCurrent depth) obstruction)

def oldU7 : U7ProducerCalculus CanonicalUnitArithmeticRoot.N :=
  RootGeneratedEmptyObstructionU7.producer CanonicalUnitArithmeticRoot.N
    CanonicalUnitArithmeticRoot.rootObstructionAt_isEmpty

def oldU7Calculus :
    U7ObstructionEvolutionCalculus CanonicalUnitArithmeticRoot.N oldU7 :=
  RootGeneratedEmptyObstructionU7.calculus CanonicalUnitArithmeticRoot.N
    CanonicalUnitArithmeticRoot.rootObstructionAt_isEmpty

/-- The negative branch cannot continue the claim.  It enters the generic
debt-U7 theory audit at the same live row. -/
def obstructionTheoryAudit
    {depth : Nat}
    (obstruction : SourceNativeGatedClaimObstructionAt (gatedCurrent depth)) :=
  obstruction.toTheoryAudit oldU7 oldU7Calculus

theorem paid_branch_strict
    {depth : Nat}
    (advance : SourceNativeGatedClaimAdvanceAt (gatedCurrent depth)) :
    advance.targetCurrent.entry.progressBudget <
      (gatedCurrent depth).entry.progressBudget :=
  advance.strict_debit

theorem paid_branch_preserves_claim
    {depth : Nat}
    (advance : SourceNativeGatedClaimAdvanceAt (gatedCurrent depth)) :
    (gatedCurrent depth).entry.claim = advance.targetCurrent.entry.claim :=
  advance.claim_eq

theorem obstruction_branch_has_no_next
    {depth : Nat}
    (obstruction : SourceNativeGatedClaimObstructionAt (gatedCurrent depth)) :
    IsEmpty obstruction.GeneratedNextAt :=
  inferInstance

/-- A raw old-runtime next has no constructor into either gated outcome. -/
theorem old_runtime_next_cannot_fill_gated_disposition
    (_depth : Nat)
    (_oldNext : LivingRuntimeState runtimeFacade.process) : True := by
  fail_if_success
    exact (show GeneratedGatedDispositionAt _depth from _oldNext)
  trivial

end


end ParticleWaveFockPrimePairGatedClaimCurrent
end NoIslandNoMagic.CanonicalArithmeticState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
