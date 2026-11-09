import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Failure
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Realize

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open Reparation.Actual (Resident)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (prior : Installation.Live.Ledger seed community cut)
  (grammar : Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument))
  (observed : Set (Effect Party Good Port Technology Instrument))
  (lane : LocalU7 prior.world)
  (novel : ¬ observed ⊆ grammar.covered)

local notation "Old" => auditResident prior grammar observed lane novel
local notation "Rooted" => rootedFailure prior grammar observed lane novel
local notation "First" => auditFirst prior grammar observed lane
local notation "New" => GeneratedMinimalCofaceAt.worldNetwork (root_obstruction_generates_minimal_coface Rooted)

theorem audit_successor_support :
    (Old).root.toAuthoritativeRoot.toRoot.supportAt (Rooted).oldSuccessor.next = prior.resident.support := by
  change (First).support (Rooted).oldSuccessor.next = _
  cases (Rooted).oldSuccessor.next <;> rfl

theorem targetFinite :
    Finite (OpenResponsibilityAt _ ((Old).root.toAuthoritativeRoot.toRoot.supportAt (Rooted).oldSuccessor.next)) :=
  (audit_successor_support prior grammar observed lane novel).symm ▸ (First).beforeFinite

theorem targetUnique :
    ∀ actual : (Old).root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt (Rooted).oldSuccessor.next,
      actual = (Old).root.emitted (Rooted).oldSuccessor.next :=
  Compiler.occurrence_eq_emitted (First).flow

/-- Construct the literal minimal world from the installed failure. Its
first-write compiler publishes the exact operational language repair. -/
def revised : FieldGroundedTypedSemanticWorldNetworkRevisionAt Rooted :=
  realize Rooted (targetFinite prior grammar observed lane novel) (First).openFibres
    (targetUnique prior grammar observed lane novel) (grammar.repair observed)

def generatedNext : Resident New :=
  landing Rooted (targetFinite prior grammar observed lane novel) (First).openFibres (grammar.repair observed)

def revisionAnswers :=
  TypedSemanticWorldNetworkU8Recovery.factorizesThroughInitialCofaceAnswerAndNext
    (revised prior grammar observed lane novel)

theorem the_first_write_is_the_generated_next :
    let revised := (revised prior grammar observed lane novel).generate
    (⟨revised.NewN, revised.newLivingRoot.generatedNextCurrentAt (.finite revised.newRoot.toRoot.initialVisit)⟩ :
      AnyAuthoritativeRootCurrent) = (generatedNext prior grammar observed lane novel).erase :=
  landing_is_the_generated_first_target Rooted (targetFinite prior grammar observed lane novel)
    (First).openFibres (grammar.repair observed)

def generatedLanguageFace :=
  landingFace Rooted (targetFinite prior grammar observed lane novel) (First).openFibres (grammar.repair observed)

theorem the_generated_next_reads_the_exact_repair :
    HEq (generatedLanguageFace prior grammar observed lane novel).rootRead (grammar.repair observed) :=
  landing_reads_the_payload Rooted (targetFinite prior grammar observed lane novel)
    (First).openFibres (grammar.repair observed)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
