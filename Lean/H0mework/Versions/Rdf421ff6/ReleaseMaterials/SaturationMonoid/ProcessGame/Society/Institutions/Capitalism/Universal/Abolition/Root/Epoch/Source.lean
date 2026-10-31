import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Decision.Controller.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeFace.Compilers

/-! The epoch origin is a view of the installed controller occurrence. Its
inventory contains only executed instructions; period timing remains the
controller's source boundary, not the raw programme reader's synthetic next. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Admission.Datum input (Admission.frame input depth count)) (limit : Nat)

/-- The controller's ledger erasure, available before its dependent faces are
assembled. It has exactly the same source, emitter and compiler. -/
def ledgerRoot : SourceNativeLedgerRootClosure (Decision.Controller.N input depth count)
    (Decision.Controller.V input depth count datum limit) where
  source := Decision.Controller.ledgerSource input depth count datum limit
  emitted := Decision.Controller.emitted input depth count datum limit
  compiler_commutes := fun _ => rfl

abbrev root := (ledgerRoot input depth count datum limit).toRoot
abbrev Visit := RootVisit (root input depth count datum limit)

def occurrence (visit : Visit input depth count datum limit) :
    OriginalOccurrence (Decision.Controller.ledgerSource input depth count datum limit) :=
  ⟨visit.current, Decision.Controller.emitted input depth count datum limit visit.current⟩

def execution (visit : Visit input depth count datum limit) : ExecutionResult Party Good Port Technology Instrument :=
  Decision.Controller.actualExecution input depth count datum limit visit.current

def body (visit : Visit input depth count datum limit) : Origin Party Good Port Technology Instrument :=
  ⟨visit.current.raw, (execution input depth count datum limit visit).items.map ExecutionItem.request⟩

theorem execution_is_original_replay (current : Decision.Controller.Current input depth count datum) :
    input.law.execute current.raw 0
        ((Decision.Controller.actualExecution input depth count datum limit current).items.map ExecutionItem.request) =
      Decision.Controller.actualExecution input depth count datum limit current := by
  cases phase : current.first
  · simp only [Decision.Controller.actualExecution, phase, Review.Guarded.CompletedAt.actualExecution,
      RawLaw.inventory_requests_exact]
  · simp only [Decision.Controller.actualExecution, phase]
    rw [current.original_fee_target phase]
    unfold Decision.Controller.firstActualExecution
    split
    · rw [Review.Guarded.CompletedAt.actual_requests_exact]
      rfl
    · rfl

theorem body_inventory_is_the_installed_execution (visit : Visit input depth count datum limit) :
    input.law.rawItems (body input depth count datum limit visit).1
      (body input depth count datum limit visit).2 = (execution input depth count datum limit visit).items :=
  congrArg ExecutionResult.items (execution_is_original_replay input depth count datum limit visit.current)

def actualParties (visit : Visit input depth count datum limit) : List Party :=
  ((execution input depth count datum limit visit).items.flatMap (itemParties input.law)).dedup

theorem body_parties_are_actual (visit : Visit input depth count datum limit) :
    parties input.law (body input depth count datum limit visit) = actualParties input depth count datum limit visit := by
  unfold parties actualParties
  rw [body_inventory_is_the_installed_execution]

abbrev ActorAt (visit : Visit input depth count datum limit) :=
  ProgrammeFace.Actor input.law (body input depth count datum limit) visit

/-- Only the source M0 face is consumed here. No relation or future authority
is read from the raw programme's period convention. -/
def actorAt (visit : Visit input depth count datum limit) (party : Party)
    (present : party ∈ actualParties input depth count datum limit visit) :
    ActorAt input depth count datum limit visit :=
  ProgrammeFace.actor input.law (body input depth count datum limit) visit party
    (by rwa [body_parties_are_actual])

theorem actors_keep_actual_seed_identity (visit : Visit input depth count datum limit) (first second : Party)
    (firstPresent : first ∈ actualParties input depth count datum limit visit)
    (secondPresent : second ∈ actualParties input depth count datum limit visit)
    (same : actorAt input depth count datum limit visit first firstPresent =
      actorAt input depth count datum limit visit second secondPresent) : first = second :=
  ProgrammeFace.actor_distinguishes_original_seeds input.law (body input depth count datum limit)
    visit first second _ _ same

#print axioms execution_is_original_replay
#print axioms actors_keep_actual_seed_identity

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch
