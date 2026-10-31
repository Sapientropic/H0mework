import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission.Compilation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat) (datum : Datum input (frame input depth count))

def targetU7 : U7ProducerCalculus (Continuation.N input (frame input depth count)) where
  DemandAt := fun _ => PUnit
  generateDemand := fun _ => PUnit.unit

def targetU7Source : U7ActualSuccessorSource (Continuation.N input (frame input depth count))
    (targetU7 input depth count) where
  EventAt := SourceGeneratedU7DemandAt (targetU7 input depth count)
  emit := fun obstruction => .canonical obstruction
  demandGeneratedAt := id
  demandEntryAt := fun {support} {_} {_} _ => (frame input depth count).native.entrySupport support.1

def targetCalculus : U7ObstructionEvolutionCalculus (Continuation.N input (frame input depth count))
    (targetU7 input depth count) where
  source := targetU7Source input depth count
  compile := fun {support} {obstruction} {_} _ => {
    disposition := .redirected (successor := obstruction)
      ⟨(frame input depth count).native.disposition support.1 _, rfl⟩
    demandEntryDisposition :=
      ⟨.transferred ((frame input depth count).native.disposition support.1 _) rfl rfl (Nat.le_refl _), rfl⟩ }

/-- This is an actual, causally carried target current.  Its next review
query is supplied by the enclosing decision source, not by repeating the
fee native write as an autonomous loop. -/
def targetState : RootInquiryStateAt (generated input depth count datum).target.TargetN
    (generated input depth count datum).target.TargetV where
  root := (generated input depth count datum).target.targetRoot
  visit := (generated input depth count datum).target.targetVisit
  U7 := targetU7 input depth count
  calculus := targetCalculus input depth count
  Query := PEmpty
  entryAt := fun impossible => impossible.elim
  authorityAt := fun impossible => impossible.elim
  compilationProgramAt := fun impossible => impossible.elim
  compilationFaceAt := fun impossible => impossible.elim
  u7RootDisposition_commutes := fun impossible => impossible.elim

def targetPresentation : RootInquiryStatePresentation :=
  ⟨(generated input depth count datum).target.TargetN,
    (generated input depth count datum).target.TargetV,
    RootInquiryEngineStateAt.create (targetState input depth count datum)⟩

theorem target_is_the_literal_generated_current :
    (targetPresentation input depth count datum).erase =
      ⟨(generated input depth count datum).target.TargetN,
        (generated input depth count datum).target.targetAnswerAndNext.nextCurrent⟩ := by
  rw [(generated input depth count datum).target.targetAnswerAndNext_next_eq]
  rfl

theorem actual_successor_valid (query : (presentation input depth count datum).Query) :
    ((RootInquiryProcessNode.active (targetPresentation input depth count datum)).erase =
        (RootInquiryProcessNode.answered (presentation input depth count datum) query).erase) ∧
      (RootInquiryProcessNode.active (presentation input depth count datum)).PreservesGeneratedLivingLawAt
        query (.active (targetPresentation input depth count datum)) :=
  RootInquiryProcessNode.active_actualAction_successor_valid
    (presentation input depth count datum) (targetPresentation input depth count datum) query
    (generated input depth count datum) (original_source_compiles_actual_action input depth count datum query)
    (target_is_the_literal_generated_current input depth count datum) HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Admission
