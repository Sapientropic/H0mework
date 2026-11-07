import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Target

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)

def program : SourceNativeSequentialActualActionProgramAt
    (root (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)
    (Continuation.sourceEntry input (frame input depth sourceStart))
    (authority (review := review) input depth sourceStart datum prefixLimit renewalLimit) where
  targetAt := targetAt (review := review) input depth sourceStart datum prefixLimit renewalLimit reader

def sourceEvent := (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)

def generated := (program (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).generate
  (sourceEvent (review := review) input depth sourceStart datum prefixLimit renewalLimit)

def compilation (query : Query input depth sourceStart datum prefixLimit renewalLimit)
    (event : ExactTemporalCausalRootEventAt
      (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).toAuthoritativeRoot.toLedgerRoot
      (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)) :
    SourceNativeInquiryCompilationAt (root (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (frame input depth sourceStart).installed.U7 (frame input depth sourceStart).installed.calculus
      (root (review := review) input depth sourceStart datum prefixLimit renewalLimit).source.base.lawSurface query
      (ULift.up.{1, 0} ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current))
      (Continuation.sourceEntry input (frame input depth sourceStart))
      (authority (review := review) input depth sourceStart datum prefixLimit renewalLimit) :=
  .actualAction ((program (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).generate event)

def compilationFace (query : Query input depth sourceStart datum prefixLimit renewalLimit) :
    SourceNativeRootInquiryCompilationFaceCoreAt (root (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (visit (review := review) input depth sourceStart datum prefixLimit renewalLimit) query
      (ULift.up.{1, 0} ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current))
      (Continuation.sourceEntry input (frame input depth sourceStart))
      (authority (review := review) input depth sourceStart datum prefixLimit renewalLimit)
      (compilation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader query
        (sourceEvent (review := review) input depth sourceStart datum prefixLimit renewalLimit)) := by
  cases germ_unique input depth sourceStart datum prefixLimit renewalLimit
    ((frame input depth sourceStart).native.root.emitted (frame input depth sourceStart).visit.current) query
  exact {
    projection := (installation (review := review) input depth sourceStart datum prefixLimit renewalLimit).embed .compilation
    active := ()
    classifier_eq := rfl
    project_heq := HEq.rfl }

def state : RootInquiryStateAt (frame input depth sourceStart).native.N (frame input depth sourceStart).native.V where
  root := root (review := review) input depth sourceStart datum prefixLimit renewalLimit
  visit := visit (review := review) input depth sourceStart datum prefixLimit renewalLimit
  U7 := (frame input depth sourceStart).installed.U7
  calculus := (frame input depth sourceStart).installed.calculus
  Query := Query input depth sourceStart datum prefixLimit renewalLimit
  entryAt := fun _ => Continuation.sourceEntry input (frame input depth sourceStart)
  authorityAt := fun _ => authority (review := review) input depth sourceStart datum prefixLimit renewalLimit
  compilationProgramAt := fun query => { compile := compilation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader query }
  compilationFaceAt := compilationFace (review := review) input depth sourceStart datum prefixLimit renewalLimit reader
  u7RootDisposition_commutes := by intro query obstruction audit audited; cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨(frame input depth sourceStart).native.N, (frame input depth sourceStart).native.V,
    RootInquiryEngineStateAt.create (state (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)⟩

def nextVisit : SourceNativeTemporalVisitAt
    (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot.toLedgerRoot :=
  (SourceNativeTemporalVisitAt.finite (targetInitial (review := review) input depth sourceStart datum prefixLimit renewalLimit reader)).next
    (firstSuccessor (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).next_eq

theorem registered_input_compiles_the_same_source_action
    (query : (presentation (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).Query) :
    (state (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).compileInquiry query =
      .actualAction (generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader) := rfl

theorem full_target_living_law_is_fixed_before_first_write :
    (generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).target.targetRoot =
      (Inquiry.basePackage (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
        depth (cut input depth sourceStart) Physical.initial
        (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0 reader datum.nativeOrigin).frame.root := rfl

theorem actual_action_returns_the_literal_next_visit :
    (generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).target.targetAnswerAndNext.nextCurrent =
      ⟨Accounting.V (review := review) input depth (cut input depth sourceStart) prefixLimit renewalLimit
          depth (cut input depth sourceStart) Physical.initial
          (proposal (review := review) input depth sourceStart datum prefixLimit renewalLimit) 0,
        (targetRoot (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).toAuthoritativeRoot,
        nextVisit (review := review) input depth sourceStart datum prefixLimit renewalLimit reader⟩ :=
  (generated (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).target.canonical_targetNextVisit_eq

theorem next_visit_is_the_original_body_target :
    (nextVisit (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).current =
      bodyNext (review := review) input depth sourceStart datum prefixLimit renewalLimit :=
  first_target_is_the_source_body_next (review := review) input depth sourceStart datum prefixLimit renewalLimit reader

theorem first_inquiry_keeps_the_same_drained_account :
    (nextVisit (review := review) input depth sourceStart datum prefixLimit renewalLimit reader).current.account =
      Epoch.Finance.Legacy.generated input depth (cut input depth sourceStart)
        ((frame input depth sourceStart).cursor input).account := by
  rw [next_visit_is_the_original_body_target (review := review)]
  exact (the_first_body_keeps_the_actual_drained_account_and_full_inventory (review := review) input depth sourceStart datum prefixLimit renewalLimit).2.1

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.registered_input_compiles_the_same_source_action
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.full_target_living_law_is_fixed_before_first_write
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.actual_action_returns_the_literal_next_visit
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.first_inquiry_keeps_the_same_drained_account
