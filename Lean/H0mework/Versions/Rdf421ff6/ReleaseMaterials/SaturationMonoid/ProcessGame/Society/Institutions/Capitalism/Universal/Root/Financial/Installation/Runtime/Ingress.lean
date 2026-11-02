import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Successor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth : Nat)

def ingressState : RootInquiryStateAt (ProgrammeSource.N input) (ProgrammeSource.V input) where
  root := Ingress.sourceRoot input
  visit := Ingress.sourceVisit input depth
  U7 := ProgrammeLiving.inquiryU7 input
  calculus := ProgrammeLiving.inquiryCalculus input
  Query := PUnit
  entryAt := fun _ => Ingress.sourceEntry input depth
  authorityAt := fun _ => Ingress.sourceAuthority input depth
  compilationProgramAt := fun query => by
    cases query
    exact { compile := fun _ => .actualAction (Ingress.generated input depth) }
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .inquiry, active := (), classifier_eq := rfl, project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    cases query
    cases audited

def ingressPresentation : RootInquiryStatePresentation :=
  ⟨ProgrammeSource.N input, ProgrammeSource.V input,
    RootInquiryEngineStateAt.create (ingressState input depth)⟩

theorem ingress_keeps_original_current :
    (ingressPresentation input depth).erase = (ProgrammeInquiry.presentationAt input (depth + 1)).erase := rfl

theorem ingress_compiles : (ingressState input depth).compileInquiry PUnit.unit =
    .actualAction (Ingress.generated input depth) := rfl

theorem ingress_target_erase : ((initialFrame input depth).presentation input).erase =
    (⟨(Ingress.generated input depth).target.TargetN,
      (Ingress.generated input depth).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) := by
  rw [(Ingress.generated input depth).target.targetAnswerAndNext_next_eq]
  rfl

theorem ingress_successor_valid (query : (ingressPresentation input depth).Query) :
    ((initialFrame input depth).presentation input).erase =
        (RootInquiryProcessNode.answered (ingressPresentation input depth) query).erase ∧
      (RootInquiryProcessNode.active (ingressPresentation input depth)).PreservesGeneratedLivingLawAt
        query (.active ((initialFrame input depth).presentation input)) := by
  cases query
  exact RootInquiryProcessNode.active_actualAction_successor_valid
    (ingressPresentation input depth) ((initialFrame input depth).presentation input) PUnit.unit
    (Ingress.generated input depth) (ingress_compiles input depth)
    (ingress_target_erase input depth) HEq.rfl

theorem ingress_ne_frame (frame : Frame input) :
    (ingressPresentation input depth).erase ≠ (frame.presentation input).erase := by
  intro same
  have cards := congrArg erasedProjectionCard same
  change Nat.card ProgrammeLiving.Projection =
    Nat.card frame.native.root.toAuthoritativeRoot.source.projectionLaw.Projection at cards
  rw [programme_projection_card] at cards
  have large := frame.projectionLarge
  omega

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
