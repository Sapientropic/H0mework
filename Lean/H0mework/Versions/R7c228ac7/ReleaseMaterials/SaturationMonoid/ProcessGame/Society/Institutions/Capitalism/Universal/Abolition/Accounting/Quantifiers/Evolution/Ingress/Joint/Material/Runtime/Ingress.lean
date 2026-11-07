import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private def rowsAtEq {N : WorldRelationNetwork} {before after : N.Support} (same : before = after) :
    ConstructiveRetract (OpenResponsibilityAt N before) (OpenResponsibilityAt N after) := by
  cases same
  exact ⟨id,id,fun _ => rfl⟩

private theorem rowsAtEq_heq {N : WorldRelationNetwork} {before after : N.Support} (same : before = after) :
    HEq (rowsAtEq same) (Financial.Installation.Ingress.identityTranslation N |>.oldOpenLedger before) := by
  cases same
  rfl

private theorem rowsAtEq_forward_backward {N : WorldRelationNetwork} {before after : N.Support}
    (same : before = after) (row : OpenResponsibilityAt N after) :
    (rowsAtEq same).forward ((rowsAtEq same).backward row) = row := by cases same; rfl

private theorem rowsAtEq_key {N : WorldRelationNetwork} {before after : N.Support}
    (same : before = after) (row : OpenResponsibilityAt N before) :
    ((rowsAtEq same).forward row).1 = row.1 := by cases same; rfl

private theorem rowsAtEq_claim {N : WorldRelationNetwork} {before after : N.Support}
    (same : before = after) (row : OpenResponsibilityAt N before) :
    ((rowsAtEq same).forward row).claim = row.claim := by cases same; rfl

private theorem rowsAtEq_budget {N : WorldRelationNetwork} {before after : N.Support}
    (same : before = after) (row : OpenResponsibilityAt N before) :
    ((rowsAtEq same).forward row).progressBudget = row.progressBudget := by cases same; rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def occurrencePresentation : ConstructivePresentation
    ((Origin.root seed claim).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (Admission.nextVisit seed claim).current)
    ((Inquiry.root seed claim).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (initial seed)) where
  forward := fun _ => (Inquiry.root seed claim).emitted (initial seed)
  backward := fun _ => (Origin.root seed claim).emitted (Admission.nextVisit seed claim).current
  backward_forward := fun occurrence =>
    (Abolition.Accounting.Root.Compiler.occurrence_eq_emitted (Admission.flow seed claim) occurrence).symm
  forward_backward := fun occurrence =>
    (Abolition.Accounting.Root.Compiler.occurrence_eq_emitted (flow seed claim) occurrence).symm

def initialLedger := rowsAtEq (Inquiry.the_initial_support_is_the_literal_original_declared_whole_account seed claim)

theorem initialLedger_heq : HEq (initialLedger seed claim)
    ((Financial.Installation.Ingress.identityTranslation (Admission.N seed claim)).oldOpenLedger
      ((Origin.root seed claim).toAuthoritativeRoot.toRoot.supportAt (Admission.nextVisit seed claim).current)) := rowsAtEq_heq _

theorem initialLedger_no_fresh (row : OpenResponsibilityAt (Admission.N seed claim) (support seed claim (initial seed))) :
    (initialLedger seed claim).forward ((initialLedger seed claim).backward row) = row := rowsAtEq_forward_backward _ _

theorem initialLedger_key (row) : ((initialLedger seed claim).forward row).1 = row.1 := rowsAtEq_key _ _
theorem initialLedger_claim (row) : ((initialLedger seed claim).forward row).claim = row.claim := rowsAtEq_claim _ _
theorem initialLedger_budget (row) : ((initialLedger seed claim).forward row).progressBudget = row.progressBudget := rowsAtEq_budget _ _

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
