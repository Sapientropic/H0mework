import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry.Fields

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def root := (priorRoot seed claim).withProjectionCoface (component seed claim)

def historyInstallation :=
  (SourceNativeProjectionLaw.InstallationAt.componentCoface (baseRoot seed claim).source.base (previous seed claim)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (priorRoot seed claim).source.base (component seed claim))

def oldProjection := (historyInstallation seed claim).embed

theorem oldProjection_injective : Function.Injective (oldProjection seed claim) :=
  (historyInstallation seed claim).embed_injective

theorem every_original_query_outcome_is_retained
    (projection : (Origin.root seed claim).source.base.projectionLaw.Projection) :
    HEq ((root seed claim).source.base.projectionLaw.outcomeAt (oldProjection seed claim projection)
      ((root seed claim).emitted (initial seed)))
      ((Origin.root seed claim).source.base.projectionLaw.outcomeAt projection
        ((Origin.root seed claim).emitted (Admission.nextVisit seed claim).current)) :=
  ((historyInstallation seed claim).outcome_heq ((baseRoot seed claim).emitted (initial seed)) projection).trans
    (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome _ _ _ _ projection)

theorem the_initial_support_is_the_literal_original_declared_whole_account :
    (Origin.root seed claim).toAuthoritativeRoot.toRoot.supportAt (Admission.nextVisit seed claim).current =
      support seed claim (initial seed) :=
  (Admission.the_actual_next_has_one_shared_declared_current seed claim).trans
    (congrArg (fun old => (old,some (Material.shared seed claim)))
      (Admission.the_old_side_of_the_declaration_already_uses_the_same_shared_pointer seed claim))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Inquiry
