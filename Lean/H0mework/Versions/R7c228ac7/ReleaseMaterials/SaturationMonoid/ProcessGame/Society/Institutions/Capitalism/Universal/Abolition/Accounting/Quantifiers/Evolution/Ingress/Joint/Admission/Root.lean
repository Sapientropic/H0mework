import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.QueryHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def previousInquiry := QueryHistory.freeze (Origin.root seed grossClaim).source.base.projectionLaw
  ((Origin.root seed grossClaim).emitted (sourceVisit seed grossClaim).current)
  (baseRoot seed grossClaim).toAuthoritativeRoot.toLedgerRoot.source

def root := (baseRoot seed grossClaim).withProjectionCoface (previousInquiry seed grossClaim)

def oldProjection (projection : (Origin.root seed grossClaim).source.base.projectionLaw.Projection) :
    (root seed grossClaim).source.base.projectionLaw.Projection := .component projection

theorem oldProjection_injective : Function.Injective (oldProjection seed grossClaim) := by
  intro left right same
  injection same

theorem every_original_query_outcome_is_retained
    (projection : (Origin.root seed grossClaim).source.base.projectionLaw.Projection) :
    HEq ((root seed grossClaim).source.base.projectionLaw.outcomeAt (oldProjection seed grossClaim projection)
      ((root seed grossClaim).emitted false))
      ((Origin.root seed grossClaim).source.base.projectionLaw.outcomeAt projection
        ((Origin.root seed grossClaim).emitted (sourceVisit seed grossClaim).current)) := by
  exact ((SourceNativeProjectionLaw.InstallationAt.componentCoface
    (baseRoot seed grossClaim).source.base (previousInquiry seed grossClaim)).outcome_heq
      ((baseRoot seed grossClaim).emitted false) projection).trans
    (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome _ _ _ _ projection)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Admission
