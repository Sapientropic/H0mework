import H0mework.Versions.R2.Foundation.Runtime.AnswerNext

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.QueryHistory

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

universe u

variable {OldN NewN : WorldRelationNetwork.{u}} {OldV NewV : ConstructiveRoot.Vocabulary.{u}}
  {source : SourceNativeLedgerSource OldN OldV} {current : OldV.Current}
  (law : SourceNativeProjectionLaw source)
  (past : source.source.toRootSource.actual.OccurrenceAt current)
  (target : SourceNativeLedgerSource NewN NewV)

/-- Preserve every dependent old query outcome as history of the new
representation. This component grants no new execution authority. -/
def freeze : SourceNativeProjectionLaw target where
  Projection := law.Projection
  ActiveAt := fun projection {_} _ => law.ActiveAt projection past
  InactiveAt := fun projection {_} _ => law.InactiveAt projection past
  classify := fun projection {_} _ => law.classify projection past
  PayloadAt := fun projection {_} _ active => law.PayloadAt projection past active
  project := fun projection {_} _ active => law.project projection past active

theorem every_frozen_outcome_is_the_same_original_dependent_outcome
    {next : NewV.Current} (occurrence : target.source.toRootSource.actual.OccurrenceAt next)
    (projection : law.Projection) :
    HEq ((freeze law past target).outcomeAt projection occurrence) (law.outcomeAt projection past) := by
  dsimp only [freeze,SourceNativeProjectionLaw.outcomeAt]
  cases law.classify projection past <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.QueryHistory
