import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Occurrence
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

abbrev targetV := Compiler.V (code claim current word)

/-- Every old face is retained as the exact historical source reading. The
updated native row is the sole live physical cursor. -/
def previousInquiry : SourceNativeProjectionLaw (Compiler.ledgerSource (code claim current word)) where
  Projection := current.root.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_} occurrence => current.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection
    (Compiler.originalOccurrence (code claim current word) occurrence)
  InactiveAt := fun projection {_} occurrence => current.root.toAuthoritativeRoot.source.projectionLaw.InactiveAt projection
    (Compiler.originalOccurrence (code claim current word) occurrence)
  classify := fun projection {_} occurrence => current.root.toAuthoritativeRoot.source.projectionLaw.classify projection
    (Compiler.originalOccurrence (code claim current word) occurrence)
  PayloadAt := fun projection {_} occurrence active => current.root.toAuthoritativeRoot.source.projectionLaw.PayloadAt projection
    (Compiler.originalOccurrence (code claim current word) occurrence) active
  project := fun projection {_} occurrence active => current.root.toAuthoritativeRoot.source.projectionLaw.project projection
    (Compiler.originalOccurrence (code claim current word) occurrence) active

def targetRoot := (Compiler.livingRoot (code claim current word)).withProjectionCoface (previousInquiry claim current word)

def oldProjection (projection : current.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (targetRoot claim current word).toAuthoritativeRoot.source.projectionLaw.Projection := .component projection

theorem oldProjection_injective : Function.Injective (oldProjection claim current word) := by
  intro left right same
  injection same

theorem every_source_fibre_query_is_retained (phase : Bool)
    (origin : Fibre.Origin claim current)
    (projection : current.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((targetRoot claim current word).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection claim current word projection) (Compiler.represented (code claim current word) phase origin))
      (current.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection origin) := by
  dsimp only [targetRoot,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt,oldProjection,previousInquiry,
    Compiler.originalOccurrence,Compiler.represented]
  cases current.root.source.base.projectionLaw.classify projection origin <;> rfl

theorem every_old_query_is_retained (phase : Bool)
    (projection : current.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((targetRoot claim current word).toAuthoritativeRoot.source.projectionLaw.outcomeAt
      (oldProjection claim current word projection) ((targetRoot claim current word).emitted phase))
      (current.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection
        (current.root.emitted current.visit.current)) :=
  every_source_fibre_query_is_retained claim current word phase
    (current.root.emitted current.visit.current) projection

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
