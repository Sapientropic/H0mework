import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

def previousInquiry : SourceNativeProjectionLaw (Sparse.Compiler.ledgerSource (code current)) where
  Projection := current.root.toAuthoritativeRoot.source.projectionLaw.Projection
  ActiveAt := fun projection {_} occurrence => current.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection
    (Sparse.Compiler.originalOccurrence (code current) occurrence)
  InactiveAt := fun projection {_} occurrence => current.root.toAuthoritativeRoot.source.projectionLaw.InactiveAt projection
    (Sparse.Compiler.originalOccurrence (code current) occurrence)
  classify := fun projection {_} occurrence => current.root.toAuthoritativeRoot.source.projectionLaw.classify projection
    (Sparse.Compiler.originalOccurrence (code current) occurrence)
  PayloadAt := fun projection {_} occurrence active => current.root.toAuthoritativeRoot.source.projectionLaw.PayloadAt projection
    (Sparse.Compiler.originalOccurrence (code current) occurrence) active
  project := fun projection {_} occurrence active => current.root.toAuthoritativeRoot.source.projectionLaw.project projection
    (Sparse.Compiler.originalOccurrence (code current) occurrence) active

def historyRoot := (Sparse.Compiler.livingRoot (code current)).withProjectionCoface (previousInquiry current)

/-- The new active context is admitted only on the actual source occurrence.
Historical queries keep their original meanings on every source fibre. -/
def activeContext : SourceNativeProjectionLaw (historyRoot current).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} occurrence => PLift
    (Sparse.Compiler.originalOccurrence (code current) occurrence = current.root.emitted current.visit.current)
  InactiveAt := fun _ {_} occurrence => PLift
    (Sparse.Compiler.originalOccurrence (code current) occurrence ≠ current.root.emitted current.visit.current)
  classify := by
    intro projection phase occurrence
    classical
    exact if same : Sparse.Compiler.originalOccurrence (code current) occurrence = current.root.emitted current.visit.current
      then .inl ⟨same⟩ else .inr ⟨same⟩
  PayloadAt := fun _ {_} _ _ => Source.Program.RawLaw Party Good Port Technology Instrument × List Party
  project := fun _ {phase} _ _ => effectiveAt current phase

def targetRoot := (historyRoot current).withProjectionCoface (activeContext current)

def oldProjection (projection : current.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    (targetRoot current).toAuthoritativeRoot.source.projectionLaw.Projection := .inherited (.component projection)

theorem every_old_query_is_retained (phase : Bool) (origin : (code current).Fibre)
    (projection : current.root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((targetRoot current).toAuthoritativeRoot.source.projectionLaw.outcomeAt (oldProjection current projection)
      (Sparse.Compiler.represented (code current) phase origin))
      (current.root.toAuthoritativeRoot.source.projectionLaw.outcomeAt projection origin) := by
  dsimp only [targetRoot,historyRoot,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeLivingRootClosure.toAuthoritativeRoot,SourceNativeAuthoritySource.withProjectionCoface,
    SourceNativeProjectionLaw.outcomeAt,oldProjection,previousInquiry,
    Sparse.Compiler.originalOccurrence,Sparse.Compiler.represented]
  cases current.root.source.base.projectionLaw.classify projection origin <;> rfl

def activeFace (visit : SourceNativeTemporalVisitAt (targetRoot current).toAuthoritativeRoot.toLedgerRoot) :
    SourceNativeRootSemanticFaceAt (targetRoot current) visit where
  projection := .component PUnit.unit
  active := ⟨rfl⟩
  classifier_eq := by
    classical
    change (if same : _ then _ else _) = _
    exact dif_pos rfl

theorem the_effective_context_is_the_active_source_face
    (visit : SourceNativeTemporalVisitAt (targetRoot current).toAuthoritativeRoot.toLedgerRoot) :
    (activeFace current visit).rootRead = effectiveAt current visit.current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
