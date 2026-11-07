import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix.Code

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (cut : frame.V.Current)

def oldCurrent : Option frame.V.Current → frame.V.Current
  | none => cut
  | some current => current

def oldOccurrence {phase : Option frame.V.Current}
    (occurrence : (Sparse.Compiler.source (code frame cut)).toRootSource.actual.OccurrenceAt phase) :
    frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt (oldCurrent frame cut phase) :=
  match phase with
  | none => Sparse.Compiler.originalOccurrence (code frame cut) occurrence
  | some current => frame.root.emitted current

def component : SourceNativeProjectionLaw (Sparse.Compiler.ledgerSource (code frame cut)) where
  Projection := frame.root.source.base.projectionLaw.Projection ⊕ Unit
  ActiveAt := fun projection {_} occurrence => match projection with
    | .inl old => frame.root.source.base.projectionLaw.ActiveAt old (oldOccurrence frame cut occurrence)
    | .inr _ => Unit
  InactiveAt := fun projection {_} occurrence => match projection with
    | .inl old => frame.root.source.base.projectionLaw.InactiveAt old (oldOccurrence frame cut occurrence)
    | .inr _ => PEmpty
  classify := fun projection {_} occurrence => match projection with
    | .inl old => frame.root.source.base.projectionLaw.classify old (oldOccurrence frame cut occurrence)
    | .inr _ => .inl ()
  PayloadAt := fun projection {phase} occurrence active => match projection with
    | .inl old => frame.root.source.base.projectionLaw.PayloadAt old (oldOccurrence frame cut occurrence) active
    | .inr _ => Σ original : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt (oldCurrent frame cut phase),
        SourceNativeLedgerEvolutionAt frame.root.toAuthoritativeRoot.toLedgerRoot.source.source original
  project := fun projection {_} occurrence active => match projection with
    | .inl old => frame.root.source.base.projectionLaw.project old (oldOccurrence frame cut occurrence) active
    | .inr _ => ⟨oldOccurrence frame cut occurrence,
        frame.root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile (oldOccurrence frame cut occurrence)⟩

def root := (Sparse.Compiler.livingRoot (code frame cut)).withProjectionCoface (component frame cut)

theorem every_dynamic_old_query_reads_its_original_current {phase : Option frame.V.Current}
    (occurrence : (Sparse.Compiler.source (code frame cut)).toRootSource.actual.OccurrenceAt phase)
    (projection : frame.root.source.base.projectionLaw.Projection) :
    HEq ((root frame cut).source.base.projectionLaw.outcomeAt (.component (.inl projection)) occurrence)
      (frame.root.source.base.projectionLaw.outcomeAt projection (oldOccurrence frame cut occurrence)) := by
  dsimp only [root,component,SourceNativeLivingRootClosure.withProjectionCoface,
    SourceNativeAuthoritySource.withProjectionCoface,SourceNativeProjectionLaw.outcomeAt]
  cases frame.root.source.base.projectionLaw.classify projection (oldOccurrence frame cut occurrence) <;> rfl

theorem dynamic_source_is_the_literal_original_occurrence (phase : Option frame.V.Current) :
    oldOccurrence frame cut ((root frame cut).emitted phase) = frame.root.emitted (oldCurrent frame cut phase) := by
  cases phase <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix
