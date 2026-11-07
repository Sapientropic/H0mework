import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Context

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program Innovation Quantifiers.Joint

noncomputable section

private def normalizeVisit {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLedgerRootClosure N V} (visit : SourceNativeTemporalVisitAt root)
    (current : V.Current) (same : visit.current = current) : SourceNativeTemporalVisitAt root :=
  ⟨current,same ▸ visit.history⟩

private theorem normalizeVisit_eq {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    {root : SourceNativeLedgerRootClosure N V} (visit : SourceNativeTemporalVisitAt root)
    (current : V.Current) (same : visit.current = current) : normalizeVisit visit current same = visit := by
  cases same
  rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

/-- Normalize only the displayed coordinate; the sealed chronological
history is transported unchanged. -/
def cut := normalizeVisit (nextVisit seed grossClaim) Stage.entered
  (Abolition.Accounting.Root.Compiler.successor_current (flow seed grossClaim) Stage.pending)

theorem cut_is_the_same_actual_visit : cut seed grossClaim = nextVisit seed grossClaim :=
  normalizeVisit_eq _ _ _

def cutRowAndAuthority : Sigma fun row : OpenResponsibilityAt (NewN seed grossClaim)
    ((root seed grossClaim).toAuthoritativeRoot.toRoot.supportAt (cut seed grossClaim).current) =>
    SourceNativeLivingTemporalCausalEntryAuthorityAt (root seed grossClaim) (cut seed grossClaim) row :=
  (cut_is_the_same_actual_visit seed grossClaim).symm ▸
    ⟨nextRow seed grossClaim,nextAuthority seed grossClaim⟩

def cutRow := (cutRowAndAuthority seed grossClaim).1
def cutAuthority := (cutRowAndAuthority seed grossClaim).2

theorem cut_still_reads_the_single_original_live_raw :
    (rawFace seed grossClaim (cut seed grossClaim)).rootRead = currentRaw seed := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
