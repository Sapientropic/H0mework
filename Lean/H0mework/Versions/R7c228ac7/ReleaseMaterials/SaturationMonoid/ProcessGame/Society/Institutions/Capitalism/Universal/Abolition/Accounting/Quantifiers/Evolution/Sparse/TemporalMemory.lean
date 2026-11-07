import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Current

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLedgerRootClosure N V)

/-- A readout of registered past positions. A boundary retains the original
source event, rather than relabelling the new representation's first step. -/
inductive View : Type
  | finite (positions : List V.Current)
  | postCofinal (past : SourceNativeCofinalVisitAt root) (positions : List V.Current)

private def append (view : View root) (next : V.Current) : View root := match view with
  | .finite positions => .finite (positions ++ [next])
  | .postCofinal past positions => .postCofinal past (positions ++ [next])

private def finitePositions {current : V.Current} (history : root.toRoot.ReachableAt current) : List V.Current := by
  induction history with
  | initial => exact [root.toRoot.source.initial]
  | @step before next prior next_eq inherited => exact inherited ++ [next]

private def postView {current : V.Current} (history : SourceNativePostCofinalReachableAt root current) : View root := by
  induction history with
  | cofinal past => exact .postCofinal past [past.current]
  | @step before next prior next_eq inherited => exact append root inherited next

def read (visit : SourceNativeTemporalVisitAt root) : View root := match visit.history with
  | .finite history => .finite (finitePositions root history)
  | .postCofinal history => postView root history

def View.cofinalPast? : View root → Option (SourceNativeCofinalVisitAt root)
  | .finite _ => none
  | .postCofinal past _ => some past

theorem every_recorded_boundary_is_the_original_source_event (view : View root)
    (past : SourceNativeCofinalVisitAt root) (_recorded : view.cofinalPast? root = some past) :
    V.cofinal.emit? = some past.event := past.emitted_eq_event

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TemporalMemory
