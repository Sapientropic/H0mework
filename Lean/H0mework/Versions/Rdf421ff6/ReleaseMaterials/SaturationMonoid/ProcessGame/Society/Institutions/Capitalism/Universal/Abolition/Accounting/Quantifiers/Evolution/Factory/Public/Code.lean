import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Complete

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

/-- The public-context event changes the active interpreter, with no material
effect or discharge. Every existing support fibre and ledger entry is retained. -/
def code : Sparse.Compiler.Code N where
  Current := Bool
  Fibre := current.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.visit.current
  emission := current.root.emitted current.visit.current
  initial := false
  supportAt := fun _ origin => origin.1
  anchor_coherent := fun _ origin =>
    (current.root.toAuthoritativeRoot.toRoot.account.anchor_commutes _).symm.trans
      (current.root.toAuthoritativeRoot.toRoot.account.anchor_commutes origin)
  incidence_coherent := fun _ origin =>
    (current.root.toAuthoritativeRoot.toRoot.account.incidence_commutes _).symm.trans
      (current.root.toAuthoritativeRoot.toRoot.account.incidence_commutes origin)
  lineage_coherent := fun _ origin =>
    (current.root.toAuthoritativeRoot.toRoot.account.lineage_commutes _).symm.trans
      (current.root.toAuthoritativeRoot.toRoot.account.lineage_commutes origin)
  next := fun _ => true
  writes := fun phase => !phase
  evolution := fun _ _ => LedgerWriteEvolutionAt.identity _
  inverse_origin := fun _ _ _ => rfl
  inverse_destination := fun _ _ _ => rfl

abbrev V := Sparse.Compiler.V (code current)

theorem the_original_raw_world_support_is_literal (phase : Bool) :
    (code current).support phase = Context.support current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
