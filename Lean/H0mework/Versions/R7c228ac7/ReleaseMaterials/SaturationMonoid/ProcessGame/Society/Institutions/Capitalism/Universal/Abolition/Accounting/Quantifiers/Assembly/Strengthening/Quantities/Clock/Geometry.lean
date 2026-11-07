import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Planning
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.UBI.Capacity.CanonicalMaximumMatching
import Mathlib.Data.Fintype.Fin

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock

open Source.Program PublicFunction
open _root_.SaturationMonoid.ProcessGame.Society.UBI.Capacity

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- Original service slots match distinct original debit positions, with
the same law, signed operation and real clock at that position. -/
def geometryOf (law : RawLaw Party Good Port Technology Instrument)
    (task : PublicTaskSpec Party Good) (inventory : List (ExecutionItem Party Good Port Technology Instrument)) :
    CanonicalBipartiteFeasibility (Fin task.slots.length) (Fin inventory.length) where
  leftCarrier := Finset.univ.filter fun slot => (task.slots.get slot).goods ≠ []
  rightCarrier := Finset.univ
  Feasible := fun slot ordinal =>
    let need := task.slots.get slot
    let item := inventory.get ordinal
    task.earliest ≤ item.before.clock ∧ law.Valid item.before item.request ∧
      Exit.Necessity.UseMatches item.request.operation need.bearer need.goods need.purpose
  feasibleDecidable := fun slot ordinal => by
    let need := task.slots.get slot
    let item := inventory.get ordinal
    exact inferInstanceAs (Decidable (task.earliest ≤ item.before.clock ∧ law.Valid item.before item.request ∧
      Exit.Necessity.UseMatches item.request.operation need.bearer need.goods need.purpose))

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock
