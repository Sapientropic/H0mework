import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Local
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Selection

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Quota

open Institutions.Capitalism.Universal.Source.Program Distributed

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument) (position : Position Party Instrument)
  (current : RawCurrent Party Good Technology Instrument) (support : ℚ)

def quantity : ℚ := max 0 (min support (Repayment.quantity law position current))

def payment : Request Party Good Port Technology Instrument :=
  ⟨position.debtor, [], law.issuerPort position.instrument, [],
    .settle position.instrument position.debtor position.creditor (quantity law position current support)⟩

def candidate : RawEvent Party Good Port Technology Instrument :=
  Repayment.preparation law position current ++ [payment law position current support]

def Ready : Prop := 0 < quantity law position current support ∧
  ∀ item ∈ law.rawItems current (candidate law position current support), law.Valid item.before item.request

instance : Decidable (Ready law position current support) := by unfold Ready; infer_instance

theorem quantity_nonnegative : 0 ≤ quantity law position current support := le_max_left _ _

theorem quantity_is_supported (nonnegative : 0 ≤ support) :
    quantity law position current support ≤ support :=
  max_le nonnegative (min_le_left _ _)

structure Refusal where
  private mk ::
  item : ExecutionItem Party Good Port Technology Instrument
  original : item ∈ law.rawItems current (candidate law position current support)
  refused : ¬ law.Valid item.before item.request

inductive Outcome where
  | noSupportedPayment (zero : quantity law position current support = 0)
  | ready (paid : Ready law position current support)
  | blocked (positive : 0 < quantity law position current support) (failure : Refusal law position current support)

def generate : Outcome law position current support :=
  if positive : 0 < quantity law position current support then
    match inspect (fun item : ExecutionItem Party Good Port Technology Instrument => law.Valid item.before item.request)
        (law.rawItems current (candidate law position current support)) with
    | .accepted all => .ready ⟨positive, all⟩
    | .rejected item original refused => .blocked positive ⟨item, original, refused⟩
  else .noSupportedPayment (le_antisymm (le_of_not_gt positive) (quantity_nonnegative law position current support))

end SaturationMonoid.ProcessGame.Society.PublicFunction.Repayment.Quota
