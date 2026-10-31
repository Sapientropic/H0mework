import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion.Open

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  {source target : Evolution.Sparse.Current (oldN := oldN) claim}

theorem every_open_history_preserves_the_complete_old_world
    (history : Evolution.Sparse.History.Actual claim source target) :
    (Evolution.Sparse.Current.support claim target).1 = (Evolution.Sparse.Current.support claim source).1 := by
  induction history with
  | empty => rfl
  | step current programme input later inherited =>
      exact inherited.trans (Evolution.Sparse.the_entire_original_support_is_literal claim
        (Evolution.Sparse.Mechanism.native claim current programme input)
        (Evolution.Sparse.Mechanism.word claim current programme input))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Completion
