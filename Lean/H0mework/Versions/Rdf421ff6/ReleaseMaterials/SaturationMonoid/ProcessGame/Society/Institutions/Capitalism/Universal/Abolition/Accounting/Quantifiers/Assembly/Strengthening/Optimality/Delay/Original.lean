import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay

open Source.Program Innovation
noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

theorem every_program_retains_both_original_residual_matrices
    (current : Joint.Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    (∀ key, (Joint.Boundary.afterInputs seed claim current inputs).productive key ≤ current.productive key) ∧
      (∀ key, (Joint.Boundary.afterInputs seed claim current inputs).gross key ≤ current.gross key) := by
  induction inputs generalizing current with
  | nil => exact ⟨fun _ => le_rfl,fun _ => le_rfl⟩
  | cons input rest inherited =>
      have later := inherited (Joint.Boundary.next seed claim current input)
      exact ⟨fun key => (later.1 key).trans
          (Joint.Current.actual_word_never_refills_productive seed claim current _ key),
        fun key => (later.2 key).trans (Joint.Current.actual_word_never_refills_gross seed claim current _ key)⟩

theorem the_observed_words_have_the_same_single_material_successor
    (current : Joint.Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    Coalition.Restitution.afterWords seed claim current (executedWords seed claim current inputs) =
      Joint.Boundary.afterInputs seed claim current inputs := by
  induction inputs generalizing current with
  | nil => rfl
  | cons input rest inherited =>
      change Coalition.Restitution.afterWords seed claim (Joint.Boundary.next seed claim current input)
        (executedWords seed claim (Joint.Boundary.next seed claim current input) rest) = _
      exact inherited _

theorem the_original_declared_rows_are_not_reset_by_any_program
    (current : Joint.Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    (Joint.Boundary.afterInputs seed claim current inputs).productiveDeclared = current.productiveDeclared ∧
      (Joint.Boundary.afterInputs seed claim current inputs).grossDeclared = current.grossDeclared := by
  induction inputs generalizing current with
  | nil => exact ⟨rfl,rfl⟩
  | cons input rest inherited => exact inherited (Joint.Boundary.next seed claim current input)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay
