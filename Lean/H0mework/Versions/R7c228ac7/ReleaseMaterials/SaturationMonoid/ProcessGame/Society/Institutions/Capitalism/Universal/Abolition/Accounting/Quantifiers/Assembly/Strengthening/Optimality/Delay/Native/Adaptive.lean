import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native.Source
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Adaptive

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native

open Source.Program Innovation
noncomputable section
attribute [local irreducible] Joint.actualLaw

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Joint.window seed))

theorem no_original_retirement_proposal_mints_full_income (current : Joint.Current seed claim)
    (proposal : RawEvent Party Good Port Technology Instrument)
    (retirement : ∀ request ∈ proposal, RetirementRequest request) : incomeAt seed claim current proposal = 0 := by
  apply every_retirement_program_has_zero_full_income
  intro request actual
  apply retirement request
  rw [Joint.Boundary.the_submitted_word_keeps_the_actual_prefix_and_unexecuted_suffix seed claim current proposal]
  exact List.mem_append_left _ actual

theorem every_original_retirement_history_has_zero_full_income
    (current : Joint.Current seed claim) (inputs : List (RawEvent Party Good Port Technology Instrument))
    (retirement : ∀ proposal ∈ inputs, ∀ request ∈ proposal, RetirementRequest request) :
    income seed claim current inputs = 0 := by
  induction inputs generalizing current with
  | nil => rfl
  | cons proposal rest inherited =>
      change incomeAt seed claim current proposal + income seed claim (Joint.Boundary.next seed claim current proposal) rest = 0
      rw [no_original_retirement_proposal_mints_full_income seed claim current proposal
        (retirement proposal List.mem_cons_self),
        inherited _ (fun next listed => retirement next (List.mem_cons_of_mem _ listed)),add_zero]

theorem an_arbitrary_adaptive_retirement_strategy_cannot_gain_at_any_unpaid_prefix
    (opening : Joint.Current seed claim) (policy : Strategy seed claim)
    (retirement : ∀ past current request, request ∈ policy past current → RetirementRequest request)
    (ticks : Nat) (members : Party → Bool) (good : Good) :
    Coalition.read members good (income seed claim opening (observe seed claim policy opening ticks).2) = 0 := by
  have only : ∀ proposal ∈ (observe seed claim policy opening ticks).2,
      ∀ request ∈ proposal, RetirementRequest request := by
    induction ticks with
    | zero => simp only [observe,List.not_mem_nil,false_implies,implies_true]
    | succ ticks inherited =>
        intro proposal listed request requested
        rcases List.mem_append.mp listed with earlier | last
        · exact inherited proposal earlier request requested
        · have same := List.mem_singleton.mp last
          cases same
          exact retirement _ _ request requested
  rw [every_original_retirement_history_has_zero_full_income seed claim opening _ only,map_zero]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Optimality.Delay.Native
