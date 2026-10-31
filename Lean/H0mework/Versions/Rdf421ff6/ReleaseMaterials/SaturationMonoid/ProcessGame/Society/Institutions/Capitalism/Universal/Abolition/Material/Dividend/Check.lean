import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend.Trace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan
import Mathlib.Data.List.Dedup

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend

open Source.Program

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (baseline replacement : List (RawEvent Party Good Port Technology Instrument))

def comparisonCells : List (Party × Good) := (cells law current baseline ++ cells law current replacement).dedup

def delta (person : Party) (good : Good) : ℚ :=
  net law current replacement person good - net law current baseline person good

theorem dividend_is_one_actual_stock_difference (person : Party) (good : Good) :
    delta law current baseline replacement person good =
      (final law current replacement).stock person good - (final law current baseline).stock person good := by
  rw [final_stock_is_exact_net, final_stock_is_exact_net]
  unfold delta
  ring

def Checks : Prop :=
  NonFinancial (baseline ++ replacement) ∧
    (final law current replacement).clock ≤ (final law current baseline).clock ∧
    (∀ cell ∈ comparisonCells law current baseline replacement, 0 ≤ delta law current baseline replacement cell.1 cell.2) ∧
    ∃ cell ∈ comparisonCells law current baseline replacement, 0 < delta law current baseline replacement cell.1 cell.2

instance : Decidable (Checks law current baseline replacement) := by unfold Checks; infer_instance

inductive Issue : Type
  | financial (word : RawEvent Party Good Port Technology Instrument) (period : word ∈ baseline ++ replacement)
      (request : Request Party Good Port Technology Instrument) (original : request ∈ word)
      (unsupported : ¬ Root.Settlement.NonFinancialRequest request)
  | longerWindow (late : (final law current baseline).clock < (final law current replacement).clock)
  | hiddenLoser (cell : Party × Good) (affected : cell ∈ comparisonCells law current baseline replacement)
      (loss : delta law current baseline replacement cell.1 cell.2 < 0)
  | noStrictMaterialGain
      (nonpositive : ∀ cell ∈ comparisonCells law current baseline replacement,
        delta law current baseline replacement cell.1 cell.2 ≤ 0)

theorem Issue.refutes (issue : Issue law current baseline replacement) : ¬ Checks law current baseline replacement := by
  intro checked
  cases issue with
  | financial word period request original unsupported => exact unsupported (checked.1 word period request original)
  | longerWindow late => exact (not_le_of_gt late) checked.2.1
  | hiddenLoser cell affected loss => exact (not_le_of_gt loss) (checked.2.2.1 cell affected)
  | noStrictMaterialGain nonpositive =>
      obtain ⟨cell, affected, gain⟩ := checked.2.2.2
      exact (not_lt_of_ge (nonpositive cell affected)) gain

inductive Decision : Type
  | accepted (checked : Checks law current baseline replacement)
  | rejected (issue : Issue law current baseline replacement)

def check : Decision law current baseline replacement :=
  match inspectList Root.Settlement.NonFinancial (baseline ++ replacement) with
  | .failure word period failed =>
      match Root.Settlement.checkFinancial word with
      | .accepted safe => False.elim (failed safe)
      | .rejected request original unsupported => .rejected (.financial word period request original unsupported)
  | .clear financial =>
      if timely : (final law current replacement).clock ≤ (final law current baseline).clock then
        match inspectList (fun cell : Party × Good => 0 ≤ delta law current baseline replacement cell.1 cell.2)
            (comparisonCells law current baseline replacement) with
        | .failure cell affected loss => .rejected (.hiddenLoser cell affected (lt_of_not_ge loss))
        | .clear noLoss =>
            match inspectList (fun cell : Party × Good => delta law current baseline replacement cell.1 cell.2 ≤ 0)
                (comparisonCells law current baseline replacement) with
            | .clear noGain => .rejected (.noStrictMaterialGain noGain)
            | .failure cell affected gain => .accepted ⟨financial, timely, noLoss, cell, affected, lt_of_not_ge gain⟩
      else .rejected (.longerWindow (lt_of_not_ge timely))

def Decision.isAccepted (decision : Decision law current baseline replacement) : Bool :=
  match decision with | .accepted _ => true | .rejected _ => false

theorem check_accepts_iff :
    (check law current baseline replacement).isAccepted law current baseline replacement = true ↔
      Checks law current baseline replacement := by
  cases found : check law current baseline replacement with
  | accepted checked => exact ⟨fun _ => checked, fun _ => rfl⟩
  | rejected issue =>
      constructor
      · intro impossible; cases impossible
      · intro checked; exact (issue.refutes law current baseline replacement checked).elim

theorem all_bearers_and_goods_keep_their_material_share (checked : Checks law current baseline replacement)
    (person : Party) (good : Good) :
    (final law current baseline).stock person good ≤ (final law current replacement).stock person good := by
  have positive : 0 ≤ delta law current baseline replacement person good := by
    by_cases affected : (person, good) ∈ comparisonCells law current baseline replacement
    · exact checked.2.2.1 (person, good) affected
    · have absent : (person, good) ∉ cells law current baseline ∧ (person, good) ∉ cells law current replacement := by
        simpa only [comparisonCells, List.mem_dedup, List.mem_append, not_or] using affected
      rw [delta, no_effect_outside_actual_cells law current replacement person good absent.2,
        no_effect_outside_actual_cells law current baseline person good absent.1, sub_self]
  rw [final_stock_is_exact_net, final_stock_is_exact_net]
  exact add_le_add (le_refl _) (sub_nonneg.mp positive)

theorem one_real_unit_strictly_increases (checked : Checks law current baseline replacement) :
    ∃ person good, (final law current baseline).stock person good < (final law current replacement).stock person good := by
  obtain ⟨cell, affected, positive⟩ := checked.2.2.2
  refine ⟨cell.1, cell.2, ?_⟩
  rw [final_stock_is_exact_net, final_stock_is_exact_net]
  exact add_lt_add_of_le_of_lt (le_refl _) (sub_pos.mp positive)

theorem no_debt_reset_or_new_financial_claim (checked : Checks law current baseline replacement) :
    (final law current baseline).claims = current.claims ∧ (final law current replacement).claims = current.claims :=
  ⟨original_claims_are_retained law current baseline (fun word inside => checked.1 word (List.mem_append_left _ inside)),
    original_claims_are_retained law current replacement (fun word inside => checked.1 word (List.mem_append_right _ inside))⟩

#print axioms check
#print axioms dividend_is_one_actual_stock_difference
#print axioms check_accepts_iff
#print axioms all_bearers_and_goods_keep_their_material_share
#print axioms one_real_unit_strictly_increases
#print axioms no_debt_reset_or_new_financial_claim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Dividend
