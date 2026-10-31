import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.Stable
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Scan

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance

open Source.Program

inductive Mode where
  | closed
  | accumulating
  deriving DecidableEq

def Mode.cellPass (mode : Mode) (debit credit : ℚ) : Prop :=
  match mode with | .closed => debit = credit | .accumulating => debit ≤ credit

instance (mode : Mode) (debit credit : ℚ) : Decidable (mode.cellPass debit credit) := by
  cases mode <;> unfold Mode.cellPass <;> infer_instance

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (mode : Mode) (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (word : RawEvent Party Good Port Technology Instrument)

def FiniteChecks : Prop :=
  StableWord word ∧ ∀ cell ∈ cells law current word,
    mode.cellPass (law.totalDebit (law.rawItems current word) cell.1 cell.2)
      (law.totalCredit (law.rawItems current word) cell.1 cell.2)

instance : Decidable (FiniteChecks mode law current word) := by unfold FiniteChecks; infer_instance

/-- Unsupported financial or technology changes remain original requests;
an imbalance names the exact materially affected party/good cell. Neither
case asserts that no different migration or production recipe can work. -/
inductive Issue : Type
  | unsupported (request : Request Party Good Port Technology Instrument)
      (original : request ∈ word) (unstable : ¬ StableRequest request)
  | imbalance (cell : Party × Good) (original : cell ∈ cells law current word)
      (failed : ¬ mode.cellPass (law.totalDebit (law.rawItems current word) cell.1 cell.2)
        (law.totalCredit (law.rawItems current word) cell.1 cell.2))

theorem Issue.refutes (issue : Issue mode law current word) : ¬ FiniteChecks mode law current word := by
  intro checked
  cases issue with
  | unsupported request original unstable => exact unstable (checked.1 request original)
  | imbalance cell original failed => exact failed (checked.2 cell original)

inductive Decision : Type
  | accepted (checked : FiniteChecks mode law current word)
  | rejected (issue : Issue mode law current word)

def check : Decision mode law current word :=
  match inspectList StableRequest word with
  | .failure request original unstable => .rejected (.unsupported request original unstable)
  | .clear stable =>
      match inspectList (fun cell : Party × Good =>
          mode.cellPass (law.totalDebit (law.rawItems current word) cell.1 cell.2)
            (law.totalCredit (law.rawItems current word) cell.1 cell.2)) (cells law current word) with
      | .failure cell original failed => .rejected (.imbalance cell original failed)
      | .clear balanced => .accepted ⟨stable, balanced⟩

def Decision.isAccepted (decision : Decision mode law current word) : Bool :=
  match decision with | .accepted _ => true | .rejected _ => false

theorem accepts_iff : (check mode law current word).isAccepted mode law current word = true ↔
    FiniteChecks mode law current word := by
  cases outcome : check mode law current word with
  | accepted checked => exact ⟨fun _ => checked, fun _ => rfl⟩
  | rejected issue =>
      constructor
      · intro impossible
        cases impossible
      · intro checked
        exact (issue.refutes mode law current word checked).elim

theorem checked_word_is_nonfinancial (checked : FiniteChecks mode law current word) :
    Root.Settlement.NonFinancial word :=
  fun request present => (checked.1 request present).1

/-- A successful finite scan computes the whole-state closure used by the
continuation theorem. The caller supplies no endpoint equality. -/
theorem checked_closed_period (checked : FiniteChecks .closed law current word) :
    (law.execute current 0 word).final = current :=
  finite_balance_generates_closed_period law current word checked.1 checked.2

theorem checked_productive_period (checked : FiniteChecks .accumulating law current word) :
    (law.execute current 0 word).final = current.addReserve (gain law current word) ∧
      ∀ person good, 0 ≤ gain law current word person good :=
  ⟨generated_gain_endpoint law current word checked.1,
    regenerative_gain_nonnegative law current word checked.2⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.check
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.accepts_iff
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Balance.checked_closed_period
