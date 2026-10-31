import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Allocation.Bounds

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint

open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (window seed))

/-- One source-owned live material cursor. Rebased row states refer to this
same value; neither row retains an independently spendable raw projection. -/
structure Current
    (scope : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
    (_receipt : Entitlement.Source.Claim (window scope)) where
  private mk ::
  raw : RawCurrent Party Good Technology Instrument
  productive : Party × Good → ℚ
  productive_nonnegative : ∀ key, 0 ≤ productive key
  productive_outside : ∀ key, key ∉ Responsibility.Family.positiveScope mechanism past nature response → productive key = 0
  productiveDeclared : Bool
  gross : Entitlement.Duty.Key (Party := Party) (Good := Good) → ℚ
  gross_nonnegative : ∀ key, 0 ≤ gross key
  grossDeclared : Bool

namespace Current

def initial : Current seed grossClaim :=
  ⟨currentRaw seed,(productiveState seed).remaining,(productiveState seed).nonnegative,
    (productiveState seed).outside,(productiveState seed).declared,
    (Entitlement.Duty.State.initial grossClaim).remaining,
    (Entitlement.Duty.State.initial grossClaim).nonnegative,false⟩

def declareGross (current : Current seed grossClaim) : Current seed grossClaim := { current with grossDeclared := true }

def productivePaid (current : Current seed grossClaim) : Prop :=
  ∀ key ∈ Responsibility.Family.positiveScope mechanism past nature response, current.productive key = 0

def grossPaid (current : Current seed grossClaim) : Prop :=
  ∀ key ∈ Entitlement.Duty.scope (window seed), current.gross key = 0

instance (current : Current seed grossClaim) : Decidable (productivePaid seed grossClaim current) := by
  unfold productivePaid
  infer_instance

instance (current : Current seed grossClaim) : Decidable (grossPaid seed grossClaim current) := by
  unfold grossPaid
  infer_instance

def productiveBudget (current : Current seed grossClaim) : Nat :=
  if current.productiveDeclared then if productivePaid seed grossClaim current then 0 else 1 else 2

def grossBudget (current : Current seed grossClaim) : Nat :=
  if current.grossDeclared then if grossPaid seed grossClaim current then 0 else 1 else 2

theorem the_initial_cursor_is_the_actual_current_source :
    (initial seed grossClaim).raw = (productiveState seed).raw ∧
      (initial seed grossClaim).productive = (productiveState seed).remaining ∧
      (initial seed grossClaim).productiveDeclared = (productiveState seed).declared := ⟨rfl,rfl,rfl⟩

theorem the_productive_initial_budget_is_literal :
    productiveBudget seed grossClaim (initial seed grossClaim) =
      (Responsibility.Family.activationLaw seed.claim).budget (productiveState seed) := rfl

theorem declaring_gross_spends_no_material_and_no_productive_quota (current : Current seed grossClaim) :
    (declareGross seed grossClaim current).raw = current.raw ∧
      (declareGross seed grossClaim current).productive = current.productive ∧
      (declareGross seed grossClaim current).gross = current.gross ∧
      productiveBudget seed grossClaim (declareGross seed grossClaim current) = productiveBudget seed grossClaim current :=
  ⟨rfl,rfl,rfl,rfl⟩

def analysis (current : Current seed grossClaim) (word : RawEvent Party Good Port Technology Instrument) :=
  Allocation.run seed current.productive current.productiveDeclared current.grossDeclared
    current.gross current.gross_nonnegative current.raw word

/-- Execute the physical word once, then project its source allocation.
The row matrices never execute their own copy of that word. -/
def advance (current : Current seed grossClaim) (word : RawEvent Party Good Port Technology Instrument) :
    Current seed grossClaim :=
  let computed := analysis seed grossClaim current word
  ⟨(actualLaw seed).next current.raw word,
    (fun key => max 0 (current.productive key - max 0 (computed.netProductive key))),
    (fun _ => le_max_left _ _),
    (by
      intro key outside
      rw [current.productive_outside key outside]
      apply max_eq_left
      simpa only [zero_sub] using
        neg_nonpos.mpr (le_max_left (0 : ℚ) (computed.netProductive key))),
    current.productiveDeclared,computed.gross,computed.gross_nonnegative,current.grossDeclared⟩

theorem actual_word_has_only_one_material_successor (current : Current seed grossClaim)
    (word : RawEvent Party Good Port Technology Instrument) :
    (advance seed grossClaim current word).raw = (actualLaw seed).next current.raw word := rfl

theorem actual_word_never_refills_productive (current : Current seed grossClaim)
    (word : RawEvent Party Good Port Technology Instrument) (key : Party × Good) :
    (advance seed grossClaim current word).productive key ≤ current.productive key :=
  max_le (current.productive_nonnegative key) (sub_le_self _ (le_max_left _ _))

theorem actual_word_never_refills_gross (current : Current seed grossClaim)
    (word : RawEvent Party Good Port Technology Instrument)
    (key : Entitlement.Duty.Key (Party := Party) (Good := Good)) :
    (advance seed grossClaim current word).gross key ≤ current.gross key :=
  Allocation.actual_source_run_never_refills_gross seed _ _ _ _ _ current.raw word key

end Current
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint
