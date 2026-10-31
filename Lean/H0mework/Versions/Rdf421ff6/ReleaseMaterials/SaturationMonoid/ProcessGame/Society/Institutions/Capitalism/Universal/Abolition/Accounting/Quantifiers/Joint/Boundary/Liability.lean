import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Coalition.Restitution.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation Priority.Adequacy.Capacity.Inspection

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

inductive ResidualAt (after : Current seed claim) : Type
  | productive (key : Party × Good)
      (original : key ∈ Responsibility.Family.positiveScope mechanism past nature response)
      (unpaid : 0 < after.productive key)
  | gross (key : Entitlement.Duty.Key (Party := Party) (Good := Good))
      (original : key ∈ Entitlement.Duty.scope (window seed))
      (unpaid : 0 < after.gross key)

inductive DebtStatus (after : Current seed claim) : Type
  | paid (productive : Current.productivePaid seed claim after) (gross : Current.grossPaid seed claim after)
  | unpaid (issue : ResidualAt seed claim after)

def inspectDebt (after : Current seed claim) : DebtStatus seed claim after :=
  match inspectAll (fun key => after.productive key = 0)
    (Responsibility.Family.positiveScope mechanism past nature response) with
  | .blocked key original failed => .unpaid (.productive key original
      (lt_of_le_of_ne (after.productive_nonnegative key) (Ne.symm failed)))
  | .ready productive =>
    match inspectAll (fun key => after.gross key = 0) (Entitlement.Duty.scope (window seed)) with
    | .blocked key original failed => .unpaid (.gross key original
        (lt_of_le_of_ne (after.gross_nonnegative key) (Ne.symm failed)))
    | .ready gross => .paid productive gross

/-- The original two row matrices and independent need bearers are read at
the same actual next. Refusal itself creates no claim or new positive amount. -/
structure LiabilityAt (current : Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument) : Type where
  payment : DebtStatus seed claim (next seed claim current proposal)
  needs : Responsibility.Family.NeedDisposition (actualLaw seed) current.raw
    (executed seed claim current proposal) seed.current.members
  gross_allocation : ∀ key, (next seed claim current proposal).gross key +
    Coalition.Restitution.credits seed claim current (executed seed claim current proposal) key = current.gross key

def carryLiability (current : Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument) :
    LiabilityAt seed claim current proposal :=
  ⟨inspectDebt seed claim (next seed claim current proposal),
    Responsibility.Family.inspectNeeds (actualLaw seed) current.raw (executed seed claim current proposal) seed.current.members,
    Coalition.Restitution.the_actual_allocation_conserves_every_original_cell seed claim current
      (executed seed claim current proposal)⟩

theorem a_refused_attempt_cannot_reopen_either_original_paid_row
    (current : Current seed claim) (proposal : RawEvent Party Good Port Technology Instrument)
    (paid : Current.productivePaid seed claim current ∧ Current.grossPaid seed claim current) :
    Current.productivePaid seed claim (next seed claim current proposal) ∧
      Current.grossPaid seed claim (next seed claim current proposal) := by
  constructor
  · intro key original
    exact le_antisymm ((Current.actual_word_never_refills_productive seed claim current _ key).trans (paid.1 key original).le)
      ((next seed claim current proposal).productive_nonnegative key)
  · intro key original
    exact le_antisymm ((Current.actual_word_never_refills_gross seed claim current _ key).trans (paid.2 key original).le)
      ((next seed claim current proposal).gross_nonnegative key)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
