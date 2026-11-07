import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Reserve

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve

open Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good]
  (law : RawLaw Party Good Port Technology Instrument)
  (current : RawCurrent Party Good Technology Instrument)
  (request : Request Party Good Port Technology Instrument)

def NonmaterialGuards : Prop :=
  (RawLaw.SignerMatches request ∧ law.operationAllowed current request = true) ∧
    (∀ port ∈ law.requiredPorts current request,
      law.allowed current.technology port request.signer = true ∨
        law.controller current.technology port ∈ request.consents) ∧
    law.ClaimGuard current request ∧
    NonnegativeBundle (Party × Good) (law.debit current request) ∧
    NonnegativeBundle (Party × Good) (law.credit current request)

instance : Decidable (NonmaterialGuards law current request) := by
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  unfold NonmaterialGuards RawLaw.SignerMatches RawLaw.ClaimGuard
  cases operation with
  | use _ _ kind => cases kind <;> infer_instance
  | _ => infer_instance

def StockFits (reserve : Party → Good → ℚ) : Prop :=
  ∀ cell ∈ law.debit current request,
    flowAt (law.debit current request) cell.1.1 cell.1.2 - current.stock cell.1.1 cell.1.2 ≤
      reserve cell.1.1 cell.1.2

omit [DecidableEq Party] [DecidableEq Good] in
private theorem debit_unchanged (reserve : Party → Good → ℚ) :
    law.debit (current.addReserve reserve) request = law.debit current request := by
  cases request.operation <;> rfl

omit [DecidableEq Party] [DecidableEq Good] in
private theorem credit_unchanged (reserve : Party → Good → ℚ) :
    law.credit (current.addReserve reserve) request = law.credit current request := by
  cases request.operation <;> rfl

theorem valid_iff_guards_and_stock (reserve : Party → Good → ℚ) :
    law.Valid (current.addReserve reserve) request ↔
      NonmaterialGuards law (current.addReserve reserve) request ∧ StockFits law current request reserve := by
  unfold RawLaw.Valid NonmaterialGuards StockFits
  rw [debit_unchanged]
  simp only [RawCurrent.addReserve, sub_le_iff_le_add', add_comm, and_assoc]

variable [DecidableEq Instrument]

/-- The prospective fold uses this affine stock identity.
Admission and actual execution still use the original interpreter. -/
theorem paid_step_carries_the_exact_reserve (reserve : Party → Good → ℚ) :
    law.paidStep (current.addReserve reserve) request = (law.paidStep current request).addReserve reserve := by
  apply RawCurrent.ext
  · funext party good
    change (current.stock party good + reserve party good) -
        flowAt (law.debit (current.addReserve reserve) request) party good +
        flowAt (law.credit (current.addReserve reserve) request) party good =
      current.stock party good - flowAt (law.debit current request) party good +
        flowAt (law.credit current request) party good + reserve party good
    rw [debit_unchanged, credit_unchanged]
    ring
  · cases request.operation <;> rfl
  · cases request.operation <;> rfl
  · rfl
  · rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Reserve
