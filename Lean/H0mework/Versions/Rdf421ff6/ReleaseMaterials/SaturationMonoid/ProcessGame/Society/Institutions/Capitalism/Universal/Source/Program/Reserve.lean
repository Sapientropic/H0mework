import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def RawCurrent.addReserve (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) : RawCurrent Party Good Technology Instrument :=
  { current with stock := fun party good => current.stock party good + reserve party good }

/-- This local policy property is verified for a concrete source; additional
resources need not preserve arbitrary stock-sensitive laws. -/
structure RawLaw.ReserveInsensitive (law : RawLaw Party Good Port Technology Instrument) : Prop where
  operationAllowed : ∀ current reserve request,
    law.operationAllowed (current.addReserve reserve) request = law.operationAllowed current request
  necessities : ∀ current reserve party,
    law.necessities (current.addReserve reserve) party = law.necessities current party
  maintenance : ∀ current reserve party,
    law.mandatoryMaintenance (current.addReserve reserve) party = law.mandatoryMaintenance current party

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument) (policy : law.ReserveInsensitive)

include policy

omit [DecidableEq Instrument] in
theorem valid_addReserve (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ party good, 0 ≤ reserve party good)
    (request : Request Party Good Port Technology Instrument)
    (accepted : law.Valid current request) : law.Valid (current.addReserve reserve) request := by
  have guard : law.ClaimGuard (current.addReserve reserve) request ↔ law.ClaimGuard current request := by
    rcases request with ⟨signer, consents, purpose, gates, operation⟩
    cases operation with
    | use bearer goods purpose =>
        cases purpose <;> simp only [ClaimGuard, policy.necessities, policy.maintenance]
    | _ => rfl
  have debit : law.debit (current.addReserve reserve) request = law.debit current request := by
    cases request.operation <;> rfl
  have credit : law.credit (current.addReserve reserve) request = law.credit current request := by
    cases request.operation <;> rfl
  have ports : law.requiredPorts (current.addReserve reserve) request = law.requiredPorts current request := by
    cases request.operation <;> rfl
  refine ⟨⟨accepted.1.1, ?_⟩, ?_, guard.mpr accepted.2.2.1, ?_, ?_, ?_⟩
  · rw [policy.operationAllowed]; exact accepted.1.2
  · intro port inside
    exact accepted.2.1 port (ports ▸ inside)
  · rw [debit]; exact accepted.2.2.2.1
  · rw [credit]; exact accepted.2.2.2.2.1
  · intro item inside
    rw [debit] at inside ⊢
    exact (accepted.2.2.2.2.2 item inside).trans (le_add_of_nonneg_right (nonnegative _ _))

theorem step_addReserve (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ party good, 0 ≤ reserve party good)
    (request : Request Party Good Port Technology Instrument)
    (accepted : law.Valid current request) :
    law.step (current.addReserve reserve) request = (law.step current request).addReserve reserve := by
  have enlarged := law.valid_addReserve policy current reserve nonnegative request accepted
  simp only [step, if_pos accepted, if_pos enlarged]
  apply RawCurrent.ext
  · funext party good
    cases request.operation <;> dsimp [paidStep, RawCurrent.addReserve, debit, credit] <;> ring
  · cases request.operation <;> rfl
  · cases request.operation <;> rfl
  · rfl
  · rfl

/-- The original accepted word remains executable and carries its unused
reserve through every instruction.  Rejected words are not silently promoted. -/
theorem execute_addReserve (current : RawCurrent Party Good Technology Instrument)
    (reserve : Party → Good → ℚ) (nonnegative : ∀ party good, 0 ≤ reserve party good)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument)
    (accepted : ∀ item ∈ (law.execute current index word).items, law.Valid item.before item.request) :
    (law.execute (current.addReserve reserve) index word).final =
        (law.execute current index word).final.addReserve reserve ∧
      (∀ item ∈ (law.execute (current.addReserve reserve) index word).items,
        law.Valid item.before item.request) := by
  induction word generalizing current index with
  | nil => exact ⟨rfl, by simp [execute]⟩
  | cons request tail ih =>
      have front : law.Valid current request := accepted ⟨index, current, request⟩ (List.mem_cons_self)
      have rest : ∀ item ∈ (law.execute (law.step current request) (index + 1) tail).items,
          law.Valid item.before item.request := by
        intro item inside
        exact accepted item (List.mem_cons_of_mem _ inside)
      obtain ⟨same, valid⟩ := ih (law.step current request) (index + 1) rest
      simp only [execute, law.step_addReserve policy current reserve nonnegative request front]
      refine ⟨same, ?_⟩
      simp only [List.forall_mem_cons]
      exact ⟨law.valid_addReserve policy current reserve nonnegative request front, valid⟩

end RawLaw
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
