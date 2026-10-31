import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

/-! Local programmes whose permissions and needs do not inspect the clock
can reuse one exact finite execution at every clock.  This property is proved
for each such source law; it is not imposed on the general social source. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program

universe u

variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

def RawCurrent.retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round : Nat) : RawCurrent Party Good Technology Instrument :=
  { current with clock := clock, round := round }

structure RawLaw.TimeIndependent (law : RawLaw Party Good Port Technology Instrument) : Prop where
  operationAllowed : ∀ current clock round request,
    law.operationAllowed (current.retime clock round) request = law.operationAllowed current request
  necessities : ∀ current clock round party,
    law.necessities (current.retime clock round) party = law.necessities current party
  maintenance : ∀ current clock round party,
    law.mandatoryMaintenance (current.retime clock round) party = law.mandatoryMaintenance current party

namespace RawLaw

variable (law : RawLaw Party Good Port Technology Instrument) (timing : law.TimeIndependent)

include timing

omit [DecidableEq Instrument] in
theorem valid_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round : Nat) (request : Request Party Good Port Technology Instrument) :
    law.Valid (current.retime clock round) request ↔ law.Valid current request := by
  have guard : law.ClaimGuard (current.retime clock round) request ↔ law.ClaimGuard current request := by
    rcases request with ⟨signer, consents, purpose, gates, operation⟩
    cases operation with
    | use bearer goods purpose =>
        cases purpose <;> simp only [ClaimGuard, timing.necessities, timing.maintenance]
    | _ => rfl
  simp only [Valid, timing.operationAllowed, guard]
  rcases request with ⟨signer, consents, purpose, gates, operation⟩
  cases operation <;> rfl

theorem step_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round : Nat) (request : Request Party Good Port Technology Instrument) :
    law.step (current.retime clock round) request = (law.step current request).retime clock round := by
  unfold step
  simp only [law.valid_retime timing]
  split
  · rcases request with ⟨signer, consents, purpose, gates, operation⟩
    cases operation <;> rfl
  · rfl

theorem execute_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round index : Nat) (requests : RawEvent Party Good Port Technology Instrument) :
    (law.execute (current.retime clock round) index requests).final =
      (law.execute current index requests).final.retime clock round := by
  induction requests generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [execute, law.step_retime timing, ih]

theorem accepted_retime (current : RawCurrent Party Good Technology Instrument)
    (clock : ℚ) (round index : Nat) (requests : RawEvent Party Good Port Technology Instrument) :
    (∀ item ∈ (law.execute (current.retime clock round) index requests).items,
      law.Valid item.before item.request) ↔
    (∀ item ∈ (law.execute current index requests).items,
      law.Valid item.before item.request) := by
  induction requests generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [execute, List.forall_mem_cons, law.valid_retime timing, law.step_retime timing, ih]

end RawLaw
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program
