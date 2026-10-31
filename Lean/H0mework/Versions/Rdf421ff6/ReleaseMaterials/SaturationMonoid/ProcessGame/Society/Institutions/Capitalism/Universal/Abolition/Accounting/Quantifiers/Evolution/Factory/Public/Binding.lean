import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Installation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

/-- A dependent compiler primitive: the body is retained, while law and cursor
are reads of the active source. Binding does not execute the body. -/
structure BoundContinuation : Type where
  private mk ::
  program : RawProgram Party Good Port Technology Instrument
  interpreter : program.law = Context.readLaw current
  initial : program.initial = Context.readRaw current

def bindContinuation (original : RawProgram Party Good Port Technology Instrument) : BoundContinuation current :=
  ⟨{ original with law := Context.readLaw current,initial := Context.readRaw current },rfl,rfl⟩

theorem the_original_body_is_retained (original : RawProgram Party Good Port Technology Instrument) :
    (bindContinuation current original).program.body = original.body := rfl

variable [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

theorem every_bound_tick_uses_the_active_interpreter (bound : BoundContinuation current) :
    bound.program.tick (Context.readRaw current) = (Context.readLaw current).next (Context.readRaw current)
      (bound.program.body (Context.readRaw current)) := by
  unfold RawProgram.tick RawProgram.emit
  rw [bound.interpreter]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem every_returned_continuation_uses_the_enacted_public_interpreter
    (bound : BoundContinuation (next current)) :
    bound.program.law = law current := bound.interpreter.trans (next_reads_the_new_active_interpreter current)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] in
theorem an_old_private_face_cannot_be_the_continuation_interpreter
    (old : RawLaw Party Good Port Technology Instrument) (technology : Technology) (port : Port) (person : Party)
    (denied : old.allowed technology port person = false) (bound : BoundContinuation (next current)) :
    bound.program.law ≠ old := by
  intro same
  have active := every_returned_continuation_uses_the_enacted_public_interpreter current bound
  have permission := congrArg (fun interpreter => interpreter.allowed technology port person) (same.symm.trans active)
  rw [denied] at permission
  exact Bool.noConfusion permission

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
