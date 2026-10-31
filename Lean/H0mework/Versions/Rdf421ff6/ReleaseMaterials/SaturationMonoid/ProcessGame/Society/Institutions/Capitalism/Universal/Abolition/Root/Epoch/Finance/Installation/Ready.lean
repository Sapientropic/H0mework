import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Support

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

namespace Shape

theorem ready_next {native : Financial.Installation.NativeFrame input} (shape : Shape input native)
    (current : native.V.Current) (ready : shape.Ready input current) :
    shape.Ready input (native.V.nativeTarget (native.program.emit current).write) := by
  induction shape with
  | base _ _ => trivial
  | @born old prior origin registered inherited =>
      rcases current with ⟨current, event⟩
      change prior.Ready input (old.V.nativeTarget (old.program.emit current).write) ∧ _
      refine ⟨inherited current ready.1, ?_⟩
      cases event <;> trivial

theorem ready_after_actual_birth (frame : Financial.Installation.Runtime.Frame input)
    (shape : Shape input frame.native) (ready : shape.Ready input frame.visit.current)
    (registered : Financial.Installation.Registration input frame.native frame.visit.current) :
    (Generated.born input frame shape registered).Ready input (frame.born input registered).visit.current := by
  change shape.Ready input (frame.native.V.nativeTarget (frame.native.program.emit frame.visit.current).write) ∧ True
  exact ⟨ready_next input shape frame.visit.current ready, trivial⟩

end Shape

namespace Generated

private theorem ready_atDecision (frame : Financial.Installation.Runtime.Frame input) (shape : Shape input frame.native)
    (ready : shape.Ready input frame.visit.current)
    (decision : Option (Financial.Installation.Registration input frame.native frame.visit.current)) :
    (atDecision input frame shape decision).Ready input (match decision with
      | some registered => frame.born input registered
      | none => frame.ordinary input).visit.current := by
  cases decision with
  | none => exact shape.ready_next input frame.visit.current ready
  | some registered => exact Shape.ready_after_actual_birth input frame shape ready registered

theorem ready_next (frame : Financial.Installation.Runtime.Frame input) (shape : Shape input frame.native)
    (ready : shape.Ready input frame.visit.current) :
    (next input frame shape).Ready input (frame.next input).visit.current :=
  ready_atDecision input frame shape ready (Financial.Installation.registration? input frame.native frame.visit.current)

theorem all_registered_rows_are_at_the_actual_current (sourceDepth : Nat) (count : Nat) :
    (shape input sourceDepth count).Ready input
      (Financial.Installation.Runtime.frames input sourceDepth count).visit.current := by
  induction count with
  | zero => trivial
  | succ count previous => exact ready_next input _ _ previous

end Generated

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.all_registered_rows_are_at_the_actual_current
