import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start}

namespace ActualAt

variable {current : frame.V.Current} (atCurrent : ActualAt frame current)
  (reader : Macro.Raw.Reader input depth count)

theorem sourceAnswer_internal_heq (work : HasWork frame atCurrent.actual) :
    HEq (atCurrent.sourceAnswer reader) (internalAnswer frame atCurrent.actual) := by
  simp [sourceAnswer, AnswerAt, work]

theorem sourceAnswer_raw_heq (complete : ¬ HasWork frame atCurrent.actual) :
    HEq (atCurrent.sourceAnswer reader) (atCurrent.rawAnswer reader) := by
  simp [sourceAnswer, AnswerAt, complete]

end ActualAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
