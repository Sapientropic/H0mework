import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.NativeFrame

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

private def DestinationExact (current : Current frame registered)
    (image : SourceNativeLedgerEvolutionAt (source frame registered) (emitted frame registered current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emitted frame registered current) image,
    HEq actual.ledgerEvolution.destination (wholeEvolution frame registered current).destination

theorem successor_destination (current : Current frame registered) :
    HEq (successor frame registered current).ledgerEvolution.destination (wholeEvolution frame registered current).destination := by
  have exactImage : DestinationExact frame registered current
      ((ledgerCompiler frame registered).compile (emitted frame registered current)) := by
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> intro actual <;> exact heq_of_eq (patch_destination frame registered current)
  exact exactImage _

theorem successor_support (current : Current frame registered) :
    (successor frame registered current).targetOccurrence.1 = supportAt frame registered (next frame registered current) := by
  have emittedAt := (nativeFrame frame registered).target_occurrence current
  exact (congrArg (fun occurrence => occurrence.1) emittedAt).trans
    (congrArg (supportAt frame registered) (successor_current frame registered current))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
