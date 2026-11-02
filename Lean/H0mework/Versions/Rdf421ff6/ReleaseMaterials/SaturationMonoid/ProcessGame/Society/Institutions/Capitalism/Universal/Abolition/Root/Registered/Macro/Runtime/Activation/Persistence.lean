import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Registry
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Activation.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Conservation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth sourceStart : Nat)
  (datum : Ingress.Datum input depth sourceStart) (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (review : Option (ReviewPhase.ContextAt input) := none)
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth (Ingress.cut input depth sourceStart) prefixLimit renewalLimit depth (Ingress.cut input depth sourceStart)}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}
  (frame : Public.Runtime.Frame origin admission) (tick : Nat)
  (selected : actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader tick =
    .enacted origin admission frame)

include selected

theorem the_actual_public_tail_is_the_same_generated_lineage (steps : Nat) :
    actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps) =
      .enacted origin admission (frame.visits steps) := by
  unfold actualFrame at *
  induction steps with
  | zero => exact selected
  | succ steps prior =>
      change (activatedFrames (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).next = _
      rw [prior]
      simp only [ActivatedFrame.next, Public.Runtime.Frame.visits, Function.iterate_succ_apply']

def the_actual_public_tail_keeps_the_original_native_run (steps : Nat) :
    (Epoch.Finance.process input depth (Ingress.cut input depth sourceStart)).Run frame.account.current
      (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).nativeAccount.current := by
  rw [the_actual_public_tail_is_the_same_generated_lineage input depth sourceStart datum prefixLimit renewalLimit reader review frame tick selected steps]
  exact frame.visitsNative steps

theorem the_actual_public_tail_keeps_its_effective_interpreter (steps : Nat) :
    (actualFrame (review := review) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).interpreter =
      Physical.Public.interpreter input := by
  rw [the_actual_public_tail_is_the_same_generated_lineage input depth sourceStart datum prefixLimit renewalLimit reader review frame tick selected steps]
  rfl

#print axioms the_actual_public_tail_is_the_same_generated_lineage
#print axioms the_actual_public_tail_keeps_the_original_native_run
#print axioms the_actual_public_tail_keeps_its_effective_interpreter

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
