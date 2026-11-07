import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Effects
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime.Registry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Invariants

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}

namespace Frame
variable (frame : Frame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount)

def nativeOrdinary : (Epoch.Finance.process input depth count).Run
    frame.account.current frame.ordinary.account.current :=
  frame.package.frame.native frame.visit.current

def nativeBorn (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount
    frame.start frame.proposal frame.sourcePosition frame.package.frame frame.visit.current) :
    (Epoch.Finance.process input depth count).Run frame.account.current (frame.born registered).account.current := by
  rw [show (frame.born registered).account = registered.admitted from frame.born_account_is_the_actual_admission registered]
  rw [← registered.actual_next_account]
  exact frame.package.frame.native frame.visit.current

def nativeReentry (germ : Raw.GermAt frame.package.source frame.package.sourceData frame.package.reader frame.visit.current) :
    (Epoch.Finance.process input depth count).Run frame.account.current (frame.reenter germ).account.current := by
  rw [frame.reentry_preserves_the_literal_existing_account germ]
  exact .nil

/-- A query changes the installed source, not the identity of the financial
process. Even a new debt uses its original native admission. -/
def nativeNextAt (chosen : frame.presentation.Query) : (Epoch.Finance.process input depth count).Run
    frame.account.current (frame.nextAt chosen).account.current := by
  cases chosen with
  | internal work =>
      change (Epoch.Finance.process input depth count).Run _ frame.internalNext.account.current
      unfold internalNext
      split
      · exact frame.nativeBorn _
      · exact frame.nativeOrdinary
  | raw germ => exact frame.nativeReentry germ

def nativeNext : (Epoch.Finance.process input depth count).Run
    frame.account.current frame.next.account.current := frame.nativeNextAt frame.query

end Frame

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth sourceStart : Nat) (datum : Ingress.Datum input depth sourceStart)
  (prefixLimit renewalLimit : Nat)
  (reader : Raw.Reader input depth (Ingress.cut input depth sourceStart))
  (phase : Option (ReviewPhase.ContextAt input) := none)

def registeredNative (tick : Nat) : (steps : Nat) →
    (Epoch.Finance.process input depth (Ingress.cut input depth sourceStart)).Run
      (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader tick).account.current
      (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).account.current
  | 0 => .nil
  | steps + 1 => NativeResponsibilityProcess.Run.concatRuns
      (Epoch.Finance.process input depth (Ingress.cut input depth sourceStart)) (registeredNative tick steps)
      (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).nativeNext

theorem every_actual_successor_retains_all_original_claims (tick steps : Nat) :
    (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader tick).account.current.slots.map
        (Epoch.Finance.slotClaim input depth (Ingress.cut input depth sourceStart)) <+:
      (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).account.current.slots.map
        (Epoch.Finance.slotClaim input depth (Ingress.cut input depth sourceStart)) :=
  Epoch.Finance.run_retains_all_claims input depth (Ingress.cut input depth sourceStart)
    (registeredNative (phase := phase) input depth sourceStart datum prefixLimit renewalLimit reader tick steps)

theorem every_actual_successor_retains_the_complete_native_history (tick steps : Nat) :
    (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader tick).account.current.history <+:
      (batchFrame (review := phase) input depth sourceStart datum prefixLimit renewalLimit reader (tick + steps)).account.current.history := by
  rw [(registeredNative (phase := phase) input depth sourceStart datum prefixLimit renewalLimit reader tick steps).history_eq]
  exact List.prefix_append _ _

#print axioms Frame.nativeNext
#print axioms registeredNative
#print axioms every_actual_successor_retains_all_original_claims
#print axioms every_actual_successor_retains_the_complete_native_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Runtime
