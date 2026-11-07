import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Initial
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Effects
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Native.Handler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro Evolution

noncomputable section
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (current : Current (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def raw := (Source.originalState current.native).raw
def state := current.control.atRaw current.raw

def members := Abolition.Root.Epoch.Interface.Actors.PublicCensus.parties current.native.input current.native.depth
  current.native.count current.native.prefixLimit current.native.renewalLimit current.native.oldPast current.native.actual.snapshot

def proposal := current.native.actual.proposal current.native.reader

/-- The law is the live public interpreter. The original origin and current
actor fold are explicit; checker views never re-run an old bootstrap. -/
def choice := select (Public.Scope.checkInput current.native.input)
  (Actual.origin current.native.input current.native.depth current.native.count)
  current.raw current.members current.native.depth current.native.count current.native.prefixLimit
  current.native.renewalLimit current.control current.proposal

def executionRaw := current.choice.executionRaw

def executionReader : Macro.Raw.Reader current.native.input current.native.depth current.native.count :=
  fun _ _ => current.executionRaw

def physicalResult := Public.Scope.actualResult current.native.input current.native.depth current.native.count
  current.native.prefixLimit current.native.renewalLimit current.native.oldPast current.native.actual.snapshot current.executionRaw

def afterControl := current.choice.controlAfter current.physicalResult.next.raw current.physicalResult.isAccepted

theorem the_choice_reads_the_actual_root_control :
    current.choice = select (Public.Scope.checkInput current.native.input)
      (Actual.origin current.native.input current.native.depth current.native.count)
      current.raw current.members current.native.depth current.native.count current.native.prefixLimit
      current.native.renewalLimit
      (cast (current.binding.typeAt current.native.visit current.native.actual current.native.bodyPaid) current.controlFace.rootRead)
      current.proposal := rfl

theorem the_checker_uses_the_actual_active_public_law :
    (Public.Scope.checkInput current.native.input).law = current.native.handlerFace.rootRead := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Current
