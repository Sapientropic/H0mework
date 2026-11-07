import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.World.Continuation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Frame

/-! A dependent view of the actual native frame constructors. The world
translation follows `Frame.born`, not an account-equality guess. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

inductive Shape : Financial.Installation.NativeFrame input → Type 2
  | base (start : Financial.Installation.Cursor.State input)
      (positive : 0 < Financial.Installation.Cursor.physicalVisitIndex input start) :
      Shape (Financial.Installation.AccountSource.nativeFrame input start positive)
  | born {old : Financial.Installation.NativeFrame input} (prior : Shape old)
      {origin : old.V.Current} (registered : Financial.Installation.Registration input old origin) :
      Shape (Financial.Installation.Admission.nativeFrame input old registered)

namespace Shape

variable (epochDepth epochCount : Nat)

def world : {native : Financial.Installation.NativeFrame input} → Shape input native → WorldRelationNetwork
  | _, .base start _ => World.folded input epochDepth epochCount (ProgrammeSource.N input) start.account.generated
  | _, .born prior registered => ExtendedNetwork (world prior)
      (World.LegacyLaw.law input epochDepth epochCount (registered.before input _) registered.claim)

def translation : {native : Financial.Installation.NativeFrame input} → (shape : Shape input native) →
    TypedSemanticWorldNetworkTranslationAt native.N (shape.world input epochDepth epochCount)
  | _, .base start _ => World.foldTranslation input epochDepth epochCount
      (Financial.Installation.Ingress.identityTranslation (ProgrammeSource.N input)) start.account.generated
  | _, .born prior registered => World.translation input epochDepth epochCount
      (registered.before input _) registered.claim (translation prior)

end Shape

namespace Generated

def ordinary (frame : Financial.Installation.Runtime.Frame input) (shape : Shape input frame.native) :
    Shape input (frame.ordinary input).native := shape

def born (frame : Financial.Installation.Runtime.Frame input) (shape : Shape input frame.native)
    (registered : Financial.Installation.Registration input frame.native frame.visit.current) :
    Shape input (frame.born input registered).native := .born shape registered

def atDecision (frame : Financial.Installation.Runtime.Frame input) (shape : Shape input frame.native) :
    (decision : Option (Financial.Installation.Registration input frame.native frame.visit.current)) →
    Shape input (match decision with
      | some registered => frame.born input registered
      | none => frame.ordinary input).native
  | some registered => born input frame shape registered
  | none => ordinary input frame shape

def next (frame : Financial.Installation.Runtime.Frame input) (shape : Shape input frame.native) :
    Shape input (frame.next input).native :=
  atDecision input frame shape (Financial.Installation.registration? input frame.native frame.visit.current)

def shape (sourceDepth : Nat) : (count : Nat) →
    Shape input (Financial.Installation.Runtime.frames input sourceDepth count).native
  | 0 => .base (Financial.Installation.Ingress.start input sourceDepth)
      (Financial.Installation.Ingress.start_positive input sourceDepth)
  | count + 1 => next input (Financial.Installation.Runtime.frames input sourceDepth count) (shape sourceDepth count)

/-- The source is literally the current runtime frame's original world. -/
def translation (epochDepth epochCount sourceDepth sourceCount : Nat) :
    TypedSemanticWorldNetworkTranslationAt
      (Financial.Installation.Runtime.frames input sourceDepth sourceCount).native.N
      ((shape input sourceDepth sourceCount).world input epochDepth epochCount) :=
  (shape input sourceDepth sourceCount).translation input epochDepth epochCount

end Generated

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Installation.Generated.translation
