import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.NativeFrame

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
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)

abbrev InternalAnswer := Accounting.Current input depth count frame.anchor × Accounting.Current input depth count frame.anchor

def internalAnswer (actual : Accounting.Current input depth count frame.anchor) : InternalAnswer frame :=
  ⟨actual, Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start actual⟩

def HasWork (actual : Accounting.Current input depth count frame.anchor) : Prop :=
  actual.bodyPaid = false ∨ (Accounting.item? input depth count prefixLimit renewalLimit oldPast start actual).isSome = true

instance (actual : Accounting.Current input depth count frame.anchor) : Decidable (HasWork frame actual) :=
  inferInstanceAs (Decidable (_ ∨ _))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
