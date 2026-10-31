import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch.Source.Binding

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

namespace Source
variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (value : Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))

def ActiveAt {current : frame.V.Current} (_occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :=
  {actual : Public.Inquiry.ActualAt frame current // actual.actual.bodyPaid = true}

instance {current : frame.V.Current} (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :
    Subsingleton (ActiveAt frame occurrence) := by
  dsimp only [ActiveAt]
  infer_instance

def classify {current : frame.V.Current} (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :
    ActiveAt frame occurrence ⊕ PLift (¬ Nonempty (ActiveAt frame occurrence)) := by
  classical
  exact if active : Nonempty (ActiveAt frame occurrence) then .inl (Classical.choice active) else .inr ⟨active⟩

theorem active_selected {current : frame.V.Current} (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current)
    (active : ActiveAt frame occurrence) : classify frame occurrence = .inl active := by
  unfold classify
  rw [dif_pos ⟨active⟩]
  exact congrArg Sum.inl (Subsingleton.elim _ _)

def component : SourceNativeProjectionLaw frame.root.toAuthoritativeRoot.toLedgerRoot.source where
  Projection := PUnit
  ActiveAt := fun _ {_} occurrence => ActiveAt frame occurrence
  InactiveAt := fun _ {_} occurrence => PLift (¬ Nonempty (ActiveAt frame occurrence))
  classify := fun _ {_} occurrence => classify frame occurrence
  PayloadAt := fun _ {_} _ _ => Control (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
  project := fun _ {_} _ _ => value

end Source
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Evolving.Epoch
