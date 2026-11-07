import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Readout
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Completion.Actual.Dividend.Financial.Check

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)

inductive Projection
  | query | answer | compilation | consumer | snapshot | nativeAccount | publicLaw | sourceReport

structure Snapshot where
  oldPast : List (Compile.RawInput Party Good Port Technology Instrument)
  physical : Physical.Cursor Party Good Port Technology Instrument
  actual : Abolition.Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)
  account : (Epoch.Finance.process input depth count).GeneratedState
  planningWindow : Nat × Nat
  fullAccount : Abolition.Completion.Actual.Dividend.Financial.Decision
    input depth count planningWindow.1 planningWindow.2 oldPast physical

def ActiveAt (projection : Projection) {current : frame.V.Current}
    (_occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) : Type :=
  match projection with
  | .answer => {atCurrent : ActualAt frame current // HasWork frame atCurrent.actual}
  | .consumer => {atCurrent : ActualAt frame current // HasWork frame atCurrent.actual ∧
      Accounting.registration? input depth count prefixLimit renewalLimit oldPast start atCurrent.actual = none}
  | .sourceReport => {atCurrent : ActualAt frame current // ¬ HasWork frame atCurrent.actual}
  | _ => ActualAt frame current

instance (projection : Projection) {current : frame.V.Current}
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :
    Subsingleton (ActiveAt frame projection occurrence) := by
  cases projection <;> dsimp only [ActiveAt] <;> exact inferInstance

def InactiveAt (projection : Projection) {current : frame.V.Current}
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) : Type :=
  PLift (¬ Nonempty (ActiveAt frame projection occurrence))

def classify (projection : Projection) {current : frame.V.Current}
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current) :
    ActiveAt frame projection occurrence ⊕ InactiveAt frame projection occurrence := by
  classical
  exact if available : Nonempty (ActiveAt frame projection occurrence) then
    .inl (Classical.choice available) else .inr ⟨available⟩

theorem the_unique_source_active_is_selected (projection : Projection) {current : frame.V.Current}
    (occurrence : frame.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current)
    (active : ActiveAt frame projection occurrence) : classify frame projection occurrence = .inl active := by
  unfold classify
  rw [dif_pos ⟨active⟩]
  exact congrArg Sum.inl (Subsingleton.elim _ _)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
