import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry.Internal
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Scope.Effects
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Raw.Source

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

structure ActualAt (current : frame.V.Current) where
  actual : Accounting.Current input depth count frame.anchor
  aligned : frame.cursor current = some actual

variable {frame}

instance (current : frame.V.Current) : Subsingleton (ActualAt frame current) := by
  refine ⟨?_⟩
  intro left right
  rcases left with ⟨left, leftEq⟩
  rcases right with ⟨right, rightEq⟩
  have same := Option.some.inj (leftEq.symm.trans rightEq)
  cases same
  rfl

variable (frame)

def actual? (current : frame.V.Current) : Option (ActualAt frame current) :=
  match aligned : frame.cursor current with
  | none => none
  | some actual => some ⟨actual, aligned⟩

variable {frame} {current : frame.V.Current}
  (atCurrent : ActualAt frame current)

namespace ActualAt

def snapshot : Physical.Cursor Party Good Port Technology Instrument :=
  if atCurrent.actual.bodyPaid then Physical.next start else start

def readerCursor : Physical.Cursor Party Good Port Technology Instrument :=
  Physical.receive (Physical.Prefix.cursor (oldPast ++ atCurrent.snapshot.past)) atCurrent.snapshot.incoming

def proposal (reader : Macro.Raw.Reader input depth count) :=
  reader atCurrent.readerCursor atCurrent.actual.account

def selectedCursor (reader : Macro.Raw.Reader input depth count) :=
  Scope.selectedCursor input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot (atCurrent.proposal reader)

abbrev RawAnswer (reader : Macro.Raw.Reader input depth count) :=
  Scope.Decision input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot (atCurrent.proposal reader) ×
    type_of% (Scope.actualResult input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot (atCurrent.proposal reader))

def rawAnswer (reader : Macro.Raw.Reader input depth count) : atCurrent.RawAnswer reader :=
  ⟨Scope.inspect input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot (atCurrent.proposal reader),
    Scope.actualResult input depth count prefixLimit renewalLimit oldPast atCurrent.snapshot (atCurrent.proposal reader)⟩

def AnswerAt (reader : Macro.Raw.Reader input depth count) : Type :=
  if HasWork frame atCurrent.actual then InternalAnswer frame else atCurrent.RawAnswer reader

def sourceAnswer (reader : Macro.Raw.Reader input depth count) : atCurrent.AnswerAt reader := by
  unfold AnswerAt
  split_ifs
  · exact internalAnswer frame atCurrent.actual
  · exact atCurrent.rawAnswer reader

#print axioms sourceAnswer

end ActualAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Inquiry
