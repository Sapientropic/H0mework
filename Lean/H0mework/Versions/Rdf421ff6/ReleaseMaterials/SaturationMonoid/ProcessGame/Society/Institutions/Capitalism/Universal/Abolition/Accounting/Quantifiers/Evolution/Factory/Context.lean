import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Foundation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Trace

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program

noncomputable section

private def readBound {α β : Sort _} (value : α) (bound : β) (same : HEq value bound) : β :=
  cast (type_eq_of_heq same) value

private theorem readBound_eq {α β : Sort _} (value : α) (bound : β) (same : HEq value bound) :
    readBound value bound same = bound := by cases same; rfl

variable {Party Good Port Technology Instrument : Type}

/-- Source access to an actual continuation row and its live interpreter.
There is no material-claim, finite-ledger or row-position restriction. -/
structure Context (N : WorldRelationNetwork) : Type 4 where
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure N V
  visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot
  row : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted visit.current))
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit row
  basis : Abolition.Root.Registered.Macro.Inquiry.Basis N
  raw : RawCurrent Party Good Technology Instrument
  rawFace : SourceNativeRootSemanticFaceAt root visit
  raw_heq : HEq rawFace.rootRead raw
  actualLaw : RawLaw Party Good Port Technology Instrument
  members : List Party
  contextFace : SourceNativeRootSemanticFaceAt root visit
  context_heq : HEq contextFace.rootRead (actualLaw,members)

namespace Context

variable {N : WorldRelationNetwork} (current : Context (Party := Party) (Good := Good)
  (Port := Port) (Technology := Technology) (Instrument := Instrument) N)

def support : N.Support := current.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
  (current.root.emitted current.visit.current)

def readRaw : RawCurrent Party Good Technology Instrument :=
  readBound current.rawFace.rootRead current.raw current.raw_heq

theorem readRaw_eq : readRaw current = current.raw := readBound_eq _ _ current.raw_heq

def readContext : RawLaw Party Good Port Technology Instrument × List Party :=
  readBound current.contextFace.rootRead (current.actualLaw,current.members) current.context_heq

theorem readContext_eq : readContext current = (current.actualLaw,current.members) := readBound_eq _ _ current.context_heq

def readLaw := (readContext current).1
def readMembers := (readContext current).2

theorem readLaw_eq : readLaw current = current.actualLaw := congrArg Prod.fst (readContext_eq current)
theorem readMembers_eq : readMembers current = current.members := congrArg Prod.snd (readContext_eq current)

def erase : AnyAuthoritativeRootCurrent :=
  ⟨N,⟨current.V,current.root.toAuthoritativeRoot,current.visit⟩⟩

end Context

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory
