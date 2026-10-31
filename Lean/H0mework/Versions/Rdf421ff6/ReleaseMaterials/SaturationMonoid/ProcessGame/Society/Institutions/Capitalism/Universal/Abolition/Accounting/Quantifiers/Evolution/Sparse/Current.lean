import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Mechanism.Action

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)

/-- Source access to one already admitted native row. The complete old ledger
may be infinite and its open witnesses may be proof relevant. -/
structure Current : Type 4 where
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure (ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)) V
  visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot
  row : OpenResponsibilityAt (ExtendedNetwork oldN (Responsibility.Family.activationLaw claim))
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf (root.emitted visit.current))
  rowKey : row.1 = .inr (Responsibility.Family.activationLaw claim).debtId
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit row
  basis : Abolition.Root.Registered.Macro.Inquiry.Basis (ExtendedNetwork oldN (Responsibility.Family.activationLaw claim))
  actualLaw : RawLaw Party Good Port Technology Instrument
  members : List Party
  contextFace : SourceNativeRootSemanticFaceAt root visit
  context_heq : HEq contextFace.rootRead (actualLaw,members)

private theorem native_row_is_active {network : WorldRelationNetwork} {law : DebtActivationLaw}
    (support : network.Support × Option law.DebtState)
    (opened : DebtOpenAt network law support (.inr law.debtId)) : support.2.isSome = true := by
  rcases support with ⟨old,state⟩
  cases state with
  | none => exact nomatch opened
  | some state => rfl

private def readBound {α β : Sort _} (value : α) (bound : β) (same : HEq value bound) : β :=
  cast (type_eq_of_heq same) value

private theorem readBound_eq {α β : Sort _} (value : α) (bound : β) (same : HEq value bound) :
    readBound value bound same = bound := by cases same; rfl

namespace Current
variable (current : Current (oldN := oldN) claim)

def erase : AnyAuthoritativeRootCurrent :=
  ⟨ExtendedNetwork oldN (Responsibility.Family.activationLaw claim),
    ⟨current.V,current.root.toAuthoritativeRoot,current.visit⟩⟩

def support := current.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
  (current.root.emitted current.visit.current)

theorem active : (support claim current).2.isSome = true := by
  have opened := current.row.2
  rw [current.rowKey] at opened
  exact native_row_is_active (support claim current) opened

def state : Responsibility.Family.State claim := (support claim current).2.get (active claim current)

theorem support_eq : support claim current = ((support claim current).1,some (state claim current)) :=
  Prod.ext rfl (Option.some_get (active claim current)).symm

def readContext : RawLaw Party Good Port Technology Instrument × List Party :=
  readBound current.contextFace.rootRead (current.actualLaw,current.members) current.context_heq

theorem readContext_eq : readContext claim current = (current.actualLaw,current.members) :=
  readBound_eq _ _ current.context_heq

def readLaw := (readContext claim current).1

def readMembers := (readContext claim current).2

theorem readLaw_eq : readLaw claim current = current.actualLaw := congrArg Prod.fst (readContext_eq claim current)

theorem readMembers_eq : readMembers claim current = current.members := congrArg Prod.snd (readContext_eq claim current)

end Current

def ofFrame (frame : Root.Reentry.Frame (oldN := oldN) claim) : Current (oldN := oldN) claim where
  V := frame.V
  root := frame.root
  visit := frame.visit
  row := frame.row
  rowKey := frame.rowKey
  authority := frame.authority
  basis := frame.basis
  actualLaw := frame.actualLaw
  members := frame.members
  contextFace := frame.contextFace
  context_heq := frame.context_heq

theorem ofFrame_state (frame : Root.Reentry.Frame (oldN := oldN) claim) :
    Current.state claim (ofFrame claim frame) = Root.Reentry.Frame.state claim frame := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
