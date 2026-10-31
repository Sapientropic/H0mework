import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Born
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

private theorem cast_keys {N : WorldRelationNetwork} {before left right : N.Support}
    (same : left = right) (evolution : LedgerWriteEvolutionAt N ⟨before⟩ ⟨left⟩)
    (keys : Financial.Installation.KeepsKeys evolution) :
    Financial.Installation.KeepsKeys
      (Eq.mp (congrArg (fun support => LedgerWriteEvolutionAt N ⟨before⟩ ⟨support⟩) same) evolution) := by
  cases same
  exact keys

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}

namespace NativeFrame
variable (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)

def wholeEvolution (current : frame.V.Current) :
    LedgerWriteEvolutionAt frame.N ⟨frame.sourceSupport current⟩
      ⟨frame.sourceSupport (frame.successor current).targetCurrent⟩ :=
  Eq.mp (congrArg (fun occurrence => LedgerWriteEvolutionAt frame.N ⟨frame.sourceSupport current⟩
    ⟨frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence⟩)
      (frame.target_occurrence current)) (frame.successor current).ledgerEvolution

theorem whole_keys (current : frame.V.Current) : Financial.Installation.KeepsKeys (frame.wholeEvolution current) :=
  cast_keys (congrArg frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (frame.target_occurrence current))
    (frame.successor current).ledgerEvolution (frame.successor_keys current)

end NativeFrame

namespace Runtime
abbrev entryCard := @Financial.Installation.Runtime.entryCard

theorem native_entry_card
    (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start) (current : frame.V.Current) :
    entryCard frame.root.toAuthoritativeRoot.toLedgerRoot current =
      entryCard frame.root.toAuthoritativeRoot.toLedgerRoot (frame.successor current).targetCurrent := by
  change Nat.card (OpenResponsibilityAt frame.N (frame.sourceSupport current)) =
    Nat.card (OpenResponsibilityAt frame.N (frame.sourceSupport (frame.successor current).targetCurrent))
  have sourceFinite : Finite (OpenResponsibilityAt frame.N (frame.sourceSupport current)) := frame.entries_finite current
  have targetFinite : Finite (OpenResponsibilityAt frame.N (frame.sourceSupport (frame.successor current).targetCurrent)) :=
    frame.entries_finite (frame.successor current).targetCurrent
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective _ (Financial.Installation.keys_imply_destination_injective
      (frame.wholeEvolution current) (frame.whole_keys current) frame.family.open_fibres))
    (Nat.card_le_card_of_injective _ (Financial.Installation.keys_imply_origin_injective
      (frame.wholeEvolution current) (frame.whole_keys current) frame.family.open_fibres))

theorem born_initial_entry_card
    (frame : NativeFrame input depth count prefixLimit renewalLimit oldPast start)
    (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
    (actual : Accounting.Current input depth count frame.anchor)
    (aligned : frame.cursor visit.current = some actual)
    (registered : Accounting.Registration input depth count prefixLimit renewalLimit oldPast start actual)
    (reader : Macro.Raw.Reader input depth count) :
    entryCard (Accounting.Born.Action.completeFrame frame visit actual registered reader).root.toAuthoritativeRoot.toLedgerRoot
        (Accounting.Born.Source.initialVisit frame.family actual registered).current =
      entryCard frame.root.toAuthoritativeRoot.toLedgerRoot visit.current + 1 := by
  change Nat.card (OpenResponsibilityAt (Accounting.Born.N frame.family actual registered)
      (Accounting.Born.initialSupport frame.family actual registered)) =
    Nat.card (OpenResponsibilityAt frame.N (frame.sourceSupport visit.current)) + 1
  have oldSupport := frame.support_exact visit.current actual aligned
  change frame.sourceSupport visit.current = Accounting.Born.oldSupport frame.family actual at oldSupport
  rw [oldSupport]
  have sourceFinite : Finite (OpenResponsibilityAt frame.N (Accounting.Born.oldSupport frame.family actual)) :=
    frame.family.entries_finite actual.account actual.native
  let rows := activeInventoryPresentation (law := Accounting.Born.law actual registered)
    .pending (ConstructivePresentation.refl
      (OpenResponsibilityAt frame.N (Accounting.Born.oldSupport frame.family actual)))
  exact (Nat.card_congr (show Option (OpenResponsibilityAt frame.N (Accounting.Born.oldSupport frame.family actual)) ≃
      OpenResponsibilityAt (Accounting.Born.N frame.family actual registered) (Accounting.Born.initialSupport frame.family actual registered) from
      ⟨rows.forward, rows.backward, rows.backward_forward, rows.forward_backward⟩)).symm.trans Finite.card_option

#print axioms native_entry_card
#print axioms born_initial_entry_card

end Runtime
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public
