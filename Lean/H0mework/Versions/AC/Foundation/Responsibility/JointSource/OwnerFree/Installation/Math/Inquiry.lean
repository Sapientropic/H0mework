import H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry.Source
/-! The old inquiry-state entry delegates to the exact source-root mouth. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
open RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt old.visit.current →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))

abbrev original := Source.original old.root
abbrev baseRoot := Source.baseRoot old.root old.visit reader
abbrev visit := Source.visit old.root old.visit reader
abbrev entry := Source.entry old.root old.visit reader
abbrev authority := Source.authority old.root old.visit reader
abbrev Ledger := Source.Ledger old.root old.visit reader
abbrev Occurrence := Source.Occurrence old.root old.visit reader
abbrev World := Source.World old.root old.visit reader
abbrev exactOccurrence := Source.exactOccurrence old.root old.visit reader
abbrev U7 := Source.U7 old.root old.visit old.U7 reader
abbrev calculus := Source.calculus old.root old.visit old.U7 old.calculus reader
abbrev entryAt := Source.entryAt old.root old.visit reader
abbrev Readout := Source.Readout old.root old.visit reader
abbrev readout {current : (vocabulary old.root.toAuthoritativeRoot old.visit.current reader).Current} :=
  Source.readout (current:=current) old.root old.visit reader
abbrev ActiveAt := Source.ActiveAt old.root old.visit reader
abbrev InactiveAt := Source.InactiveAt old.root old.visit reader
abbrev classify := Source.classify old.root old.visit reader
abbrev consumerLaw := Source.consumerLaw old.root old.visit reader
abbrev consumerRoot := Source.consumerRoot old.root old.visit reader
abbrev compilationLaw := Source.compilationLaw old.root old.visit old.U7 old.calculus reader
abbrev compilationRoot := Source.compilationRoot old.root old.visit old.U7 old.calculus reader
abbrev queryLaw := Source.queryLaw old.root old.visit reader
abbrev root := Source.root old.root old.visit old.U7 old.calculus reader
abbrev answerFace := Source.answerFace old.root old.visit old.U7 old.calculus reader
abbrev consumer := Source.consumer old.root old.visit old.U7 old.calculus reader
abbrev entryAuthority := Source.entryAuthority old.root old.visit old.U7 old.calculus reader
abbrev compilation := Source.compilation old.root old.visit old.U7 old.calculus reader
abbrev state := Source.state old.root old.visit old.U7 old.calculus reader
abbrev input := Source.input old.root old.visit old.U7 old.calculus reader
abbrev actual_state := Source.actual_state old.root old.visit old.U7 old.calculus reader
abbrev compiled := Source.compiled old.root old.visit old.U7 old.calculus reader
abbrev actual_next := Source.actual_next old.root old.visit old.U7 old.calculus reader
abbrev endpointCount := Source.endpointCount old.root old.visit reader
abbrev endpointState := Source.endpointState old.root old.visit old.U7 old.calculus reader
abbrev endpointInput := Source.endpointInput old.root old.visit old.U7 old.calculus reader
abbrev endpoint_source_state := Source.endpoint_source_state old.root old.visit old.U7 old.calculus reader
abbrev originalMaterialFace := Source.originalMaterialFace old.root old.visit old.U7 old.calculus reader
abbrev original_material := Source.original_material old.root old.visit old.U7 old.calculus reader

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
