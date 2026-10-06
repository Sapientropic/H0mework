import H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Inquiry
import H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
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

abbrev packet := Source.packet old.root old.visit old.U7 old.calculus reader
abbrev residualMaterial := Source.residualMaterial old.root old.visit old.U7 old.calculus reader
abbrev residualRegistered := Source.residualRegistered old.root old.visit old.U7 old.calculus reader
abbrev residualEnvironment {current : (vocabulary old.root.toAuthoritativeRoot old.visit.current reader).Current} :=
  Source.residualEnvironment (current:=current) old.root old.visit old.U7 old.calculus reader
abbrev residualFirstStep := Source.residualFirstStep old.root old.visit old.U7 old.calculus reader
abbrev residual_first_action := Source.residual_first_action old.root old.visit old.U7 old.calculus reader
abbrev residualTarget := Source.residualTarget old.root old.visit old.U7 old.calculus reader
abbrev frame := Source.frame old.root old.visit old.U7 old.calculus reader
abbrev residual_first_receipt := Source.residual_first_receipt old.root old.visit old.U7 old.calculus reader
abbrev residual_frame_next := Source.residual_frame_next old.root old.visit old.U7 old.calculus reader
abbrev runtime := Source.runtime old.root old.visit old.U7 old.calculus reader
abbrev activated_next := Source.activated_next old.root old.visit old.U7 old.calculus reader
abbrev activated_query := Source.activated_query old.root old.visit old.U7 old.calculus reader
abbrev activated_answer := Source.activated_answer old.root old.visit old.U7 old.calculus reader

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
