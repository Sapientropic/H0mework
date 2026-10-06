import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Programme

/-! The calculation query is a source-generated germ at the supplied
occurrence. Its epoch-wide family retains complete raw pair syntax and does
not capture the moving visit in the source projection vocabulary. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (resultLaw resultAt ResultAt)
end O
namespace I
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathEntry)
end I
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def epoch : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort) := { frame with depth := 0 }
namespace Shared
variable (programme : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
abbrev base := Mother.baseState (epoch frame)
abbrev datum := programme.datum (epoch frame)
abbrev baseRoot := optionalSourceRoot (base frame).root (datum frame programme).component

abbrev baseInstallation := optionalInstallation (base frame).root (datum frame programme).component

abbrev Occurrence {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} :=
  SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)

structure GermAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) : Type u where
  private mk ::
  raw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := programme.LowVar) (sort := sort)
  private raw_eq : raw = (datum frame programme).reader occurrence

def germAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) : GermAt frame programme occurrence :=
  ⟨(datum frame programme).reader occurrence, rfl⟩

theorem germ_unique {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) (query : GermAt frame programme occurrence) :
    query = germAt frame programme occurrence := by
  rcases query with ⟨raw, same⟩
  cases same
  rfl

abbrev queryLaw : SourceNativeProjectionLaw (baseRoot frame programme).source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => GermAt (epoch frame) programme occurrence
  project := fun _ {_current} occurrence _ => germAt (epoch frame) programme occurrence

abbrev resultLaw := O.resultLaw (baseRoot frame programme).toAuthoritativeRoot ((datum frame programme).reader)
abbrev resultAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) :=
  O.resultAt (baseRoot frame programme).toAuthoritativeRoot ((datum frame programme).reader) occurrence

def entryAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) :=
  RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly.entryAt
    frame.old frame.registered frame.packetAt occurrence

abbrev consumerLaw : SourceNativeProjectionLaw (baseRoot frame programme).source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => SourceNativeInquiryAnswerConsumerTokenAt
    (germAt (epoch frame) programme occurrence) (ULift.up.{u + 1, u} occurrence) (entryAt frame occurrence) (resultAt frame programme occurrence)
  project := fun _ {_current} _ _ => .canonical

abbrev compilationLaw : SourceNativeProjectionLaw (baseRoot frame programme).source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => SourceNativeInquiryCompilationTokenAt
    (U7 := (base frame).U7) (calculus := (base frame).calculus) (oldTheory := (baseRoot frame programme).source.base.lawSurface)
    (entryAt frame occurrence) (germAt (epoch frame) programme occurrence) (ULift.up.{u + 1, u} occurrence) .answered
    (O.ResultAt (baseRoot frame programme).toAuthoritativeRoot ((datum frame programme).reader) occurrence)
  project := fun _ {_current} occurrence _ => .canonical (resultAt frame programme occurrence)

abbrev queryRoot := (baseRoot frame programme).withProjectionCoface (queryLaw (epoch frame) programme)
abbrev resultRoot := (queryRoot frame programme).withProjectionCoface (resultLaw (epoch frame) programme)
abbrev consumerRoot := (resultRoot frame programme).withProjectionCoface (consumerLaw (epoch frame) programme)
abbrev root := (consumerRoot frame programme).withProjectionCoface (compilationLaw (epoch frame) programme)

theorem root_math : root frame.mathNext programme = root frame programme := rfl

end Shared

abbrev base := Shared.base frame
abbrev Occurrence {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered} :=
  Shared.Occurrence frame (current := current)
abbrev GermAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) := Shared.GermAt frame originalProgramme occurrence
abbrev germAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) := Shared.germAt frame originalProgramme occurrence
abbrev germ_unique {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) := Shared.germ_unique frame originalProgramme occurrence
abbrev queryLaw := Shared.queryLaw frame originalProgramme
abbrev resultLaw := Shared.resultLaw frame originalProgramme
abbrev resultAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) := Shared.resultAt frame originalProgramme occurrence
abbrev entryAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : Occurrence frame (current := current)) := Shared.entryAt frame occurrence
abbrev consumerLaw := Shared.consumerLaw frame originalProgramme
abbrev compilationLaw := Shared.compilationLaw frame originalProgramme
abbrev queryRoot := Shared.queryRoot frame originalProgramme
abbrev resultRoot := Shared.resultRoot frame originalProgramme
abbrev consumerRoot := Shared.consumerRoot frame originalProgramme
abbrev root := Shared.root frame originalProgramme

theorem epoch_math : epoch frame.mathNext = epoch frame := rfl
theorem root_math : root frame.mathNext = root frame := Shared.root_math frame originalProgramme

end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
