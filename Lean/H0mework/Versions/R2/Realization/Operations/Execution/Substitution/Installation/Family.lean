import H0mework.Realization.Operations.Execution.Substitution.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Programme
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Reverse.Coefficients.Family
/-! Each supplied occurrence generates the actual source binding trace,
its complete replay and raw programme. Original whole material and every
charged stage stay in the before-emitter packet of the existing engine. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.ForwardSubstitution
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift RootInquiryCompletion
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme epoch)
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end A
namespace C
export SourceOperationInquiry.Context.Installation (Occurrence MaterialAt materialAt)
end C
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw action whole authoritativeRoot)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (SourceMaterialAt sourceMaterialAt)
end I
namespace K
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion (state)
end K
end O
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ sort, AddCommGroup (PhysicalValue sort)] {sort : Sorts}
variable (binding : ∀ target, PhysicalVar target → Expr PhysicalValue PhysicalVar target)
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (o : C.Occurrence frame (current := current))
abbrev original := C.materialAt frame o
abbrev oldEnv := (original frame o).raw.environment
abbrev newEnv := (original frame o).nextRaw.environment
abbrev delta := newEnv frame o - oldEnv frame o
abbrev pairEnv := pairEnvironment (oldEnv frame o) (delta frame o)
abbrev sourceExpr := liftExpr (original frame o).raw.expression
abbrev pairBinding : ∀ target, PhysicalVar target → Expr (PairValue PhysicalValue) PhysicalVar target :=
  fun target name => liftExpr (binding target name)

def sourceTrace := execution (fun target name => (pairBinding binding target name).eval (pairEnv frame o)) (sourceExpr frame o)
def replayTrace := (sourceTrace binding frame o).substitutedTrace (pairBinding binding) (pairEnv frame o)
def raw : O.Raw (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  ⟨pairEnv frame o, (sourceExpr frame o).subst (pairBinding binding)⟩

theorem source_cost : (replayTrace binding frame o).length = remaining (raw binding frame o).expression :=
  substituted_charge (pairBinding binding) (pairEnv frame o) (sourceTrace binding frame o)
abbrev originRoot := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.toAuthoritativeRoot
abbrev reader := fun (_ : (originRoot frame).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) => raw binding frame o
abbrev state (count : Nat) := O.K.state (originRoot frame) current (reader binding frame o) count
abbrev calculationRoot := O.authoritativeRoot (originRoot frame) current (reader binding frame o)
abbrev StageMaterial (count : Nat) := O.I.SourceMaterialAt (calculationRoot binding frame o)
  ((calculationRoot binding frame o).emitted (state binding frame o count))

abbrev PacketAt := O.I.SourceMaterialAt frame.currentState.root.toAuthoritativeRoot o × C.MaterialAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar)
  (sort := sort) (lower := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.ledgerRoot frame.registered frame.packetAt) o ×
  (Σ source : O.Raw (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort),
    Trace source.environment source.expression
      (.const ((sourceExpr frame o).eval
        (fun target name => (pairBinding binding target name).eval (pairEnv frame o)))) ×
    ((count : Fin (remaining source.expression + 1)) → StageMaterial binding frame o count.1))

def packetAt : PacketAt binding frame o :=
  ⟨O.I.sourceMaterialAt frame.currentState.root.toAuthoritativeRoot o, C.materialAt frame o, raw binding frame o, replayTrace binding frame o,
    fun count => O.I.sourceMaterialAt (calculationRoot binding frame o)
      ((calculationRoot binding frame o).emitted (state binding frame o count.1))⟩

def component : SourceNativeProjectionLaw
    (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.base frame).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} o _ => PacketAt binding (A.epoch frame) o
  project := fun _ {_current} o _ => packetAt binding (A.epoch frame) o

def programme : A.Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) where
  LowVar := PhysicalVar
  datum frame := {
    component := some (component binding frame)
    reader := fun {_current} o => ((component binding frame).project PUnit.unit o PUnit.unit).2.2.1 }

theorem packet_raw : (packetAt binding frame o).2.2.1 = raw binding frame o := rfl

theorem packet_original : (packetAt binding frame o).1 =
    O.I.sourceMaterialAt frame.currentState.root.toAuthoritativeRoot o := rfl

end SourceOperationInquiry.Context.ForwardSubstitution
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
