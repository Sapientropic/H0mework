import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Mother
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Consumer

/-! Every supplied occurrence generates its full physical next trace and
reverse target. Original units, coefficients and source material remain low;
no target representative or recovered constant enters the source. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Reverse.Family
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationScalarInventoryLift
open SourceOperationLogic SourceOperationLogic.FibreLift SourceGeneratedScalarDifferentialResidual
namespace F
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Execution.Residual.Family
  (PacketAt packetAt programme frames runtime)
end F
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (base root query resultFace actualOccurrence next state)
end S
namespace C
export SourceOperationInquiry.Context.Faces.Execution (expression expression_eval value_recovered)
end C
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : SourceOperationInquiry.Context.Faces.Execution.Activation.M.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current))

abbrev material := SourceOperationInquiry.Context.Installation.materialAt frame occurrence
abbrev oldEnv := (material frame occurrence).raw.environment
abbrev nextEnv := (material frame occurrence).nextRaw.environment
abbrev delta := nextEnv frame occurrence - oldEnv frame occurrence
abbrev expression := (material frame occurrence).raw.expression
abbrev oldWord := relationMap (R := ℤ) (oldEnv frame occurrence) (material frame occurrence).relations

def nextTrace : Trace (nextEnv frame occurrence) (expression frame occurrence)
    (.const ((expression frame occurrence).eval (nextEnv frame occurrence))) :=
  execution (nextEnv frame occurrence) (expression frame occurrence)
abbrev nextWord := relationMap (R := ℤ) (nextEnv frame occurrence) (nextTrace frame occurrence).relationWords
abbrev morphism := updateMorphism (R := ℤ) (s := sort) (oldEnv frame occurrence) (delta frame occurrence)

private theorem updated_env : oldEnv frame occurrence + delta frame occurrence = nextEnv frame occurrence := by
  change oldEnv frame occurrence + (nextEnv frame occurrence - oldEnv frame occurrence) = _
  abel

def target : Fibre (evaluation (R := ℤ) (nextEnv frame occurrence))
    (q (evaluation (R := ℤ) (nextEnv frame occurrence)) (oldWord frame occurrence)) :=
  ⟨oldWord frame occurrence + nextWord frame occurrence, by
    apply (q_eq_iff _ _ _).mpr
    rw [LinearMap.mem_ker, add_sub_cancel_left]
    exact (nextTrace frame occurrence).relation_old (R := ℤ)⟩

def sourceTarget : Fibre (evaluation (R := ℤ) (oldEnv frame occurrence + delta frame occurrence))
    (q (evaluation (R := ℤ) (oldEnv frame occurrence + delta frame occurrence))
      ((morphism frame occurrence).sourceMap (oldWord frame occurrence))) :=
  Eq.mpr (congrArg (fun environment : Env PhysicalValue PhysicalVar =>
    Fibre (evaluation (R := ℤ) environment) (q (evaluation (R := ℤ) environment) (oldWord frame occurrence)))
      (updated_env frame occurrence)) (target frame occurrence)

abbrev reverse := liftingResidual (morphism frame occurrence) (oldWord frame occurrence) (sourceTarget frame occurrence)

private theorem transport_target_value
    {first second : Env PhysicalValue PhysicalVar} (same : first = second)
    (word : Formal ℤ PhysicalValue PhysicalVar sort)
    (target : Fibre (evaluation (R := ℤ) second) (q (evaluation (R := ℤ) second) word)) :
    (Eq.mpr (congrArg (fun environment : Env PhysicalValue PhysicalVar =>
      Fibre (evaluation (R := ℤ) environment) (q (evaluation (R := ℤ) environment) word)) same) target).val = target.val := by
  cases same
  rfl

theorem target_coordinate : (targetCoordinate (morphism frame occurrence) (oldWord frame occurrence)
    (sourceTarget frame occurrence)).val = nextWord frame occurrence := by
  change (sourceTarget frame occurrence).val - oldWord frame occurrence = _
  exact (congrArg (fun word => word - oldWord frame occurrence)
    (transport_target_value (updated_env frame occurrence) (oldWord frame occurrence) (target frame occurrence))).trans
      (add_sub_cancel_left _ _)

abbrev pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  ⟨pairEnvironment (oldEnv frame occurrence) (delta frame occurrence), liftExpr (C.expression (nextWord frame occurrence))⟩

def LowPacket : Type u := F.PacketAt frame occurrence ×
  (Σ _retainedWord : Formal ℤ PhysicalValue PhysicalVar sort,
    Fibre (evaluation (R := ℤ) (nextEnv frame occurrence))
      (q (evaluation (R := ℤ) (nextEnv frame occurrence)) (oldWord frame occurrence)) ×
    (RelationIndex ℤ (nextEnv frame occurrence) sort →₀ ℤ) ×
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort))

def lowPacket : LowPacket frame occurrence :=
  ⟨F.packetAt frame occurrence, nextWord frame occurrence, target frame occurrence,
    (nextTrace frame occurrence).relationWords, pairRaw frame occurrence⟩

theorem packet_word : (lowPacket frame occurrence).2.1 = nextWord frame occurrence := rfl

theorem packet_target_word : (lowPacket frame occurrence).2.2.1.val =
    oldWord frame occurrence + (lowPacket frame occurrence).2.1 := rfl

theorem packet_programme_word : relationMap (R := ℤ) (nextEnv frame occurrence)
    (lowPacket frame occurrence).2.2.2.1 = (lowPacket frame occurrence).2.1 := rfl

end SourceOperationInquiry.Context.Faces.Reverse.Family
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
