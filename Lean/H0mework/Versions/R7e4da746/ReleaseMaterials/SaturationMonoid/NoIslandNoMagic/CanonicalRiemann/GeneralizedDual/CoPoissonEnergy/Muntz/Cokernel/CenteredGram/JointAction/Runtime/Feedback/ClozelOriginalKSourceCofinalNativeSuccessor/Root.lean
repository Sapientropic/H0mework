import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.ConsumerCore
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace RC
export ActualCofinalRootResidualConsumer (actual_generated_current rooted_request_model original_whole original_compiles)
end RC
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance rootFamilyGroups (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n
variable (fixedFactory : SF.Factory W X ())
variable (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))

private theorem actual_target_root
 {Value Var : Unit→Type} [∀ target,AddCommGroup (Value target)]
 (frame : M.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (base : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (event : ExactTemporalCausalRootEventAt (SO.root frame (AS.stockCfg base)).toAuthoritativeRoot.toLedgerRoot
  (SO.visit frame (AS.stockCfg base))) : type_of% (ST.target_root frame (AS.stockCfg base) event) :=
 ST.target_root _ _ _

private theorem actual_target_current
 {Value Var : Unit→Type} [∀ target,AddCommGroup (Value target)]
 (frame : M.Frame (Value:=Value) (Var:=Var) (sort:=()))
 (base : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=()))
 (event : ExactTemporalCausalRootEventAt (SO.root frame (AS.stockCfg base)).toAuthoritativeRoot.toLedgerRoot
  (SO.visit frame (AS.stockCfg base))) : type_of% (ST.target_current frame (AS.stockCfg base) event) :=
 ST.target_current _ _ _

/-- The real whole's source event supplies this same root and current consumer. -/
theorem source_actual_whole_root : type_of%
 (actual_target_root (Native.selected fixedFactory packet) (Native.nativePacket fixedFactory packet).2.2.1
  ((SO.root (Native.selected fixedFactory packet) (AS.stockCfg (Native.nativePacket fixedFactory packet).2.2.1)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (SO.visit (Native.selected fixedFactory packet) (AS.stockCfg (Native.nativePacket fixedFactory packet).2.2.1)))) := actual_target_root _ _ _

theorem source_actual_whole_current : type_of%
 (actual_target_current (Native.selected fixedFactory packet) (Native.nativePacket fixedFactory packet).2.2.1
  ((SO.root (Native.selected fixedFactory packet) (AS.stockCfg (Native.nativePacket fixedFactory packet).2.2.1)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (SO.visit (Native.selected fixedFactory packet) (AS.stockCfg (Native.nativePacket fixedFactory packet).2.2.1)))) := actual_target_current _ _ _

/-- The original runtime's certified residual remains the source of the actual generated next current. -/
def SourceCofinalCurrentAcceptance
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
 (language : cfg.LowVar=X) (ordinal : Nat) : Prop :=
 (type_of% (RC.actual_generated_current fixedFactory initial cfg language ordinal)) ∧
 (type_of% (RC.rooted_request_model fixedFactory initial cfg language ordinal)) ∧
 (type_of% (RC.original_whole fixedFactory initial cfg language ordinal)) ∧
 (type_of% (RC.original_compiles fixedFactory initial cfg language ordinal))

attribute [local irreducible] SourceCofinalCurrentAcceptance

theorem source_actual_cofinal_current
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
 (language : cfg.LowVar=X) (ordinal : Nat) : SourceCofinalCurrentAcceptance fixedFactory initial cfg language ordinal := by
 unfold SourceCofinalCurrentAcceptance
 exact ⟨RC.actual_generated_current _ _ _ _ _,RC.rooted_request_model _ _ _ _ _,
  RC.original_whole _ _ _ _ _,RC.original_compiles _ _ _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
