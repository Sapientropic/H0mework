import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.Root
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceCofinalNativeSuccessor.ConsumerPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction
local instance mainFamilyGroups {W : Unit→Type} [∀ target,AddCommGroup (W target)]
 (n : Nat) : ∀ target,AddCommGroup (L.Value W n target) := L.groups W n
attribute [local irreducible] sourcePacketWhole SourceActualWriteAcceptance SourceActualInventoryAcceptance SourceActualWholeAcceptance SourceCofinalCurrentAcceptance
attribute [local irreducible] actualFutureFactory actualFuturePacket actualFutureInitial actualFutureLiteral actualFutureMother
variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ())
variable (packet : OriginalKSourceFeedbackSuccessorAction.AP.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=()))
variable (ordinal : Nat)

private theorem source_three_joint {P Q R : Prop} (first : P) (second : Q) (third : R) : P ∧ Q ∧ R := ⟨first,second,third⟩

private def SourceSyntaxAcceptance
 {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
 (literalCode : Expr (PairValue W) X ()) (mother : SF.Factory W X ())
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
 (language : cfg.LowVar=X) (stage : Nat) : Prop :=
 (type_of% (cofinal_source_moving_equation literalCode mother initial cfg language stage)) ∧
 (type_of% (cofinal_source_correction_boundary literalCode mother initial cfg language stage)) ∧
 (type_of% (cofinal_source_correction_pair literalCode mother initial cfg language stage))
attribute [local irreducible] SourceSyntaxAcceptance
private theorem source_syntax_acceptance
 {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
 (literalCode : Expr (PairValue W) X ()) (mother : SF.Factory W X ())
 (initial : M.Frame (Value:=W) (Var:=X) (sort:=()))
 (cfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=()))
 (language : cfg.LowVar=X) (stage : Nat) : SourceSyntaxAcceptance literalCode mother initial cfg language stage := by
 unfold SourceSyntaxAcceptance
 exact source_three_joint (cofinal_source_moving_equation literalCode mother initial cfg language stage)
  (cofinal_source_correction_boundary literalCode mother initial cfg language stage)
  (cofinal_source_correction_pair literalCode mother initial cfg language stage)

/-- The joint source acceptance directly consumes each existing paid obligation. -/
def ActualCofinalSourceAcceptance : Prop :=
 (type_of% (source_actual_write_acceptance (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal))) ∧
 (type_of% (source_actual_inventory_acceptance (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal))) ∧
 (type_of% (source_actual_whole_acceptance (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal)))
attribute [local irreducible] ActualCofinalSourceAcceptance
theorem actualCofinalSourceAcceptance : ActualCofinalSourceAcceptance t factory packet ordinal := by
 unfold ActualCofinalSourceAcceptance
 exact ⟨source_actual_write_acceptance (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal),
  source_actual_inventory_acceptance (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal),
  source_actual_whole_acceptance (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal)⟩

/-- The joint source acceptance directly consumes each existing paid obligation. -/
def ActualCofinalPriceAcceptance : Prop :=
 (type_of% (actual_future_whole_raw_action t factory packet ordinal)) ∧
 (type_of% (actual_future_whole_raw_fee t factory packet ordinal)) ∧
 (type_of% (actual_future_whole_tail_budget t factory packet ordinal))
attribute [local irreducible] ActualCofinalPriceAcceptance
theorem actualCofinalPriceAcceptance : ActualCofinalPriceAcceptance t factory packet ordinal := by
 unfold ActualCofinalPriceAcceptance
 exact ⟨actual_future_whole_raw_action t factory packet ordinal,
  actual_future_whole_raw_fee t factory packet ordinal,
  actual_future_whole_tail_budget t factory packet ordinal⟩

/-- The joint source acceptance directly consumes each existing paid obligation. -/
def ActualCofinalRuntimeAcceptance : Prop :=
 (type_of% (source_installed_actual_successor (Parent.actualCofinalLiteralCode t factory packet) (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet) (ordinal+1))) ∧
 (type_of% (source_installed_cofinal_code (Parent.actualCofinalLiteralCode t factory packet) (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet) ordinal)) ∧
 (type_of% (source_cofinal_current_environment (actualFutureLiteral t factory packet) (actualFutureMother t factory packet) (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl ordinal))
attribute [local irreducible] ActualCofinalRuntimeAcceptance
theorem actualCofinalRuntimeAcceptance : ActualCofinalRuntimeAcceptance t factory packet ordinal := by
 unfold ActualCofinalRuntimeAcceptance
 exact ⟨source_installed_actual_successor (Parent.actualCofinalLiteralCode t factory packet) (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet) (ordinal+1),
  source_installed_cofinal_code (Parent.actualCofinalLiteralCode t factory packet) (Parent.actualCofinalMotherFactory t factory packet) (Parent.actualIncomingBornPacket t factory packet) ordinal,
  source_cofinal_current_environment (actualFutureLiteral t factory packet) (actualFutureMother t factory packet) (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl ordinal⟩

/-- The joint source acceptance directly consumes each existing paid obligation. -/
def ActualCofinalSyntaxAcceptance : Prop := SourceSyntaxAcceptance (actualFutureLiteral t factory packet) (actualFutureMother t factory packet) (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl ordinal
attribute [local irreducible] ActualCofinalSyntaxAcceptance
theorem actualCofinalSyntaxAcceptance : ActualCofinalSyntaxAcceptance t factory packet ordinal := by
 unfold ActualCofinalSyntaxAcceptance
 exact source_syntax_acceptance (actualFutureLiteral t factory packet) (actualFutureMother t factory packet) (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl ordinal

/-- The joint source acceptance directly consumes each existing paid obligation. -/
def ActualCofinalRootAcceptance : Prop :=
 (type_of% (source_actual_whole_root (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal))) ∧
 (type_of% (source_actual_whole_current (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal))) ∧
 (type_of% (source_actual_cofinal_current (actualFutureFactory t factory packet) (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl (ordinal+1)))
attribute [local irreducible] ActualCofinalRootAcceptance
theorem actualCofinalRootAcceptance : ActualCofinalRootAcceptance t factory packet ordinal := by
 unfold ActualCofinalRootAcceptance
 exact ⟨source_actual_whole_root (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal),
  source_actual_whole_current (actualFutureFactory t factory packet) (actualFuturePacket t factory packet ordinal),
  source_actual_cofinal_current (actualFutureFactory t factory packet) (actualFutureInitial t factory packet) (actualFutureProgramme t factory packet) rfl (ordinal+1)⟩

/-- Every real source admission consumes the same complete source, whole, syntax and independent prices. -/
theorem actual_source_cofinal_native_successor :
 ActualCofinalSourceAcceptance t factory packet ordinal ∧
 ActualCofinalPriceAcceptance t factory packet ordinal ∧
 ActualCofinalRuntimeAcceptance t factory packet ordinal ∧
 ActualCofinalSyntaxAcceptance t factory packet ordinal ∧
 ActualCofinalRootAcceptance t factory packet ordinal :=
 ⟨actualCofinalSourceAcceptance t factory packet ordinal,
  actualCofinalPriceAcceptance t factory packet ordinal,
  actualCofinalRuntimeAcceptance t factory packet ordinal,
  actualCofinalSyntaxAcceptance t factory packet ordinal,
  actualCofinalRootAcceptance t factory packet ordinal⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceCofinalNativeSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
