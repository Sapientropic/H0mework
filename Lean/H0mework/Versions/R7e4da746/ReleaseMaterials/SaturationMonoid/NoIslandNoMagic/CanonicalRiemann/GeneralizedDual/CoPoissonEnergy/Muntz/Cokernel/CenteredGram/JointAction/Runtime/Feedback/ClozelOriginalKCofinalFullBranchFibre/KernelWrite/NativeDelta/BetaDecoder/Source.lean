import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Root
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Affine.Lift
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction.Continuation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.CofinalQuery.Decoder

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
open private native_decoded_old native_decoded_increment native_decoded_residual complete_update_fibre from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.CofinalQuery.Decoder
open private receipt_expression material_sigma_effect from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Source
namespace WB
export NativeSigma.Writeback
 (nativeBoundary nativeInverseValue bornWord admissionWord receiptSelected)
end WB
namespace RB
export ActualRegisteredBornEffect (registered_inverse registered_effect)
end RB
local instance decoderGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

section AffineReceipts
variable {V X : Unit→Type} [∀ target,AddCommGroup (V target)]
variable (initial : A.M.Frame (Value:=V) (Var:=X) (sort:=()))
variable (cfg : A.Programme (PhysicalValue:=V) (PhysicalVar:=X) (sort:=()))

private theorem receipt_effect_at (before change : Env V X) :
 effectEvaluator (R:=ℤ) before change
  (NativeSigma.FF.boundary (NativeSigma.AN.paid (S.Complete.atReceipt cfg initial 0)))=
 initial.registered.input.expression.effect before change := by
 rw [NativeSigma.FF.source_boundary]
 have endpoint : (NativeSigma.AN.paid (S.Complete.atReceipt cfg initial 0)).state.1=
  .const (S.Complete.receipt cfg initial 0).2.1.1 := (S.Complete.receipt cfg initial 0).2.1.2.down
 rw [endpoint,SourceSigmaAffineAction.literal_boundary_effect,NativeSigma.AN.paid_raw,receipt_expression]

private theorem receipt_lift_effect_at (before change : Env (PairValue V) X) :
 effectEvaluator (R:=ℤ) before change
  (liftMap (R:=ℤ) (NativeSigma.FF.boundary (NativeSigma.AN.paid (S.Complete.atReceipt cfg initial 0))))=
 (liftExpr initial.registered.input.expression).effect before change := by
 rw [NativeSigma.FF.source_boundary]
 have endpoint : (NativeSigma.AN.paid (S.Complete.atReceipt cfg initial 0)).state.1=
  .const (S.Complete.receipt cfg initial 0).2.1.1 := (S.Complete.receipt cfg initial 0).2.1.2.down
 rw [endpoint,SourceSigmaAffineAction.lift_literal_boundary_effect,NativeSigma.AN.paid_raw,receipt_expression]

private theorem lift_sigma_effect (before change : Env (PairValue (PairValue V)) cfg.LowVar) :
 (liftExpr (NativeSigma.N.expression (NativeSigma.R.actualMaterial initial cfg))).effect before change=
 (liftExpr (NativeSigma.R.actualMaterial initial cfg).raw).effect before change := by
 have endpoint : (NativeSigma.R.actualMaterial initial cfg).state.1=
  .const (NativeSigma.R.actionResultAt initial cfg (S.actualOccurrence initial)).2.2.1 :=
  NativeSigma.Own.target_expression (NativeSigma.Shared.baseRoot initial cfg).toAuthoritativeRoot _
   (fun _=>NativeSigma.R.actionReader initial cfg (S.actualOccurrence initial))
 rw [NativeSigma.N.expression,endpoint]
 exact SourceSigmaAffineAction.lift_affine_effect _ _ before change
end AffineReceipts

variable (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket)
abbrev nextNative := AS.nativeAfterAdmission factory (AS.bornAfterNative native)
def admittedBeta := WB.admissionWord factory (AS.bornAfterNative native)
 (liftMap (R:=ℤ) (WB.bornWord native (WB.nativeBoundary native)))
def old := (NativeSigma.AN.paid (WB.receiptSelected (nextNative factory native))).environment
def increment := NativeSigma.RB.delta (WB.receiptSelected (nextNative factory native)) (nextNative factory native).2.2.1

/-- Read the actual following decoder, retaining the entire admitted source word. -/
theorem actual_decoder_inverse :
 (residualEquivRange
  (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
  (canonicalResidual
   (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
   (admittedBeta factory native))).val=
 evaluation (R:=ℤ) (old factory native) (admittedBeta factory native)+
 effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native) :=
 native_decoded_residual (nextNative factory native) (admittedBeta factory native)

private theorem next_native_inverse :
 WB.nativeInverseValue (nextNative factory native)=
 effectEvaluator (R:=ℤ) (old factory native) (increment factory native)
  (WB.nativeBoundary (nextNative factory native)) :=
 (RB.registered_inverse (WB.receiptSelected (nextNative factory native)) (nextNative factory native).2.2.1).trans
  (RB.registered_effect (WB.receiptSelected (nextNative factory native)) (nextNative factory native).2.2.1)

variable (code : Expr (PairValue (PairValue C.Value)) C.Var ())
variable (packet : NativeSigma.NativePacket)
private abbrev sourceFactory := NativeSigma.Writeback.Input.withActualInput code
 (SF.defaultFactory (PairValue C.Value) C.Var ())

private theorem beta_action_step
 (source : NativeSigma.Writeback.Input.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down)
 (factory_actual : factory=sourceFactory code)
 (native_actual : native=AS.nativeAfterAdmission factory packet) :
 effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
 WB.nativeInverseValue (nextNative factory native) := by
 subst factory
 subst native
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  let packet : NativeSigma.NativePacket:=⟨grade,data,cfg,⟨rfl⟩⟩
  let factory:=sourceFactory code
  let first:=AS.nativeAfterAdmission factory packet
  let born:=AS.bornAfterNative first
  let second:=AS.nativeAfterAdmission factory born
  let before : Env (PairValue (PairValue (L.Value (PairValue C.Value) grade))) C.Var:=old factory first
  let change : Env (PairValue (PairValue (L.Value (PairValue C.Value) grade))) C.Var:=increment factory first
  have raw : (NativeSigma.R.actualMaterial data.1 cfg).raw=CF.codeAt code grade := by
   have input := (AS.stock_action_reader data.1 cfg (S.actualOccurrence data.1)).symm.trans
    (source data.1 (S.actualOccurrence data.1))
   exact congrArg (fun input=>input.expression) input
  have firstExpr:=NativeSigma.CA.receiver_ast factory packet
  have firstEffect : effectEvaluator (R:=ℤ) before change (admittedBeta factory first)=
   (liftExpr (CF.codeAt code grade)).effect before change := by
   have receiptRead:=receipt_lift_effect_at (V:=PairValue (L.Value (PairValue C.Value) grade)) (X:=C.Var) first.2.1.1 (AS.stockCfg first.2.2.1) before change
   have residualRead:=congrArg (fun expression : Expr (PairValue (L.Value (PairValue C.Value) grade)) C.Var ()=>(liftExpr expression).effect before change) firstExpr
   have sigmaRead:=lift_sigma_effect (V:=L.Value (PairValue C.Value) grade) (X:=C.Var) data.1 cfg before change
   have codeRead:=congrArg (fun expression : Expr (PairValue (L.Value (PairValue C.Value) grade)) C.Var ()=>(liftExpr expression).effect before change) raw
   exact receiptRead.trans (residualRead.trans (sigmaRead.trans codeRead))
  have installed:=NativeSigma.Writeback.Input.born_after_native_input code first
   (NativeSigma.Writeback.Input.native_after_admission_input code
    (SF.defaultFactory (PairValue C.Value) C.Var ()) packet)
  have nextRaw : (NativeSigma.R.actualMaterial born.2.1.1 born.2.2.1).raw=CF.codeAt code first.1 := by
   have input := (AS.stock_action_reader born.2.1.1 born.2.2.1 (S.actualOccurrence born.2.1.1)).symm.trans
    (installed born.2.1.1 (S.actualOccurrence born.2.1.1))
   exact congrArg (fun input=>input.expression) input
  have secondExpr:=NativeSigma.CA.receiver_ast factory born
  have secondEffect : effectEvaluator (R:=ℤ) before change (WB.nativeBoundary second)=
   (CF.codeAt code first.1).effect before change := by
   have receiptRead:=receipt_effect_at (V:=PairValue (PairValue (L.Value (PairValue C.Value) grade))) (X:=C.Var) second.2.1.1 (AS.stockCfg second.2.2.1) before change
   have residualRead:=congrArg (fun expression : Expr (PairValue (PairValue (L.Value (PairValue C.Value) grade))) C.Var ()=>expression.effect before change) secondExpr
   have sigmaRead:=material_sigma_effect (V:=PairValue (L.Value (PairValue C.Value) grade)) (X:=C.Var) born.2.1.1 born.2.2.1 before change
   have codeRead:=congrArg (fun expression : Expr (PairValue (PairValue (L.Value (PairValue C.Value) grade))) C.Var ()=>expression.effect before change) nextRaw
   exact receiptRead.trans (residualRead.trans (sigmaRead.trans codeRead))
  have sourceLift : liftExpr (CF.codeAt code grade)=CF.codeAt code first.1 := rfl
  exact firstEffect.trans ((congrArg (fun expression=>expression.effect before change) sourceLift).trans
   (secondEffect.symm.trans (next_native_inverse factory first).symm))

def ActionAt (code : Expr (PairValue (PairValue C.Value)) C.Var ()) (packet : NativeSigma.NativePacket) : Prop :=
 let factory:=sourceFactory code
 let native:=AS.nativeAfterAdmission factory packet
 effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
 WB.nativeInverseValue (nextNative factory native)

/-- The source's actual input profile generates the entire uncollapsed beta action equation. -/
theorem source_action
 (source : NativeSigma.Writeback.Input.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
 ActionAt code packet :=
 beta_action_step (factory:=sourceFactory code) (native:=AS.nativeAfterAdmission (sourceFactory code) packet)
  (code:=code) (packet:=packet) source rfl rfl

def EffectNonzeroAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)≠0

private theorem consume_nonzero
 (action : effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
  WB.nativeInverseValue (nextNative factory native))
 (independent : Rooting.NativeNonzeroAt (nextNative factory native)) : EffectNonzeroAt factory native :=
 fun zero=>independent (action.symm.trans zero)

def PairReadAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 (residualEquivRange (updateInventory (R:=ℤ) (old factory native) (increment factory native))
  (canonicalResidual (updateInventory (R:=ℤ) (old factory native) (increment factory native))
   (admittedBeta factory native))).val=
 (evaluation (R:=ℤ) (old factory native) (admittedBeta factory native),WB.nativeInverseValue (nextNative factory native))

private theorem consume_pair
 (action : effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
  WB.nativeInverseValue (nextNative factory native)) : PairReadAt factory native := by
 have generated :
  (residualEquivRange (updateInventory (R:=ℤ) (old factory native) (increment factory native))
   (canonicalResidual (updateInventory (R:=ℤ) (old factory native) (increment factory native))
    (admittedBeta factory native))).val=
  (evaluation (R:=ℤ) (old factory native) (admittedBeta factory native),
   effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)) := rfl
 exact generated.trans (congrArg (fun value=>(evaluation (R:=ℤ) (old factory native) (admittedBeta factory native),value)) action)

def UpdatedReadAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 (residualEquivRange
 (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
 (canonicalResidual (evaluation (R:=ℤ) (AS.bornAfterNative (nextNative factory native)).2.1.1.activeEnvironment)
  (admittedBeta factory native))).val=
 evaluation (R:=ℤ) (old factory native) (admittedBeta factory native)+WB.nativeInverseValue (nextNative factory native)

private theorem consume_updated
 (action : effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
  WB.nativeInverseValue (nextNative factory native)) : UpdatedReadAt factory native :=
 (actual_decoder_inverse factory native).trans
  (congrArg (evaluation (R:=ℤ) (old factory native) (admittedBeta factory native)+·) action)

def FibreReadAt (factory : NativeSigma.NativeFactory) (native : NativeSigma.NativePacket) : Prop :=
 ∀ candidate : type_of% (admittedBeta factory native),
 canonicalResidual (updateInventory (R:=ℤ) (old factory native) (increment factory native)) candidate=
 canonicalResidual (updateInventory (R:=ℤ) (old factory native) (increment factory native)) (admittedBeta factory native) ↔
 evaluation (R:=ℤ) (old factory native) candidate=evaluation (R:=ℤ) (old factory native) (admittedBeta factory native) ∧
 effectEvaluator (R:=ℤ) (old factory native) (increment factory native) candidate=WB.nativeInverseValue (nextNative factory native)

private theorem consume_fibre
 (action : effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
  WB.nativeInverseValue (nextNative factory native)) : FibreReadAt factory native := by
 intro candidate
 exact (complete_update_fibre (old factory native) (increment factory native) (admittedBeta factory native) candidate).trans
  (by rw [action])

def transportedEffect (target : NativeSigma.NativePacket) (same : nextNative factory native=target) :
 L.Value (PairValue C.Value) target.1 () :=
 Eq.mp (congrArg (fun packet=>L.Value (PairValue C.Value) packet.1 ()) same)
  (effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native))

private theorem transported_read (target : NativeSigma.NativePacket) (same : nextNative factory native=target)
 (action : effectEvaluator (R:=ℤ) (old factory native) (increment factory native) (admittedBeta factory native)=
  WB.nativeInverseValue (nextNative factory native)) :
 transportedEffect factory native target same=WB.nativeInverseValue target :=
 (congrArg (fun value=>Eq.mp (congrArg (fun packet=>L.Value (PairValue C.Value) packet.1 ()) same) value) action).trans
  (Rooting.inverse_transport same)

attribute [local irreducible] AS.localNativeReceipt
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem original_action : ActionAt (FR.jointCode (RSource.code observation nontrivial half))
 (originalPredecessor observation nontrivial half depth (ordinal+1)) :=
 source_action (FR.jointCode (RSource.code observation nontrivial half))
  (originalPredecessor observation nontrivial half depth (ordinal+1))
  (original_predecessor_actual_input observation nontrivial half depth (ordinal+1))

theorem original_effect_nonzero : EffectNonzeroAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 consume_nonzero _ _ (original_action observation nontrivial half depth ordinal)
  (Rooting.next_inverse_nonzero observation nontrivial half depth ordinal)

theorem original_pair : PairReadAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 consume_pair _ _ (original_action observation nontrivial half depth ordinal)

theorem original_updated : UpdatedReadAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 consume_updated _ _ (original_action observation nontrivial half depth ordinal)

theorem original_fibre : FibreReadAt (D.factory observation nontrivial half)
 (originalNative observation nontrivial half depth (ordinal+1)) :=
 consume_fibre _ _ (original_action observation nontrivial half depth ordinal)

/-- This quantity is transported by the full source-packet successor identity. -/
def originalEffectAtNext : L.Value (PairValue C.Value)
 (originalNative observation nontrivial half depth (ordinal+2)).1 () :=
 transportedEffect (D.factory observation nontrivial half)
  (originalNative observation nontrivial half depth (ordinal+1))
  (originalNative observation nontrivial half depth (ordinal+2))
  (Rooting.native_successor observation nontrivial half depth (ordinal+1)).symm

theorem original_effect_at_next : originalEffectAtNext observation nontrivial half depth ordinal=
 WB.nativeInverseValue (originalNative observation nontrivial half depth (ordinal+2)) :=
 transported_read _ _ _ (Rooting.native_successor observation nontrivial half depth (ordinal+1)).symm
  (original_action observation nontrivial half depth ordinal)

/-- The actual beta effect is consumed by the original full four-R action, before a physical sum. -/
theorem original_four_R :
 NativeSigma.collapseNative (D.factory observation nontrivial half)
  (originalPredecessor observation nontrivial half depth (ordinal+2))
  (originalEffectAtNext observation nontrivial half depth ordinal)=
 Full.branches observation nontrivial half (incrementInput observation nontrivial half depth (ordinal+2)) :=
 (congrArg (NativeSigma.collapseNative (D.factory observation nontrivial half)
  (originalPredecessor observation nontrivial half depth (ordinal+2)))
  (original_effect_at_next observation nontrivial half depth ordinal)).trans
  (actual_inverse_branches observation nontrivial half depth (ordinal+2))

private def total (value : (BurnolPhysicalState.BurnolL2×BurnolPhysicalState.BurnolL2)×
 (BurnolPhysicalState.BurnolL2×BurnolPhysicalState.BurnolL2)) :=
 (value.1.1+value.1.2)+(value.2.1+value.2.2)

def physicalEffect := total (NativeSigma.collapseNative (D.factory observation nontrivial half)
 (originalPredecessor observation nontrivial half depth (ordinal+2))
 (originalEffectAtNext observation nontrivial half depth ordinal))

private theorem physical_total : physicalEffect observation nontrivial half depth ordinal=
 inverseTotal observation nontrivial half depth (ordinal+2) :=
 congrArg total ((original_four_R observation nontrivial half depth ordinal).trans
  (actual_inverse_branches observation nontrivial half depth (ordinal+2)).symm)

/-- The original physical Division retains its complete invisible term on this exact beta action. -/
theorem original_division : physicalEffect observation nontrivial half depth ordinal=
 (responseDifference observation nontrivial half depth (ordinal+1):BurnolPhysicalState.BurnolL2)+
 P.R observation nontrivial half (Pa.invisible (physicalIncrement observation nontrivial half depth (ordinal+2))) :=
 (physical_total observation nontrivial half depth ordinal).trans
  (actual_inverse_division_split observation nontrivial half depth (ordinal+1))

theorem original_R2 : P.R observation nontrivial half (physicalEffect observation nontrivial half depth ordinal)=
 P.R observation nontrivial half (responseDifference observation nontrivial half depth (ordinal+1):BurnolPhysicalState.BurnolL2)+
 P.R observation nontrivial half (P.R observation nontrivial half
  (Pa.invisible (physicalIncrement observation nontrivial half depth (ordinal+2)))) :=
 (congrArg (P.R observation nontrivial half) (physical_total observation nontrivial half depth ordinal)).trans
  (actual_inverse_R2 observation nontrivial half depth (ordinal+1))

open private original_R_fixed_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal

/-- Nonzero physical action is derived from the original raw source and independent Gram/Q consumer. -/
theorem original_physical_nonzero : physicalEffect observation nontrivial half depth ordinal≠0 := by
 intro zero
 have rawDifference : D.raw observation nontrivial half depth (ordinal+3)-
  D.raw observation nontrivial half depth (ordinal+2)=0 :=
  (actual_inverse_successor observation nontrivial half depth (ordinal+1)).symm.trans
   ((physical_total observation nontrivial half depth ordinal).symm.trans zero)
 have fixed : P.R observation nontrivial half (D.raw observation nontrivial half depth (ordinal+2))=
  D.raw observation nontrivial half depth (ordinal+2) :=
  (D.raw_successor observation nontrivial half depth (ordinal+2)).symm.trans (sub_eq_zero.mp rawDifference)
 exact Terminal.actual_raw_ne_zero observation nontrivial half depth (ordinal+2)
  (original_R_fixed_zero observation nontrivial half _ fixed)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
