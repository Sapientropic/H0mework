import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Finite.Reader.Next
import H0mework.Versions.MF.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Psi.Action.Equation

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference
namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (nextPacket)
end A
namespace R
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual (cfg after material expression)
end R
namespace Sc
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Scope (requestWord)
end Sc
namespace E
export Lower.SourceFamily.Foresight.Contextual.Effect (actualDecoder actualIncrement actual_paid_value)
end E
namespace Claim
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim (activeExpression activeEnv activeWord input_environment input_expression)
end Claim
namespace Env
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Environment (decoder_active head_channels activeIncrement)
end Env
namespace Pmt
export Lower.SourceFamily.Effect.PaidSource (Paid paid_of_budget)
end Pmt
namespace Ph
export Lower.SourceFamily.Foresight.Contextual.Profile.ActiveClaim.Clock (active_remainder_positive)
end Ph
namespace T
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (writerValue writer_head afterq constant writer_affine head head_constant)
end T
namespace Ps
export Lower.SourceFamily.Foresight.Contextual.Psi.Equation (terminalValue terminal_value beta boundary_affine)
end Ps
namespace Nx
export Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.Next
 (boundary nextHistory actual_relation)
end Nx
namespace Cl
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure (actual_after_boundary)
end Cl
namespace G
export Lower.SourceFamily.Foresight.Contextual.Profile.Generated (source_scope_action)
end G
namespace K
export Lower.SourceFamily.Foresight.Contextual.Profile.Kernel (afterFace afterDisposition)
end K
namespace A2
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly (afterFrame afterIndex afterSource)
end A2
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (free_evaluation)
end D
namespace Projection
export Lower.SourceFamily.Foresight.Contextual.Phase.Scope.ClosureProjection (evaluation)
end Projection
namespace Disposition
export Lower.SourceFamily.Foresight.Contextual.Psi.Closure.DispositionProjection (At read)
end Disposition
namespace DispositionEffect
export Lower.SourceFamily.Foresight.Contextual.Psi.EffectConsumption.DispositionProjection (At read)
end DispositionEffect
private theorem pair_difference {A:Type u} [AddCommGroup A] (left right:A):
 (left,right)-(left,0)=(0,right):=
 Prod.ext (sub_self _) (sub_zero _)
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (prior:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev packet:=A.nextPacket binding n prior

theorem actual_paid:Pmt.Paid (packet binding n prior).1:=
 Pmt.paid_of_budget (packet binding n prior).1 (Ph.active_remainder_positive binding n prior)

theorem own_after_decoder:E.actualDecoder binding (n+1) (packet binding n prior)=
 R.after binding (n+1) (packet binding n prior):=
 (Env.decoder_active binding (n+1) (packet binding n prior) (actual_paid binding n prior)).trans
 (Claim.input_environment binding (n+1) (packet binding n prior))

theorem same_expression:Claim.activeExpression binding (n+1) (packet binding n prior)=
 R.expression binding (n+1) (packet binding n prior):=Claim.input_expression _ _ _

theorem same_word:Claim.activeWord binding (n+1) (packet binding n prior)=
 Sc.requestWord binding (n+1) (packet binding n prior):=
 congrArg (fun expression=>Finsupp.single expression (1:ℤ)) (same_expression binding n prior)

theorem terminal_value:Ps.terminalValue binding (n+1) (packet binding n prior)=
 (R.expression binding (n+1) (packet binding n prior)).eval (R.after binding (n+1) (packet binding n prior)):=
 (Ps.terminal_value binding (n+1) (packet binding n prior)).trans
 (congrArg₂ (fun expression=>fun environment=>expression.eval environment)
  (same_expression binding n prior) (Claim.input_environment binding (n+1) (packet binding n prior)))

theorem actual_pair:
 T.writerValue binding (n+1) (packet binding n prior) (Sc.requestWord binding (n+1) (packet binding n prior))=
 ((R.expression binding (n+1) (packet binding n prior)).eval (R.after binding (n+1) (packet binding n prior)),
  (R.expression binding (n+1) (packet binding n prior)).effect (R.after binding (n+1) (packet binding n prior))
   (Env.activeIncrement binding (n+1) (packet binding n prior))):=by
 have word:=same_word binding n prior
 have head:=T.writer_head binding (n+1) (packet binding n prior) (Sc.requestWord binding (n+1) (packet binding n prior))
 have channels:=Env.head_channels binding (n+1) (packet binding n prior) (actual_paid binding n prior)
 rw [word] at channels
 exact head.symm.trans (channels.trans (congrArg₂ Prod.mk
  (congrArg₂ (fun expression=>fun environment=>expression.eval environment)
   (same_expression binding n prior) (Claim.input_environment binding (n+1) (packet binding n prior)))
  (congrArg₂ (fun expression=>fun environment=>expression.effect environment
    (Env.activeIncrement binding (n+1) (packet binding n prior)))
   (same_expression binding n prior) (Claim.input_environment binding (n+1) (packet binding n prior)))))

theorem same_increment:E.actualIncrement binding (n+1) (packet binding n prior)=
 Env.activeIncrement binding (n+1) (packet binding n prior):=
 congrArg (fun environment=>SourceSubstitution.sourceEnvironment
  (Future.Replay.Binding.at binding (n+1+1)) environment-environment)
  (Env.decoder_active binding (n+1) (packet binding n prior) (actual_paid binding n prior))

def sigmaEffect:Lower.Value W (n+1+1) s:=(R.expression binding (n+1) (packet binding n prior)).effect
 (R.after binding (n+1) (packet binding n prior)) (E.actualIncrement binding (n+1) (packet binding n prior))

theorem generated_pair:
 T.writerValue binding (n+1) (packet binding n prior) (Sc.requestWord binding (n+1) (packet binding n prior))=
 (Ps.terminalValue binding (n+1) (packet binding n prior),sigmaEffect binding n prior):=
 (actual_pair binding n prior).trans (congrArg₂ Prod.mk (terminal_value binding n prior).symm
  (congrArg ((R.expression binding (n+1) (packet binding n prior)).effect
   (R.after binding (n+1) (packet binding n prior))) (same_increment binding n prior).symm))

def correction:=T.writerValue binding (n+1) (packet binding n prior)
 (Sc.requestWord binding (n+1) (packet binding n prior))-
 (Ps.terminalValue binding (n+1) (packet binding n prior),0)
theorem correction_generated:correction binding n prior=(0,sigmaEffect binding n prior):=
 (congrArg (fun value:PairValue (Lower.Value W (n+1+1)) s=>value-
  (Ps.terminalValue binding (n+1) (packet binding n prior),0)) (generated_pair binding n prior)).trans
 (pair_difference (Ps.terminalValue binding (n+1) (packet binding n prior)) (sigmaEffect binding n prior))

def difference:=liftMap (Ps.beta binding (n+1) (packet binding n prior))-
 Nx.boundary binding (n+1) (packet binding n prior)
theorem difference_in_actual_history:difference binding n prior∈
 (Nx.nextHistory binding (n+1) (packet binding n prior)).relationClosure:=
 (Nx.nextHistory binding (n+1) (packet binding n prior)).relationClosure.sub_mem
  (Cl.actual_after_boundary binding (n+1) (packet binding n prior))
  (Nx.actual_relation binding (n+1) (packet binding n prior))

def vector:(Nx.nextHistory binding (n+1) (packet binding n prior)).generatorClosure:=
 ⟨difference binding n prior,
  (Nx.nextHistory binding (n+1) (packet binding n prior)).relationClosure_le_generatorClosure
   (difference_in_actual_history binding n prior)⟩
theorem vector_val:(vector binding n prior).val=difference binding n prior:=rfl

theorem scope_constant_difference:
 T.afterq binding (n+1) (packet binding n prior) (difference binding n prior)=
 T.constant binding (n+1) (packet binding n prior) (correction binding n prior):=by
 let rootPoint:=T.afterq binding (n+1) (packet binding n prior)
  (liftMap (Sc.requestWord binding (n+1) (packet binding n prior)))
 let psiPoint:=T.constant binding (n+1) (packet binding n prior)
  (Ps.terminalValue binding (n+1) (packet binding n prior),0)
 let muPoint:=T.constant binding (n+1) (packet binding n prior)
  (T.writerValue binding (n+1) (packet binding n prior) (Sc.requestWord binding (n+1) (packet binding n prior)))
 have psi:T.afterq binding (n+1) (packet binding n prior) (liftMap (Ps.beta binding (n+1) (packet binding n prior)))=
  rootPoint-psiPoint:=
  (Ps.boundary_affine binding (n+1) (packet binding n prior)).trans
  (congrArg (fun word=>T.afterq binding (n+1) (packet binding n prior) (liftMap word)-psiPoint)
   (same_word binding n prior))
 have mu:T.afterq binding (n+1) (packet binding n prior)
  (Nx.boundary binding (n+1) (packet binding n prior))=rootPoint-muPoint:=
  (T.writer_affine binding (n+1) (packet binding n prior) rfl (Sc.requestWord binding (n+1) (packet binding n prior))).trans
  (congrArg (fun coordinate=>coordinate-muPoint)
   (G.source_scope_action binding (n+1) (packet binding n prior) rfl (Sc.requestWord binding (n+1) (packet binding n prior))))
 have sources:T.afterq binding (n+1) (packet binding n prior) (difference binding n prior)=
  (rootPoint-psiPoint)-(rootPoint-muPoint):=
  ((T.afterq binding (n+1) (packet binding n prior)).map_sub _ _).trans (congrArg₂ (·-·) psi mu)
 have subtract:(rootPoint-psiPoint)-(rootPoint-muPoint)=muPoint-psiPoint:=by abel
 exact sources.trans (subtract.trans ((T.constant binding (n+1) (packet binding n prior)).map_sub _ _).symm)

theorem actual_source_value:(K.afterFace binding (n+1) (packet binding n prior)).closureEvaluation
 (vector binding n prior)=T.constant binding (n+1) (packet binding n prior) (0,sigmaEffect binding n prior):=
 (Projection.evaluation (K.afterFace binding (n+1) (packet binding n prior)) (vector binding n prior)).trans
 ((congrArg (K.afterFace binding (n+1) (packet binding n prior)).freeEvaluation (vector_val binding n prior)).trans
  ((D.free_evaluation (A.nextPacket binding (n+1) (packet binding n prior)).2
    (A2.afterFrame binding (n+1) (packet binding n prior))
    (A2.afterIndex binding (n+1) (packet binding n prior)).2
    (A2.afterSource binding (n+1) (packet binding n prior)) (difference binding n prior)).trans
   ((scope_constant_difference binding n prior).trans
    (congrArg (T.constant binding (n+1) (packet binding n prior)) (correction_generated binding n prior)))))

def dispositionRead:Prop:=Disposition.At (K.afterFace binding (n+1) (packet binding n prior))
 (difference binding n prior) (K.afterDisposition binding (n+1) (packet binding n prior))
theorem actual_disposition:dispositionRead binding n prior:=
 Disposition.read (K.afterFace binding (n+1) (packet binding n prior)) (difference binding n prior)
  (difference_in_actual_history binding n prior) (K.afterDisposition binding (n+1) (packet binding n prior))

private theorem sound_sigma_zero (sound:GeneratedRelationSoundnessAt (K.afterFace binding (n+1) (packet binding n prior))):
 sigmaEffect binding n prior=0:=by
 have zero: T.constant binding (n+1) (packet binding n prior) (0,sigmaEffect binding n prior)=0:=
  (actual_source_value binding n prior).symm.trans
   (LinearMap.mem_ker.mp ((K.afterFace binding (n+1) (packet binding n prior)).relationInGeneratorClosure_le_kernel
    sound (difference_in_actual_history binding n prior)))
 have channels:((0:Lower.Value W (n+1+1) s),sigmaEffect binding n prior)=0:=
  (T.head_constant binding (n+1) (packet binding n prior) _).symm.trans
   ((congrArg (T.head binding (n+1) (packet binding n prior)) zero).trans
    (map_zero (T.head binding (n+1) (packet binding n prior))))
 exact congrArg Prod.snd channels

def effectRead:Prop:=DispositionEffect.At (K.afterFace binding (n+1) (packet binding n prior))
 (sigmaEffect binding n prior=0) (K.afterDisposition binding (n+1) (packet binding n prior))
theorem actual_disposition_effect:effectRead binding n prior:=
 DispositionEffect.read (K.afterFace binding (n+1) (packet binding n prior)) (sigmaEffect binding n prior=0)
  (sound_sigma_zero binding n prior) (K.afterDisposition binding (n+1) (packet binding n prior))
end Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.PaidDifference
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
