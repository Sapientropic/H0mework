import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage
open RootInquiryCompletion SourceOperationEffects
variable {S : Type u} {A X : S → Type u} [∀ s,AddCommGroup (A s)] {s : S}
variable (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame (Value:=A) (Var:=X) (sort:=s))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme (PhysicalValue:=A) (PhysicalVar:=X) (sort:=s))
theorem stateAt_injective : Function.Injective (Shared.runtime initial configuration).stateAt := by
 intro first second same
 have engines := congrArg (fun state => state.engine.node) same
 rw [Shared.actual_node,Shared.actual_node] at engines
 exact Shared.frames_erase_injective initial configuration
   (congrArg RootInquiryProcessNode.erase engines)
theorem generated_next_injective (first second : Nat)
    (same : ((Shared.runtime initial configuration).stateAt first).tick.nextState=
      ((Shared.runtime initial configuration).stateAt second).tick.nextState) : first=second := by
  have indices : first+1=second+1 := stateAt_injective initial configuration same
  exact Nat.add_right_cancel indices
theorem embed_injective : Function.Injective (embed initial configuration) :=
 Finsupp.mapDomain_injective (stateAt_injective initial configuration)
theorem action_source : (SourceOperationInquiry.sourceAction (Shared.runtime initial configuration)).comp (embed initial configuration)=
    (embed initial configuration).comp shift := by
 apply Finsupp.lhom_ext
 intro stage coefficient
 simp only [LinearMap.comp_apply,embed,shift,SourceOperationInquiry.sourceAction,
   SourceOwnedObservationHistory.sourceAction,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
 rfl
theorem shift_injective : Function.Injective (shift : Word →ₗ[ℤ] Word) :=
 Finsupp.mapDomain_injective Nat.succ_injective
theorem action_generated_injective (first second : Word)
    (same : SourceOperationInquiry.sourceAction (Shared.runtime initial configuration) (embed initial configuration first)=
      SourceOperationInquiry.sourceAction (Shared.runtime initial configuration) (embed initial configuration second)) : first=second := by
 have left := LinearMap.congr_fun (action_source initial configuration) first
 have right := LinearMap.congr_fun (action_source initial configuration) second
 exact shift_injective (embed_injective initial configuration (left.symm.trans (same.trans right)))
theorem observed_effect : (observed initial configuration).comp shift-observed initial configuration=effect initial configuration := by
 apply Finsupp.lhom_ext
 intro stage coefficient
 simp only [LinearMap.sub_apply,LinearMap.comp_apply,shift,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single,
   observed,effect,Finsupp.linearCombination_single]
 change coefficient • SourceOperationInquiry.Context.readEnv _ _ ((Shared.runtime initial configuration).stateAt (stage+1)) -
   coefficient • SourceOperationInquiry.Context.readEnv _ _ ((Shared.runtime initial configuration).stateAt stage)=
   coefficient • (SourceOperationInquiry.Context.readEnv _ _ ((Shared.runtime initial configuration).stateAt (stage+1))-
     SourceOperationInquiry.Context.readEnv _ _ ((Shared.runtime initial configuration).stateAt stage))
 exact (smul_sub coefficient _ _).symm
theorem environment_source (word : Word) :
    SourceOperationInquiry.Context.environment (Shared.runtime initial configuration) (source initial configuration)
      (embed initial configuration word)=observed initial configuration word := by
 change (Finsupp.linearCombination ℤ (SourceOperationInquiry.Context.readEnv (Shared.runtime initial configuration)
   (source initial configuration))) (embed initial configuration word)=_
 exact LinearMap.congr_fun (Finsupp.linearCombination_comp_lmapDomain ℤ _) word
theorem whole_effect (word : Word) :
    SourceOperationInquiry.Context.environment (Shared.runtime initial configuration) (source initial configuration)
      (SourceOperationInquiry.sourceAction (Shared.runtime initial configuration) (embed initial configuration word)-
        embed initial configuration word)=effect initial configuration word := by
 have acted : SourceOperationInquiry.sourceAction (Shared.runtime initial configuration) (embed initial configuration word)=
   embed initial configuration (shift word) := LinearMap.congr_fun (action_source initial configuration) word
 rw [map_sub,acted,environment_source,environment_source]
 exact LinearMap.congr_fun (observed_effect initial configuration) word
theorem observation_complete (word : Word) :
    (observationFibre initial configuration).symm (observationFibre initial configuration word)=word :=
 (observationFibre initial configuration).symm_apply_apply word
theorem effect_complete (word : Word) :
    (effectFibre initial configuration).symm (effectFibre initial configuration word)=word :=
 (effectFibre initial configuration).symm_apply_apply word
theorem after_source (word : Word) :
    embed initial configuration (shift word)=
      SourceOperationInquiry.sourceAction (Shared.runtime initial configuration) (embed initial configuration word) :=
 (LinearMap.congr_fun (action_source initial configuration) word).symm
theorem after_observed (word : Word) :
    observed initial configuration (shift word)-observed initial configuration word=effect initial configuration word :=
 LinearMap.congr_fun (observed_effect initial configuration) word
theorem embed_point (stage : Nat) : embed initial configuration (Finsupp.single stage 1)=
    SourceOperationInquiry.point (Shared.runtime initial configuration) ((Shared.runtime initial configuration).stateAt stage) := by
 simp only [embed,Finsupp.lmapDomain_apply,Finsupp.mapDomain_single]
 rfl
end SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation.Lineage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
