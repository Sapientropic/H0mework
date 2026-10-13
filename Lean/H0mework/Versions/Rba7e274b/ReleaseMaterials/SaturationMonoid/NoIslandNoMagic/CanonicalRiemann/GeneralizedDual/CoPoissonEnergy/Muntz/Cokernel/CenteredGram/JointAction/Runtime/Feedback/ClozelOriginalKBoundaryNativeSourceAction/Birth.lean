import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNativeSourceAction.Payment
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
local instance birthGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade target
namespace Native
export ActualCofinalSourceAction (receipt)
end Native
namespace ST
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
 (birthProgram compiles_settled target_current target_root)
end ST
namespace SO
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
 (root visit)
end SO

private def birthAt
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :=
 (ST.birthProgram (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)).generate
 ((SO.root (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (SO.visit (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)))

private theorem birth_compiles_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (ST.compiles_settled (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)
   (Native.receipt producer packet).2.1 (Native.receipt producer packet).2.2.2) :=
 ST.compiles_settled (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)
   (Native.receipt producer packet).2.1 (Native.receipt producer packet).2.2.2

private theorem birth_next_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (ST.target_current (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)
   ((SO.root (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (SO.visit (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)))) :=
 ST.target_current _ _ _

private theorem birth_whole_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (birthAt producer packet).target.firstDestination_heq :=
 (birthAt producer packet).target.firstDestination_heq

private theorem birth_source_root_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) :
 HEq (birthAt producer packet).target.targetRoot
 (SO.root (ActualCofinalSourceAction.sourceBorn producer packet).2.1.1
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1)) :=
 heq_of_eq (ST.target_root (Native.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (Native.nativePacket producer packet).2.2.1) _)

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h : ℝ)
def actualBirth := birthAt (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)

theorem actual_born_compiles : type_of% (birth_compiles_at
 (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)) :=
 birth_compiles_at _ _

theorem actual_born_whole : type_of% (birth_whole_at
 (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)) :=
 birth_whole_at _ _

theorem actual_born_next : type_of% (birth_next_at
 (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)) :=
 birth_next_at _ _

theorem actual_born_source_root : type_of% (birth_source_root_at
 (factory observation nontrivial half depth ordinal h)
 (actionPacket observation nontrivial half depth ordinal h)) :=
 birth_source_root_at _ _

theorem actual_born_environment : type_of%
 (actual_orbit_born_environment observation nontrivial half depth ordinal h) :=
 actual_orbit_born_environment _ _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
