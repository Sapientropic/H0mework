import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeRuntimeFace.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeRuntimeFace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
local instance birthGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade target
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
 (ST.birthProgram (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)).generate
 ((SO.root (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
 (SO.visit (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)))

private theorem birth_compiles_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (ST.compiles_settled (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   (N.receipt producer packet).2.1 (N.receipt producer packet).2.2.2) :=
 ST.compiles_settled (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   (N.receipt producer packet).2.1 (N.receipt producer packet).2.2.2

private theorem birth_next_at
 (producer : SF.Factory (PairValue C.Value) C.Var ())
 (packet : AS.AdmissionPacket (W:=PairValue C.Value) (X:=C.Var) (s:=())) : type_of%
 (ST.target_current (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)
   ((SO.root (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
   (SO.visit (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)))) :=
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
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1)) :=
 heq_of_eq (ST.target_root (N.selected producer packet)
   (ActualCofinalSourceAction.AS.stockCfg (N.nativePacket producer packet).2.2.1) _)

variable (observation : NoIslandNoMagic.CanonicalRiemann.GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
def actualBirth := birthAt (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)

theorem actual_born_compiles : type_of% (birth_compiles_at
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 birth_compiles_at _ _

theorem actual_born_whole : type_of% (birth_whole_at
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 birth_whole_at _ _

theorem actual_born_next : type_of% (birth_next_at
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 birth_next_at _ _

theorem actual_born_source_root : type_of% (birth_source_root_at
 (OriginalKFullSourceRAction.factory observation nontrivial half)
 (OriginalKFullSourceRAction.actionPacket observation nontrivial half depth ordinal)) :=
 birth_source_root_at _ _

theorem actual_born_environment : type_of%
 (OriginalKFullSourceRAction.actual_R_born_environment observation nontrivial half depth ordinal) :=
 OriginalKFullSourceRAction.actual_R_born_environment _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeRuntimeFace
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
