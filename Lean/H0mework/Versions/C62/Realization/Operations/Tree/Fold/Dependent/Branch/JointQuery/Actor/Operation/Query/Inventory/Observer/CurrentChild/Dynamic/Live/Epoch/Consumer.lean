import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Origin.Consumer
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Epoch
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
variable (frame : Dynamic.Frame root visit recognition) (count : Nat)
variable (sourceOrigin : Origin.UniformAt root visit recognition frame count)
variable {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
variable (supplied : Dynamic.C.Occurrence frame (current:=current))

theorem current_read : Dynamic.currentRead root visit recognition (E.epoch frame) supplied =
 Dynamic.currentRead root visit recognition frame supplied := rfl

include sourceOrigin in
theorem current_support : Dynamic.supportFor root visit recognition (E.epoch frame)
 (Dynamic.currentRead root visit recognition (E.epoch frame)) supplied =
 [Dynamic.actorAtCount root visit recognition (count+1)] := by
 apply Dynamic.support_of_origin root visit recognition (E.epoch frame)
  (Dynamic.currentRead root visit recognition (E.epoch frame)) supplied count
 intro datum
 rw [current_read]
 exact sourceOrigin current supplied datum

include sourceOrigin in
theorem next_support : Dynamic.supportFor root visit recognition (E.epoch frame)
 (Dynamic.nextRead root visit recognition (E.epoch frame)) supplied =
 [Dynamic.actorAtCount root visit recognition (count+2)] := by
 apply Dynamic.support_of_origin root visit recognition (E.epoch frame)
  (Dynamic.nextRead root visit recognition (E.epoch frame)) supplied (count+1)
 intro datum
 have shift : Dynamic.generatedEnvironmentAt root visit recognition (E.epoch frame) supplied
   (Origin.coreSlot root recognition) (datum,.old) (0:Fin 2) =
   Dynamic.environmentAt root visit recognition (E.epoch frame) supplied
    (Origin.coreSlot root recognition) (Branch.nextNode root visit recognition datum,.old) (0:Fin 2) := rfl
 apply shift.trans
 have prior := sourceOrigin current supplied (Branch.nextNode root visit recognition datum)
 change Dynamic.currentRead root visit recognition frame supplied (Origin.coreSlot root recognition)
  (Branch.nextNode root visit recognition datum,.old) (0:Fin 2) = _ at prior
 rw [←current_read root visit recognition frame supplied] at prior
 apply prior.trans
 unfold Origin.pairAt Dynamic.orbitPair
 rw [←Function.iterate_succ_apply,←Function.iterate_succ_apply]

end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Epoch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
