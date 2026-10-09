import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Producer
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Substitution.Source
import H0mework.Realization.ObservationActions.WordsModel
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Next
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedActionObservationHistory SourceGeneratedScalarDifferentialResidual
open CategoryTheory SourceGeneratedScalarCofinalKernelCompletion
namespace Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.SourceCore
 (carry read sigma nativeCursor profile nativeSource jointSource)
end P
namespace Main
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (sourceTarget jointSource bindingOperator)
end Main
namespace B
export Lower.SourceFamily.Foresight.Contextual.Profile.BindingSource (actions source operator operator_source)
end B
namespace F
export Lower.SourceFamily.Foresight
 (Word Model action read data completion sourceMap next next_source)
end F
namespace I
export Lower.SourceFamily.Foresight.Installed (nativeState epochIndex)
end I
namespace E
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
end E
namespace C
export SourceGeneratedScalarCharacterExact
 (Carrier canonicalMap factor factor_canonicalMap map map_canonicalMap)
end C
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
def nextPacket:=Lower.SourceFamily.step (Lower.SourceFamily.Foresight.Contextual.factory (s:=s) binding) n packet
abbrev beforeFrame:=E.epoch packet.1
abbrev afterFrame:=E.epoch (nextPacket binding n packet).1
abbrev beforeIndex:=I.epochIndex n (beforeFrame n packet)
abbrev afterIndex:=I.epochIndex (n+1) (afterFrame binding n packet)
abbrev beforeState:=I.nativeState n packet.2 (beforeFrame n packet)
abbrev afterState:=I.nativeState (n+1) (nextPacket binding n packet).2 (afterFrame binding n packet)
abbrev afterCursor:=P.nativeCursor (n+1) (afterFrame binding n packet) (afterIndex binding n packet)
def afterCarry:=P.carry (V:=Lower.Value W (n+1)) (X:=X) (s:=s)
def afterRead:=P.read (P.sigma binding (n+1)) (afterCursor binding n packet)
abbrev profileData:=AlgebraicDependent.data (afterCarry (W:=W) (X:=X) (s:=s) n) (afterRead binding n packet) 0
abbrev profileCompletion:=AlgebraicDependent.completion (afterCarry (W:=W) (X:=X) (s:=s) n) (afterRead binding n packet) 0
abbrev beforeProfile:=P.profile binding n (beforeFrame n packet) (beforeIndex n packet)
abbrev beforeProfileCompletion:=AlgebraicDependent.completion
 (P.carry (V:=Lower.Value W n) (X:=X) (s:=s))
 (P.read (P.sigma binding n) (P.nativeCursor n (beforeFrame n packet) (beforeIndex n packet))) 0
local instance beforeNativeModule (k:Nat) :Module ℤ (F.Model binding (beforeState n packet) s k):=
 (C.Carrier ℤ (F.completion binding (beforeState n packet) s k)).module
local instance afterNativeModule :Module ℤ (F.Model binding (afterState binding n packet) s 0):=
 (C.Carrier ℤ (F.completion binding (afterState binding n packet) s 0)).module
abbrev OriginalBeforeTarget:=beforeProfileCompletion binding n packet×F.Model binding (beforeState n packet) s 0
abbrev OriginalAfterTarget:=profileCompletion binding n packet×F.Model binding (afterState binding n packet) s 0
local instance originalBeforeJointModule :Module ℤ (OriginalBeforeTarget binding n packet):=Prod.instModule
local instance originalAfterJointModule :Module ℤ (OriginalAfterTarget binding n packet):=Prod.instModule
def originalBeforeSource :Formal ℤ (PairValue (Lower.Value W n)) X s→ₗ[ℤ]OriginalBeforeTarget binding n packet:=
 P.jointSource binding n packet.2 (beforeFrame n packet) (beforeIndex n packet)
def originalAfterSource :Formal ℤ (PairValue (Lower.Value W (n+1))) X s→ₗ[ℤ]OriginalAfterTarget binding n packet:=
 P.jointSource binding (n+1) (nextPacket binding n packet).2 (afterFrame binding n packet) (afterIndex binding n packet)

structure ReadMorphisms where
 profile:SourceGeneratedScalarCofinalNaturality.Morphism
  (F.data binding (beforeState n packet) s 1) (profileData binding n packet)
 native:SourceGeneratedScalarCofinalNaturality.Morphism
  (F.data binding (beforeState n packet) s 1) (F.data binding (afterState binding n packet) s 0)
 profile_generator:profile.generatorMap=LinearMap.id
 native_generator:native.generatorMap=LinearMap.id

variable (moves:ReadMorphisms binding n packet)
abbrev oldCompatible:=AlgebraicDependent.compatible (F.action binding (beforeState n packet) s)
 (F.read binding (beforeState n packet) s) 1
abbrev profileCompatible:=AlgebraicDependent.compatible (afterCarry (W:=W) (X:=X) (s:=s) n) (afterRead binding n packet) 0
abbrev nativeCompatible:=AlgebraicDependent.compatible (F.action binding (afterState binding n packet) s)
 (F.read binding (afterState binding n packet) s) 0

def profileMove:F.completion binding (beforeState n packet) s 1→ₗ[ℤ]profileCompletion binding n packet:=
 (moves.profile.completionMorphism (oldCompatible binding n packet) (profileCompatible binding n packet)).hom
def nativeMove:F.completion binding (beforeState n packet) s 1→ₗ[ℤ]F.completion binding (afterState binding n packet) s 0:=
 (moves.native.completionMorphism (oldCompatible binding n packet) (nativeCompatible binding n packet)).hom

theorem profile_completion_source (word:F.Word binding (beforeState n packet) s 1):
 profileMove binding n packet moves
  (AlgebraicDependent.sourceMap (F.action binding (beforeState n packet) s) (F.read binding (beforeState n packet) s) 1 word)=
 AlgebraicDependent.sourceMap (afterCarry (W:=W) (X:=X) (s:=s) n) (afterRead binding n packet) 0 word :=by
 have generated:=ConcreteCategory.congr_hom
  (moves.profile.completionMorphism_source_naturality
   (oldCompatible binding n packet) (profileCompatible binding n packet)) word
 exact generated.trans (congrArg
  (AlgebraicDependent.sourceMap (afterCarry (W:=W) (X:=X) (s:=s) n) (afterRead binding n packet) 0)
  (LinearMap.congr_fun moves.profile_generator word))

theorem native_completion_source (word:F.Word binding (beforeState n packet) s 1):
 nativeMove binding n packet moves
  (AlgebraicDependent.sourceMap (F.action binding (beforeState n packet) s) (F.read binding (beforeState n packet) s) 1 word)=
 AlgebraicDependent.sourceMap (F.action binding (afterState binding n packet) s) (F.read binding (afterState binding n packet) s) 0 word :=by
 have generated:=ConcreteCategory.congr_hom
  (moves.native.completionMorphism_source_naturality
   (oldCompatible binding n packet) (nativeCompatible binding n packet)) word
 exact generated.trans (congrArg
  (AlgebraicDependent.sourceMap (F.action binding (afterState binding n packet) s) (F.read binding (afterState binding n packet) s) 0)
  (LinearMap.congr_fun moves.native_generator word))

def profileCharacter:F.Model binding (beforeState n packet) s 1→ₗ[ℤ]profileCompletion binding n packet:=
 C.factor (profileMove binding n packet moves)
def nativeCharacter:F.Model binding (beforeState n packet) s 1→ₗ[ℤ]F.Model binding (afterState binding n packet) s 0:=
 C.map (nativeMove binding n packet moves)

theorem profile_character_source (word:F.Word binding (beforeState n packet) s 1):
 profileCharacter binding n packet moves (F.sourceMap binding (beforeState n packet) s 1 word)=
 AlgebraicDependent.sourceMap (afterCarry (W:=W) (X:=X) (s:=s) n) (afterRead binding n packet) 0 word :=
 (LinearMap.congr_fun (C.factor_canonicalMap (profileMove binding n packet moves))
  (AlgebraicDependent.sourceMap (F.action binding (beforeState n packet) s) (F.read binding (beforeState n packet) s) 1 word)).trans
 (profile_completion_source binding n packet moves word)

theorem native_character_source (word:F.Word binding (beforeState n packet) s 1):
 nativeCharacter binding n packet moves (F.sourceMap binding (beforeState n packet) s 1 word)=
 F.sourceMap binding (afterState binding n packet) s 0 word :=
 (C.map_canonicalMap (nativeMove binding n packet moves)
  (AlgebraicDependent.sourceMap (F.action binding (beforeState n packet) s) (F.read binding (beforeState n packet) s) 1 word)).trans
 (congrArg (C.canonicalMap ℤ (F.completion binding (afterState binding n packet) s 0))
  (native_completion_source binding n packet moves word))

def shiftedRead:F.Model binding (beforeState n packet) s 1→ₗ[ℤ]OriginalAfterTarget binding n packet:=
 (profileCharacter binding n packet moves).prod (nativeCharacter binding n packet moves)
def nativeRead:F.Model binding (beforeState n packet) s 0→ₗ[ℤ]OriginalAfterTarget binding n packet:=
 (shiftedRead binding n packet moves).comp (F.next binding (beforeState n packet) s 0)
def originalTargetMap:OriginalBeforeTarget binding n packet→ₗ[ℤ]OriginalAfterTarget binding n packet:=
 (nativeRead binding n packet moves).comp
  (LinearMap.snd ℤ (beforeProfileCompletion binding n packet) (F.Model binding (beforeState n packet) s 0))

theorem original_source_square (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 originalTargetMap binding n packet moves (originalBeforeSource binding n packet word)=originalAfterSource binding n packet (liftMap word) :=by
 change shiftedRead binding n packet moves
  (F.next binding (beforeState n packet) s 0 (F.sourceMap binding (beforeState n packet) s 0 word))=_
 apply (congrArg (shiftedRead binding n packet moves)
  (F.next_source binding (beforeState n packet) s 0 word)).trans
 apply Prod.ext
 · exact profile_character_source binding n packet moves (liftMap word)
 · exact native_character_source binding n packet moves (liftMap word)

def originalMorphism:SourceGeneratedScalarDifferentialResidual.Morphism (originalBeforeSource binding n packet) (originalAfterSource binding n packet) where
 sourceMap:=liftMap
 targetMap:=originalTargetMap binding n packet moves
 commutes:=by
  apply LinearMap.ext
  intro word
  exact original_source_square binding n packet moves word

theorem original_scope_action (word:Formal ℤ (PairValue (Lower.Value W n)) X s):
 inducedResidualMap (originalMorphism binding n packet moves) (SourceOperationLogic.q (originalBeforeSource binding n packet) word)=
 SourceOperationLogic.q (originalAfterSource binding n packet) (liftMap word) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (originalMorphism binding n packet moves)) word

include moves in
theorem original_kernel_preserved (word:Formal ℤ (PairValue (Lower.Value W n)) X s)
 (kernel:SourceOperationLogic.q (originalBeforeSource binding n packet) word=0):
 SourceOperationLogic.q (originalAfterSource binding n packet) (liftMap word)=0 :=
 (original_scope_action binding n packet moves word).symm.trans
  ((congrArg (inducedResidualMap (originalMorphism binding n packet moves)) kernel).trans (map_zero _))

namespace AW
export SourceGeneratedActionWords (run inventory original_kernel)
end AW
attribute [local instance 2000] Finsupp.module Pi.Function.module Submodule.Quotient.module

abbrev BeforeTarget := Main.sourceTarget binding n packet.2 (beforeFrame n packet) (beforeIndex n packet)
abbrev AfterTarget := Main.sourceTarget binding (n+1) (nextPacket binding n packet).2
 (afterFrame binding n packet) (afterIndex binding n packet)
local instance beforeJointModule : Module ℤ (BeforeTarget binding n packet) := Submodule.Quotient.module _
local instance afterJointModule : Module ℤ (AfterTarget binding n packet) := Submodule.Quotient.module _

def beforeSource : Formal ℤ (PairValue (Lower.Value W n)) X s→ₗ[ℤ]BeforeTarget binding n packet :=
 Main.jointSource binding n packet.2 (beforeFrame n packet) (beforeIndex n packet)
def afterSource : Formal ℤ (PairValue (Lower.Value W (n+1))) X s→ₗ[ℤ]AfterTarget binding n packet :=
 Main.jointSource binding (n+1) (nextPacket binding n packet).2 (afterFrame binding n packet) (afterIndex binding n packet)

private abbrev wordSource := SourceGeneratedActionObservationHistory.sourceMap (B.actions (s:=s) binding n PUnit.unit)
 (AW.inventory (B.actions (s:=s) binding n) (originalBeforeSource binding n packet))
private abbrev nextWordSource := SourceGeneratedActionObservationHistory.sourceMap (B.actions (s:=s) binding (n+1) PUnit.unit)
 (AW.inventory (B.actions (s:=s) binding (n+1)) (originalAfterSource binding n packet))

theorem lift_run (path : List PUnit.{u+1})
 (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 liftMap (AW.run (B.actions binding n) path word)=
 AW.run (B.actions binding (n+1)) path (liftMap word) :=by
 induction path generalizing word with
 | nil=>rfl
 | cons letter rest previous=>
  exact (previous ((B.actions binding n letter) word)).trans
   (congrArg (AW.run (B.actions binding (n+1)) rest)
    (LinearMap.congr_fun (Lower.SourceFamily.Foresight.Contextual.Profile.Substitution.word (s:=s) binding n) word))

theorem all_word_square (path : List PUnit.{u+1})
 (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 originalAfterSource binding n packet (AW.run (B.actions binding (n+1)) path (liftMap word))=
 originalTargetMap binding n packet moves
  (originalBeforeSource binding n packet (AW.run (B.actions binding n) path word)) :=
 (congrArg (originalAfterSource binding n packet) (lift_run binding n path word)).symm.trans
 (LinearMap.congr_fun (originalMorphism binding n packet moves).commutes (AW.run (B.actions binding n) path word)).symm

include moves in
private theorem word_kernel_transport : LinearMap.ker (wordSource binding n packet)≤
 (LinearMap.ker (nextWordSource binding n packet)).comap (liftMap (R:=ℤ)) :=by
 rw [AW.original_kernel,AW.original_kernel]
 intro word member
 change AW.inventory (B.actions binding (n+1)) (originalAfterSource binding n packet) (liftMap word)=0
 funext path
 have zero:=congrFun (LinearMap.mem_ker.mp member) path
 exact (all_word_square binding n packet moves path word).trans
  ((congrArg (originalTargetMap binding n packet moves) zero).trans (map_zero _))

def targetMap : BeforeTarget binding n packet→ₗ[ℤ]AfterTarget binding n packet :=
 (LinearMap.ker (wordSource binding n packet)).mapQ (LinearMap.ker (nextWordSource binding n packet))
  liftMap (word_kernel_transport binding n packet moves)

theorem actual_source_square (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 targetMap binding n packet moves (beforeSource binding n packet word)=
 afterSource binding n packet (liftMap word) :=rfl

def morphism : SourceGeneratedScalarDifferentialResidual.Morphism
 (beforeSource binding n packet) (afterSource binding n packet) where
 sourceMap:=liftMap
 targetMap:=targetMap binding n packet moves
 commutes:=by
  apply LinearMap.ext
  intro word
  exact actual_source_square binding n packet moves word

theorem actual_scope_action (word : Formal ℤ (PairValue (Lower.Value W n)) X s) :
 inducedResidualMap (morphism binding n packet moves) (SourceOperationLogic.q (beforeSource binding n packet) word)=
 SourceOperationLogic.q (afterSource binding n packet) (liftMap word) :=
 LinearMap.congr_fun (inducedResidualMap_comp_canonical (morphism binding n packet moves)) word

include moves in
theorem actual_kernel_preserved (word : Formal ℤ (PairValue (Lower.Value W n)) X s)
 (kernel : SourceOperationLogic.q (beforeSource binding n packet) word=0) :
 SourceOperationLogic.q (afterSource binding n packet) (liftMap word)=0 :=
 (actual_scope_action binding n packet moves word).symm.trans
 ((congrArg (inducedResidualMap (morphism binding n packet moves)) kernel).trans (map_zero _))
end Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
