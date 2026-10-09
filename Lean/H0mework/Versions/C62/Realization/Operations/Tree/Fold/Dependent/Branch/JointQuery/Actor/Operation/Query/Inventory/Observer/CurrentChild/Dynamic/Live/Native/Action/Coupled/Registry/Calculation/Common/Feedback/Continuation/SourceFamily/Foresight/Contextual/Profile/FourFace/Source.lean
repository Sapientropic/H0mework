import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Profile.Character.Source
import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Whole.Occurrence
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
import H0mework.Realization.Perfectification.LivingLawRootGeneratedUnifiedFourFaceEvaluationKernel

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement CategoryTheory
namespace Lower.SourceFamily.Foresight.Contextual.Profile.FourFace

namespace A
export Lower.SourceFamily.Foresight.Contextual.Profile.Assembly
  (beforeFrame beforeIndex nextPacket BeforeTarget AfterTarget beforeJointModule afterJointModule beforeSource afterSource)
end A
namespace P
export Lower.SourceFamily.Foresight.Contextual.Profile.Producer (actionBinding)
end P
namespace D
export Lower.SourceFamily.Foresight.Contextual.Forecast.Dispatch (free_evaluation)
end D
namespace R
export Lower.SourceFamily.Foresight.Contextual.Reader (material pairWritten)
end R
namespace F
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine (BeforeScope AfterScope afterq rawWord rawBoundaryVector)
end F
namespace C
export Lower.SourceFamily.Foresight.Contextual.Profile.Affine.Cochain
  (history face complex actualRelation effect generated_effect generated_differential source_completion_zero)
end C
namespace Ch
export Lower.SourceFamily.Foresight.Contextual.Profile.Character
  (beforeCharacters afterCharacters characterMorphism characterAction source_kernel)
end Ch
namespace Whole
export Lower.SourceFamily.Foresight.Whole
  (Full Word recover rawSource sourceOccurrence occurrence_root occurrence_keeps_inventory occurrenceInput)
end Whole
namespace E
export UnifiedFourFace.Evaluation (Input RootEvaluation Coimage generate canonical move)
end E

universe u
variable {S:Type u} {W X:S→Type u} [∀t,AddCommGroup (W t)] {s:S}
attribute [local instance] Lower.SourceFamily.Foresight.Contextual.groups
attribute [local instance 2000] CharacterModule.instModule
variable (binding:∀t,X t→Expr W X t) (n:Nat)
variable (packet:Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
variable (native:packet.1.depth=0)
local instance beforeModule:Module ℤ (A.BeforeTarget binding n packet):=A.beforeJointModule binding n packet
local instance afterModule:Module ℤ (A.AfterTarget binding n packet):=A.afterJointModule binding n packet

def algebraAt (point:Whole.Full binding n packet s) :=
  ((Whole.occurrenceInput binding n packet).algebraAt point,
   Ch.beforeCharacters binding n packet (Whole.recover binding n packet s point),
   Ch.afterCharacters binding n packet (liftMap (Whole.recover binding n packet s point)))
def combinatorialAt (point:Whole.Full binding n packet s) :=
  ((Whole.occurrenceInput binding n packet).combinatorialAt point,
   R.material binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet),
   R.pairWritten binding n packet.2 (A.beforeFrame n packet) (A.beforeIndex n packet),
   C.history binding n packet)
def topologicalAt (point:Whole.Full binding n packet s) :=
  ((Whole.occurrenceInput binding n packet).topologicalAt point,
   CofinalAllPrimeTopology.TopologicalAt.generate (C.history binding n packet))
def logicalAt (point:Whole.Full binding n packet s) :=
  ((Whole.occurrenceInput binding n packet).logicalAt point,
   PLift.up (fun degree:Nat => CofinalRelationGeneratedComplex.differential_sq (C.history binding n packet) degree))
def relationAt (point:Whole.Full binding n packet s) :=
  ((Whole.occurrenceInput binding n packet).relationAt point,
   C.face binding n packet,C.actualRelation binding n packet)
def cochainAt (point:Whole.Full binding n packet s) :=
  ((Whole.occurrenceInput binding n packet).cochainAt point,C.complex binding n packet)

abbrev Algebra := type_of% (algebraAt binding n packet (Whole.rawSource binding n packet))
abbrev Combinatorial := type_of% (combinatorialAt binding n packet (Whole.rawSource binding n packet))
abbrev Topological := type_of% (topologicalAt binding n packet (Whole.rawSource binding n packet))
abbrev Logical := type_of% (logicalAt binding n packet (Whole.rawSource binding n packet))
abbrev Relation := type_of% (relationAt binding n packet (Whole.rawSource binding n packet))
abbrev Cochain := type_of% (cochainAt binding n packet (Whole.rawSource binding n packet))

def input : E.Input (Whole.Full binding n packet s)
    (Algebra binding n packet) (Combinatorial binding n packet) (Topological binding n packet)
    (Logical binding n packet) (Relation binding n packet) (Cochain binding n packet)
    (Formal ℤ (PairValue (Lower.Value W n)) X s)
    (SourceGeneratedScalarCharacterExact.DoubleDual (A.BeforeTarget binding n packet)) where
  occurrence := Whole.sourceOccurrence binding n packet
  algebraAt := algebraAt binding n packet
  combinatorialAt := combinatorialAt binding n packet
  topologicalAt := topologicalAt binding n packet
  logicalAt := logicalAt binding n packet
  relationAt := relationAt binding n packet
  cochainAt := cochainAt binding n packet
  evaluationAt := fun _ => Ch.beforeCharacters binding n packet
  faithfulAt := fun _ => substitution (R:=ℤ) (P.actionBinding binding n)

def beforeFaces := E.generate (input binding n packet)
def afterInput := input binding (n+1) (A.nextPacket binding n packet)
def afterFaces := E.generate (afterInput binding n packet)

theorem original_source_root :
    (input binding n packet).occurrence.root = Whole.rawSource binding n packet :=
  Whole.occurrence_root binding n packet

include native in
def sourceAction : Morphism (E.RootEvaluation (input binding n packet))
    (E.RootEvaluation (afterInput binding n packet)) :=
  Ch.characterMorphism binding n packet native

include native in
def coimageAction := E.move (input:=input binding n packet) (input':=afterInput binding n packet)
  (sourceAction binding n packet native)

include native in
theorem actual_action (word:Formal ℤ (PairValue (Lower.Value W n)) X s) :
    coimageAction binding n packet native ((beforeFaces binding n packet).canonical word) =
      (afterFaces binding n packet).canonical (liftMap word) :=
  UnifiedFourFace.Evaluation.generated_action (sourceAction binding n packet native) word

include native in
theorem actual_action_embedding (value:E.Coimage (input binding n packet)) :
    (afterFaces binding n packet).embedding (coimageAction binding n packet native value) =
      Ch.characterAction binding n packet native ((beforeFaces binding n packet).embedding value) :=
  UnifiedFourFace.Evaluation.generated_action_embedding (sourceAction binding n packet native) value

def generatedRelation := (beforeFaces binding n packet).relationFace.root.2.2
theorem generated_relation_original : generatedRelation binding n packet = C.actualRelation binding n packet := by
  change ((input binding n packet).occurrence.map (relationAt binding n packet)).root.2.2 = _
  rw [RootedAccountedUnfolding.root_map]
  rfl

def actualMu : Formal ℤ (PairValue (Lower.Value W (n+1))) X s :=
  (generatedRelation binding n packet).val
def paidCoordinate := (afterFaces binding n packet).canonical (actualMu binding n packet)

private theorem character_kernel :
    LinearMap.ker (E.RootEvaluation (afterInput binding n packet)) = LinearMap.ker (A.afterSource binding n packet) :=
  Ch.source_kernel binding (n+1) (A.nextPacket binding n packet)

local instance afterCoimageModule : Module ℤ (E.Coimage (afterInput binding n packet)) :=
  Submodule.Quotient.module (LinearMap.ker (E.RootEvaluation (afterInput binding n packet)))

def scopeRead : E.Coimage (afterInput binding n packet) →ₗ[ℤ] F.AfterScope binding n packet :=
  (LinearMap.ker (E.RootEvaluation (afterInput binding n packet))).liftQ (F.afterq binding n packet) (by
    intro word member
    rw [character_kernel] at member
    apply LinearMap.mem_ker.mpr
    exact (canonicalResidual_eq_zero_iff (A.afterSource binding n packet) word).mpr (LinearMap.mem_ker.mp member))

private theorem scope_source (word:Formal ℤ (PairValue (Lower.Value W (n+1))) X s):
 scopeRead binding n packet ((afterFaces binding n packet).canonical word)=F.afterq binding n packet word :=rfl

private theorem closure_scope_source (vector:(C.history binding n packet).generatorClosure):
 (C.face binding n packet).closureEvaluation vector=F.afterq binding n packet vector.val :=
 D.free_evaluation (A.nextPacket binding n packet).2
  (Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.afterFrame binding n packet)
  (Lower.SourceFamily.Foresight.Contextual.Profile.Assembly.afterIndex binding n packet).2
  (A.afterSource binding n packet) vector.val

include native in
theorem paid_source_equation :
 scopeRead binding n packet (paidCoordinate binding n packet)=C.effect binding n packet native :=by
 have differentialValue:
  (((C.complex binding n packet).d 0 1).hom (C.actualRelation binding n packet)).val=
  (C.actualRelation binding n packet).val :=
  congrArg (fun vector:(C.history binding n packet).generatorClosure=>vector.val)
   (C.generated_differential binding n packet)
 have original:actualMu binding n packet=(C.actualRelation binding n packet).val :=
  congrArg (fun relation:(C.history binding n packet).relationClosure=>relation.val)
   (generated_relation_original binding n packet)
 have source:
  (C.face binding n packet).closureEvaluation
   (((C.complex binding n packet).d 0 1).hom (C.actualRelation binding n packet))=
  F.afterq binding n packet (actualMu binding n packet) :=
  (closure_scope_source binding n packet _).trans
   (congrArg (F.afterq binding n packet) (differentialValue.trans original.symm))
 exact (scope_source binding n packet (actualMu binding n packet)).trans
  (source.symm.trans (C.generated_effect binding n packet native))

include native in
theorem paid_coordinate_zero_iff :
    paidCoordinate binding n packet = 0 ↔ C.effect binding n packet native = 0 := by
  have effect := paid_source_equation binding n packet native
  change canonicalResidual (E.RootEvaluation (afterInput binding n packet)) (actualMu binding n packet) = 0 ↔ _
  rw [canonicalResidual_eq_zero_iff]
  have kernel := character_kernel binding n packet
  have sourceZero : E.RootEvaluation (afterInput binding n packet) (actualMu binding n packet) = 0 ↔
      A.afterSource binding n packet (actualMu binding n packet) = 0 := by
    change actualMu binding n packet ∈ LinearMap.ker (E.RootEvaluation (afterInput binding n packet)) ↔
      actualMu binding n packet ∈ LinearMap.ker (A.afterSource binding n packet)
    rw [kernel]
  apply sourceZero.trans
  apply (canonicalResidual_eq_zero_iff (A.afterSource binding n packet) (actualMu binding n packet)).symm.trans
  exact Iff.of_eq (congrArg (fun value => value=0) effect)

theorem paid_completion_zero :
    (C.history binding n packet).completionProjection
      (((C.complex binding n packet).d 0 1).hom (C.actualRelation binding n packet)) = 0 :=
  C.source_completion_zero binding n packet

end Lower.SourceFamily.Foresight.Contextual.Profile.FourFace
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
