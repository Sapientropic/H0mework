import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentActor.Source
import Mathlib.Algebra.Group.Pi.Lemmas

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
open RootInquiryCompletion RootLawDependentJointStateController SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (recognition : RecognitionAt H root)
abbrev SourceActor := SourceOperationNative.Tree.Fold.Dependent.Branch.Fresh.Complete root recognition
def rowsAtActor (source : SourceActor root recognition) := Observer.rowsAtCode root recognition source.1.1
abbrev Index := Σ source : SourceActor root recognition, Fin (rowsAtActor root recognition source).length
def rowAt (index : Index root recognition) := (rowsAtActor root recognition index.1).get index.2
abbrev Sample := Index root recognition × Fin 4
abbrev Observations := Index root recognition → Fin 4 → Observer.Measured (H:=H)
abbrev Gram := Sample root recognition → Sample root recognition → ULift.{u} ℂ
abbrev Output := Observer.Output root visit recognition × Actor.Output root visit recognition ×
 Observations root recognition × Gram root recognition
abbrev Slot := Actor.Extension.Slot (S:=Observer.Slot root recognition)
abbrev Value := Actor.Extension.Value (Observer.Value root visit recognition) (Output root visit recognition)
abbrev Variable := Actor.Extension.Var (Observer.Variable root visit recognition)
instance : ∀ slot, AddCommGroup (Value root visit recognition slot) :=
 Actor.Extension.instAddCommGroupValue (Observer.Value root visit recognition) (Output root visit recognition)
abbrev resultSlot : Slot root recognition := .inr PUnit.unit
abbrev embed {slot : Observer.Slot root recognition} := Actor.Extension.embed
 (Observer.Value root visit recognition) (Observer.Variable root visit recognition) (Output root visit recognition) (slot:=slot)
def oldInjection : Observer.Output root visit recognition →+ Output root visit recognition := (AddMonoidHom.id _).prod 0
def actorInjection : Actor.Output root visit recognition →+ Output root visit recognition :=
 (0 : Actor.Output root visit recognition →+ Observer.Output root visit recognition).prod ((AddMonoidHom.id _).prod 0)
def observationInjection (index : Index root recognition) (kind : Fin 4) :
 Observer.Measured (H:=H) →+ Output root visit recognition := by
 classical
 exact (0 : Observer.Measured (H:=H) →+ Observer.Output root visit recognition).prod
  ((0 : Observer.Measured (H:=H) →+ Actor.Output root visit recognition).prod
   (((AddMonoidHom.single (fun _ : Index root recognition => Fin 4 → Observer.Measured (H:=H)) index).comp
    (AddMonoidHom.single (fun _ : Fin 4 => Observer.Measured (H:=H)) kind)).prod 0))
def gramInjection (first second : Sample root recognition) : ULift.{u} ℂ →+ Output root visit recognition := by
 classical
 exact (0 : ULift.{u} ℂ →+ Observer.Output root visit recognition).prod
  ((0 : ULift.{u} ℂ →+ Actor.Output root visit recognition).prod
   ((0 : ULift.{u} ℂ →+ Observations root recognition).prod
    ((AddMonoidHom.single (fun _ : Sample root recognition => Sample root recognition → ULift.{u} ℂ) first).comp
     (AddMonoidHom.single (fun _ : Sample root recognition => ULift.{u} ℂ) second))))
def observationTerm (index : Index root recognition) (kind : Fin 4) :=
 let row := rowAt root recognition index
 match kind.val with
 | 0 => Observer.measuredTerm root visit recognition row
 | 1 => Observer.nextMeasuredTerm root visit recognition row
 | 2 => Observer.coherentTerm root visit recognition row
 | _ => Observer.residualTerm root visit recognition row
def observationOutput (index : Index root recognition) (kind : Fin 4) :
 Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
 .linear (s:=.inl (Observer.measuredSlot root recognition)) (observationInjection root visit recognition index kind)
 (embed root visit recognition (observationTerm root visit recognition index kind))
def gramOutput (first second : Sample root recognition) :
 Expr (Value root visit recognition) (Variable root visit recognition) (resultSlot root recognition) :=
 .linear (s:=.inl (Observer.gramSlot root recognition)) (gramInjection root visit recognition first second)
 (.bilinear (s:=.inl (Observer.measuredSlot root recognition)) (t:=.inl (Observer.measuredSlot root recognition))
  Observer.innerOperation (embed root visit recognition (observationTerm root visit recognition first.1 first.2))
   (embed root visit recognition (observationTerm root visit recognition second.1 second.2)))
def indices (source : SourceActor root recognition) : List (Index root recognition) :=
 List.ofFn (fun position : Fin (rowsAtActor root recognition source).length => ⟨source,position⟩)
def samples (source : SourceActor root recognition) :=
 ((indices root recognition source).map (fun index => List.ofFn (fun kind : Fin 4 => (index,kind)))).flatten
end SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
