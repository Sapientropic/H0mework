import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Recovery.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)

def evolution (bound : Nat) (letter : Letter root recognition visit successor) :
    Space root recognition visit successor bound →ₗᵢ[ℂ] Space root recognition visit successor bound where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (Cells root recognition visit successor bound → H)).symm.toLinearMap.comp
    ((LinearMap.pi (fun cell => (NodeHilbert.nodeEvolution root recognition visit successor letter cell.2).toLinearMap.comp
      (LinearMap.proj cell))).comp
      (WithLp.linearEquiv 2 ℂ (Cells root recognition visit successor bound → H)).toLinearMap)
  norm_map' value := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro cell _
    exact congrArg (fun amount : ℝ => amount^2)
      ((NodeHilbert.nodeEvolution root recognition visit successor letter cell.2).norm_map (value cell))

def wordEvolution (bound : Nat) : List (Letter root recognition visit successor) →
    Space root recognition visit successor bound →ₗᵢ[ℂ] Space root recognition visit successor bound
 | [] => LinearIsometry.id
 | letter::rest => (wordEvolution bound rest).comp (evolution root recognition visit successor bound letter)

theorem evolution_cell (bound : Nat) (letter : Letter root recognition visit successor)
    (cell : Cells root recognition visit successor bound) (value : Space root recognition visit successor bound) :
    evolution root recognition visit successor bound letter value cell=
      NodeHilbert.nodeEvolution root recognition visit successor letter cell.2 (value cell) := rfl

def action (bound : Nat) (letters : List (Letter root recognition visit successor)) :
    SourceGeneratedIntegralCoherentCovariance.ActionData (observation root recognition visit successor transition alignment U7 calculus count bound) where
  integralTransition := SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters
  hilbertEvolution := wordEvolution root recognition visit successor bound letters
abbrev effect (bound : Nat) (letters : List (Letter root recognition visit successor)) :=
  SourceGeneratedIntegralCoherentCovariance.couplingResidual (action root recognition visit successor transition alignment U7 calculus count bound letters)
abbrev disposition (bound : Nat) (letters : List (Letter root recognition visit successor)) :=
  SourceGeneratedIntegralCoherentCovariance.settleCovariance (action root recognition visit successor transition alignment U7 calculus count bound letters)

theorem single_cell (bound : Nat) (letter : Letter root recognition visit successor)
    (cell : Cells root recognition visit successor bound)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    effect root recognition visit successor transition alignment U7 calculus count bound [letter] value cell=
      NodeHilbert.nodeEvolution root recognition visit successor letter cell.2
        (Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
          (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (word root recognition visit successor cell.1) value))-
      Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (letter::word root recognition visit successor cell.1) value) := rfl

theorem word_cell (bound : Nat) (letters : List (Letter root recognition visit successor))
    (cell : Cells root recognition visit successor bound) (value : Space root recognition visit successor bound) :
    wordEvolution root recognition visit successor bound letters value cell=
      (NodeHilbert.Words.wordEvolution root recognition visit successor letters
        ((WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).symm
          (fun index => value (cell.1,index)))) cell.2 := by
  induction letters generalizing value with
  | nil => rfl
  | cons letter rest previous =>
    change wordEvolution root recognition visit successor bound rest
      (evolution root recognition visit successor bound letter value) cell=_
    rw [previous]
    have same : (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).symm
        (fun index => evolution root recognition visit successor bound letter value (cell.1,index))=
      NodeHilbert.evolution root recognition visit successor letter
        ((WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).symm
          (fun index => value (cell.1,index))) := by
      apply (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).injective
      funext index
      rfl
    exact congrArg (fun measured => NodeHilbert.Words.wordEvolution root recognition visit successor rest measured cell.2) same

theorem effect_cell (bound : Nat) (letters : List (Letter root recognition visit successor))
    (cell : Cells root recognition visit successor bound) (value : Model root recognition visit successor transition alignment U7 calculus count) :
    effect root recognition visit successor transition alignment U7 calculus count bound letters value cell=
      (NodeHilbert.Words.wordEvolution root recognition visit successor letters
        (NodeHilbert.measurement root recognition visit successor transition alignment U7 calculus count
          (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (word root recognition visit successor cell.1) value))) cell.2-
      Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count)
          (letters++word root recognition visit successor cell.1) value) := by
  change wordEvolution root recognition visit successor bound letters (observation root recognition visit successor transition alignment U7 calculus count bound value) cell-
    observation root recognition visit successor transition alignment U7 calculus count bound (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters value) cell=_
  apply congrArg₂ (· - ·)
  · have same : (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).symm
        (fun index => observation root recognition visit successor transition alignment U7 calculus count bound value (cell.1,index))=
      NodeHilbert.measurement root recognition visit successor transition alignment U7 calculus count
        (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) (word root recognition visit successor cell.1) value) := by
      apply (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).injective
      funext index
      exact (cell_read root recognition visit successor transition alignment U7 calculus count bound (cell.1,index) value).trans
        (NodeHilbert.measurement_node root recognition visit successor transition alignment U7 calculus count index _).symm
    exact (word_cell root recognition visit successor bound letters cell (observation root recognition visit successor transition alignment U7 calculus count bound value)).trans
      (congrArg (fun measured => NodeHilbert.Words.wordEvolution root recognition visit successor letters measured cell.2) same)
  · exact (cell_read root recognition visit successor transition alignment U7 calculus count bound cell (SourceGeneratedActionWords.run (advance root recognition visit successor transition alignment U7 calculus count) letters value)).trans
      (congrArg (fun operation => Covariance.feature root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor cell.2)
        (operation value)) (SourceGeneratedActionWords.run_append (advance root recognition visit successor transition alignment U7 calculus count) letters
          (word root recognition visit successor cell.1)).symm)

theorem restriction_wave (bound : Nat) (letter : Letter root recognition visit successor)
    (value : Space root recognition visit successor (bound+1)) :
    restriction root recognition visit successor bound
      (evolution root recognition visit successor (bound+1) letter value)=
    evolution root recognition visit successor bound letter (restriction root recognition visit successor bound value) := rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
