import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.Covariance.Execution.Consumer
import Mathlib.Analysis.InnerProductSpace.PiL2
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
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

abbrev Index := Fin (sourceTree root recognition visit).trace.length ⊕ Fin (targetTree root recognition visit successor).trace.length
abbrev Space := PiLp 2 (fun _ : Index root recognition visit successor => H)
def actor : Index root recognition visit successor → Covariance.Actor root recognition visit successor
 | .inl index => .inl ⟨(sourceTree root recognition visit).trace.get index,List.get_mem _ _⟩
 | .inr index => .inr ⟨(targetTree root recognition visit successor).trace.get index,List.get_mem _ _⟩
def measurement : Model root recognition visit successor transition alignment U7 calculus count →ₗ[ℤ] Space root recognition visit successor :=
  (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).symm.toLinearMap.comp
    (LinearMap.pi (fun index => Covariance.feature root recognition visit successor transition alignment U7 calculus count
      (actor root recognition visit successor index)))
theorem measurement_node (index : Index root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    measurement root recognition visit successor transition alignment U7 calculus count value index =
      Covariance.feature root recognition visit successor transition alignment U7 calculus count
        (actor root recognition visit successor index) value := rfl

def nodeEvolution (letter : Letter root recognition visit successor) (index : Index root recognition visit successor) : H →ₗᵢ[ℂ] H := by
  classical
  let node := actor root recognition visit successor index
  exact if node = match letter with
      | .source selected => .inl selected
      | .target selected => .inr selected
      | .simultaneous => .inl (sourceRootActor root recognition visit)
    then Covariance.evolution root recognition visit successor node
    else if letter=(.simultaneous : Letter root recognition visit successor) ∧
      node=.inr (targetRootActor root recognition visit successor)
    then Covariance.evolution root recognition visit successor node
    else LinearIsometry.id

def evolution (letter : Letter root recognition visit successor) : Space root recognition visit successor →ₗᵢ[ℂ] Space root recognition visit successor where
  toLinearMap := (WithLp.linearEquiv 2 ℂ (Index root recognition visit successor → H)).symm.toLinearMap.comp
    ((LinearMap.pi (fun index => (nodeEvolution root recognition visit successor letter index).toLinearMap.comp
      (LinearMap.proj index))).comp
        (WithLp.linearEquiv 2 ℂ (Index root recognition visit successor → H)).toLinearMap)
  norm_map' value := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro index _
    exact congrArg (fun amount : ℝ => amount^2) (nodeEvolution root recognition visit successor letter index |>.norm_map (value index))
theorem actor_surjective : Function.Surjective (actor root recognition visit successor) := by
  intro selected
  cases selected with
  | inl source =>
    obtain ⟨index,same⟩ := List.mem_iff_get.mp source.property
    refine ⟨.inl index,?_⟩
    exact congrArg Sum.inl (Subtype.ext same)
  | inr target =>
    obtain ⟨index,same⟩ := List.mem_iff_get.mp target.property
    refine ⟨.inr index,?_⟩
    exact congrArg Sum.inr (Subtype.ext same)

theorem measurement_source (index : Index root recognition visit successor) (point : Carrier root recognition visit successor) :
    measurement root recognition visit successor transition alignment U7 calculus count
      (projection root recognition visit successor transition alignment U7 calculus count point) index =
      Covariance.originalFeature root recognition visit successor (actor root recognition visit successor index) point :=
  Covariance.feature_source root recognition visit successor transition alignment U7 calculus count (actor root recognition visit successor index) point

theorem energy_source (point : Carrier root recognition visit successor) :
    ‖measurement root recognition visit successor transition alignment U7 calculus count
      (projection root recognition visit successor transition alignment U7 calculus count point)‖^2 =
      ∑ index : Index root recognition visit successor,
        ‖Covariance.originalFeature root recognition visit successor (actor root recognition visit successor index) point‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun value : H => ‖value‖^2) (measurement_source root recognition visit successor transition alignment U7 calculus count index point)

def action (letter : Letter root recognition visit successor) : SourceGeneratedIntegralCoherentCovariance.ActionData
    (measurement root recognition visit successor transition alignment U7 calculus count) where
  integralTransition := advance root recognition visit successor transition alignment U7 calculus count letter
  hilbertEvolution := evolution root recognition visit successor letter
abbrev effect (letter : Letter root recognition visit successor) (value : Model root recognition visit successor transition alignment U7 calculus count) :=
  SourceGeneratedIntegralCoherentCovariance.couplingResidual
    (action root recognition visit successor transition alignment U7 calculus count letter) value
abbrev disposition (letter : Letter root recognition visit successor) := SourceGeneratedIntegralCoherentCovariance.settleCovariance
  (action root recognition visit successor transition alignment U7 calculus count letter)

theorem effect_node (letter : Letter root recognition visit successor) (index : Index root recognition visit successor)
    (value : Model root recognition visit successor transition alignment U7 calculus count) :
    effect root recognition visit successor transition alignment U7 calculus count letter value index =
      nodeEvolution root recognition visit successor letter index
        (Covariance.feature root recognition visit successor transition alignment U7 calculus count
          (actor root recognition visit successor index) value) -
      Covariance.feature root recognition visit successor transition alignment U7 calculus count
        (actor root recognition visit successor index)
        (advance root recognition visit successor transition alignment U7 calculus count letter value) := rfl
theorem measurement_fibre (left right : Model root recognition visit successor transition alignment U7 calculus count) :
    measurement root recognition visit successor transition alignment U7 calculus count left =
      measurement root recognition visit successor transition alignment U7 calculus count right ↔
    ∀ selected : Covariance.Actor root recognition visit successor,
      Covariance.feature root recognition visit successor transition alignment U7 calculus count selected left =
        Covariance.feature root recognition visit successor transition alignment U7 calculus count selected right := by
  constructor
  · intro equal selected
    obtain ⟨index,rfl⟩ := actor_surjective root recognition visit successor selected
    exact congrArg (fun value : Space root recognition visit successor => value index) equal
  · intro equal
    apply (WithLp.linearEquiv 2 ℤ (Index root recognition visit successor → H)).injective
    funext index
    exact equal (actor root recognition visit successor index)

theorem evolution_node (letter : Letter root recognition visit successor) (index : Index root recognition visit successor)
    (value : Space root recognition visit successor) :
    evolution root recognition visit successor letter value index=nodeEvolution root recognition visit successor letter index (value index) := rfl

theorem wave_node (letter : Letter root recognition visit successor) (index : Index root recognition visit successor)
    (values : Covariance.Actor root recognition visit successor → H) :
    nodeEvolution root recognition visit successor letter index (values (actor root recognition visit successor index)) =
      EffectHistory.wave root recognition visit successor letter values (actor root recognition visit successor index) := by
  classical
  cases letter <;> (
    unfold nodeEvolution EffectHistory.wave
    dsimp only
    simp only [LinearMap.pi_apply]
    split_ifs <;> rfl)

theorem effect_full (letter : Letter root recognition visit successor) (index : Index root recognition visit successor)
    (point : Carrier root recognition visit successor) :
    effect root recognition visit successor transition alignment U7 calculus count letter
      (projection root recognition visit successor transition alignment U7 calculus count point) index =
      EffectHistory.total root recognition visit successor transition alignment U7 calculus count point [letter]
        (actor root recognition visit successor index) := by
  rw [effect_node]
  have joint := wave_node root recognition visit successor letter index
    (EffectHistory.measurement root recognition visit successor transition alignment U7 calculus count
      (projection root recognition visit successor transition alignment U7 calculus count point))
  change nodeEvolution root recognition visit successor letter index
      (EffectHistory.measurement root recognition visit successor transition alignment U7 calculus count
        (projection root recognition visit successor transition alignment U7 calculus count point) (actor root recognition visit successor index)) - _ = _
  rw [joint]
  rw [SourceGeneratedActionWords.advance_source]
  rfl
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
