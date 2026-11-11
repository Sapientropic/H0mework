import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKForcingGapAction.FourierControls

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction

private theorem pair_heq {A B : Type u} {C D : Type v} {a : A} {b : B} {c : C} {d : D}
 (first : HEq a b) (second : HEq c d) : HEq (a,c) (b,d) := by
 cases first
 cases second
 rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (rightHalf : 1/2<observation.coordinate.re)
local notation "c" => originalKCoordinate observation.coordinate
 (And.right (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial)) rightHalf
local notation "h" => Real.log stageZeroSonineQ
local notation "Gamma" => ∑ i : Fin 2,sourceCoefficients c i*sourcePositionCoefficients c i
local notation "X" => gapZeroPart c

/-- The same original evolution carries the aggregated residual and actual receipt energy, with explicit unit-removal controls. -/
theorem actual_position_aggregate_gate :
 (let root:=runtimeEffectRoot observation nontrivial
  let visit:=runtimeEffectVisit observation nontrivial
  let registered:=runtimeEffectRootedActive observation nontrivial
  let receipt:=installedOriginalKReceiptAt observation nontrivial rightHalf
  let evolution:=root.canonicalCausalAnswerAndNext (ULift.up visit)
  HEq ((evolution.generated,
         evolution.generated.projectionOutcome (runtimeEffectRecognition observation nontrivial).rootEffectProjection,
         evolution.nextCurrent,receipt.kernel,receipt.fixedResidual),‖receipt.kernel‖^2)
      ((root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit,
         registered.installedFiber,root.generatedNextCurrentAt visit,X+Gamma • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed,
         finitePair c h X X + Gamma*inner ℂ X (outwardConstantShell h)/2 +
         star Gamma*star (inner ℂ X (outwardConstantShell h))/2 +
         star Gamma*Gamma*((Real.exp (-h/2) : ℂ)-pairedMellinTranslationCharacter (c).value h)/2),
       ‖X‖^2+‖Gamma‖^2/2)) ∧
 type_of% (installed_unit_removal_effect observation nontrivial rightHalf) ∧
 (∀ coefficientZero : Gamma=0,
  type_of% (installed_gap_coefficient_zero observation nontrivial rightHalf coefficientZero)) := by
 constructor
 · have actual := installed_calculated_position_on_original_evolution observation nontrivial rightHalf
   rw [sourceGram_aggregate_position c h] at actual
   exact pair_heq actual (heq_of_eq (installed_kernel_gap_energy observation nontrivial rightHalf))
 · exact ⟨installed_unit_removal_effect observation nontrivial rightHalf,
    fun coefficientZero => installed_gap_coefficient_zero observation nontrivial rightHalf coefficientZero⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKForcingGapAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
