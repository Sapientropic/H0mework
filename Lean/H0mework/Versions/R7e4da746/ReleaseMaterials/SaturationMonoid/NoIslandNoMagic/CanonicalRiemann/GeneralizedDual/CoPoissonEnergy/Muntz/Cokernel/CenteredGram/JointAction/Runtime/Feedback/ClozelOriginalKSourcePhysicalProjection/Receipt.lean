import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourcePhysicalProjection.Action

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourcePhysicalProjection
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKForcingGapAction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace
local instance receiptPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance receiptPaComplete : CompleteSpace ↥burnolCompactCoPoissonClosedRange.toSubmodule := by
  apply IsComplete.completeSpace_coe
  exact burnolCompactCoPoissonClosedRange.isClosed.isComplete
local notation "Γ[" coordinate "]" => ∑ i : Fin 2,sourceCoefficients coordinate i*sourcePositionCoefficients coordinate i

private theorem physical_fixed (value : BurnolPaAmbientCarrier) :
    burnolEvenAmbientProjection (value : BurnolL2) = value :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _

/-- The complete Pa and Pa-perp unit prices are paid only on the generated physical pC. -/
theorem constantPhysical_Pa_Q_energy :
    (((‖OriginalKCombCofinalPaAction.E (constantPhysical : BurnolL2)‖^2+
        ‖OriginalKCombCofinalPaAction.Q (constantPhysical : BurnolL2)‖^2 : ℝ)) : ℂ) =
      (1-constantResponseMean)/2 := by
  have energy := Submodule.norm_sq_eq_add_norm_sq_starProjection constantPhysical
    burnolCompactCoPoissonClosedRange.toSubmodule
  have e : OriginalKCombCofinalPaAction.E (constantPhysical : BurnolL2) =
      burnolCompactCoPoissonClosedRange.toSubmodule.starProjection constantPhysical := by
    change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolEvenAmbientProjection (constantPhysical : BurnolL2)) = _
    rw [physical_fixed]
  have q : OriginalKCombCofinalPaAction.Q (constantPhysical : BurnolL2) =
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection constantPhysical := by
    change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolEvenAmbientProjection (constantPhysical : BurnolL2)) = _
    rw [physical_fixed]
  rw [e,q,←energy]
  exact constantPhysicalVector_energy

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
local notation "X" => gapZeroPart c
local notation "PX" => physicalGapZeroPart c
local notation "Gamma" => Γ[c]

/-- The original source anchor and factorization deliver the actual input to the new R/projection action. -/
def consume_installed_physical_source {Result : Sort u}
    (consumer :
      type_of% (generatedK_eq_original c) →
      type_of% (installedOriginalKReceiptAt_eq_source observation nontrivial rightHalf) →
      type_of% (original_fixedResidual_source_Gram c observation.mathlibZero) →
      type_of% (installedRuntimeEffect_factorizes observation nontrivial) →
      type_of% (physicalGapZeroPart_source c) →
      type_of% (original_R_physicalGapZeroPart_quarter c) →
      (∀ left : BurnolPaAmbientCarrier,type_of% (original_R_physicalGapZeroPart_test c left)) →
      type_of% (physicalGapZeroPart_Pa_Q c observation.mathlibZero) →
      type_of% (physicalGapZeroPart_loss_calculated c) →
      type_of% constantPhysical_Pa_Q_energy → Result) : Result :=
  consume_installed_source_Gram observation nontrivial rightHalf
    (fun sourceIdentity sourceAnchor sourceGram factorization =>
      consumer sourceIdentity sourceAnchor sourceGram factorization
        (physicalGapZeroPart_source c) (original_R_physicalGapZeroPart_quarter c)
        (original_R_physicalGapZeroPart_test c)
        (physicalGapZeroPart_Pa_Q c observation.mathlibZero)
        (physicalGapZeroPart_loss_calculated c) constantPhysical_Pa_Q_energy)

/-- The receipt residual keeps all four physical-pC matrix terms after the actual source projection. -/
theorem installed_residual_physical_decomposition :
    (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual =
      finitePair c h (PX : BurnolL2) (PX : BurnolL2) +
      Gamma*finitePair c h (PX : BurnolL2) constantPhysicalVector +
      star Gamma*finitePair c h constantPhysicalVector (PX : BurnolL2) +
      star Gamma*Gamma*finitePair c h constantPhysicalVector constantPhysicalVector := by
  apply consume_installed_physical_source observation nontrivial rightHalf
  intro sourceIdentity sourceAnchor sourceGram _ projectionAction _ _ _ _ _
  have kernelSource : generatedK c = (PX : BurnolL2)+Gamma • constantPhysicalVector := by
    rw [sourceIdentity,projectionAction]
    change (burnolCompletedMellinRieszVector c : BurnolL2) =
      ((burnolCompletedMellinRieszVector c : BurnolL2)-Gamma • constantPhysicalVector)+Gamma • constantPhysicalVector
    module
  have residual := (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.fixedResidual) sourceAnchor).trans sourceGram
  rw [←generatedK_finite_Gram] at residual
  change (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual =
    finitePair c h (generatedK c) (generatedK c) at residual
  rw [residual,kernelSource]
  simp only [finitePair,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,starRingEnd_apply]
  ring

/-- The same original whole and next consume the calculated R field, full physical loss and legal Pa/Q inventory. -/
theorem installed_physical_source_on_original_evolution :
    let root := runtimeEffectRoot observation nontrivial
    let visit := runtimeEffectVisit observation nontrivial
    let registered := runtimeEffectRootedActive observation nontrivial
    let receipt := installedOriginalKReceiptAt observation nontrivial rightHalf
    let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
    let actualX := receipt.kernel-Gamma • ConstantDual.seed
    let actualPX := burnolEvenAmbientProjection actualX
    (HEq (evolution.generated,
          evolution.generated.projectionOutcome (runtimeEffectRecognition observation nontrivial).rootEffectProjection,
          evolution.nextCurrent,receipt.kernel,receipt.fixedResidual)
        (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit,
          registered.installedFiber,root.generatedNextCurrentAt visit,
          (PX : BurnolL2)+Gamma • constantPhysicalVector,
          finitePair c h (PX : BurnolL2) (PX : BurnolL2) +
          Gamma*finitePair c h (PX : BurnolL2) constantPhysicalVector +
          star Gamma*finitePair c h constantPhysicalVector (PX : BurnolL2) +
          star Gamma*Gamma*finitePair c h constantPhysicalVector constantPhysicalVector)) ∧
    (actualPX = burnolCompletedMellinRieszVector c-Gamma • constantPhysical) ∧
    (burnolQuarterRestriction (burnolDirectRightResolvent ((c).value/2) (actualPX : BurnolL2)) =
      (-2*Gamma*constantResponseMean/(c).value) • intervalConstant (1/4 : ℝ)) ∧
    (∀ left : BurnolPaAmbientCarrier,
      inner ℂ (left : BurnolL2) (burnolDirectRightResolvent ((c).value/2) (actualPX : BurnolL2)) =
      inner ℂ (left : BurnolL2) (burnolDirectRightResolvent ((c).value/2) receipt.kernel) -
      (Gamma/2)*star (OriginalKGapProjectionEulerSource.actualFourierGapRPrice
        (OriginalKQuarterTailPhysicalSource.actualStarSource c)
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius left))) ∧
    (OriginalKCombCofinalPaAction.E (actualPX : BurnolL2) =
      -Gamma • OriginalKCombCofinalPaAction.E (constantPhysical : BurnolL2)) ∧
    (OriginalKCombCofinalPaAction.Q (actualPX : BurnolL2) =
      burnolCompletedMellinRieszVector c-Gamma • OriginalKCombCofinalPaAction.Q (constantPhysical : BurnolL2)) ∧
    ((((‖actualX‖^2-‖actualPX‖^2 : ℝ)) : ℂ) = ((‖Gamma‖^2 : ℝ) : ℂ)*constantResponseMean/2) ∧
    ((((‖OriginalKCombCofinalPaAction.E (constantPhysical : BurnolL2)‖^2+
      ‖OriginalKCombCofinalPaAction.Q (constantPhysical : BurnolL2)‖^2 : ℝ)) : ℂ) =
      (1-constantResponseMean)/2) := by
  apply consume_installed_physical_source observation nontrivial rightHalf
  intro sourceIdentity sourceAnchor _ factorization projectionAction quarterAction fullTest paQ loss unitCost
  have originalKernel : (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel =
      (burnolCompletedMellinRieszVector c : BurnolL2) :=
    congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel) sourceAnchor
  have sourceKernel : (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel =
      (PX : BurnolL2)+Gamma • constantPhysicalVector := by
    rw [originalKernel,projectionAction]
    change (burnolCompletedMellinRieszVector c : BurnolL2) =
      ((burnolCompletedMellinRieszVector c : BurnolL2)-Gamma • constantPhysicalVector)+Gamma • constantPhysicalVector
    module
  have actualInput : (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel-Gamma • ConstantDual.seed = X := by
    rw [originalKernel,←sourceIdentity,generatedK_gap_decomposition]
    module
  have residual := installed_residual_physical_decomposition observation nontrivial rightHalf
  refine ⟨pair_heq (heq_of_eq factorization.1)
      (pair_heq factorization.2.1
        (pair_heq (heq_of_eq factorization.2.2)
          (pair_heq (heq_of_eq sourceKernel) (heq_of_eq residual)))),?_,?_,?_,?_,?_,?_,unitCost⟩
  · rw [actualInput]
    exact projectionAction
  · rw [actualInput]
    exact quarterAction
  · intro left
    rw [actualInput,originalKernel]
    exact fullTest left
  · rw [actualInput]
    exact paQ.1
  · rw [actualInput]
    exact paQ.2
  · change (((‖(installedOriginalKReceiptAt observation nontrivial rightHalf).kernel-Gamma • ConstantDual.seed‖^2-
      ‖burnolEvenAmbientProjection ((installedOriginalKReceiptAt observation nontrivial rightHalf).kernel-Gamma • ConstantDual.seed)‖^2 : ℝ)) : ℂ) = _
    rw [actualInput]
    exact loss

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourcePhysicalProjection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
