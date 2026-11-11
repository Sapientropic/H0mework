import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceGramAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Receipt

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceGramAction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction
open scoped InnerProductSpace

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

/-- The actual installed source supplies both the complete action and its invertible coefficient. -/
def consume_installed_source_action {Result : Sort u}
 (consumer :
  type_of% (generatedK_eq_original c) →
  type_of% (installedOriginalKReceiptAt_eq_source observation nontrivial rightHalf) →
  type_of% (original_fixedResidual_source_Gram c observation.mathlibZero) →
  type_of% (installedRuntimeEffect_factorizes observation nontrivial) →
  type_of% (original_fixedResidual_source_action c observation.mathlibZero) →
  type_of% (sourceRate_sum_ne_zero c) → Result) : Result :=
 consume_installed_source_Gram observation nontrivial rightHalf
  (fun sourceIdentity sourceAnchor sourceGram factorization =>
   consumer sourceIdentity sourceAnchor sourceGram factorization
    (original_fixedResidual_source_action c observation.mathlibZero) (sourceRate_sum_ne_zero c))

/-- The already installed receipt evaluates the inverse source action at its own source coordinate. -/
theorem installed_fixedResidual_from_source_forcing :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual=
 (star (sourceRate c)+sourceRate c)⁻¹ *
  ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
   sourceGramForcing c (Real.log stageZeroSonineQ) i j := by
 rw [installedOriginalKReceiptAt_eq_source]
 exact original_fixedResidual_from_source_forcing c observation.mathlibZero

/-- Every action premise is consumed before the value travels through the original whole-next factorization. -/
theorem installed_source_action_on_original_evolution :
 let root:=runtimeEffectRoot observation nontrivial
 let visit:=runtimeEffectVisit observation nontrivial
 let registered:=runtimeEffectRootedActive observation nontrivial
 let receipt:=installedOriginalKReceiptAt observation nontrivial rightHalf
 let evolution:=root.canonicalCausalAnswerAndNext (ULift.up visit)
 HEq (evolution.generated,
       evolution.generated.projectionOutcome (runtimeEffectRecognition observation nontrivial).rootEffectProjection,
       evolution.nextCurrent,receipt.kernel,receipt.fixedResidual)
     (root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit,
       registered.installedFiber,root.generatedNextCurrentAt visit,generatedK c,
       (star (sourceRate c)+sourceRate c)⁻¹ *
        ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
         sourceGramForcing c (Real.log stageZeroSonineQ) i j) := by
 apply consume_installed_source_action observation nontrivial rightHalf
 intro sourceIdentity sourceAnchor sourceGram factorization sourceAction coefficientNonzero
 have kernel : (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel=generatedK c :=
  (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel) sourceAnchor).trans sourceIdentity.symm
 have matrixAction :
   (star (sourceRate c)+sourceRate c) *
    (∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
     sourceFiniteGram c (Real.log stageZeroSonineQ) i j) =
    ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
     sourceGramForcing c (Real.log stageZeroSonineQ) i j := by
  rw [← sourceGram]
  exact sourceAction
 have evaluated :
   (∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
     sourceFiniteGram c (Real.log stageZeroSonineQ) i j) =
   (star (sourceRate c)+sourceRate c)⁻¹ *
    ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
     sourceGramForcing c (Real.log stageZeroSonineQ) i j := by
  apply mul_left_cancel₀ coefficientNonzero
  rw [← mul_assoc, mul_inv_cancel₀ coefficientNonzero, one_mul]
  exact matrixAction
 have residual :=
  (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.fixedResidual) sourceAnchor).trans
   (sourceGram.trans evaluated)
 exact pair_heq (heq_of_eq factorization.1)
  (pair_heq factorization.2.1
   (pair_heq (heq_of_eq factorization.2.2)
    (pair_heq (heq_of_eq kernel) (heq_of_eq residual))))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceGramAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
