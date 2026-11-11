import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResolventReconstruction.Action
import H0mework.Versions.Rdf421ff6.Arithmetic.RiemannRuntime.PairedOmegaEffectRowRoot

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u v
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
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

/-- The coordinate is read from the installed source receipt, with the exact original visit. -/
def consume_installed_source_Gram {Result : Sort u}
 (consumer :
  type_of% (generatedK_eq_original c) →
  type_of% (installedOriginalKReceiptAt_eq_source observation nontrivial rightHalf) →
  type_of% (original_fixedResidual_source_Gram c observation.mathlibZero) →
  type_of% (installedRuntimeEffect_factorizes observation nontrivial) → Result) : Result :=
 consumer (generatedK_eq_original c)
  (installedOriginalKReceiptAt_eq_source observation nontrivial rightHalf)
  (original_fixedResidual_source_Gram c observation.mathlibZero)
  (installedRuntimeEffect_factorizes observation nontrivial)

/-- The actual receipt reads the source Gram at its existing right-half fibre. -/
theorem installed_fixedResidual_source_Gram :
 (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual=
 ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
  sourceFiniteGram c (Real.log stageZeroSonineQ) i j := by
 rw [installedOriginalKReceiptAt_eq_source]
 exact original_fixedResidual_source_Gram c observation.mathlibZero

/-- This concrete reader transports source kernel and Gram values through the original whole-next factorization. -/
theorem installed_source_Gram_on_original_evolution :
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
       ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
        sourceFiniteGram c (Real.log stageZeroSonineQ) i j) := by
 apply consume_installed_source_Gram observation nontrivial rightHalf
 intro sourceIdentity sourceAnchor sourceGram factorization
 have kernel : (installedOriginalKReceiptAt observation nontrivial rightHalf).kernel=generatedK c :=
  (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.kernel) sourceAnchor).trans sourceIdentity.symm
 have residual : (installedOriginalKReceiptAt observation nontrivial rightHalf).fixedResidual=
  ∑ i : Fin 2,∑ j : Fin 2,star (sourceCoefficients c i)*sourceCoefficients c j*
   sourceFiniteGram c (Real.log stageZeroSonineQ) i j :=
  (congrArg (fun receipt : OriginalRieszFiniteSource.Receipt => receipt.fixedResidual) sourceAnchor).trans sourceGram
 exact pair_heq (heq_of_eq factorization.1)
  (pair_heq factorization.2.1
   (pair_heq (heq_of_eq factorization.2.2)
    (pair_heq (heq_of_eq kernel) (heq_of_eq residual))))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceResolventReconstruction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
