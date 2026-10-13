import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Prior
export OriginalKFullSourceRAction (factory actionPacket actualWriteRead actual_R_source_equation oldIncrement actualDelta originalField)
end Prior
namespace C
export OriginalKFullSourceRAction.C (Value Var)
end C
namespace Flux
export FiniteMobiusResolventFlux (sourceA primitiveSource)
end Flux
namespace Source
export OriginalKBoundarySourceAction.Source (value velocity seed)
end Source
abbrev Branches := OriginalKDefectAction.Branches
local notation "P" => burnolEvenAmbientProjection
local notation "F" => fourierL2.toLinearIsometry.toContinuousLinearMap

def sourceFields : BurnolL2 →L[ℂ] Branches :=
 ((ContinuousLinearMap.id ℂ BurnolL2).prod FiniteMobiusResolventFlux.D).prod
 ((F).prod ((F).comp FiniteMobiusResolventFlux.D))

def pairedAction (h : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
 (1/2 : ℂ) • ((burnolMultiplicativeDilation h).toLinearIsometry.toContinuousLinearMap +
  (burnolMultiplicativeDilation (-h)).toLinearIsometry.toContinuousLinearMap)

theorem paired_action_read (h : ℝ) (field : BurnolL2) :
 pairedAction h field = pairedBurnolMultiplicativeDilation h field := rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

def actualRecoveryStock : BurnolL2 :=
 Flux.primitiveSource observation nontrivial half +
 Flux.sourceA observation • OriginalKCombPhysicalAction.R observation nontrivial half
  (Prior.oldIncrement observation nontrivial half depth ordinal) +
 Flux.sourceA observation • OriginalKCombPhysicalAction.R observation nontrivial half
  (Prior.actualDelta observation nontrivial half depth ordinal)

def recoverSource (value : Branches) : BurnolL2 :=
 Flux.sourceA observation • Prior.originalField value - actualRecoveryStock observation nontrivial half depth ordinal

/-- All inherited and current R increments remain in their own source recovery stock. -/
theorem actual_source_recovered :
 recoverSource observation nontrivial half depth ordinal
  (Prior.actualWriteRead observation nontrivial half depth ordinal) =
 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2) := by
 have source := Prior.actual_R_source_equation observation nontrivial half depth ordinal
 have parent := OriginalKDefectAction.actual_native_physical_field observation nontrivial half depth ordinal
 change OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal |>.1.1 =
  (burnolCompletedMellinRieszVector _ : BurnolL2) +
  OriginalKDefectAction.inheritedIncrement observation nontrivial half depth ordinal +
  OriginalKDefectAction.actualDelta observation nontrivial half depth ordinal at parent
 rw [add_assoc] at parent
 change Prior.originalField (OriginalKDefectAction.actualWriteRead observation nontrivial half depth ordinal) =
  (burnolCompletedMellinRieszVector _ : BurnolL2) +
  Prior.oldIncrement observation nontrivial half depth ordinal at parent
 rw [parent] at source
 unfold recoverSource actualRecoveryStock
 change Flux.sourceA observation • (Prior.actualWriteRead observation nontrivial half depth ordinal).1.1 - _ = _
 linear_combination (norm := module) source

/-- The input contains only the actual R recovery stock and the two original source contacts. -/
def actualContactStock : BurnolL2 :=
 actualRecoveryStock observation nontrivial half depth ordinal +
 OriginalRieszSource.Kernel.A (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) • Source.seed -
 OriginalRieszSource.Kernel.beta (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) • fourierL2 Source.seed

def correctedSource (value : Branches) : BurnolL2 :=
 Flux.sourceA observation • Prior.originalField value - actualContactStock observation nontrivial half depth ordinal

theorem actual_corrected_source_recovered :
 correctedSource observation nontrivial half depth ordinal
  (Prior.actualWriteRead observation nontrivial half depth ordinal) =
 Source.value (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) := by
 unfold correctedSource actualContactStock
 have source := actual_source_recovered observation nontrivial half depth ordinal
 unfold recoverSource at source
 unfold Source.value
 linear_combination (norm := module) source

/-- The variable programme first computes the complete corrected orbit increment. -/
def orbitAction (h : ℝ) : Branches →L[ℂ] Branches :=
 sourceFields.comp ((pairedAction h - ContinuousLinearMap.id ℂ BurnolL2).comp
  ((Flux.sourceA observation) • Prior.originalField))

def correctedSourceLinear : Branches →L[ℂ] Branches :=
 sourceFields.comp ((Flux.sourceA observation) • Prior.originalField)

def correctedOrbitLinear (h : ℝ) : Branches →L[ℂ] Branches :=
 sourceFields.comp ((pairedAction h - ContinuousLinearMap.id ℂ BurnolL2).comp Prior.originalField)

def sourceCode (h : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
 .linear (s:=()) (t:=()) (correctedOrbitLinear h).toLinearMap.toAddMonoidHom
  (.add (.linear (s:=()) (t:=()) (correctedSourceLinear observation).toLinearMap.toAddMonoidHom (.var ()))
   (.const (sourceFields (-(actualContactStock observation nontrivial half depth ordinal)))))

theorem source_fields_first (field : BurnolL2) : Prior.originalField (sourceFields field) = field := rfl

theorem source_code_read (h : ℝ) (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceCode observation nontrivial half depth ordinal h).eval environment =
 sourceFields ((pairedAction h - ContinuousLinearMap.id ℂ BurnolL2)
  (correctedSource observation nontrivial half depth ordinal (environment () ()))) := by
 change correctedOrbitLinear h
  (correctedSourceLinear observation (environment () ()) + sourceFields (-(actualContactStock observation nontrivial half depth ordinal))) = _
 unfold correctedOrbitLinear correctedSourceLinear correctedSource
 simp only [ContinuousLinearMap.comp_apply, smul_apply, map_sub, source_fields_first, map_neg, ← sub_eq_add_neg]


theorem source_code_effect (h : ℝ) (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
 (sourceCode observation nontrivial half depth ordinal h).effect environment increment =
 orbitAction observation h (increment () ()) := by
 have source := Expr.eval_update (sourceCode observation nontrivial half depth ordinal h) environment increment
 rw [source_code_read, source_code_read] at source
 have split : correctedSource observation nontrivial half depth ordinal ((environment+increment) () ()) =
  correctedSource observation nontrivial half depth ordinal (environment () ()) +
  Flux.sourceA observation • Prior.originalField (increment () ()) := by
  unfold correctedSource
  change Flux.sourceA observation • Prior.originalField (environment () () + increment () ()) - _ = _
  rw [map_add, smul_add]
  abel
 rw [split, map_add, map_add] at source
 exact add_left_cancel source.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundaryNativeSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
