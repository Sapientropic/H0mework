import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceResidualRNativeSuccessor.Projection
import H0mework.Versions.R7e4da746.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Realization.Operations.Execution.Relations

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFullRBlockRelationSource
open Complex BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation
open SourceGeneratedObservationAction SourceGeneratedScalarDifferentialResidual

abbrev PhysicalValue := PairValue (PairValue OriginalKFullSourceRAction.C.Value)
abbrev PhysicalBranches := PhysicalValue ()

local instance physicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)

abbrev sourceP := OriginalKSourceResidualRNativeSuccessor.sourcePaInput
abbrev sourceN := OriginalKSourceResidualRNativeSuccessor.sourceNonPaInput
abbrev sourceR := OriginalKFullSourceRAction.variableAction observation nontrivial half

def paAction : PhysicalBranches →L[ℂ] PhysicalBranches :=
  (sourceR observation nontrivial half).comp sourceP

def npAction : PhysicalBranches →L[ℂ] PhysicalBranches :=
  sourceN.comp (paAction observation nontrivial half)

def unitField : PhysicalBranches →L[ℂ] BurnolL2 :=
  ((burnolPaResolventSourceCoefficient
    (burnolDivisionZeroCompletedMellinCoordinate observation
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)).comp
    (OriginalKCombCofinalPaAction.E.comp OriginalKFullSourceRAction.originalField)).smulRight
  (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
    (burnolZeroOwnedUnitTailState observation nontrivial
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf) : BurnolL2)

/-- Only the physical coordinate is replaced by its generated unit formula. -/
def npUnitSource : PhysicalBranches →L[ℂ] PhysicalBranches :=
  ((unitField observation nontrivial half).prod
    ((ContinuousLinearMap.snd ℂ BurnolL2 BurnolL2).comp
      ((ContinuousLinearMap.fst ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2)).comp
        (paAction observation nontrivial half)))).prod
    ((ContinuousLinearMap.snd ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2)).comp
      (paAction observation nontrivial half))

private def paSource (value : PhysicalBranches) : BurnolPaAmbientCarrier :=
  OriginalKCombCofinalPaAction.E (OriginalKFullSourceRAction.originalField value)

private theorem pa_physical (value : PhysicalBranches) :
    (paAction observation nontrivial half value).1.1 ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  change OriginalKCombPhysicalAction.R observation nontrivial half
    (paSource value : BurnolL2) ∈ _
  rw [OriginalKCombCofinalRAction.original_R_direct]
  exact burnolPaResolvent_physical observation nontrivial
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf _
    (OriginalKSourceResidualRNativeSuccessor.source_Pa_qualified value)

private def paPhysical (value : PhysicalBranches) : BurnolPaAmbientCarrier :=
  ⟨(paAction observation nontrivial half value).1.1,
    pa_physical observation nontrivial half value⟩

private theorem pa_response (value : PhysicalBranches) :
    paPhysical observation nontrivial half value =
      burnolPaResolventPhysicalResponse observation nontrivial
        (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
        (paSource value) (OriginalKSourceResidualRNativeSuccessor.source_Pa_qualified value) := by
  apply Subtype.ext
  change OriginalKCombPhysicalAction.R observation nontrivial half
    (paSource value : BurnolL2) = _
  rw [OriginalKCombCofinalRAction.original_R_direct]
  rfl

theorem np_unit_first (value : PhysicalBranches) :
    (npAction observation nontrivial half value).1.1 = unitField observation nontrivial half value := by
  have physical :
      burnolEvenAmbientProjection (paAction observation nontrivial half value).1.1 =
        paPhysical observation nontrivial half value :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (paPhysical observation nontrivial half value)
  have complement := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_orthogonal_val
    (paPhysical observation nontrivial half value)
  have unit := burnolPaResolventPhysicalResponse_Q observation nontrivial
    (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
    (paSource value) (OriginalKSourceResidualRNativeSuccessor.source_Pa_qualified value)
  rw [← pa_response observation nontrivial half value] at unit
  change (paAction observation nontrivial half value).1.1 -
    (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (burnolEvenAmbientProjection (paAction observation nontrivial half value).1.1) : BurnolL2) = _
  rw [physical]
  change ((paPhysical observation nontrivial half value -
    burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
      (paPhysical observation nontrivial half value) : BurnolPaAmbientCarrier) : BurnolL2) = _
  exact congrArg (fun entry : BurnolPaAmbientCarrier => (entry : BurnolL2)) (complement.symm.trans unit)

theorem np_action_source :
    npAction observation nontrivial half = npUnitSource observation nontrivial half := by
  apply ContinuousLinearMap.ext
  intro value
  apply Prod.ext
  · apply Prod.ext
    · exact np_unit_first observation nontrivial half value
    · change (paAction observation nontrivial half value).1.2 - 0 = _
      exact sub_zero _
  · change (paAction observation nontrivial half value).2 - 0 = _
    exact sub_zero _

variable {Var : Unit → Type}

/-- The original nested P, R and N actions retain the supplied source body. -/
def npCode (body : Expr PhysicalValue Var ()) : Expr PhysicalValue Var () :=
  .linear (s := ()) (t := ()) sourceN.toLinearMap.toAddMonoidHom
    (.linear (s := ()) (t := ()) (sourceR observation nontrivial half).toLinearMap.toAddMonoidHom
      (.linear (s := ()) (t := ()) sourceP.toLinearMap.toAddMonoidHom body))

def npSourceCode (body : Expr PhysicalValue Var ()) : Expr PhysicalValue Var () :=
  .linear (s := ()) (t := ()) (npUnitSource observation nontrivial half).toLinearMap.toAddMonoidHom body

theorem np_code_eval (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    (npCode observation nontrivial half body).eval environment =
      npAction observation nontrivial half (body.eval environment) := rfl

theorem np_source_code_eval (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    (npSourceCode observation nontrivial half body).eval environment =
      npUnitSource observation nontrivial half (body.eval environment) := rfl

theorem np_code_eval_source (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    (npCode observation nontrivial half body).eval environment =
      (npSourceCode observation nontrivial half body).eval environment :=
  congrArg (fun action : PhysicalBranches →L[ℂ] PhysicalBranches => action (body.eval environment))
    (np_action_source observation nontrivial half)

theorem np_code_effect_source (body : Expr PhysicalValue Var ())
    (environment increment : Env PhysicalValue Var) :
    (npCode observation nontrivial half body).effect environment increment =
      (npSourceCode observation nontrivial half body).effect environment increment := by
  have actual := Expr.eval_update (npCode observation nontrivial half body) environment increment
  have source := Expr.eval_update (npSourceCode observation nontrivial half body) environment increment
  rw [np_code_eval_source observation nontrivial half body environment,
    np_code_eval_source observation nontrivial half body (environment + increment)] at actual
  exact add_left_cancel (actual.symm.trans source)

def npWord (body : Expr PhysicalValue Var ()) : Formal ℤ PhysicalValue Var () :=
  Finsupp.single (npCode observation nontrivial half body) 1 -
    Finsupp.single (npSourceCode observation nontrivial half body) 1

theorem np_word_eval (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    evaluation (R := ℤ) environment (npWord observation nontrivial half body) = 0 := by
  simp only [npWord, map_sub, evaluation, Finsupp.linearCombination_single, one_smul]
  exact sub_eq_zero.mpr (np_code_eval_source observation nontrivial half body environment)

theorem np_code_source_distinct (body : Expr PhysicalValue Var ()) :
    npCode observation nontrivial half body ≠ npSourceCode observation nontrivial half body := by
  intro same
  have costs := congrArg remaining same
  simp only [npCode, npSourceCode, remaining] at costs
  omega

theorem np_word_nonzero (body : Expr PhysicalValue Var ()) :
    npWord observation nontrivial half body ≠ 0 := by
  intro zero
  apply np_code_source_distinct observation nontrivial half body
  exact Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0) (sub_eq_zero.mp zero)

def pnAction : PhysicalBranches →L[ℂ] PhysicalBranches :=
  sourceP.comp ((sourceR observation nontrivial half).comp sourceN)

def invisibleInput : PhysicalBranches →ₗ[ℂ] OriginalKCombCofinalPaAction.E.toLinearMap.ker :=
  LinearMap.codRestrict OriginalKCombCofinalPaAction.E.toLinearMap.ker
    (OriginalKFullSourceRAction.originalField.toLinearMap.comp sourceN.toLinearMap) (by
      intro value
      change OriginalKCombCofinalPaAction.invisible (OriginalKFullSourceRAction.originalField value) ∈ _
      exact OriginalKCombCofinalPaAction.invisible_mem _)

def firstEmbedding : BurnolL2 →L[ℂ] PhysicalBranches :=
  ((ContinuousLinearMap.id ℂ BurnolL2).prod (0 : BurnolL2 →L[ℂ] BurnolL2)).prod
    (0 : BurnolL2 →L[ℂ] (BurnolL2 × BurnolL2))

def pnInverseField : PhysicalBranches →ₗ[ℂ] BurnolL2 :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL.toLinearMap.comp
    ((LinearMap.range OriginalKCombCofinalPaAction.E.toLinearMap).subtype.comp
      ((residualEquivRange OriginalKCombCofinalPaAction.E.toLinearMap).toLinearMap.comp
        ((actionDefect (OriginalKCombPhysicalAction.R observation nontrivial half).toLinearMap
          OriginalKCombCofinalPaAction.E.toLinearMap).comp invisibleInput)))

def pnInverseSource : PhysicalBranches →ₗ[ℂ] PhysicalBranches :=
  firstEmbedding.toLinearMap.comp (pnInverseField observation nontrivial half)

theorem pn_source_inverse (value : PhysicalBranches) :
    (pnInverseSource observation nontrivial half value).1.1 =
      (((residualEquivRange OriginalKCombCofinalPaAction.E.toLinearMap)
        (actionDefect (OriginalKCombPhysicalAction.R observation nontrivial half).toLinearMap
          OriginalKCombCofinalPaAction.E.toLinearMap (invisibleInput value))).val : BurnolL2) := rfl

theorem pn_action_source :
    (pnAction observation nontrivial half).toLinearMap = pnInverseSource observation nontrivial half := by
  apply LinearMap.ext
  intro value
  rfl

def pnCode (body : Expr PhysicalValue Var ()) : Expr PhysicalValue Var () :=
  .linear (s := ()) (t := ()) sourceP.toLinearMap.toAddMonoidHom
    (.linear (s := ()) (t := ()) (sourceR observation nontrivial half).toLinearMap.toAddMonoidHom
      (.linear (s := ()) (t := ()) sourceN.toLinearMap.toAddMonoidHom body))

def pnSourceCode (body : Expr PhysicalValue Var ()) : Expr PhysicalValue Var () :=
  .linear (s := ()) (t := ()) (pnInverseSource observation nontrivial half).toAddMonoidHom body

theorem pn_code_eval (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    (pnCode observation nontrivial half body).eval environment =
      pnAction observation nontrivial half (body.eval environment) := rfl

theorem pn_source_code_eval (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    (pnSourceCode observation nontrivial half body).eval environment =
      pnInverseSource observation nontrivial half (body.eval environment) := rfl

theorem pn_code_eval_source (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    (pnCode observation nontrivial half body).eval environment =
      (pnSourceCode observation nontrivial half body).eval environment :=
  LinearMap.congr_fun (pn_action_source observation nontrivial half) (body.eval environment)

theorem pn_code_effect_source (body : Expr PhysicalValue Var ())
    (environment increment : Env PhysicalValue Var) :
    (pnCode observation nontrivial half body).effect environment increment =
      (pnSourceCode observation nontrivial half body).effect environment increment := by
  have actual := Expr.eval_update (pnCode observation nontrivial half body) environment increment
  have source := Expr.eval_update (pnSourceCode observation nontrivial half body) environment increment
  rw [pn_code_eval_source observation nontrivial half body environment,
    pn_code_eval_source observation nontrivial half body (environment + increment)] at actual
  exact add_left_cancel (actual.symm.trans source)

def pnWord (body : Expr PhysicalValue Var ()) : Formal ℤ PhysicalValue Var () :=
  Finsupp.single (pnCode observation nontrivial half body) 1 -
    Finsupp.single (pnSourceCode observation nontrivial half body) 1

theorem pn_word_eval (body : Expr PhysicalValue Var ()) (environment : Env PhysicalValue Var) :
    evaluation (R := ℤ) environment (pnWord observation nontrivial half body) = 0 := by
  simp only [pnWord, map_sub, evaluation, Finsupp.linearCombination_single, one_smul]
  exact sub_eq_zero.mpr (pn_code_eval_source observation nontrivial half body environment)

theorem pn_code_source_distinct (body : Expr PhysicalValue Var ()) :
    pnCode observation nontrivial half body ≠ pnSourceCode observation nontrivial half body := by
  intro same
  have costs := congrArg remaining same
  simp only [pnCode, pnSourceCode, remaining] at costs
  omega

theorem pn_word_nonzero (body : Expr PhysicalValue Var ()) :
    pnWord observation nontrivial half body ≠ 0 := by
  intro zero
  apply pn_code_source_distinct observation nontrivial half body
  exact Finsupp.single_left_injective (by norm_num : (1 : ℤ) ≠ 0) (sub_eq_zero.mp zero)

end OriginalKFullRBlockRelationSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
