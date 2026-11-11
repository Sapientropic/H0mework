import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Bilinear
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalCFixedAdjoint.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxErrors 2
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalContactPriceInput
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace P
export OriginalConstantFourierPriceProgram
  (code driveCode sumCode rowCode coefficientACode coefficientBetaCode familyCode uCode vCode
   coefficientA coefficientBeta sourceEnvironment originalB originalSB u_actual v_actual coefficient_A_actual coefficient_beta_actual)
end P
namespace M
export OriginalConstantFourierPriceMath (seed embed scalarRead)
end M
namespace S
export OriginalConstantFourierPriceSource (seedValue bValue sbValue)
end S
namespace G
export OriginalConstantFourierPriceSource.Generated (reader environment)
end G
namespace C
export OriginalConstantFourierPriceConsumer (nextState nextValue)
end C
namespace A
export OriginalCFixedAdjointAction (actualInputFace target_input_state)
end A
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (state)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value)
end OC
open private expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private coefficient_A_read coefficient_beta_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKConstantFourierPriceProgram

namespace Traced
variable (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2)
variable {env:Env Prog.Value Prog.Var} {total:BurnolL2}
variable (actual:Trace env (P.code c b sb) (.const total))
noncomputable def drive := OriginalConstantFourierPriceSource.Traced.secondTrace c b sb actual
noncomputable def sum := Trace.splitLinear (drive c b sb actual)
noncomputable def firstRow := Trace.splitAdd (sum c b sb actual).trace
noncomputable def rowU := Trace.splitAdd (firstRow c b sb actual).leftTrace
noncomputable def alphaCut := Trace.splitBilinear (rowU c b sb actual).leftTrace
noncomputable def betaCut := Trace.splitBilinear (rowU c b sb actual).rightTrace
noncomputable def uCut := Trace.splitLinear (alphaCut c b sb actual).rightTrace
noncomputable def remainingRows := Trace.splitAdd (firstRow c b sb actual).rightTrace
noncomputable def rowV := Trace.splitAdd (remainingRows c b sb actual).leftTrace
noncomputable def vProduct := Trace.splitBilinear (rowV c b sb actual).leftTrace
noncomputable def vCut := Trace.splitLinear (vProduct c b sb actual).rightTrace
noncomputable def uValue := (uCut c b sb actual).input
noncomputable def vValue := (vCut c b sb actual).input
noncomputable def alphaLift := (alphaCut c b sb actual).leftValue
noncomputable def betaLift := (betaCut c b sb actual).leftValue
noncomputable def uTrace := (uCut c b sb actual).trace
noncomputable def vTrace := (vCut c b sb actual).trace
noncomputable def alphaTrace := (alphaCut c b sb actual).leftTrace
noncomputable def betaTrace := (betaCut c b sb actual).leftTrace
noncomputable def bEndpoint := Trace.splitAdd (alphaTrace c b sb actual)
noncomputable def bInput := Trace.splitLinear (bEndpoint c b sb actual).rightTrace
theorem b_input : (bInput c b sb actual).input=b := (bInput c b sb actual).trace.sound.symm
theorem u_equation : uValue c b sb actual=P.uCode.eval env := (uTrace c b sb actual).sound.symm
theorem v_equation : vValue c b sb actual=P.vCode.eval env := (vTrace c b sb actual).sound.symm
theorem alpha_equation : M.scalarRead (alphaLift c b sb actual)=P.coefficientA c (env () 0) b :=
  (congrArg M.scalarRead (alphaTrace c b sb actual).sound.symm).trans (coefficient_A_read c b env)
theorem beta_equation : M.scalarRead (betaLift c b sb actual)=P.coefficientBeta c (env () 0) sb :=
  (congrArg M.scalarRead (betaTrace c b sb actual).sound.symm).trans (coefficient_beta_read c sb env)
end Traced

private theorem cast_same {α β:Type} (actual:α) (reference:β) (same:HEq actual reference) :
    Eq.mp (type_eq_of_heq same) actual=reference := by cases same; rfl
private noncomputable def retype {α β:Type} (actual:α) (reference:β) (same:HEq actual reference) : β :=
  Eq.mp (type_eq_of_heq same) actual

namespace CastState
variable {env:Env Prog.Value Prog.Var} {raw:Prog.E} {α:Type}
variable (actual:α) (reference:SourceOperationExecutionDebt.State env raw) (same:HEq actual reference)
noncomputable def state : SourceOperationExecutionDebt.State env raw := retype actual reference same
theorem state_source : state actual reference same=reference := cast_same actual reference same
noncomputable def trace (value:BurnolL2) (terminal:reference.1=.const value) :
    Trace env raw (.const value) :=
  Eq.mp (congrArg (Trace env raw)
    ((congrArg Sigma.fst (state_source actual reference same)).trans terminal))
    (state actual reference same).2
end CastState

private theorem terminal_readback {env:Env Prog.Value Prog.Var} {raw:Prog.E}
    (state:SourceOperationExecutionDebt.State env raw) {value:BurnolL2}
    (terminal:state.1=.const value) : state.1=.const (state.1.eval env) := by
  rw [terminal]
  rfl

namespace Retained
variable (c:BurnolCompletedMellinCoordinate) (seed b sb:BurnolL2)
variable (reference:SourceOperationExecutionDebt.State (G.environment seed) (P.code c b sb))
variable (total:BurnolL2) (terminal:reference.1=.const total)
variable {α:Type} (actual:α) (same:HEq actual reference)
noncomputable def state : SourceOperationExecutionDebt.State (G.environment seed) (P.code c b sb) :=
  CastState.state (env := G.environment seed) (raw := P.code c b sb) actual reference same
noncomputable def trace : Trace (G.environment seed) (P.code c b sb) (.const total) :=
  CastState.trace (env := G.environment seed) (raw := P.code c b sb) actual reference same total terminal
noncomputable def uValue := Traced.uValue c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def vValue := Traced.vValue c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def alphaLift := Traced.alphaLift c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def betaLift := Traced.betaLift c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def uTrace := Traced.uTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def vTrace := Traced.vTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def alphaTrace := Traced.alphaTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def betaTrace := Traced.betaTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def bInput := Traced.bInput c b sb (trace c seed b sb reference total terminal actual same)
theorem b_input : type_of% (Traced.b_input c b sb (trace c seed b sb reference total terminal actual same)) :=
  Traced.b_input c b sb (trace c seed b sb reference total terminal actual same)
theorem u_actual (source:seed=M.seed) : uValue c seed b sb reference total terminal actual same=M.embed OriginalRieszSource.Response.u := by
  rw [uValue,Traced.u_equation]
  have environment : G.environment seed=P.sourceEnvironment := congrArg G.environment source
  rw [environment,P.u_actual]
theorem v_actual (source:seed=M.seed) : vValue c seed b sb reference total terminal actual same=M.embed OriginalRieszSource.Response.v := by
  rw [vValue,Traced.v_equation]
  have environment : G.environment seed=P.sourceEnvironment := congrArg G.environment source
  rw [environment,P.v_actual]
theorem alpha_actual (source:seed=M.seed) (coefficient:b=P.originalB c) :
    M.scalarRead (alphaLift c seed b sb reference total terminal actual same)=OriginalRieszSource.Kernel.A c := by
  rw [alphaLift,Traced.alpha_equation]
  change P.coefficientA c seed b=_
  rw [source,coefficient,P.coefficient_A_actual]
theorem beta_actual (source:seed=M.seed) (coefficient:sb=P.originalSB c) :
    M.scalarRead (betaLift c seed b sb reference total terminal actual same)=OriginalRieszSource.Kernel.beta c := by
  rw [betaLift,Traced.beta_equation]
  change P.coefficientBeta c seed sb=_
  rw [source,coefficient,P.coefficient_beta_actual]
end Retained

namespace OriginalB
namespace B
export OriginalKBFiniteCalculation (Value Var coefficientSourceCode)
end B
variable (c:BurnolCompletedMellinCoordinate) {env:Env B.Value B.Var} {value:BurnolL2}
variable (actual:Trace env (B.coefficientSourceCode c) (.const value))
noncomputable def inverseInput := originalInput actual
noncomputable def centeredInput := originalInput (inverseInput c actual).2.1
noncomputable def fourierInput := originalInput (centeredInput c actual).2.1
noncomputable def gapValue := (fourierInput c actual).1
noncomputable def gapTrace := (fourierInput c actual).2.1
theorem gap_source : gapValue c actual=OriginalRieszSourceGreen.gapState c := by
  exact (gapTrace c actual).sound.symm
end OriginalB

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "root" => OriginalConstantFourierPriceAction.sourceRoot observation nontrivial half depth ordinal t
local notation "visit" => OriginalConstantFourierPriceAction.sourceVisit observation nontrivial half depth ordinal t
local notation "u7" => OriginalConstantFourierPriceAction.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus" => OriginalConstantFourierPriceAction.sourceCalculus observation nontrivial half depth ordinal t
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "seed" => S.seedValue observation nontrivial half depth ordinal t
local notation "b" => S.bValue observation nontrivial half depth ordinal t
local notation "sb" => S.sbValue observation nontrivial half depth ordinal t
noncomputable def actualFace := A.actualInputFace observation nontrivial half depth ordinal t
noncomputable def actualState := (actualFace observation nontrivial half depth ordinal t).rootRead
noncomputable def referenceState : SourceOperationExecutionDebt.State (G.environment seed) (P.code c b sb) :=
  C.nextState observation nontrivial half depth ordinal t
private theorem same_state : HEq (actualState observation nontrivial half depth ordinal t)
    (referenceState observation nontrivial half depth ordinal t) :=
  A.target_input_state observation nontrivial half depth ordinal t
private noncomputable def endpointValue := C.nextValue observation nontrivial half depth ordinal t
private theorem endpoint_source : (referenceState observation nontrivial half depth ordinal t).1=
    .const (endpointValue observation nontrivial half depth ordinal t) := by
  change (referenceState observation nontrivial half depth ordinal t).1=
    .const ((referenceState observation nontrivial half depth ordinal t).1.eval (G.environment seed))
  exact terminal_readback (referenceState observation nontrivial half depth ordinal t)
    (expression (Value := Prog.Value) (Var := Prog.Var) (sort := ()) root visit u7 calculus
      (OriginalConstantFourierPriceAction.sourceReader observation nontrivial half depth ordinal t))
local notation "reference" => referenceState observation nontrivial half depth ordinal t
local notation "total" => endpointValue observation nontrivial half depth ordinal t
local notation "terminal" => endpoint_source observation nontrivial half depth ordinal t
local notation "actual" => actualState observation nontrivial half depth ordinal t
local notation "same" => same_state observation nontrivial half depth ordinal t
noncomputable def state := Retained.state c seed b sb reference actual same
noncomputable def trace := Retained.trace c seed b sb reference total terminal actual same
noncomputable def uValue := Retained.uValue c seed b sb reference total terminal actual same
noncomputable def vValue := Retained.vValue c seed b sb reference total terminal actual same
noncomputable def alphaLift := Retained.alphaLift c seed b sb reference total terminal actual same
noncomputable def betaLift := Retained.betaLift c seed b sb reference total terminal actual same
noncomputable def uTrace := Retained.uTrace c seed b sb reference total terminal actual same
noncomputable def vTrace := Retained.vTrace c seed b sb reference total terminal actual same
noncomputable def alphaTrace := Retained.alphaTrace c seed b sb reference total terminal actual same
noncomputable def betaTrace := Retained.betaTrace c seed b sb reference total terminal actual same
noncomputable def bInput := Retained.bInput c seed b sb reference total terminal actual same
noncomputable def inheritedBTrace :=
  Eq.mp (congrArg (fun value => Trace
    (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment
    (OriginalKBFiniteCalculation.coefficientSourceCode c) (.const value))
    (Retained.b_input c seed b sb reference total terminal actual same).symm)
    (OriginalConstantFourierPriceSource.inputBTrace observation nontrivial half depth ordinal t)
noncomputable def gapValue := OriginalB.gapValue c (inheritedBTrace observation nontrivial half depth ordinal t)
noncomputable def gapTrace := OriginalB.gapTrace c (inheritedBTrace observation nontrivial half depth ordinal t)
theorem gap_actual : type_of% (OriginalB.gap_source c (inheritedBTrace observation nontrivial half depth ordinal t)) :=
  OriginalB.gap_source c (inheritedBTrace observation nontrivial half depth ordinal t)
private theorem seed_source : seed=M.seed := OriginalConstantFourierPriceOrigin.seed_actual observation nontrivial half depth ordinal t
theorem u_actual : type_of% (Retained.u_actual c seed b sb reference total terminal actual same
    (seed_source observation nontrivial half depth ordinal t)) :=
  Retained.u_actual c seed b sb reference total terminal actual same (seed_source observation nontrivial half depth ordinal t)
theorem v_actual : type_of% (Retained.v_actual c seed b sb reference total terminal actual same
    (seed_source observation nontrivial half depth ordinal t)) :=
  Retained.v_actual c seed b sb reference total terminal actual same (seed_source observation nontrivial half depth ordinal t)
theorem alpha_actual : type_of% (Retained.alpha_actual c seed b sb reference total terminal actual same
    (seed_source observation nontrivial half depth ordinal t)
    (OriginalConstantFourierPriceMaterial.b_actual observation nontrivial half depth ordinal t)) :=
  Retained.alpha_actual c seed b sb reference total terminal actual same
    (seed_source observation nontrivial half depth ordinal t)
    (OriginalConstantFourierPriceMaterial.b_actual observation nontrivial half depth ordinal t)
theorem beta_actual : type_of% (Retained.beta_actual c seed b sb reference total terminal actual same
    (seed_source observation nontrivial half depth ordinal t)
    (OriginalConstantFourierPriceMaterial.sb_actual observation nontrivial half depth ordinal t)) :=
  Retained.beta_actual c seed b sb reference total terminal actual same
    (seed_source observation nontrivial half depth ordinal t)
    (OriginalConstantFourierPriceMaterial.sb_actual observation nontrivial half depth ordinal t)
end OriginalContactPriceInput
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalContactPriceInput"
