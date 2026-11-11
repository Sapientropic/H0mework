import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteContactPrice.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantDual

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeUnitInput
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution OriginalRieszSource
namespace P
export OriginalConstantFourierPriceProgram
  (code coefficientACode coefficientBetaCode coefficientA coefficientBeta originalB originalSB
   coefficient_A_actual coefficient_beta_actual)
end P
namespace M
export OriginalConstantFourierPriceMath (seed scalarRead scalarLift scalar_seed embed)
end M
namespace G
export OriginalConstantFourierPriceSource.Generated (environment)
end G
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog

namespace Retained
variable (c:BurnolCompletedMellinCoordinate) (seed b sb:BurnolL2)
variable (reference:SourceOperationExecutionDebt.State (G.environment seed) (P.code c b sb))
variable (total:BurnolL2) (terminal:reference.1=.const total)
variable {α:Type} (actual:α) (same:HEq actual reference)
noncomputable def trace := OriginalContactPriceInput.Retained.trace c seed b sb reference total terminal actual same
noncomputable def alphaLift := OriginalContactPriceInput.Traced.alphaLift c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def betaLift := OriginalContactPriceInput.Traced.betaLift c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def alphaTrace := OriginalContactPriceInput.Traced.alphaTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def betaTrace := OriginalContactPriceInput.Traced.betaTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def uValue := OriginalContactPriceInput.Traced.uValue c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def vValue := OriginalContactPriceInput.Traced.vValue c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def uTrace := OriginalContactPriceInput.Traced.uTrace c b sb (trace c seed b sb reference total terminal actual same)
noncomputable def vTrace := OriginalContactPriceInput.Traced.vTrace c b sb (trace c seed b sb reference total terminal actual same)

theorem alpha_lift (source:seed=M.seed) :
    alphaLift c seed b sb reference total terminal actual same=M.scalarLift (P.coefficientA c seed b) := by
  have generated := (alphaTrace c seed b sb reference total terminal actual same).sound.symm
  change alphaLift c seed b sb reference total terminal actual same=(P.coefficientACode c b).eval (G.environment seed) at generated
  rw [generated]
  change (star c.value*GapEuler.gapMean (1/4:ℝ) c) • seed+
    M.scalarLift (OriginalKBFiniteCalculation.endpointRead b)=
    M.scalarLift (star c.value*GapEuler.gapMean (1/4:ℝ) c*M.scalarRead seed+OriginalKBFiniteCalculation.endpointRead b)
  rw [source,M.scalar_seed,mul_one,map_add]
  rfl

theorem beta_lift (source:seed=M.seed) :
    betaLift c seed b sb reference total terminal actual same=M.scalarLift (P.coefficientBeta c seed sb) := by
  have generated := (betaTrace c seed b sb reference total terminal actual same).sound.symm
  change betaLift c seed b sb reference total terminal actual same=(P.coefficientBetaCode c sb).eval (G.environment seed) at generated
  rw [generated]
  change (burnolRieszFourierForcingRaw c (1/4:ℝ)) • seed+
    M.scalarLift (OriginalKBFiniteCalculation.endpointRead sb)=
    M.scalarLift (burnolRieszFourierForcingRaw c (1/4:ℝ)*M.scalarRead seed+OriginalKBFiniteCalculation.endpointRead sb)
  rw [source,M.scalar_seed,mul_one,map_add]
  rfl

theorem alpha_actual (source:seed=M.seed) (coefficient:b=P.originalB c) :
    alphaLift c seed b sb reference total terminal actual same=
      OriginalRieszSource.Kernel.A c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed := by
  rw [alpha_lift c seed b sb reference total terminal actual same source,source,coefficient,P.coefficient_A_actual]
  rfl

theorem beta_actual (source:seed=M.seed) (coefficient:sb=P.originalSB c) :
    betaLift c seed b sb reference total terminal actual same=
      OriginalRieszSource.Kernel.beta c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed := by
  rw [beta_lift c seed b sb reference total terminal actual same source,source,coefficient,P.coefficient_beta_actual]
  rfl

theorem u_actual (source:seed=M.seed) :
    uValue c seed b sb reference total terminal actual same=OriginalRieszSource.Response.wholeU :=
  OriginalContactPriceInput.Retained.u_actual c seed b sb reference total terminal actual same source

theorem v_actual (source:seed=M.seed) :
    vValue c seed b sb reference total terminal actual same=OriginalRieszSource.Response.wholeV :=
  OriginalContactPriceInput.Retained.v_actual c seed b sb reference total terminal actual same source
end Retained

namespace A
export OriginalCompleteFeeAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader
  actualTarget actualFrame actualOriginFace actualInputFace actualParentFace actualAdjointFace
  target_source_payload target_input_state target_parent_state target_adjoint_state)
end A
namespace C
export OriginalCompleteFeeConsumer (nextFace nextState nextValue nextTrace kernelInput actual_kernel_read)
end C
namespace Old
export OriginalCompleteFeeInput (kernelValue kernelTrace kernel_actual bValue bTrace)
end Old
open private targetRoot targetVisit frame_root frame_visit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private same_state endpoint_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKContactAction.Origin

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "root"=>A.sourceRoot observation nontrivial half depth ordinal t
local notation "visit"=>A.sourceVisit observation nontrivial half depth ordinal t
local notation "u7"=>A.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus"=>A.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader"=>A.sourceReader observation nontrivial half depth ordinal t
local notation "c"=>OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "seed"=>OriginalConstantFourierPriceSource.seedValue observation nontrivial half depth ordinal t
local notation "b"=>OriginalConstantFourierPriceSource.bValue observation nontrivial half depth ordinal t
local notation "sb"=>OriginalConstantFourierPriceSource.sbValue observation nontrivial half depth ordinal t
noncomputable def sourceRoot := targetRoot root visit u7 calculus reader
noncomputable def sourceVisit := targetVisit root visit u7 calculus reader
theorem source_frame_root : type_of% (frame_root root visit u7 calculus reader) := frame_root root visit u7 calculus reader
theorem source_frame_visit : type_of% (frame_visit root visit u7 calculus reader) := frame_visit root visit u7 calculus reader
noncomputable def oldInputFace := C.nextFace observation nontrivial half depth ordinal t
noncomputable def oldInputState := (oldInputFace observation nontrivial half depth ordinal t).rootRead
noncomputable def kernelInput := C.kernelInput observation nontrivial half depth ordinal t
noncomputable def kernelValue : BurnolL2 := (kernelInput observation nontrivial half depth ordinal t).1
theorem kernel_read : kernelValue observation nontrivial half depth ordinal t=Old.kernelValue observation nontrivial half depth ordinal t :=
  C.actual_kernel_read observation nontrivial half depth ordinal t
noncomputable def kernelTrace : Trace
    (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment
    (OriginalKCoefficientBSelfCalculation.sourceKernelCode c)
    (.const (kernelValue observation nontrivial half depth ordinal t)) :=
  Eq.mp (congrArg (fun value=>Trace
    (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment
    (OriginalKCoefficientBSelfCalculation.sourceKernelCode c) (.const value))
      (kernel_read observation nontrivial half depth ordinal t).symm)
    (Old.kernelTrace observation nontrivial half depth ordinal t)
theorem kernel_actual : kernelValue observation nontrivial half depth ordinal t=(burnolCompletedMellinRieszVector c:BurnolL2) :=
  (kernel_read observation nontrivial half depth ordinal t).trans (Old.kernel_actual observation nontrivial half depth ordinal t)
noncomputable def originFace := A.actualOriginFace observation nontrivial half depth ordinal t
noncomputable def priceFace := A.actualInputFace observation nontrivial half depth ordinal t
noncomputable def contactFace := A.actualParentFace observation nontrivial half depth ordinal t
noncomputable def adjointFace := A.actualAdjointFace observation nontrivial half depth ordinal t
theorem origin_source : type_of% (A.target_source_payload observation nontrivial half depth ordinal t) :=
  A.target_source_payload observation nontrivial half depth ordinal t
noncomputable def priceState := (priceFace observation nontrivial half depth ordinal t).rootRead
noncomputable def priceReference : SourceOperationExecutionDebt.State (G.environment seed) (P.code c b sb) :=
  OriginalContactPriceInput.referenceState observation nontrivial half depth ordinal t
private theorem price_same : HEq (priceState observation nontrivial half depth ordinal t)
    (priceReference observation nontrivial half depth ordinal t) :=
  (A.target_input_state observation nontrivial half depth ordinal t).trans
    ((OriginalContactAction.target_input_state observation nontrivial half depth ordinal t).trans
      (same_state observation nontrivial half depth ordinal t))
private noncomputable def priceTotal : BurnolL2 := OriginalConstantFourierPriceConsumer.nextValue observation nontrivial half depth ordinal t
private theorem price_terminal : (priceReference observation nontrivial half depth ordinal t).1=
    .const (priceTotal observation nontrivial half depth ordinal t) :=
  endpoint_source observation nontrivial half depth ordinal t
local notation "reference"=>priceReference observation nontrivial half depth ordinal t
local notation "total"=>priceTotal observation nontrivial half depth ordinal t
local notation "terminal"=>price_terminal observation nontrivial half depth ordinal t
local notation "actual"=>priceState observation nontrivial half depth ordinal t
local notation "same"=>price_same observation nontrivial half depth ordinal t
noncomputable def priceTrace := Retained.trace c seed b sb reference total terminal actual same
noncomputable def alphaLift := Retained.alphaLift c seed b sb reference total terminal actual same
noncomputable def betaLift := Retained.betaLift c seed b sb reference total terminal actual same
noncomputable def alphaTrace := Retained.alphaTrace c seed b sb reference total terminal actual same
noncomputable def betaTrace := Retained.betaTrace c seed b sb reference total terminal actual same
noncomputable def uValue := Retained.uValue c seed b sb reference total terminal actual same
noncomputable def vValue := Retained.vValue c seed b sb reference total terminal actual same
noncomputable def uTrace := Retained.uTrace c seed b sb reference total terminal actual same
noncomputable def vTrace := Retained.vTrace c seed b sb reference total terminal actual same
private theorem seed_actual : seed=M.seed := OriginalConstantFourierPriceOrigin.seed_actual observation nontrivial half depth ordinal t
theorem alpha_actual : alphaLift observation nontrivial half depth ordinal t=OriginalRieszSource.Kernel.A c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed :=
  Retained.alpha_actual c seed b sb reference total terminal actual same (seed_actual observation nontrivial half depth ordinal t)
    (OriginalConstantFourierPriceMaterial.b_actual observation nontrivial half depth ordinal t)
theorem beta_actual : betaLift observation nontrivial half depth ordinal t=OriginalRieszSource.Kernel.beta c • OriginalRieszFinitePairing.CoPoisson.Ward.ConstantDual.seed :=
  Retained.beta_actual c seed b sb reference total terminal actual same (seed_actual observation nontrivial half depth ordinal t)
    (OriginalConstantFourierPriceMaterial.sb_actual observation nontrivial half depth ordinal t)
theorem u_actual : uValue observation nontrivial half depth ordinal t=OriginalRieszSource.Response.wholeU :=
  Retained.u_actual c seed b sb reference total terminal actual same (seed_actual observation nontrivial half depth ordinal t)
theorem v_actual : vValue observation nontrivial half depth ordinal t=OriginalRieszSource.Response.wholeV :=
  Retained.v_actual c seed b sb reference total terminal actual same (seed_actual observation nontrivial half depth ordinal t)
end OriginalWholeUnitInput
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeUnitInput"
