import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.PriceChannels
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativePortSourceCalculation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteMaterialSemantics

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceProgram
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution OriginalRieszSource
open FixedWindowFourierReaction
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace BigOperators
namespace M
export OriginalConstantFourierPriceMath
  (seed velocity velocity_seed scalarRead scalarLift scalar_seed scalar_lift meanRead mean_read
   rawMean ordinaryMean read embed center inverse wave wholeWindow windowMap window outer
   generatedDrive generatedPrice originalInputs original_price)
end M
namespace B
export OriginalKBFiniteCalculation
  (endpointRead constantCode coefficientSourceCode sourceEnvironment coefficient_A_code_eval coefficient_beta_code_eval)
end B
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
open private quarter_phase_pair_chart quarter_fourier_constant_chart from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.ConstantFourierEuler
open private coefficient_A_eval coefficient_beta_eval from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteMaterialSemantics
open private window_read from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.PriceChannels
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Mz" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "μq" => MeasureTheory.volume.restrict (symmetricInterval q)

/-- The complete unprojected velocity retains the ordinary edge mean. -/
theorem velocity_raw : ConstantFourierEulerVelocity.originalVelocity=
    Constructor.compact (Edge.raw q) (Edge.raw_continuous q) := by
  apply quarterChart.injective
  rw [ConstantFourierEulerVelocity.originalVelocity,quarterChart.apply_symm_apply,
    Edge.compact_raw,map_sub,map_smul,quarter_phase_pair_chart,quarter_fourier_constant_chart]
  have ward := ConstantFourierEulerVelocity.constant_column_ward q (by norm_num : 0<q)
  have normalized : (q/2:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q) e-
      (1/2:ℂ) • burnolRechartedTruncatedFourierOperator q e=
        (q:ℂ) • burnolRadiusBoundaryCosineState q-burnolRechartedTruncatedFourierOperator q e := by
    calc
      _=(1/2:ℂ) • ((q:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q) e+
          burnolRechartedTruncatedFourierOperator q e)-burnolRechartedTruncatedFourierOperator q e := by push_cast;module
      _=_ := by rw [ward];push_cast;module
  rw [normalized]
  have square : Real.sqrt q=1/2 := (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [square]
  push_cast
  module

private theorem read_embed (value:Mz) : M.read (M.embed value)=value := by
  change Constructor.zeroMean (R (E (value:Hq)))=value
  rw [burnolQuarterRestriction_zeroExtension]
  apply Subtype.ext
  exact Submodule.starProjection_eq_self_iff.mpr value.property
private theorem inverse_embed (value:Mz) : M.inverse (M.embed value)=M.embed (burnolMeanZeroBlockInverse value) := by
  change M.embed (burnolMeanZeroBlockInverse (M.read (M.embed value)))=_
  rw [read_embed]
private theorem wave_embed (value:Mz) : M.wave (M.embed value)=M.embed (burnolMeanZeroTruncatedFourier value) := by
  change M.embed (burnolMeanZeroTruncatedFourier (M.read (M.embed value)))=_
  rw [read_embed]

def endpointLift : BurnolL2 →L[ℂ] BurnolL2 := M.scalarLift.comp B.endpointRead
def scalarAction : BurnolL2 →+ BurnolL2 →+ BurnolL2 where
  toFun left := ((M.scalarRead left) • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom
  map_zero' := by ext right;simp
  map_add' := by intro left right;ext value;simp [add_smul]
private def linear (operation:BurnolL2 →L[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear operation.toLinearMap.toAddMonoidHom body
private def linearMap (operation:BurnolL2 →ₗ[ℂ] BurnolL2) (body:Prog.E) : Prog.E :=
  .linear operation.toAddMonoidHom body
private def scale (scalar:ℂ) (body:Prog.E) : Prog.E := linear (scalar • ContinuousLinearMap.id ℂ BurnolL2) body
def seedCode : Prog.E := .var (0:Fin 2)
def velocityCode : Prog.E := linear M.velocity seedCode
def etaCode : Prog.E := linear M.center velocityCode
def uCode : Prog.E := linear M.inverse etaCode
def vCode : Prog.E := linear M.wave uCode
def familyCode : Fin 6 → Prog.E :=
  ![uCode,vCode,linear M.ordinaryMean uCode,linear M.ordinaryMean vCode,linear M.rawMean velocityCode,seedCode]
def coefficientACode (c:BurnolCompletedMellinCoordinate) (b:BurnolL2) : Prog.E :=
  .add (scale (star c.value*GapEuler.gapMean q c) seedCode) (linear endpointLift (.const b))
def coefficientBetaCode (c:BurnolCompletedMellinCoordinate) (sb:BurnolL2) : Prog.E :=
  .add (scale (burnolRieszFourierForcingRaw c q) seedCode) (linear endpointLift (.const sb))
def rowCode (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) (channel:Fin 6) (side:Fin 2) : Prog.E :=
  .add (.bilinear scalarAction (coefficientACode c b)
    (linearMap (M.wholeWindow c 1 0 channel side) (familyCode channel)))
    (.bilinear scalarAction (coefficientBetaCode c sb)
      (linearMap (M.wholeWindow c 0 1 channel side) (familyCode channel)))
def sumCode (items:Fin 6→Prog.E) : Prog.E :=
  .add (items 0) (.add (items 1) (.add (items 2) (.add (items 3) (.add (items 4) (items 5)))))
def driveCode (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) (side:Fin 2) : Prog.E :=
  linear M.center (sumCode (fun channel=>rowCode c b sb channel side))
def correctionCode (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) : Prog.E :=
  linear M.inverse (.add (driveCode c b sb 1) (scale (-1) (linear M.wave (driveCode c b sb 0))))
def priceRead (c:BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] ℂ :=
  innerSL ℂ (M.embed (OriginalConstantFourierPriceFlow.power c))
def priceLift (c:BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 := M.scalarLift.comp (priceRead c)
def code (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) : Prog.E := linear (priceLift c) (correctionCode c b sb)

def coefficientA (c:BurnolCompletedMellinCoordinate) (seed b:BurnolL2) : ℂ :=
  star c.value*GapEuler.gapMean q c*M.scalarRead seed+B.endpointRead b
def coefficientBeta (c:BurnolCompletedMellinCoordinate) (seed sb:BurnolL2) : ℂ :=
  burnolRieszFourierForcingRaw c q*M.scalarRead seed+B.endpointRead sb

private theorem coefficient_A_read (c:BurnolCompletedMellinCoordinate) (b:BurnolL2) (env:Env Prog.Value Prog.Var) :
    M.scalarRead ((coefficientACode c b).eval env)=coefficientA c (env () 0) b := by
  change M.scalarRead ((star c.value*GapEuler.gapMean q c) • env () 0+M.scalarLift (B.endpointRead b))=_
  rw [map_add,map_smul,M.scalar_lift]
  rfl
private theorem coefficient_beta_read (c:BurnolCompletedMellinCoordinate) (sb:BurnolL2) (env:Env Prog.Value Prog.Var) :
    M.scalarRead ((coefficientBetaCode c sb).eval env)=coefficientBeta c (env () 0) sb := by
  change M.scalarRead ((burnolRieszFourierForcingRaw c q) • env () 0+M.scalarLift (B.endpointRead sb))=_
  rw [map_add,map_smul,M.scalar_lift]
  rfl

private theorem outer_coefficients (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (value:BurnolL2) (x:ℝ) :
    M.outer c a b channel side value x=a*M.outer c 1 0 channel side value x+b*M.outer c 0 1 channel side value x := by
  fin_cases side <;> dsimp [M.outer] <;> ring
private theorem window_coefficients (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (value:BurnolL2) : M.window c a b channel side value=
      a • M.window c 1 0 channel side value+b • M.window c 0 1 channel side value := by
  apply MeasureTheory.Lp.ext
  filter_upwards [window_read c a b channel side value,window_read c 1 0 channel side value,
    window_read c 0 1 channel side value,
    MeasureTheory.Lp.coeFn_add (a • M.window c 1 0 channel side value) (b • M.window c 0 1 channel side value),
    MeasureTheory.Lp.coeFn_smul a (M.window c 1 0 channel side value),
    MeasureTheory.Lp.coeFn_smul b (M.window c 0 1 channel side value)] with x total left right add ra rb
  rw [total,add,Pi.add_apply,ra,rb,Pi.smul_apply,Pi.smul_apply,left,right]
  unfold TwoPieceFourierAction.pieceRaw
  split_ifs
  · simp only [smul_zero,zero_add]
  · exact outer_coefficients c a b channel side value |x|

private theorem row_eval (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) (channel:Fin 6) (side:Fin 2)
    (env:Env Prog.Value Prog.Var) : (rowCode c b sb channel side).eval env=
      E (M.window c (coefficientA c (env () 0) b) (coefficientBeta c (env () 0) sb) channel side ((familyCode channel).eval env)) := by
  change M.scalarRead ((coefficientACode c b).eval env) • E (M.window c 1 0 channel side ((familyCode channel).eval env))+
    M.scalarRead ((coefficientBetaCode c sb).eval env) • E (M.window c 0 1 channel side ((familyCode channel).eval env))=_
  rw [coefficient_A_read,coefficient_beta_read]
  have actual := congrArg (fun value:Hq=>E value)
    (window_coefficients c (coefficientA c (env () 0) b) (coefficientBeta c (env () 0) sb)
      channel side ((familyCode channel).eval env))
  rw [map_add,map_smul,map_smul] at actual
  exact actual.symm

private theorem sum_eval (items:Fin 6→Prog.E) (env:Env Prog.Value Prog.Var) :
    (sumCode items).eval env=∑ i:Fin 6,(items i).eval env := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

private theorem drive_eval (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) (side:Fin 2)
    (env:Env Prog.Value Prog.Var) : (driveCode c b sb side).eval env=
      M.embed (M.generatedDrive c (coefficientA c (env () 0) b) (coefficientBeta c (env () 0) sb)
        (fun channel=>(familyCode channel).eval env) side) := by
  change M.center ((sumCode (fun channel=>rowCode c b sb channel side)).eval env)=_
  rw [sum_eval]
  simp_rw [row_eval]
  rw [←map_sum]
  change M.embed (Constructor.zeroMean (R (E _)))=_
  rw [burnolQuarterRestriction_zeroExtension]
  rfl

private theorem price_embed (c:BurnolCompletedMellinCoordinate) (value:Mz) :
    priceRead c (M.embed value)=inner ℂ (OriginalConstantFourierPriceFlow.power c) value := by
  change inner ℂ ((R).adjoint (OriginalConstantFourierPriceFlow.power c:Hq)) (E (value:Hq))=_
  rw [ContinuousLinearMap.adjoint_inner_left,burnolQuarterRestriction_zeroExtension]
  rfl

theorem programme_equation (c:BurnolCompletedMellinCoordinate) (b sb:BurnolL2) (env:Env Prog.Value Prog.Var) :
    (code c b sb).eval env=M.scalarLift (M.generatedPrice c
      (coefficientA c (env () 0) b) (coefficientBeta c (env () 0) sb)
      (fun channel=>(familyCode channel).eval env)) := by
  change M.scalarLift (priceRead c (M.inverse
    ((driveCode c b sb 1).eval env+(-1:ℂ) • M.wave ((driveCode c b sb 0).eval env))))=_
  rw [drive_eval,drive_eval,wave_embed,neg_one_smul,←sub_eq_add_neg,←map_sub,inverse_embed,price_embed]
  rfl

def sourceEnvironment : Env Prog.Value Prog.Var := fun _ _=>M.seed
theorem velocity_actual : velocityCode.eval sourceEnvironment=E ConstantFourierEulerVelocity.originalVelocity :=
  M.velocity_seed
theorem eta_actual : etaCode.eval sourceEnvironment=M.embed Response.eta := by
  change M.center (velocityCode.eval sourceEnvironment)=_
  rw [velocity_actual]
  change M.embed (Constructor.zeroMean (R (E ConstantFourierEulerVelocity.originalVelocity)))=_
  rw [burnolQuarterRestriction_zeroExtension,ConstantFourierEulerVelocity.originalVelocity_centered]
theorem u_actual : uCode.eval sourceEnvironment=M.embed Response.u := by
  change M.inverse (etaCode.eval sourceEnvironment)=_
  rw [eta_actual,inverse_embed]
  rfl
theorem v_actual : vCode.eval sourceEnvironment=M.embed Response.v := by
  change M.wave (uCode.eval sourceEnvironment)=_
  rw [u_actual,wave_embed]
  rfl
theorem family_actual (channel:Fin 6) : (familyCode channel).eval sourceEnvironment=M.originalInputs channel := by
  fin_cases channel <;> dsimp [familyCode,M.originalInputs]
  · exact u_actual
  · exact v_actual
  · change M.ordinaryMean (uCode.eval sourceEnvironment)=_
    rw [u_actual]
    change M.scalarLift (M.meanRead (burnolTruncatedFourier (R (E (Response.u:Hq)))))=_
    rw [burnolQuarterRestriction_zeroExtension,M.mean_read]
  · change M.ordinaryMean (vCode.eval sourceEnvironment)=_
    rw [v_actual]
    change M.scalarLift (M.meanRead (burnolTruncatedFourier (R (E (Response.v:Hq)))))=_
    rw [burnolQuarterRestriction_zeroExtension,M.mean_read]
  · change M.rawMean (velocityCode.eval sourceEnvironment)=_
    rw [velocity_actual]
    change M.scalarLift (M.meanRead (R (E ConstantFourierEulerVelocity.originalVelocity)))=_
    rw [burnolQuarterRestriction_zeroExtension,M.mean_read,velocity_raw]
    rfl
  · rfl

def originalB (c:BurnolCompletedMellinCoordinate) : BurnolL2 := (B.coefficientSourceCode c).eval B.sourceEnvironment
def originalSB (c:BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (OriginalKCoefficientBSelfCalculation.coefficientSCode c).eval B.sourceEnvironment
theorem coefficient_A_actual (c:BurnolCompletedMellinCoordinate) : coefficientA c M.seed (originalB c)=Kernel.A c := by
  have source := (B.coefficient_A_code_eval c B.constantCode B.sourceEnvironment).symm.trans
    (coefficient_A_eval c B.constantCode)
  have read := congrArg M.scalarRead source
  change M.scalarRead ((star c.value*GapEuler.gapMean q c+B.endpointRead (originalB c)) • M.seed)=
    M.scalarRead (Kernel.A c • M.seed) at read
  rw [map_smul,map_smul,M.scalar_seed,smul_eq_mul,smul_eq_mul,mul_one,mul_one] at read
  unfold coefficientA
  rw [M.scalar_seed,mul_one]
  exact read
theorem coefficient_beta_actual (c:BurnolCompletedMellinCoordinate) : coefficientBeta c M.seed (originalSB c)=Kernel.beta c := by
  have source := (B.coefficient_beta_code_eval c B.constantCode B.sourceEnvironment).symm.trans
    (coefficient_beta_eval c B.constantCode)
  have read := congrArg M.scalarRead source
  change M.scalarRead ((burnolRieszFourierForcingRaw c q+B.endpointRead (originalSB c)) • M.seed)=
    M.scalarRead (Kernel.beta c • M.seed) at read
  rw [map_smul,map_smul,M.scalar_seed,smul_eq_mul,smul_eq_mul,mul_one,mul_one] at read
  unfold coefficientBeta
  rw [M.scalar_seed,mul_one]
  exact read

theorem original_price (c:BurnolCompletedMellinCoordinate) :
    (code c (originalB c) (originalSB c)).eval sourceEnvironment=
      M.scalarLift (OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c) := by
  rw [programme_equation]
  change M.scalarLift (M.generatedPrice c (coefficientA c M.seed (originalB c))
    (coefficientBeta c M.seed (originalSB c)) (fun channel=>(familyCode channel).eval sourceEnvironment))=_
  rw [coefficient_A_actual,coefficient_beta_actual]
  have fields : (fun channel=>(familyCode channel).eval sourceEnvironment)=M.originalInputs := funext family_actual
  rw [fields,M.original_price]

end OriginalConstantFourierPriceProgram
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceProgram"
