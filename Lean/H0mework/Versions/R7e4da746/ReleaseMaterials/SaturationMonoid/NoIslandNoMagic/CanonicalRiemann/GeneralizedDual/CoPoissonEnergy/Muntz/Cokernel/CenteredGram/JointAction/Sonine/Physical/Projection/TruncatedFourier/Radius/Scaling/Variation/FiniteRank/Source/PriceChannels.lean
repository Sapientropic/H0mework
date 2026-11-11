import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.CollarValue
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.ConstantFourierEuler

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceMath
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing
open FixedWindowFourierReaction
open OriginalKPairedBEulerJunctionSource
open scoped InnerProductSpace Topology BigOperators
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier
local notation "E" => burnolQuarterZeroExtension
local notation "R" => burnolQuarterRestriction
local notation "T" => burnolTruncatedFourier
local notation "Fq" => burnolRadiusTruncatedFourierRaw q
local notation "h0" => junctionShift
local notation "p" => junctionPoint
local notation "μq" => volume.restrict (symmetricInterval q)
namespace CV
export OriginalConstantFourierCollarValue
  (collarClock transferOuter transferWindow generatedDrive generatedPrice actual_generated_price)
end CV
namespace PT
export OriginalConstantFourierPhysicalTransfer (physicalClock sourceProgramme sourceTransfer)
end PT
namespace BP
export BandFiniteSourcePrice (sourceColumn)
end BP

def seed : BurnolL2 := E (intervalConstant q)
def velocity : BurnolL2 →L[ℂ] BurnolL2 :=
  (E).comp (quarterChart.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((q/2:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q)-
       (1/2:ℂ) • burnolRechartedTruncatedFourierOperator q).comp
      (quarterChart.toContinuousLinearEquiv.toContinuousLinearMap.comp R)))

theorem velocity_seed : velocity seed=E ConstantFourierEulerVelocity.originalVelocity := by
  change E (quarterChart.symm
    (((q/2:ℂ) • burnolRadiusRechartedTruncatedFourierDerivative (by norm_num : 0<q)-
      (1/2:ℂ) • burnolRechartedTruncatedFourierOperator q) (quarterChart (R (E (intervalConstant q))))))=_
  rw [burnolQuarterRestriction_zeroExtension,quarter_constant_chart,map_smul]
  have square : Real.sqrt q=1/2 := (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  unfold ConstantFourierEulerVelocity.originalVelocity
  rw [square]
  push_cast
  rfl

def meanRead : Hq →L[ℂ] ℂ :=
  (((‖intervalConstant q‖^2:ℝ):ℂ)⁻¹) • innerSL ℂ (intervalConstant q)
def scalarRead : BurnolL2 →L[ℂ] ℂ := meanRead.comp R
def scalarLift : ℂ →L[ℂ] BurnolL2 := (ContinuousLinearMap.id ℂ ℂ).smulRight seed
def rawMean : BurnolL2 →L[ℂ] BurnolL2 := scalarLift.comp scalarRead
def ordinaryMean : BurnolL2 →L[ℂ] BurnolL2 := scalarLift.comp (meanRead.comp ((T).comp R))
def read : BurnolL2 →L[ℂ] M := Constructor.zeroMean.comp R
def embed : M →L[ℂ] BurnolL2 := (E).comp (Submodule.subtypeL burnolQuarterMeanZeroClosedFace.toSubmodule)
def center : BurnolL2 →L[ℂ] BurnolL2 := embed.comp read
def inverse : BurnolL2 →L[ℂ] BurnolL2 := embed.comp (burnolMeanZeroBlockInverse.comp read)
def wave : BurnolL2 →L[ℂ] BurnolL2 := embed.comp (burnolMeanZeroTruncatedFourier.comp read)

theorem mean_read (value:Hq) : meanRead value=burnolQuarterMeanCoefficient value := by
  change (((‖intervalConstant q‖^2:ℝ):ℂ)⁻¹)*inner ℂ (intervalConstant q) value=
    inner ℂ (intervalConstant q) value/((‖intervalConstant q‖^2:ℝ):ℂ)
  exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
theorem scalar_seed : scalarRead seed=1 := by
  change meanRead (R (E (intervalConstant q)))=1
  rw [burnolQuarterRestriction_zeroExtension,mean_read]
  have generated := Constructor.zeroMean_read (intervalConstant q)
  rw [Constructor.zeroMean_constant] at generated
  have fixed : burnolQuarterMeanCoefficient (intervalConstant q) • intervalConstant q=intervalConstant q :=
    (sub_eq_zero.mp generated.symm).symm
  have same : (burnolQuarterMeanCoefficient (intervalConstant q)-1) • intervalConstant q=0 := by
    rw [sub_smul,one_smul,fixed,sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp same).resolve_right (intervalConstant_ne_zero (by norm_num : (0:ℝ)<q)))

theorem scalar_lift (z:ℂ) : scalarRead (scalarLift z)=z := by
  change scalarRead (z • seed)=z
  rw [map_smul,scalar_seed,smul_eq_mul,mul_one]

private def fourierRead (x:ℝ) : BurnolL2 →ₗ[ℂ] ℂ where
  toFun value := Fq (R value) x
  map_add' left right := by rw [map_add,burnolRadiusTruncatedFourierRaw_add];rfl
  map_smul' z value := by rw [map_smul,burnolRadiusTruncatedFourierRaw_smul];rfl

/-- Six source channels preserve both ordinary means, the unprojected edge mean and the unit. -/
def column (channel:Fin 6) (side:Fin 2) (x:ℝ) : BurnolL2 →ₗ[ℂ] ℂ :=
  ![![fourierRead x,0,-scalarRead.toLinearMap,0,0,-scalarRead.toLinearMap] channel,
    ![0,-fourierRead x,0,scalarRead.toLinearMap,scalarRead.toLinearMap,
      (-Edge.raw q x) • scalarRead.toLinearMap] channel] side
def unitRead (channel:Fin 6) : BurnolL2 →ₗ[ℂ] ℂ := ![0,0,0,0,0,scalarRead.toLinearMap] channel

private theorem column_continuous (channel:Fin 6) (side:Fin 2) (value:BurnolL2) :
    Continuous (fun x:ℝ=>column channel side x value) := by
  fin_cases channel <;> fin_cases side <;> dsimp [column,fourierRead]
  all_goals first
    | exact burnolRadiusTruncatedFourierRaw_continuous _
    | exact (burnolRadiusTruncatedFourierRaw_continuous _).neg
    | exact continuous_const
    | exact (Edge.raw_continuous q).neg.mul continuous_const

def integral (rate:ℂ) (channel:Fin 6) (side:Fin 2) (time:ℝ) (value:BurnolL2) : ℂ :=
  ∫ s:ℝ in 0..time, Complex.exp (rate*(s:ℂ))*column channel side (PT.physicalClock s) value

private theorem integrand_continuous (rate:ℂ) (channel:Fin 6) (side:Fin 2) (value:BurnolL2) :
    Continuous (fun s:ℝ=>Complex.exp (rate*(s:ℂ))*column channel side (PT.physicalClock s) value) :=
  (by fun_prop : Continuous (fun s:ℝ=>Complex.exp (rate*(s:ℂ)))).mul
    ((column_continuous channel side value).comp (by unfold PT.physicalClock;fun_prop))

private theorem integral_continuous (rate:ℂ) (channel:Fin 6) (side:Fin 2) (value:BurnolL2) :
    Continuous (fun time:ℝ=>integral rate channel side time value) :=
  intervalIntegral.continuous_primitive (fun a b=>(integrand_continuous rate channel side value).intervalIntegrable a b) 0

private theorem integral_add (rate:ℂ) (channel:Fin 6) (side:Fin 2) (time:ℝ) (left right:BurnolL2) :
    integral rate channel side time (left+right)=integral rate channel side time left+integral rate channel side time right := by
  unfold integral
  simp only [map_add,mul_add]
  exact intervalIntegral.integral_add ((integrand_continuous rate channel side left).intervalIntegrable _ _)
    ((integrand_continuous rate channel side right).intervalIntegrable _ _)

private theorem integral_smul (rate:ℂ) (channel:Fin 6) (side:Fin 2) (time:ℝ) (z:ℂ) (value:BurnolL2) :
    integral rate channel side time (z • value)=z*integral rate channel side time value := by
  unfold integral
  simp only [map_smul,smul_eq_mul]
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

def outer (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (value:BurnolL2) (x:ℝ) : ℂ :=
  let time:=CV.collarClock x
  (Real.exp (h0/2):ℂ)/2 *
    ![Complex.exp (-(star c.value*(time:ℂ)))*
        (-a*unitRead channel value+a*integral (star c.value) channel 0 time value+
          b*integral (star c.value) channel 1 time value),
      Complex.exp (-((1-star c.value)*(time:ℂ)))*
        (b*unitRead channel value-a*integral (1-star c.value) channel 1 time value-
          b*integral (1-star c.value) channel 0 time value)] side

private theorem outer_continuous (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6)
    (side:Fin 2) (value:BurnolL2) : ContinuousOn (outer c a b channel side value) (Icc p q) := by
  have clock : ContinuousOn CV.collarClock (Icc p q) := by
    unfold CV.collarClock
    apply ContinuousOn.log (by fun_prop)
    intro x hx
    have pos:0<x:=junctionPoint_bounds.1.trans_le hx.1
    positivity
  have i0 := (integral_continuous (star c.value) channel 0 value).comp_continuousOn clock
  have i1 := (integral_continuous (star c.value) channel 1 value).comp_continuousOn clock
  have j0 := (integral_continuous (1-star c.value) channel 0 value).comp_continuousOn clock
  have j1 := (integral_continuous (1-star c.value) channel 1 value).comp_continuousOn clock
  change ContinuousOn (fun x=>outer c a b channel side value x) _
  fin_cases side <;> dsimp [outer]
  all_goals fun_prop

def window (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (value:BurnolL2) : Hq :=
  (TwoPieceFourierAction.piece_native p junctionPoint_bounds.1 junctionPoint_bounds.2
    (fun _=>0) (outer c a b channel side value) continuousOn_const
      (outer_continuous c a b channel side value)).toLp
    (TwoPieceFourierAction.pieceRaw p (fun _=>0) (outer c a b channel side value))

private theorem window_read (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (value:BurnolL2) : (window c a b channel side value:ℝ→ℂ)=ᵐ[μq]
      TwoPieceFourierAction.pieceRaw p (fun _=>0) (outer c a b channel side value) := MemLp.coeFn_toLp _

private theorem outer_add (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (left right:BurnolL2) (x:ℝ) :
    outer c a b channel side (left+right) x=outer c a b channel side left x+outer c a b channel side right x := by
  fin_cases side <;> dsimp [outer]
  all_goals rw [map_add,integral_add,integral_add]
  all_goals ring
private theorem outer_smul (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2)
    (z:ℂ) (value:BurnolL2) (x:ℝ) :
    outer c a b channel side (z • value) x=z*outer c a b channel side value x := by
  fin_cases side <;> dsimp [outer]
  all_goals rw [map_smul,integral_smul,integral_smul]
  all_goals simp only [smul_eq_mul]
  all_goals ring

def windowMap (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2) : BurnolL2 →ₗ[ℂ] Hq where
  toFun := window c a b channel side
  map_add' left right := by
    apply Lp.ext
    filter_upwards [window_read c a b channel side (left+right),window_read c a b channel side left,
      window_read c a b channel side right,Lp.coeFn_add (window c a b channel side left) (window c a b channel side right)]
      with x total l r sum
    rw [total,sum,Pi.add_apply,l,r]
    unfold TwoPieceFourierAction.pieceRaw
    split_ifs <;> simp only [outer_add,zero_add]
  map_smul' z value := by
    change window c a b channel side (z • value)=z • window c a b channel side value
    apply Lp.ext
    filter_upwards [window_read c a b channel side (z • value),window_read c a b channel side value,
      Lp.coeFn_smul z (window c a b channel side value)] with x total old scalar
    rw [total,scalar,Pi.smul_apply,old]
    unfold TwoPieceFourierAction.pieceRaw
    split_ifs <;> simp only [outer_smul,smul_eq_mul,mul_zero]

def wholeWindow (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (channel:Fin 6) (side:Fin 2) : BurnolL2 →ₗ[ℂ] BurnolL2 :=
  (E).toLinearMap.comp (windowMap c a b channel side)

/-- This recognition uses the original response only on the output side of the channel calculation. -/
def originalInputs : Fin 6 → BurnolL2 :=
  ![embed Response.u,embed Response.v,
    scalarLift (burnolQuarterMeanCoefficient (T (Response.u:Hq))),
    scalarLift (burnolQuarterMeanCoefficient (T (Response.v:Hq))),
    scalarLift Translator.ForcingMeanZero.edgeMean,seed]

theorem original_columns (side:Fin 2) (x:ℝ) :
    (∑ channel:Fin 6,column channel side x (originalInputs channel))=BP.sourceColumn side x := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  fin_cases side <;> dsimp [originalInputs,column,BP.sourceColumn,PsiDrive.psiMean]
  all_goals simp only [scalar_lift,scalar_seed]
  all_goals dsimp [fourierRead,embed]
  all_goals rw [burnolQuarterRestriction_zeroExtension]
  all_goals ring

theorem original_units : (∑ channel:Fin 6,unitRead channel (originalInputs channel))=1 := by
  simp [unitRead,originalInputs,Fin.sum_univ_succ,scalar_seed]

theorem original_integrals (rate:ℂ) (side:Fin 2) (time:ℝ) :
    (∑ channel:Fin 6,integral rate channel side time (originalInputs channel))=PT.sourceProgramme rate side time := by
  unfold integral
  rw [←intervalIntegral.integral_finsetSum]
  · unfold PT.sourceProgramme
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    exact (Finset.mul_sum Finset.univ _ _).symm.trans
      (congrArg (fun z:ℂ=>Complex.exp (rate*(x:ℂ))*z) (original_columns side (PT.physicalClock x)))
  · intro channel _
    exact (integrand_continuous rate channel side (originalInputs channel)).intervalIntegrable _ _

theorem original_outer (c:BurnolCompletedMellinCoordinate) (side:Fin 2) (x:ℝ) :
    (∑ channel:Fin 6,outer c (Kernel.A c) (Kernel.beta c) channel side (originalInputs channel) x)=
      CV.transferOuter c side x := by
  fin_cases side <;> dsimp [outer,CV.transferOuter,PT.sourceTransfer]
  all_goals rw [←Finset.mul_sum,←Finset.mul_sum]
  all_goals simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,original_units,original_integrals]
  all_goals ring

theorem original_windows (c:BurnolCompletedMellinCoordinate) (side:Fin 2) :
    (∑ channel:Fin 6,window c (Kernel.A c) (Kernel.beta c) channel side (originalInputs channel))=
      CV.transferWindow c side := by
  apply Lp.ext
  have children : ∀ᵐ x ∂μq,∀ channel:Fin 6,
      (window c (Kernel.A c) (Kernel.beta c) channel side (originalInputs channel):ℝ→ℂ) x=
        TwoPieceFourierAction.pieceRaw p (fun _=>0)
          (outer c (Kernel.A c) (Kernel.beta c) channel side (originalInputs channel)) x :=
    (ae_all_iff).mpr (fun channel=>window_read c (Kernel.A c) (Kernel.beta c) channel side (originalInputs channel))
  have target : (CV.transferWindow c side:ℝ→ℂ)=ᵐ[μq]
      TwoPieceFourierAction.pieceRaw p (fun _=>0) (CV.transferOuter c side) := MemLp.coeFn_toLp _
  filter_upwards [children,target,Lp.coeFn_fun_finsetSum Finset.univ (fun channel:Fin 6=>window c (Kernel.A c) (Kernel.beta c) channel side (originalInputs channel))]
    with x reads old sum
  rw [sum,old]
  simp only [reads,TwoPieceFourierAction.pieceRaw]
  split_ifs <;> simp only [Finset.sum_const_zero,original_outer]

def generatedDrive (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (values:Fin 6→BurnolL2) (side:Fin 2) : M :=
  Constructor.zeroMean (∑ channel:Fin 6,window c a b channel side (values channel))
def generatedPrice (c:BurnolCompletedMellinCoordinate) (a b:ℂ) (values:Fin 6→BurnolL2) : ℂ :=
  inner ℂ (OriginalConstantFourierPriceFlow.power c)
    (burnolMeanZeroBlockInverse (generatedDrive c a b values 1-
      burnolMeanZeroTruncatedFourier (generatedDrive c a b values 0)))

theorem original_price (c:BurnolCompletedMellinCoordinate) :
    generatedPrice c (Kernel.A c) (Kernel.beta c) originalInputs=
      OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c := by
  unfold generatedPrice generatedDrive
  rw [original_windows,original_windows]
  exact CV.actual_generated_price c

end OriginalConstantFourierPriceMath
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceMath"
