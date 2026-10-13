import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.Dynamics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalTwoWindowInverseForcing
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped Topology InnerProductSpace
attribute [local instance 1100] NormedSpace.complexToReal
local notation "q" => (1/4:ℝ)

def b (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ := burnolRieszSingleFourierSourceRaw coordinate
def p (coordinate : BurnolCompletedMellinCoordinate) : ℝ→ℂ := OriginalRieszFinitePairing.positionSource coordinate
def coupling (coordinate : BurnolCompletedMellinCoordinate) : ℂ := coordinate.value+star coordinate.value-1
def lowerScale (h : ℝ) : ℝ := Real.exp (-h/2)
def upperScale (h : ℝ) : ℝ := Real.exp (h/2)
def lowerRadius (h : ℝ) : ℝ := FixedWindowFourierReaction.actualRadius (-h)
def upperRadius (h : ℝ) : ℝ := FixedWindowFourierReaction.actualRadius h

def jointProduct (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  star (b coordinate (lowerScale h*x))*b coordinate (upperScale h*x)+
    star (p coordinate (lowerScale h*x))*p coordinate (upperScale h*x)
def sourceAction (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  (x:ℂ)*(star (b coordinate (lowerScale h*x))*b coordinate (upperScale h*x)-
    star (p coordinate (lowerScale h*x))*p coordinate (upperScale h*x))
def forcingCross (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  star (forceB coordinate (lowerScale h*x))*b coordinate (upperScale h*x)+
    star (b coordinate (lowerScale h*x))*forceB coordinate (upperScale h*x)-
    star (forceP coordinate (lowerScale h*x))*p coordinate (upperScale h*x)-
    star (p coordinate (lowerScale h*x))*forceP coordinate (upperScale h*x)

theorem b_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    HasDerivAt (b coordinate)
      ((lambda coordinate*b coordinate x+forceB coordinate x-(1/2:ℂ)*b coordinate x)/(x:ℂ)) x := by
  simpa only [b,original_source_euler] using OriginalRieszSourceGreen.source_hasDerivAt coordinate x positive.ne'

theorem p_hasDerivAt (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0<x) :
    HasDerivAt (p coordinate)
      ((-lambda coordinate*p coordinate x+forceP coordinate x-(1/2:ℂ)*p coordinate x)/(x:ℂ)) x := by
  have valueNonzero : coordinate.value≠0 := by
    intro zero
    have realZero:=congrArg Complex.re zero
    simp only [Complex.zero_re] at realZero
    linarith [coordinate.rightHalf]
  have power:=hasDerivAt_ofReal_cpow_const positive.ne'
    (neg_ne_zero.mpr (star_ne_zero.mpr valueNonzero))
  have generated:=((power.const_mul (1/2:ℂ)).sub_const (GapEuler.gapMean q coordinate)).sub
    (burnolRieszReturnRaw_hasDerivAt coordinate x)
  convert! generated using 1
  have raw:=original_return_euler coordinate x
  unfold p OriginalRieszFinitePairing.positionSource forceP lambda Constructor.returnEulerRaw at *
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr positive.ne'),Complex.cpow_one]
  field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
  linear_combination 4*raw

theorem original_two_leg_source_action (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) (positive : 0<x) :
    HasDerivAt (sourceAction coordinate h)
      (coupling coordinate*jointProduct coordinate h x+forcingCross coordinate h x) x := by
  have lowerPositive : 0<lowerScale h*x := mul_pos (Real.exp_pos _) positive
  have upperPositive : 0<upperScale h*x := mul_pos (Real.exp_pos _) positive
  have bLower:=(b_hasDerivAt coordinate (lowerScale h*x) lowerPositive).scomp x
    ((hasDerivAt_id x).const_mul (lowerScale h))
  have bUpper:=(b_hasDerivAt coordinate (upperScale h*x) upperPositive).scomp x
    ((hasDerivAt_id x).const_mul (upperScale h))
  have pLower:=(p_hasDerivAt coordinate (lowerScale h*x) lowerPositive).scomp x
    ((hasDerivAt_id x).const_mul (lowerScale h))
  have pUpper:=(p_hasDerivAt coordinate (upperScale h*x) upperPositive).scomp x
    ((hasDerivAt_id x).const_mul (upperScale h))
  have produced:=((Complex.ofRealCLM.hasDerivAt (x:=x)).mul (bLower.star.mul bUpper)).sub
    ((Complex.ofRealCLM.hasDerivAt (x:=x)).mul (pLower.star.mul pUpper))
  convert! produced using 1
  · funext y
    unfold sourceAction
    simp only [Function.comp_apply,Pi.mul_apply,Pi.sub_apply,Complex.ofRealCLM_apply]
    ring
  · unfold coupling lambda jointProduct forcingCross
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,
      Pi.mul_apply,Function.comp_apply,star_add,star_sub,star_mul,star_div₀,star_neg,star_one,star_ofNat,
      Complex.star_def,Complex.conj_ofReal,mul_one]
    have lowerNe : (lowerScale h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    have upperNe : (upperScale h:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne',
      lowerNe,upperNe]
    simp only [Complex.conj_conj]
    ring

theorem forceB_continuous (coordinate : BurnolCompletedMellinCoordinate) : Continuous (forceB coordinate) := by
  have left:=burnolRadiusTruncatedFourierRaw_continuous (Response.u:BurnolQuarterIntervalL2)
  have right:=burnolRadiusTruncatedFourierRaw_continuous (Response.v:BurnolQuarterIntervalL2)
  have edge:=Edge.raw_continuous q
  unfold forceB responseU responseV rawFourier
  fun_prop
theorem forceP_continuous (coordinate : BurnolCompletedMellinCoordinate) : Continuous (forceP coordinate) := by
  have left:=burnolRadiusTruncatedFourierRaw_continuous (Response.u:BurnolQuarterIntervalL2)
  have right:=burnolRadiusTruncatedFourierRaw_continuous (Response.v:BurnolQuarterIntervalL2)
  have edge:=Edge.raw_continuous q
  unfold forceP responseU responseV rawFourier
  fun_prop
theorem jointProduct_continuousAt (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) (positive : 0<x) :
    ContinuousAt (jointProduct coordinate h) x := by
  have bLower:=(b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have bUpper:=(b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have pLower:=(p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have pUpper:=(p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  exact (bLower.star.mul bUpper).add (pLower.star.mul pUpper)
theorem forcingCross_continuousAt (coordinate : BurnolCompletedMellinCoordinate) (h x : ℝ) (positive : 0<x) :
    ContinuousAt (forcingCross coordinate h) x := by
  have bLower:=(b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have bUpper:=(b_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have pLower:=(p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have pUpper:=(p_hasDerivAt coordinate _ (mul_pos (Real.exp_pos _) positive)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have forceBLower:=(forceB_continuous coordinate).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have forceBUpper:=(forceB_continuous coordinate).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  have forcePLower:=(forceP_continuous coordinate).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>lowerScale h*y) x)
  have forcePUpper:=(forceP_continuous coordinate).continuousAt.comp
    (by fun_prop : ContinuousAt (fun y:ℝ=>upperScale h*y) x)
  exact (((forceBLower.star.mul bUpper).add (bLower.star.mul forceBUpper)).sub
    (forcePLower.star.mul pUpper)).sub (pLower.star.mul forcePUpper)

end OriginalTwoWindowInverseForcing
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
