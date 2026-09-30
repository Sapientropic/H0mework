import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurBarePairing
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowHistoryMeanProjection (embed mean projection)
open NativeWindowHistoryMeanAction (meanOperator)
open NativeWindowHistoryMeanBlocks (diffusion)
open NativeWindowHistoryMeanDrift (drift)
open NativeWindowTraceWholeHistory (metric metricAction finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem young (x y eta : ℝ) (positive : 0 < eta) : 2*x*y ≤ eta*x^2+y^2/eta := by
  have cancel : eta*(y^2/eta)=y^2 := mul_div_cancel₀ _ positive.ne'
  apply (mul_le_mul_iff_left₀ positive).mp
  nlinarith only [sq_nonneg (eta*x-y),cancel]

open NativeWindowHistorySchurAdvectorAction (xAction wAction)

def pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nu : ℝ) (h l a : E) : ℝ := 2*inner ℝ h a+2*nu*inner ℝ l a

private theorem pairing_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nu : ℝ) (nu0 : 0 ≤ nu) (h l a : E) :
    |pairing nu h l a| ≤ 2*‖h‖*‖a‖+2*nu*‖l‖*‖a‖ := by
  have one := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm h a) (by norm_num : (0 : ℝ) ≤ 2)
  have two := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm l a) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nu0)
  have first : |2*inner ℝ h a| ≤ 2*‖h‖*‖a‖ := by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact one.trans_eq (by ring)
  have last : |2*nu*inner ℝ l a| ≤ 2*nu*‖l‖*‖a‖ := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num) nu0)]
    exact two.trans_eq (by ring)
  exact (abs_add_le _ _).trans (add_le_add first last)

private theorem scalar_bound (nu epsilon B m d a : ℝ) (positive : 0 < epsilon)
    (paid : a^2 ≤ (epsilon/(4*(1+2*nu^2/epsilon)))*d^2+B*m*d) :
    2*m*a+2*nu*d*a ≤ epsilon*d^2+(1+(1+2*nu^2/epsilon)^2*B^2/epsilon)*m^2 := by
  let S:=1+2*nu^2/epsilon
  have S0 : 0 < S := by dsimp only [S]; positivity
  have one := young m a 1 (by norm_num)
  have two := young d (nu*a) (epsilon/2) (by positivity)
  have three := young d (S*B*m) (epsilon/2) (by positivity)
  have first : 2*m*a+2*nu*d*a ≤ m^2+(epsilon/2)*d^2+S*a^2 := by
    have read : (nu*a)^2/(epsilon/2)=(2*nu^2/epsilon)*a^2 := by ring
    dsimp only [S]
    nlinarith only [one,two,read]
  have scaled := mul_le_mul_of_nonneg_left paid S0.le
  have cancel : S*(epsilon/(4*S))=epsilon/4 := by field_simp
  have read : (S*B*m)^2/(epsilon/2)=2*(S^2*B^2/epsilon)*m^2 := by ring
  have final : 2*m*a+2*nu*d*a ≤ epsilon*d^2+(1+S^2*B^2/epsilon)*m^2 := by
    have scaledRead : S*((epsilon/(4*S))*d^2+B*m*d)=(epsilon/4)*d^2+S*B*m*d := by rw [mul_add,← mul_assoc,cancel]; ring
    nlinarith only [first,scaled,scaledRead,three,read]
  exact final

def xWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) : ℝ :=
  pairing nu.coeff v (laplacianAction nu M v) (xAction seed M time v)

theorem source_x_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ M ≥ low,∀ time ∈ Icc 0 horizon,∀ v : H,
      |xWork seed M time v| ≤ epsilon*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  let z:=epsilon/(4*(1+2*nu.coeff^2/epsilon))
  have z0 : 0 < z := by dsimp only [z]; positivity
  obtain ⟨low,B,B0,source⟩ := NativeWindowHistorySchurAdvectorAction.source_graph_bound seed horizon nonnegative z z0
  refine ⟨low,1+(1+2*nu.coeff^2/epsilon)^2*B^2/epsilon,by positivity,fun M above time inside v => ?_⟩
  have paid := source M above time inside v
  have grad := mul_le_mul_of_nonneg_left (NativeWindowMetricGraphHistory.gradient_bound nu M v) B0
  have small : ‖xAction seed M time v‖^2 ≤ z*‖laplacianAction nu M v‖^2+B*‖v‖*‖laplacianAction nu M v‖ := by
    nlinarith only [paid,grad]
  exact (pairing_bound (E := H) nu.coeff nu.coeff_pos.le _ _ _).trans
    (scalar_bound nu.coeff epsilon B _ _ _ positive small)

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurBarePairing
