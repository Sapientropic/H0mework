import H0mework.Versions.X.NavierStokes.WindowSchurSchur.BarePairing
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.MixedAction
import H0mework.Versions.X.NavierStokes.WindowHistoryPotential.Free

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistorySchurResidualEnergy
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeWholeH1Mixed (modes)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowHistorySchurTemporalControl (temporalResponse)
open NativeWindowHistorySchurBarePairing (pairing)
open NativeWindowHistoryPotentialControl (massBudget)
noncomputable section
variable {nu : Viscosity}

private theorem young (x y eta : ℝ) (positive : 0 < eta) :
    2*x*y ≤ eta*x^2+y^2/eta := by
  have cancel : eta*(y^2/eta)=y^2 := mul_div_cancel₀ _ positive.ne'
  apply (mul_le_mul_iff_left₀ positive).mp
  nlinarith only [sq_nonneg (eta*x-y),cancel]

private theorem pair_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nu : ℝ) (nu0 : 0 ≤ nu) (h l a : E) :
    |pairing nu h l a| ≤ 2*‖h‖*‖a‖+2*nu*‖l‖*‖a‖ := by
  have first : |2*inner ℝ h a| ≤ 2*‖h‖*‖a‖ := by
    rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm h a) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have last : |2*nu*inner ℝ l a| ≤ 2*nu*‖l‖*‖a‖ := by
    rw [abs_mul,abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nu0)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm l a)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) nu0)).trans_eq (by ring)
  exact (abs_add_le _ _).trans (add_le_add first last)

private theorem scaled_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nu epsilon : ℝ) (nu0 : 0 ≤ nu) (positive : 0 < epsilon) (h l a : E) :
    |pairing nu h l a| ≤ (epsilon/2)*‖l‖^2+‖h‖^2+(1+2*nu^2/epsilon)*‖a‖^2 := by
  have first := young ‖h‖ ‖a‖ 1 (by norm_num)
  have last := young ‖l‖ (nu*‖a‖) (epsilon/2) (by positivity)
  have same : (nu*‖a‖)^2/(epsilon/2)=(2*nu^2/epsilon)*‖a‖^2 := by ring
  have paired := pair_norm nu nu0 h l a
  nlinarith only [first,last,same,paired]

private theorem scaled_distribute (S z epsilon x b : ℝ) (same : S*z=epsilon/2) :
    S*(z*x+b)=(epsilon/2)*x+S*b := by
  rw [mul_add,← mul_assoc,same]

open NativeWindowHistorySchurMixedAction (controlledInput)

def controlledWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  let h:=finiteHistory seed time M
  pairing nu.coeff h (laplacianAction nu M h) (controlledInput seed M time)

theorem source_controlled_work (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ M ≥ low,∀ time ∈ Icc 0 horizon,
      |controlledWork seed M time| ≤ epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  let S:=1+2*nu.coeff^2/epsilon
  have S0 : 0 < S := by dsimp only [S]; positivity
  let z:=epsilon/(2*S)
  have z0 : 0 < z := by dsimp only [z]; positivity
  obtain ⟨low,B,B0,source⟩ := NativeWindowHistorySchurMixedAction.source_controlled_bound seed horizon nonnegative z z0
  refine ⟨low,massBudget seed+S*B,add_nonneg (NativeWindowHistoryPotentialControl.massBudget_nonnegative seed)
    (mul_nonneg S0.le B0),fun M above time inside => ?_⟩
  have paired := scaled_pair (E := H) nu.coeff epsilon nu.coeff_pos.le positive (finiteHistory seed time M)
    (laplacianAction nu M (finiteHistory seed time M)) (controlledInput seed M time)
  have bounded := mul_le_mul_of_nonneg_left (source M above time inside) S0.le
  have mass := NativeWindowHistoryPotentialControl.source_mass_bound seed M time inside.1
  have cancel : S*z=epsilon/2 := by dsimp only [z]; field_simp
  have distribute := scaled_distribute S z epsilon
    (‖laplacianAction nu M (finiteHistory seed time M)‖^2) B cancel
  change |controlledWork seed M time| ≤ (epsilon/2)*‖laplacianAction nu M (finiteHistory seed time M)‖^2+
    ‖finiteHistory seed time M‖^2+S*‖controlledInput seed M time‖^2 at paired
  nlinarith only [paired,bounded,mass,distribute]

/-- The original temporal response acting on itself, together with the entire original forcing. -/
def residualWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  let h:=finiteHistory seed time M
  pairing nu.coeff h (laplacianAction nu M h)
    (wAction seed M time (temporalResponse seed M time)+forcingHistory seed M time)

private theorem split_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (nu : ℝ) (h l a x w f : E) (same : a+nu • l=x+w) :
    pairing nu h l (a+nu • l+f)=pairing nu h l x+pairing nu h l (w+f) := by
  rw [same]
  simp only [NativeWindowHistorySchurBarePairing.pairing,inner_add_right]
  ring

theorem freeWork_split (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryPotentialFree.freeWork seed M time=controlledWork seed M time+residualWork seed M time := by
  exact split_pair (E := H) nu.coeff (finiteHistory seed time M) (laplacianAction nu M (finiteHistory seed time M))
    (action seed M time (finiteHistory seed time M)) (controlledInput seed M time)
    (wAction seed M time (temporalResponse seed M time)) (forcingHistory seed M time)
    (NativeWindowHistorySchurMixedAction.source_action seed M time)

theorem source_generator (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M ≥ low,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,
      (∀ k ∈ integerWaveFrequencyCube cutoff,k≠0 → k∈modes M) →
      NativeWindowMetricGraphGreen.sourceRate seed frame M (integerWaveFrequencyCube cutoff) radius time ≤
        -(nu.coeff^2/4)*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C+residualWork seed M time := by
  obtain ⟨one,C1,C10,original⟩ := NativeWindowHistoryPotentialFree.source_generator seed horizon nonnegative
  obtain ⟨two,C2,C20,controlled⟩ := source_controlled_work seed horizon nonnegative (nu.coeff^2/4) (by positivity [nu.coeff_pos])
  refine ⟨max one two,C1+C2,add_nonneg C10 C20,
    fun radius above cutoff covered M included frame frameInside time timeInside cover => ?_⟩
  have full := original radius ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered)
    M frame frameInside time timeInside cover
  have paid := controlled M ((le_max_right _ _).trans included) time timeInside
  have signed := le_abs_self (controlledWork seed M time)
  have same := freeWork_split seed M time
  linarith only [full,paid,signed,same]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem residualWork_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (time : ℝ) (time0 : 0 ≤ time) :
    residualWork seed M (step.2.clockAdvance+time)=residualWork step.1 M time := by
  have actions := NativeWindowHistorySchurAdvectorAction.actions_next seed M step generated time time0
  have w : wAction seed M (step.2.clockAdvance+time)=wAction step.1 M time := congrArg Prod.snd actions
  simp only [residualWork,w,NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0,
    NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistorySchurResidualEnergy
