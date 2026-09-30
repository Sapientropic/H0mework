import H0mework.Versions.X.NavierStokes.WindowSchurSchur.FeedbackSource
import H0mework.Versions.X.NavierStokes.WindowSchurMean.JetEnergy

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryCreationMean
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean embed)
local notation "Q" => NativeWindowHistoryMeanProjection.residual
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryAdjointSpatialFeedback (read lift transportCap transportCap_nonnegative historyBudget history_bound)
open NativeWindowHistoryAdjointSpatialHalf (moment)
open NativeWindowHistoryAdjointDefect (advection)
open NativeWindowHistoryAnnihilationControl (laplacianAction laplacianFiber)
open NativeWindowTraceWholeHistory (finiteHistory)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeUnheatedSexticLatticePower (radical)
open NativeWindowHistoryMeanPhysicalJet (physicalJet)
noncomputable section
variable {nu : Viscosity}

private theorem projected_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] E) (n a l : E) (c : ℝ) (same : n=a+c • l) (zero : P l=0) : P n=P a := by
  rw [same,map_add,map_smul,zero,smul_zero,add_zero]

private theorem square_product (a x y z : ℝ) (a0 : 0≤a) (x0 : 0≤x)
    (bound : x≤Real.sqrt a*y*z) : x^2≤(a*z^2)*y^2 := by
  have paid:=pow_le_pow_left₀ x0 bound 2
  rw [mul_pow,mul_pow,Real.sq_sqrt a0] at paid
  exact paid.trans_eq (by ring)

private theorem lp_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Lp E 2 averageMeasure) : ‖v‖^2=∫lag,‖v lag‖^2 ∂averageMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem creation_advection (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    creation seed M time v=Q (advection seed M time (embed v)) := by
  have heat := (congrArg Q (NativeWindowHistoryMeanProjection.comp_embed (laplacianFiber nu M) v)).trans
    (NativeWindowHistorySchurCompletion.residual_embed (laplacianFiber nu M v))
  exact (projected_add (E := H) Q _ _ _ nu.coeff
    (NativeWindowHistoryAdjointDefect.advection_original seed M time (embed v)) heat).symm

theorem constant_transport (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : wholePhysical) :
    ‖advection seed M time (embed v)‖^2≤transportCap*
      ‖lift M (fun k => radical k^2) (finiteHistory seed time M)‖^2*‖read M (fun k => radical k^3) v‖^2 := by
  let h := lift M (fun k => radical k^2) (finiteHistory seed time M)
  let r := read M (fun k => radical k^3) v
  have point : ∀ᵐ lag ∂averageMeasure,‖advection seed M time (embed v) lag‖^2≤
      (transportCap*‖r‖^2)*‖h lag‖^2 := by
    filter_upwards [NativeWindowHistoryAdjointSpatialFeedback.transport_norm_point seed M time (embed v),
      (read M (fun k => radical k^3)).coeFn_compLpL (embed v),
      NativeWindowTraceWholeHistory.constant_ae v] with lag bound mapped constant
    have original : lift M (fun k => radical k^3) (embed v) lag=r := by
      change lift M (fun k => radical k^3) (embed v) lag=read M (fun k => radical k^3) v
      exact mapped.trans (congrArg (read M (fun k => radical k^3)) constant)
    rw [original] at bound
    exact square_product transportCap _ _ _ transportCap_nonnegative (norm_nonneg _) bound
  have integrable : Integrable (fun lag => ‖h lag‖^2) averageMeasure :=
    (Lp.memLp h).integrable_norm_pow (by decide : (2:ℕ)≠0)
  rw [NativeWindowTraceWholeHistory.norm_square]
  apply (integral_mono_ae ((Lp.memLp _).integrable_norm_pow (by decide : (2:ℕ)≠0))
    (integrable.const_mul _) point).trans_eq
  rw [integral_const_mul,← lp_square]
  ring

theorem creation_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) (v : wholePhysical) :
    ‖creation seed M time v‖^2≤transportCap*historyBudget seed horizon*‖read M (fun k => radical k^3) v‖^2 := by
  rw [creation_advection]
  apply (NativeWindowHistorySchurCenteredGraph.residual_norm_square _).trans
  exact (constant_transport seed M time v).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (history_bound seed horizon M time inside)
      transportCap_nonnegative) (sq_nonneg _))

theorem mean_moment (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    moment (modes M) 3 (physicalJet seed M order time)≤NativeWindowSobolevVelocity.budget seed order horizon := by
  have valid : -1<time := by linarith [inside.1]
  have row (k : IntegerWavevector) (included : k∈modes M) :
      radical k^(2*3)*(∑ i : Coordinate,‖(physicalJet seed M order time).1 k i‖^2)=
        NativeWindowSobolevVelocity.wholeDensity seed order time k := by
    rw [NativeWindowHistoryMeanJetEnergy.row_inside seed M order time k included]
    have exponent : radical k^(2*3)=(1+integerWaveNormSq k)*Real.sqrt (1+integerWaveNormSq k) := by
      rw [show radical k^(2*3)=radical k^4*radical k^2 by ring,
        NativeUnheatedSexticLatticePower.radical_fourth,NativeUnheatedSexticLatticePower.radical_square]
      rfl
    simp only [exponent,NativeWindowSobolevVelocity.wholeDensity,complexCoordinateAmplitudeSq,Complex.normSq_eq_norm_sq]
  have positive (k : IntegerWavevector) : 0≤NativeWindowSobolevVelocity.wholeDensity seed order time k := by
    unfold NativeWindowSobolevVelocity.wholeDensity complexCoordinateAmplitudeSq
    simp only [Complex.normSq_eq_norm_sq]
    positivity [integerWaveNormSq_nonneg k]
  rw [NativeWindowHistoryAdjointSpatialHalf.moment_original]
  rw [Finset.sum_congr rfl row]
  exact ((NativeWindowSobolevVelocity.whole_summable seed order time valid).sum_le_tsum
    (s := modes M) (fun k _ => positive k)).trans
      (NativeWindowSobolevVelocity.whole_bound_on_interval seed order time horizon valid inside.2)

def budget (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) : ℝ :=
  transportCap*historyBudget seed horizon*NativeWindowSobolevVelocity.budget seed order horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) :
    0≤budget seed order horizon := by
  unfold budget NativeWindowSobolevVelocity.budget
  positivity [transportCap_nonnegative,NativeWindowHistoryAdjointSpatialFeedback.historyBudget_nonnegative seed horizon]

theorem source_jet (seed : GeneratedWholeRestartCurrent nu) (order : ℕ) (horizon : ℝ) (M : ℕ)
    (time : ℝ) (inside : time∈Icc 0 horizon) :
    ‖creation seed M time (includeCLM (modes M) (modes_closed M) (physicalJet seed M order time))‖^2≤
      budget seed order horizon := by
  have paid:=creation_bound seed horizon M time inside
    (includeCLM (modes M) (modes_closed M) (physicalJet seed M order time))
  rw [NativeWindowHistoryAdjointSpatialFeedback.read_moment,restrict_include] at paid
  exact paid.trans (mul_le_mul_of_nonneg_left (mean_moment seed order horizon M time inside)
    (mul_nonneg transportCap_nonnegative (NativeWindowHistoryAdjointSpatialFeedback.historyBudget_nonnegative seed horizon)))

theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M time,time∈Icc 0 horizon →
      ‖creation seed M time (mean (finiteHistory seed time M))‖^2≤C := by
  refine ⟨budget seed 0 horizon,budget_nonnegative seed 0 horizon,fun M time inside => ?_⟩
  have original : includeCLM (modes M) (modes_closed M) (physicalJet seed M 0 time)=mean (finiteHistory seed time M) := by
    rw [NativeWindowHistoryMeanPhysicalJet.physicalJet_zero,NativeWindowHistoryMeanPhysicalJet.include_mean]
  rw [← original]
  exact source_jet seed 0 horizon M time inside

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryCreationMean
