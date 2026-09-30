import H0mework.Versions.X.NavierStokes.WindowHistoryPotential.Action
import H0mework.Versions.X.NavierStokes.WindowHistoryMetricGraph.Green

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryPotentialControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed NativeResolventAdjoint
open NativePhysicalFourier
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_inner)
open NativeWindowHistoryOseen (H action forcingHistory)
open NativeWindowTraceWholeHistory (metric metricAction finiteHistory)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowHistoryPotentialAction (fiber lifted rate)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem fiber_pair (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (x y : wholePhysical) :
    inner ℝ x (fiber seed frame M F R y)=pairing (modes M)
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) x)
      (NativeWindowMetricGraphPotential.potential (modes M) F (NativeWindowTraceCutTime.fieldJet seed F R 0 frame)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) y)) := by
  change inner ℝ x (includeCLM (modes M) (modes_closed M) _)=_
  rw [real_inner_comm,include_inner (modes M) (modes_zero M),pairing_symmetric]
  rfl

theorem fiber_symmetric (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (x y : wholePhysical) :
    inner ℝ (fiber seed frame M F R x) y=inner ℝ x (fiber seed frame M F R y) := by
  rw [real_inner_comm,fiber_pair,fiber_pair,NativeWindowMetricGraphPotential.potential_pairing,
    NativeWindowMetricGraphPotential.potential_pairing]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun f : C(Torus,ℝ) => inner ℝ (NativeWindowTraceCutTime.fieldJet seed F R 0 frame)
    (NativeWindowStressHeatSource.physical f)) (mul_comm _ _)

private theorem lift_symmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (same : ∀ x y,inner ℝ (P x) y=inner ℝ x (P y)) (x y : Lp E 2 averageMeasure) :
    inner ℝ (P.compLpL 2 averageMeasure x) y=inner ℝ x (P.compLpL 2 averageMeasure y) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [P.coeFn_compLpL x,P.coeFn_compLpL y] with lag first last
  rw [first,last,same]

theorem lifted_symmetric (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (x y : H) :
    inner ℝ (lifted seed frame M F R x) y=inner ℝ x (lifted seed frame M F R y) := by
  simpa only [lifted] using! lift_symmetric (E := wholePhysical) (fiber seed frame M F R)
    (fiber_symmetric seed frame M F R) x y

private theorem fiber_norm (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : wholePhysical) :
    ‖fiber seed frame M F R v‖=‖coefficients (modes M)
      (NativeWindowMetricGraphPotential.potential (modes M) F (NativeWindowTraceCutTime.fieldJet seed F R 0 frame)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) v))‖ :=
  NativePhysicalPairing.include_norm (modes M) (modes_zero M) (modes_closed M) _

theorem source_fiber_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ R≥low,∀ cutoff≥low,∀ M,∀ frame∈Icc 0 horizon,∀ v : wholePhysical,
      ‖fiber seed frame M (integerWaveFrequencyCube cutoff) R v‖≤
        epsilon*‖laplacianFiber nu M v‖+C*‖v‖ := by
  obtain ⟨low,B,B0,field⟩ := NativeWindowTraceCutTime.source_field_bound seed horizon nonnegative 0
  obtain ⟨C,C0,source⟩ := NativeWindowMetricGraphPotential.exists_potential_bound nu B B0 epsilon positive
  refine ⟨low,C,C0,fun R above cutoff covered M frame inside v => ?_⟩
  have original := source (modes M) (integerWaveFrequencyCube cutoff) (modes_zero M) (modes_closed M)
    (NativeWindowFiniteGramFourier.cube_closed cutoff) _ (field R above cutoff covered frame inside)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)
  have mass := mul_le_mul_of_nonneg_left (NativeWindowMetricGraphHistory.restricted_norm M v) C0
  rw [fiber_norm,NativeWindowMetricGraphHistory.laplacian_norm]
  linarith only [original,mass]

private theorem heat_bound (nu epsilon C p d m : ℝ) (nu0 : 0<nu) (epsilon0 : 0<epsilon) (d0 : 0≤d)
    (bound : p≤(epsilon/(4*nu))*d+C*m) :
    2*nu*p*d≤epsilon*d^2+(2*nu^2*C^2/epsilon)*m^2 := by
  have first := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (by positivity : 0≤2*nu)) d0
  have cancel : 2*nu*(epsilon/(4*nu))=epsilon/2 := by field_simp; ring
  have young := sq_nonneg (epsilon*d-2*nu*C*m)
  have denominator : epsilon*(2*nu^2*C^2/epsilon)=2*nu^2*C^2 := mul_div_cancel₀ _ epsilon0.ne'
  rw [mul_add,← mul_assoc,← mul_assoc,cancel] at first
  have paid := mul_le_mul_of_nonneg_left first epsilon0.le
  have scaled := congrArg (fun x : ℝ => x*m^2) denominator
  apply (mul_le_mul_iff_left₀ epsilon0).mp
  nlinarith only [paid,young,scaled]

private theorem norm_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Lp E 2 averageMeasure) : ‖v‖^2=∫lag,‖v lag‖^2 ∂averageMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem integrated_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P L : E →L[ℝ] E) (nu epsilon C : ℝ) (v : Lp E 2 averageMeasure)
    (point : ∀ x,|2*nu*inner ℝ (P x) (L x)|≤epsilon*‖L x‖^2+C*‖x‖^2) :
    |2*nu*inner ℝ (P.compLpL 2 averageMeasure v) (L.compLpL 2 averageMeasure v)|≤
      epsilon*‖L.compLpL 2 averageMeasure v‖^2+C*‖v‖^2 := by
  have first := (Lp.memLp (L.compLpL 2 averageMeasure v)).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have last := (Lp.memLp v).integrable_norm_pow (by norm_num : (2:ℕ)≠0)
  have paid := norm_integral_le_of_norm_le
    (f := fun lag => 2*nu*inner ℝ ((P.compLpL 2 averageMeasure v) lag) ((L.compLpL 2 averageMeasure v) lag))
    ((first.const_mul epsilon).add (last.const_mul C)) (by
    filter_upwards [P.coeFn_compLpL v,L.coeFn_compLpL v] with lag p l
    simpa only [p,l,Pi.add_apply,Real.norm_eq_abs] using point (v lag))
  have read := integral_add (first.const_mul epsilon) (last.const_mul C)
  simp only [Pi.add_apply] at read paid
  rw [read] at paid
  simpa only [integral_const_mul,← norm_square,← L2.inner_def,Real.norm_eq_abs] using paid

def heatWork (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (v : H) : ℝ :=
  2*nu.coeff*inner ℝ (lifted seed frame M F R v) (laplacianAction nu M v)

theorem source_heat_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ R≥low,∀ cutoff≥low,∀ M,∀ frame∈Icc 0 horizon,∀ v : H,
      |heatWork seed frame M (integerWaveFrequencyCube cutoff) R v|≤epsilon*‖laplacianAction nu M v‖^2+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩ := source_fiber_bound seed horizon nonnegative (epsilon/(4*nu.coeff)) (by positivity [nu.coeff_pos])
  refine ⟨low,2*nu.coeff^2*C^2/epsilon,by positivity,fun R above cutoff covered M frame inside v => ?_⟩
  have point (x : wholePhysical) : |2*nu.coeff*inner ℝ (fiber seed frame M (integerWaveFrequencyCube cutoff) R x)
      (laplacianFiber nu M x)|≤epsilon*‖laplacianFiber nu M x‖^2+(2*nu.coeff^2*C^2/epsilon)*‖x‖^2 := by
    rw [abs_mul,abs_of_nonneg (by positivity [nu.coeff_pos] : 0≤2*nu.coeff)]
    exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity [nu.coeff_pos] : 0≤2*nu.coeff)).trans
      (by simpa only [mul_assoc] using (heat_bound nu.coeff epsilon C _ _ _ nu.coeff_pos positive
        (norm_nonneg _) (source R above cutoff covered M frame inside x)))
  simpa only [heatWork,lifted,laplacianAction] using! integrated_bound (E := wholePhysical)
    (fiber seed frame M (integerWaveFrequencyCube cutoff) R) (laplacianFiber nu M) nu.coeff epsilon _ v point

def nonlinearWork (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) : ℝ :=
  2*inner ℝ (lifted seed frame M F R (finiteHistory seed time M))
    (action seed M time (finiteHistory seed time M)+nu.coeff • laplacianAction nu M (finiteHistory seed time M)+forcingHistory seed M time)

private theorem nonlinear_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (symmetric : ∀ x y,inner ℝ (P x) y=inner ℝ x (P y)) (h a l f : E) (nu : ℝ) :
    2*inner ℝ (P h) (a+nu • l+f)=inner ℝ h (P (a+f))+inner ℝ (a+f) (P h)+2*nu*inner ℝ (P h) l := by
  have same := symmetric h (a+f)
  have swap := real_inner_comm (a+f) (P h)
  rw [inner_add_right (𝕜 := ℝ) (P h) a f] at same
  rw [inner_add_right (𝕜 := ℝ) (P h) a f] at swap
  rw [inner_add_right,inner_add_right,real_inner_smul_right]
  linarith only [same,swap]

theorem nonlinear_split (seed : GeneratedWholeRestartCurrent nu) (frame : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (R : ℕ) (time : ℝ) :
    nonlinearWork seed frame M F R time=rate seed frame M F R time+heatWork seed frame M F R (finiteHistory seed time M) := by
  simpa only [nonlinearWork,rate,heatWork] using! nonlinear_algebra (E := H) (lifted seed frame M F R)
    (lifted_symmetric seed frame M F R) (finiteHistory seed time M) (action seed M time (finiteHistory seed time M))
      (laplacianAction nu M (finiteHistory seed time M)) (forcingHistory seed M time) nu.coeff

def massBudget (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  NativeWindowFiniteStressUniform.kernelBound 0*(NativeUnifiedCompleteSource.budget seed)^2

theorem massBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0≤ massBudget seed :=
  mul_nonneg (NativeWindowFiniteStressUniform.kernelBound_positive 0).le (sq_nonneg _)

theorem source_mass_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (time0 : 0≤time) :
    ‖finiteHistory seed time M‖^2≤ massBudget seed := by
  have read := NativeWindowHistoryForcingWork.mass_original seed M time
  have paid := NativeWindowHistoryForcingWork.mass_bound seed M 0 time time0
  have actual : NativeWindowHistoryForcingWork.massJet seed M 0 time≤ massBudget seed :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,massBudget] using! paid)
  exact read.trans_le actual

theorem source_nonlinear_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ R≥low,∀ cutoff≥low,∀ M,
      ∀ frame∈Icc 0 horizon,∀ time∈Icc 0 horizon,
      (∀ k∈integerWaveFrequencyCube cutoff,k≠0 →k∈modes M) →
      |nonlinearWork seed frame M (integerWaveFrequencyCube cutoff) R time|≤
        epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+C := by
  obtain ⟨first,C1,C10,source⟩ := NativeWindowHistoryPotentialAction.source_rate_bound seed horizon nonnegative
  obtain ⟨last,C2,C20,heat⟩ := source_heat_bound seed horizon nonnegative epsilon positive
  refine ⟨max first last,C1+C2*massBudget seed,by positivity [massBudget_nonnegative seed],
    fun R above cutoff covered M frame frameInside time timeInside cover => ?_⟩
  have one := source R ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered) M frame frameInside time timeInside cover
  have two := heat R ((le_max_right _ _).trans above) cutoff ((le_max_right _ _).trans covered) M frame frameInside (finiteHistory seed time M)
  have mass := mul_le_mul_of_nonneg_left (source_mass_bound seed M time timeInside.1) C20
  have summed : |rate seed frame M (integerWaveFrequencyCube cutoff) R time+
      heatWork seed frame M (integerWaveFrequencyCube cutoff) R (finiteHistory seed time M)|≤
      |rate seed frame M (integerWaveFrequencyCube cutoff) R time|+
        |heatWork seed frame M (integerWaveFrequencyCube cutoff) R (finiteHistory seed time M)| := abs_add_le _ _
  have bound : |rate seed frame M (integerWaveFrequencyCube cutoff) R time+
      heatWork seed frame M (integerWaveFrequencyCube cutoff) R (finiteHistory seed time M)|≤
      epsilon*‖laplacianAction nu M (finiteHistory seed time M)‖^2+(C1+C2*massBudget seed) := by
    linarith only [one,two,mass,summed]
  exact (congrArg abs (nonlinear_split seed frame M _ R time)).trans_le bound

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem nonlinear_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (frame time : ℝ) (frame0 : 0≤frame) (time0 : 0≤time) (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) :
    nonlinearWork seed (step.2.clockAdvance+frame) M F R (step.2.clockAdvance+time)=
      nonlinearWork step.1 frame M F R time := by
  have operators:=NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at operators
  simp only [nonlinearWork,operators.1,NativeWindowHistoryPotentialAction.lifted_next seed step generated frame frame0,
    NativeWindowTraceWholeHistory.finiteHistory_next seed step generated time time0,
    NativeWindowHistoryOseen.forcingHistory_next seed M step generated time time0]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryPotentialControl
