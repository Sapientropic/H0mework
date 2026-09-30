import H0mework.Versions.X.NavierStokes.WindowSchurSchur.FeedbackHalf
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.AdjointHeatDefect
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.CenteredGraph

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointSpatialFeedback
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowHistoryAdjointSpatialHalf (moment outputSquare energyCap)
open NativeWindowHistorySchurCompletion (complete)
open NativeWindowHistorySchurAction (response feedback effective)
noncomputable section
variable {nu : Viscosity}
local notation "Q" => NativeWindowHistoryMeanProjection.residual

abbrev Samples (M : ℕ) := EuclideanSpace ℂ ((modes M) × Coordinate)

def readLinear (M : ℕ) (a : IntegerWavevector → ℝ) : physicalSpace (modes M) →ₗ[ℝ] Samples M where
  toFun v := WithLp.toLp 2 (fun ki => a ki.1.1 • v.1 ki.1.1 ki.2)
  map_add' u v := by ext ki; simp only [Submodule.coe_add,lp.coeFn_add,Pi.add_apply,PiLp.add_apply,smul_add]
  map_smul' c v := by ext ki; simp only [Submodule.coe_smul,lp.coeFn_smul,Pi.smul_apply,PiLp.smul_apply,smul_smul,RingHom.id_apply,mul_comm]

def read (M : ℕ) (a : IntegerWavevector → ℝ) : wholePhysical →L[ℝ] Samples M :=
  (LinearMap.toContinuousLinearMap (readLinear M a)).comp (restrictCLM (modes M) (modes_zero M) (modes_closed M))

def lift (M : ℕ) (a : IntegerWavevector → ℝ) : H →L[ℝ] Lp (Samples M) 2 averageMeasure :=
  (read M a).compLpL 2 averageMeasure

def sample (M : ℕ) (v : H) (lag : ℝ) : physicalSpace (modes M) :=
  restrictCLM (modes M) (modes_zero M) (modes_closed M) (v lag)

theorem read_square (M : ℕ) (a : IntegerWavevector → ℝ) (v : wholePhysical) :
    ‖read M a v‖^2=∑ k∈modes M,a k^2*(∑i : Coordinate,‖(restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1 k i‖^2) := by
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_prod_type]
  change (∑k : modes M,∑i : Coordinate,‖a k.1 • (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1 k.1 i‖^2)=_
  simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,← Finset.mul_sum]
  exact Finset.sum_coe_sort (modes M) (fun k => a k^2*(∑i : Coordinate,‖(restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1 k i‖^2))

theorem read_moment (M n : ℕ) (v : wholePhysical) :
    ‖read M (fun k => NativeUnheatedSexticLatticePower.radical k^n) v‖^2=
      moment (modes M) n (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) := by
  rw [read_square,NativeWindowHistoryAdjointSpatialHalf.moment_original]
  simp only [← pow_mul,Nat.mul_comm n 2]

theorem read_output (M : ℕ) (strong : Bool) (v : wholePhysical) :
    ‖read M (NativeWindowHistoryAdjointSpatialHalf.weight strong) v‖^2=
      outputSquare strong (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) v) := read_square M _ v

private theorem norm_square {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Lp E 2 averageMeasure) : ‖v‖^2=∫lag,‖v lag‖^2 ∂averageMeasure := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem lift_square (M : ℕ) (a : IntegerWavevector → ℝ) (v : H) :
    ‖lift M a v‖^2=∫lag,‖read M a (v lag)‖^2 ∂averageMeasure := by
  rw [norm_square]
  exact integral_congr_ae (((read M a).coeFn_compLpL v).fun_comp (fun x => ‖x‖^2))

theorem read_integrable (M : ℕ) (a : IntegerWavevector → ℝ) (v : H) :
    Integrable (fun lag => ‖read M a (v lag)‖^2) averageMeasure :=
  (((Lp.memLp v).continuousLinearMap_comp (read M a)).integrable_norm_pow (by decide : (2 : ℕ)≠0))

private theorem integral_square_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : Lp E 2 averageMeasure) : ‖∫lag,f lag ∂averageMeasure‖^2 ≤ ‖f‖^2 := by
  have triangle := pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm (μ := averageMeasure) f) 2
  have cauchy := NativeWindowHistoryAnnihilationControl.cauchy_square (fun lag => ‖f lag‖) (fun _ => 1)
    (Lp.memLp f).norm (memLp_const 1)
  simp only [mul_one,one_pow,integral_const,probReal_univ,one_smul,mul_one] at cauchy
  exact triangle.trans (cauchy.trans_eq (norm_square f).symm)

private theorem map_embed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : wholePhysical →L[ℝ] E) (v : wholePhysical) :
    A.compLpL 2 averageMeasure (embed v)=Lp.const 2 averageMeasure (A v) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (embed v),NativeWindowTraceWholeHistory.constant_ae v,
    Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := averageMeasure) (A v)] with lag first last target
  exact first.trans ((congrArg A last).trans target.symm)

private theorem mapped_mean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : wholePhysical →L[ℝ] E) (v : H) : A (mean v)=∫lag,A.compLpL 2 averageMeasure v lag ∂averageMeasure := by
  rw [NativeWindowHistoryMeanProjection.mean_original]
  exact (A.integral_comp_comm ((Lp.memLp v).integrable (by norm_num))).symm.trans
    (integral_congr_ae (A.coeFn_compLpL v)).symm

private theorem twice_square (x : ℝ) : (x+x)^2=4*x^2 := by ring

private theorem difference_bound {E : Type*} [SeminormedAddCommGroup E] (u v : E) (bound : ‖v‖ ≤ ‖u‖) :
    ‖u-v‖^2 ≤ 4*‖u‖^2 :=
  (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le u v).trans (add_le_add le_rfl bound)) 2).trans_eq (twice_square ‖u‖)

theorem lift_residual_bound (M : ℕ) (a : IntegerWavevector → ℝ) (v : H) :
    ‖lift M a (Q v)‖^2 ≤ 4*‖lift M a v‖^2 := by
  have meanSquare : ‖read M a (mean v)‖^2 ≤ ‖lift M a v‖^2 :=
    (congrArg (fun x : Samples M => ‖x‖^2) (mapped_mean (read M a) v)).trans_le (integral_square_le (lift M a v))
  have meanNorm := (sq_le_sq₀ (norm_nonneg (read M a (mean v))) (norm_nonneg (lift M a v))).mp meanSquare
  have identity : lift M a (Q v)=lift M a v-Lp.const 2 averageMeasure (read M a (mean v)) := by
    have source := ((lift M a).map_sub v (embed (mean v))).trans
      (congrArg (fun t : Lp (Samples M) 2 averageMeasure => lift M a v-t) (map_embed (read M a) (mean v)))
    simpa only [NativeWindowHistoryMeanProjection.residual,NativeWindowHistoryMeanProjection.projection,
      sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply] using! source
  have constNorm : ‖Lp.const 2 averageMeasure (read M a (mean v))‖ ≤ ‖read M a (mean v)‖ := by
    simpa only [probReal_univ,Real.one_rpow,mul_one] using!
      Lp.norm_const_le (2 : ℝ≥0∞) averageMeasure (read M a (mean v))
  exact (congrArg (fun f : Lp (Samples M) 2 averageMeasure => ‖f‖^2) identity).trans_le
    (difference_bound _ _ (constNorm.trans meanNorm))

def completed (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) : H :=
  complete seed M time (includeCLM (modes M) (modes_closed M) v)

def centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) : H :=
  response seed M time (includeCLM (modes M) (modes_closed M) v)

theorem completed_centered (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    Q (completed seed M time v)=centered seed M time v :=
  NativeWindowHistorySchurCompletion.complete_residual seed M time _

theorem sample_solution (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    ∀ᵐ lag ∂averageMeasure,sample M (completed seed M time v) lag=
      NativeWindowHistoryFrozenInverse.physical seed M (time-lag) (NativeWindowHistoryEffectiveInverse.generator seed M time v) := by
  let x := completed seed M time v
  let f := includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v)
  have equation : x-NativeWindowHistoryOseen.action seed M time x=embed f :=
    NativeWindowHistorySchurCompletion.complete_equation seed M time _
  filter_upwards [Lp.coeFn_sub x (NativeWindowHistoryOseen.action seed M time x),
    NativeWindowHistoryOseen.action_ae seed M time x,NativeWindowTraceWholeHistory.constant_ae f] with lag subtract acted fixed
  have source := congrArg (fun h : H => h lag) equation
  rw [subtract,Pi.sub_apply,acted] at source
  have point := source.trans fixed
  have finite := congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M)) point
  simp only [map_sub,NativeWindowHistoryOseen.forwardFiber,NativeWindowHistoryOseen.lift,
    ContinuousLinearMap.comp_apply,restrict_include] at finite
  apply NativeWindowHistoryFrozenInverse.physical_unique seed M (time-lag) (sample M x lag)
  simpa only [f,sample,map_sub,restrict_include,NativeWindowHistoryEffectiveInverse.generator_original] using! finite

theorem sample_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ∀ᵐ lag ∂averageMeasure,moment (modes M) 2 (sample M (completed seed M time v) lag) ≤
      energyCap nu*NativeWindowHistorySchurForm.cap seed horizon^2*NativeWindowHistoryHeatDual.energy nu M v := by
  filter_upwards [sample_solution seed M time v] with lag actual
  rw [actual]
  exact (NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M _).trans
    ((mul_le_mul_of_nonneg_left ((NativeWindowHistoryHeatDual.source_bound seed M (time-lag) _).trans
      (NativeWindowHistorySchurWeightedInverse.source_generator_bound seed horizon M time inside v))
      (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le).trans_eq (by ring))

open NativeWindowHistoryAnnihilationControl (laplacianAction laplacianFiber)
open NativeWindowHistoryAdjointDefect (advection)

private theorem centered_algebra {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P A L N : E →L[ℝ] E) (a : ℝ) (x z c : E) (equation : x-A x=c) (center : P x=z)
    (zero : P c=0) (nonlinear : N x=A x+a • L x) (commute : P (L x)=L (P x)) :
    z+a • L z=P (N x) := by
  have source := congrArg P equation
  rw [map_sub,center,zero] at source
  have acted := (sub_eq_zero.mp source).symm
  rw [nonlinear,map_add,map_smul,commute,center,acted]

theorem centered_equation (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    centered seed M time v+nu.coeff • laplacianAction nu M (centered seed M time v)=
      Q (advection seed M time (completed seed M time v)) := by
  simpa only [] using! centered_algebra (E := H) Q (NativeWindowHistoryOseen.action seed M time)
    (laplacianAction nu M) (advection seed M time) nu.coeff (completed seed M time v) (centered seed M time v)
    (embed (includeCLM (modes M) (modes_closed M) v-effective seed M time (includeCLM (modes M) (modes_closed M) v)))
    (NativeWindowHistorySchurCompletion.complete_equation seed M time _) (completed_centered seed M time v)
    (NativeWindowHistorySchurCompletion.residual_embed _)
    (NativeWindowHistoryAdjointDefect.advection_original seed M time (completed seed M time v))
    (NativeWindowHistorySchurCenteredGraph.laplacian_center nu M (completed seed M time v))

theorem heat_gain (M : ℕ) (z f : H) (equation : z+nu.coeff • laplacianAction nu M z=f) :
    ‖lift M (fun k => NativeUnheatedSexticLatticePower.radical k^3) z‖^2 ≤
      energyCap nu^2*‖lift M (NativeWindowHistoryAdjointSpatialHalf.weight false) f‖^2 := by
  have point : ∀ᵐ lag ∂averageMeasure,
      sample M z lag+nu.coeff • NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu (sample M z lag)=
        sample M f lag := by
    filter_upwards [Lp.coeFn_add z (nu.coeff • laplacianAction nu M z),Lp.coeFn_smul nu.coeff (laplacianAction nu M z),
      (laplacianFiber nu M).coeFn_compLpL z] with lag added scaled lap
    have source := congrArg (fun h : H => h lag) equation
    change laplacianAction nu M z lag=laplacianFiber nu M (z lag) at lap
    rw [added,Pi.add_apply,scaled,Pi.smul_apply,lap] at source
    have finite := congrArg (restrictCLM (modes M) (modes_zero M) (modes_closed M)) source
    simpa only [map_add,map_smul,laplacianFiber,NativeWindowHistoryOseen.lift,ContinuousLinearMap.comp_apply,restrict_include,sample] using! finite
  rw [lift_square,lift_square,← integral_const_mul]
  apply integral_mono_ae (read_integrable M _ z) ((read_integrable M _ f).const_mul _)
  filter_upwards [point] with lag actual
  rw [read_moment,read_output]
  exact NativeWindowHistoryAdjointSpatialHalf.heat_gain nu (modes M) (modes_zero M) (modes_closed M) _ _ actual

open NativeUnheatedSexticLatticePower (radical)
open NativeWindowTraceWholeHistory (finiteHistory gradient)
open NativeWindowHistorySchurTemporalControl (massBudget gradientBudget)
open NativeWindowHistorySchurAdvectorFiber (family)

theorem whole_moment_energy (M : ℕ) (v : H) :
    ‖lift M (fun k => radical k^2) v‖^2 ≤ energyCap nu*(‖v‖^2+nu.coeff*gradient M v) := by
  have integrable := ((Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ)≠0)).add
    ((NativeWindowTraceWholeHistory.gradient_integrable nu M v).const_mul nu.coeff)
  have bound : (∫lag,‖read M (fun k => radical k^2) (v lag)‖^2 ∂averageMeasure) ≤
      ∫lag,energyCap nu*(‖v lag‖^2+nu.coeff*curlPair (modes M) (sample M v lag).1 (sample M v lag).1) ∂averageMeasure := by
    apply integral_mono_ae (read_integrable M _ v) (integrable.const_mul _)
    filter_upwards with lag
    rw [read_moment]
    have projected := pow_le_pow_left₀ (norm_nonneg _) (restrict_energy (modes M) (modes_zero M) (modes_closed M) (v lag)) 2
    exact (NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M (sample M v lag)).trans
      (mul_le_mul_of_nonneg_left (show NativeWindowHistoryHeatDual.energy nu M (sample M v lag) ≤
        ‖v lag‖^2+nu.coeff*curlPair (modes M) (sample M v lag).1 (sample M v lag).1 by
          simpa only [NativeWindowHistoryHeatDual.energy,sample] using! add_le_add projected (le_refl (nu.coeff*curlPair (modes M) (sample M v lag).1 (sample M v lag).1)))
        (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le)
  rw [lift_square]
  apply bound.trans_eq
  simp only [sample]
  rw [integral_const_mul,integral_add ((Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ)≠0))
    ((NativeWindowTraceWholeHistory.gradient_integrable nu M v).const_mul nu.coeff),integral_const_mul,← NativeWindowTraceWholeHistory.norm_square]
  rfl

def historyBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  energyCap nu*(massBudget seed+nu.coeff*gradientBudget seed horizon)

theorem historyBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ historyBudget seed horizon := by
  unfold historyBudget gradientBudget
  positivity [NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu,
    NativeWindowHistorySchurTemporalControl.massBudget_nonnegative seed,nu.coeff_pos]

theorem history_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) : ‖lift M (fun k => radical k^2) (finiteHistory seed time M)‖^2 ≤ historyBudget seed horizon :=
  (whole_moment_energy (nu := nu) M (finiteHistory seed time M)).trans
    (mul_le_mul_of_nonneg_left (add_le_add (NativeWindowHistorySchurTemporalControl.source_mass seed M time inside.1)
      (mul_le_mul_of_nonneg_left (NativeWindowHistorySchurTemporalControl.source_gradient seed horizon M time inside) nu.coeff_pos.le))
      (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le)

theorem advection_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    advection seed M time v=ᵐ[averageMeasure] fun lag => family nu M (finiteHistory seed time M lag) (v lag) := by
  filter_upwards [Lp.coeFn_add (NativeWindowHistorySchurAdvectorAction.xAction seed M time v)
    (NativeWindowHistorySchurAdvectorAction.wAction seed M time v),
    NativeWindowHistorySchurAdvectorAction.xAction_ae seed M time v,NativeWindowHistorySchurAdvectorAction.wAction_ae seed M time v,
    Lp.coeFn_add (NativeWindowHistorySchurCompletion.completion seed M time)
      (NativeWindowHistorySchurTemporalControl.temporalResponse seed M time)] with lag added first last source
  have split := (congrArg (fun h : H => h lag) (NativeWindowHistorySchurCompletion.source_split seed M time)).trans source
  have point := added.trans (congrArg₂ (fun a b : wholePhysical => a+b) first last)
  have actual := congrArg (fun a : wholePhysical => family nu M a (v lag)) split
  exact point.trans (((congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A (v lag))
    ((family nu M).map_add _ _)).symm).trans actual.symm)

def transportCap : ℝ := 3*(2*Real.pi)^2*NativeWindowHistoryAdjointSpatialHalf.cap^2

theorem transportCap_nonnegative : 0 ≤ transportCap := by unfold transportCap; positivity

theorem transport_point (strong : Bool) (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    ∀ᵐ lag ∂averageMeasure,‖read M (NativeWindowHistoryAdjointSpatialHalf.weight strong) (advection seed M time v lag)‖^2 ≤
      transportCap*‖read M (fun k => radical k^2) (finiteHistory seed time M lag)‖^2*
        ‖read M (fun k => radical k^(NativeWindowHistoryAdjointSpatialHalf.inputOrder strong)) (v lag)‖^2 := by
  filter_upwards [advection_ae seed M time v] with lag actual
  rw [actual,NativeWindowHistorySchurAdvectorFiber.family_original,read_output,restrict_include,read_moment,read_moment]
  exact NativeWindowHistoryAdjointSpatialHalf.transport_bound strong (modes M) (modes_zero M) (modes_closed M) nu _ _

theorem source_transport_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ‖lift M (NativeWindowHistoryAdjointSpatialHalf.weight false) (advection seed M time (completed seed M time v))‖^2 ≤
      transportCap*(energyCap nu*NativeWindowHistorySchurForm.cap seed horizon^2*NativeWindowHistoryHeatDual.energy nu M v)*historyBudget seed horizon := by
  let B := energyCap nu*NativeWindowHistorySchurForm.cap seed horizon^2*NativeWindowHistoryHeatDual.energy nu M v
  have B0 : 0 ≤ B := by dsimp only [B]; positivity [NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu,NativeWindowHistoryHeatDual.energy_nonnegative nu M v]
  have bound : (∫lag,‖read M (NativeWindowHistoryAdjointSpatialHalf.weight false)
      (advection seed M time (completed seed M time v) lag)‖^2 ∂averageMeasure) ≤
      ∫lag,(transportCap*B)*‖read M (fun k => radical k^2) (finiteHistory seed time M lag)‖^2 ∂averageMeasure := by
    apply integral_mono_ae (read_integrable M _ _) ((read_integrable M _ _).const_mul _)
    filter_upwards [transport_point false seed M time (completed seed M time v),sample_bound seed horizon M time inside v] with lag product uniform
    simp only [NativeWindowHistoryAdjointSpatialHalf.inputOrder,Bool.false_eq_true,if_false] at product
    have uniform' : ‖read M (fun k => radical k^2) (completed seed M time v lag)‖^2 ≤ B :=
      (read_moment M 2 _).trans_le uniform
    exact product.trans ((mul_le_mul_of_nonneg_left uniform'
      (mul_nonneg transportCap_nonnegative (sq_nonneg _))).trans_eq (by ring))
  rw [lift_square]
  apply bound.trans
  rw [integral_const_mul,← lift_square]
  exact mul_le_mul_of_nonneg_left (history_bound seed horizon M time inside) (mul_nonneg transportCap_nonnegative B0)

def centeredBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  energyCap nu^2*4*(transportCap*(energyCap nu*NativeWindowHistorySchurForm.cap seed horizon^2)*historyBudget seed horizon)

theorem centeredBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ centeredBudget seed horizon := by
  unfold centeredBudget
  positivity [transportCap_nonnegative,NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu,historyBudget_nonnegative seed horizon]

theorem source_centered_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ‖lift M (fun k => radical k^3) (centered seed M time v)‖^2 ≤ centeredBudget seed horizon*NativeWindowHistoryHeatDual.energy nu M v := by
  have heat := heat_gain M (centered seed M time v) _ (centered_equation seed M time v)
  have centering := lift_residual_bound M (NativeWindowHistoryAdjointSpatialHalf.weight false)
    (advection seed M time (completed seed M time v))
  have paid := source_transport_bound seed horizon M time inside v
  exact (heat.trans (mul_le_mul_of_nonneg_left centering (sq_nonneg _))).trans
    ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left paid (by norm_num : (0 : ℝ)≤4)) (sq_nonneg (energyCap nu))).trans_eq
      (by unfold centeredBudget; ring))

private theorem mapped_zero_sum {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F) (u v : E) (a : ℝ) (zero : A v=0) :
    A (u+a • v)=A u := by rw [map_add,map_smul,zero,smul_zero,add_zero]

theorem feedback_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : physicalSpace (modes M)) :
    feedback seed M time (includeCLM (modes M) (modes_closed M) v)=mean (advection seed M time (centered seed M time v)) := by
  let z := centered seed M time v
  have kept : Q z=z := NativeWindowHistorySchurAction.response_centered seed M time _
  have zero : mean z=0 := NativeWindowHistorySchurCompletion.mean_response seed M time _
  have lap : mean (laplacianAction nu M z)=0 :=
    (NativeWindowHistoryMeanProjection.mean_comp (laplacianFiber nu M) z).trans
      ((congrArg (laplacianFiber nu M) zero).trans (map_zero _))
  have nonlinear := congrArg mean (NativeWindowHistoryAdjointDefect.advection_original seed M time z)
  have last := nonlinear.trans (mapped_zero_sum mean (NativeWindowHistoryOseen.action seed M time z)
    (laplacianAction nu M z) nu.coeff lap)
  have result := (congrArg (fun z : H => mean (NativeWindowHistoryOseen.action seed M time z)) kept).trans last.symm
  simpa only [feedback,NativeWindowHistoryMeanBlocks.annihilation,ContinuousLinearMap.comp_apply,NativeWindowHistoryAdjointSpatialFeedback.centered,z] using! result

private theorem strong_square (M : ℕ) (v : physicalSpace (modes M)) :
    outputSquare true (modes M) v=‖includeCLM (modes M) (modes_closed M) v‖^2 := by
  rw [include_norm (modes M) (modes_zero M)]
  have source := (NativeWindowHistoryCreationGeometry.pairing_mass (modes M) v).symm.trans
    (real_inner_self_eq_norm_sq (coefficients (modes M) v))
  simpa only [NativeWindowHistoryAdjointSpatialHalf.outputSquare,NativeWindowHistoryAdjointSpatialHalf.weight,
    if_true,one_pow,one_mul] using source

private theorem root_product (a x y z : ℝ) (a0 : 0 ≤ a) (x0 : 0 ≤ x) (y0 : 0 ≤ y) (z0 : 0 ≤ z)
    (bound : z^2 ≤ a*x^2*y^2) : z ≤ Real.sqrt a*x*y := by
  apply (sq_le_sq₀ z0 (mul_nonneg (mul_nonneg (Real.sqrt_nonneg a) x0) y0)).mp
  simpa only [mul_pow,Real.sq_sqrt a0] using bound

private theorem square_constant (a i x : ℝ) (a0 : 0 ≤ a) (x0 : 0 ≤ x)
    (bound : x ≤ Real.sqrt a*i) : x^2 ≤ a*i^2 := by
  simpa only [mul_pow,Real.sq_sqrt a0] using pow_le_pow_left₀ x0 bound 2

private theorem family_strong_square (M : ℕ) (u v : wholePhysical) :
    ‖read M (NativeWindowHistoryAdjointSpatialHalf.weight true) (family nu M u v)‖^2=‖family nu M u v‖^2 := by
  rw [NativeWindowHistorySchurAdvectorFiber.family_original,read_output,restrict_include,strong_square]

theorem transport_norm_point (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    ∀ᵐ lag ∂averageMeasure,‖advection seed M time v lag‖ ≤ Real.sqrt transportCap*
      ‖lift M (fun k => radical k^2) (finiteHistory seed time M) lag‖*‖lift M (fun k => radical k^3) v lag‖ := by
  filter_upwards [transport_point true seed M time v,advection_ae seed M time v,
    (read M (fun k => radical k^2)).coeFn_compLpL (finiteHistory seed time M),
    (read M (fun k => radical k^3)).coeFn_compLpL v] with lag bounded actual first last
  have normed : ‖read M (NativeWindowHistoryAdjointSpatialHalf.weight true) (advection seed M time v lag)‖^2=
      ‖advection seed M time v lag‖^2 :=
    (congrArg (fun u : wholePhysical => ‖read M (NativeWindowHistoryAdjointSpatialHalf.weight true) u‖^2) actual).trans
      ((family_strong_square M (finiteHistory seed time M lag) (v lag)).trans (congrArg (fun u : wholePhysical => ‖u‖^2) actual.symm))
  have first' : lift M (fun k => radical k^2) (finiteHistory seed time M) lag=read M (fun k => radical k^2) (finiteHistory seed time M lag) := first
  have last' : lift M (fun k => radical k^3) v lag=read M (fun k => radical k^3) (v lag) := last
  rw [normed,← first'] at bounded
  simp only [NativeWindowHistoryAdjointSpatialHalf.inputOrder,if_true] at bounded
  rw [← last'] at bounded
  exact root_product transportCap _ _ _ transportCap_nonnegative (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) bounded

private theorem average_product_bound {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (u : ℝ → E) (f : Lp F 2 averageMeasure) (g : Lp G 2 averageMeasure) (C : ℝ) (C0 : 0 ≤ C)
    (point : ∀ᵐ lag ∂averageMeasure,‖u lag‖ ≤ Real.sqrt C*‖f lag‖*‖g lag‖) :
    ‖∫lag,u lag ∂averageMeasure‖^2 ≤ C*‖f‖^2*‖g‖^2 := by
  have products : Integrable (fun lag => ‖f lag‖*‖g lag‖) averageMeasure :=
    (Lp.memLp f).norm.integrable_mul (Lp.memLp g).norm
  have point' : ∀ᵐ lag ∂averageMeasure,‖u lag‖ ≤ Real.sqrt C*(‖f lag‖*‖g lag‖) := by
    simpa only [mul_assoc] using point
  have average := norm_integral_le_of_norm_le (products.const_mul (Real.sqrt C)) point'
  rw [integral_const_mul] at average
  have cauchy := NativeWindowHistoryAnnihilationControl.cauchy_square (fun lag => ‖f lag‖) (fun lag => ‖g lag‖)
    (Lp.memLp f).norm (Lp.memLp g).norm
  rw [← norm_square f,← norm_square g] at cauchy
  have squared := square_constant C _ _ C0 (norm_nonneg _) average
  exact squared.trans ((mul_le_mul_of_nonneg_left cauchy C0).trans_eq (mul_assoc C (‖f‖^2) (‖g‖^2)).symm)

theorem average_transport_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    ‖mean (advection seed M time v)‖^2 ≤ transportCap*‖lift M (fun k => radical k^2) (finiteHistory seed time M)‖^2*
      ‖lift M (fun k => radical k^3) v‖^2 := by
  have meanRead := congrArg (fun v : wholePhysical => ‖v‖^2) (NativeWindowHistoryMeanProjection.mean_original (advection seed M time v))
  apply meanRead.trans_le
  simpa only [] using! average_product_bound (E := wholePhysical) (F := Samples M) (G := Samples M)
    (advection seed M time v) (lift M (fun k => radical k^2) (finiteHistory seed time M))
    (lift M (fun k => radical k^3) v) transportCap transportCap_nonnegative (transport_norm_point seed M time v)

def budget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  transportCap*historyBudget seed horizon*centeredBudget seed horizon

theorem budget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0 ≤ budget seed horizon :=
  mul_nonneg (mul_nonneg transportCap_nonnegative (historyBudget_nonnegative seed horizon)) (centeredBudget_nonnegative seed horizon)

theorem feedback_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (time : ℝ)
    (inside : time∈Icc 0 horizon) (v : physicalSpace (modes M)) :
    ‖feedback seed M time (includeCLM (modes M) (modes_closed M) v)‖^2 ≤ budget seed horizon*NativeWindowHistoryHeatDual.energy nu M v := by
  rw [feedback_original]
  have first := history_bound seed horizon M time inside
  have last := source_centered_bound seed horizon M time inside v
  have product := mul_le_mul first last (sq_nonneg _ ) (historyBudget_nonnegative seed horizon)
  have result := (average_transport_bound seed M time (centered seed M time v)).trans
    (by simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left product transportCap_nonnegative)
  simpa only [budget,mul_assoc] using result

theorem source_feedback_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ M,∀ time∈Icc 0 horizon,∀ v : physicalSpace (modes M),
      ‖feedback seed M time (includeCLM (modes M) (modes_closed M) v)‖^2 ≤ B*NativeWindowHistoryHeatDual.energy nu M v :=
  ⟨budget seed horizon,budget_nonnegative seed horizon,fun M time inside v => feedback_bound seed horizon M time inside v⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem feedback_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0 ≤ time) :
    feedback seed M (step.2.clockAdvance+time)=feedback step.1 M time := by
  have blocks := NativeWindowHistoryMeanBlocks.blocks_next seed M step generated time nonnegative
  have creation := congrArg (fun x => x.2.1) blocks
  have annihilation := congrArg (fun x => x.2.2.1) blocks
  have responseNext := congrArg₂ (fun (R : H →L[ℝ] H) (C : wholePhysical →L[ℝ] H) => R.comp C)
    (NativeWindowHistoryBathResolvent.resolve_next seed M step generated time nonnegative) creation
  exact congrArg₂ (fun (A : H →L[ℝ] wholePhysical) (C : wholePhysical →L[ℝ] H) => A.comp C) annihilation responseNext

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAdjointSpatialFeedback
