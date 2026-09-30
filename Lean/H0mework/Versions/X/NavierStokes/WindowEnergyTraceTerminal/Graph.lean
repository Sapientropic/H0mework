import H0mework.Versions.X.NavierStokes.WindowEnergyTraceTerminal.Average
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceEndpoint.Window

set_option autoImplicit false
open scoped BigOperators Topology ENNReal Pointwise
namespace SaturationMonoid.NavierStokes.NativeWindowTraceTerminalGraph
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeResolventAdjoint NativeWholeH1Mixed NativeWindowOperatorGreen
open NativeWindowStressOseenTest (evaluate)
open NativeWindowStressHeatBalance (viscousRead)
open NativeWindowStressHeatSource (physical)
open NativeWindowTraceTerminalOperator (remainder remainder_pairing)
open NativeWindowTraceCutOperator (jointTest)
open NativeWindowConvectionCutoffTrace (relative)
open NativeWindowTraceAdjoint (value value_continuous)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceEndpointWindow (terminal terminalEnergy)
noncomputable section
variable {nu : Viscosity}

theorem square_split (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M F : Finset IntegerWavevector)
    (radius : ℕ) (zero : 0∉M) (closed : FiniteModeNegClosed M) (v : physicalSpace M) :
    ‖coefficients M (jointTest seed observation M F radius v)‖^2=
      nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2-
        2*nu.coeff*pairing M (laplacian M zero closed nu v) (remainder seed observation M F radius zero closed v)+
          ‖coefficients M (remainder seed observation M F radius zero closed v)‖^2 := by
  have same : jointTest seed observation M F radius v=remainder seed observation M F radius zero closed v-
      nu.coeff • laplacian M zero closed nu v := by unfold remainder; abel
  rw [same,map_sub,map_smul,norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_of_nonneg nu.coeff_pos.le]
  change _=nu.coeff^2*‖coefficients M (laplacian M zero closed nu v)‖^2-
    2*nu.coeff*inner ℝ (coefficients M (laplacian M zero closed nu v))
      (coefficients M (remainder seed observation M F radius zero closed v))+
        ‖coefficients M (remainder seed observation M F radius zero closed v)‖^2
  rw [real_inner_comm (coefficients M (laplacian M zero closed nu v))]
  ring

theorem viscous_evaluate (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector)
    (cover : ∀ k∈F,k≠0 →k∈modes M) (sample : ℝ) (nonnegative : 0 ≤ sample) (i : Coordinate) :
    evaluate (modes M) F i (laplacian (modes M) (modes_zero M) (modes_closed M) nu (value seed M sample))=
      -viscousRead F i (NativeUnifiedCompleteSource.source seed sample) := by
  change evaluate (modes M) F i (laplacian (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowTraceDualWindow.value seed M sample))=_
  rw [NativeWindowTraceDualWindow.value_load seed M sample nonnegative]
  simp only [NativeWindowStressOseenTest.evaluate_apply,viscousRead,sum_apply,smul_apply,
    ContinuousLinearMap.comp_apply,neg_smul,Finset.sum_neg_distrib,neg_neg]
  apply Finset.sum_congr rfl
  intro k inside
  change NativeWindowStressHeatBalance.basis k ((laplacian (modes M) (modes_zero M) (modes_closed M) nu
    (NativeWindowStressOseenSource.load M seed sample)).1 k i)=_
  rw [laplacian_row]
  have source:=NativeWindowAugmentedFixedOperator.load_reads seed sample nonnegative M F cover k inside i
  change NativeUnheatedTriadRows.velocity seed sample k i=_ at source
  rw [NativeUnheatedTriadRows.velocity_original] at source
  change NativeForwardWindowPairingReadout.velocityRead k i (NativeUnifiedCompleteSource.source seed sample)=
    (NativeWindowStressOseenSource.load M seed sample).1 k i at source
  change NativeWindowStressHeatBalance.basis k ((integerWaveViscousMultiplier k : ℝ) •
    (NativeWindowStressOseenSource.load M seed sample).1 k i)=_
  rw [← source]
  exact (NativeWindowStressHeatBalance.basis k).map_smul (integerWaveViscousMultiplier k) _

def heatRead (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (radius : ℕ) : C(NativePhysicalFourier.Torus,ℝ) →L[ℝ] ℝ :=
  (innerSL ℝ (relative seed F radius observation)).comp physical

theorem cross_original (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) (cover : ∀ k∈F,k≠0 →k∈modes M)
    (sample : ℝ) (nonnegative : 0 ≤ sample) :
    2*nu.coeff*pairing (modes M)
      (laplacian (modes M) (modes_zero M) (modes_closed M) nu (value seed M sample))
      (remainder seed observation (modes M) F radius (modes_zero M) (modes_closed M) (value seed M sample))=
      ∑ i : Coordinate,heatRead seed observation F radius (NativeWindowStressHeatBalance.heatPair seed F i i sample) := by
  rw [remainder_pairing,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have read:=NativeWindowTraceDualWindow.value_read seed M sample nonnegative F cover i
  change evaluate (modes M) F i (value seed M sample)=_ at read
  rw [viscous_evaluate seed M F cover sample nonnegative i,read]
  simp only [heatRead,ContinuousLinearMap.comp_apply,innerSL_apply_apply,NativeWindowStressHeatBalance.heatPair,
    mul_comm (NativeWindowStressHeatTime.field seed F i sample),map_smul,map_add,
    neg_mul,map_neg,inner_neg_right]
  ring

theorem continuous_memLp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (observation : ℝ) (f : ℝ → E) (continuous : Continuous f) (p : ℝ≥0∞) :
    MemLp (fun shift => f (observation-shift)) p averageMeasure := by
  obtain ⟨bound,bounded⟩:=isCompact_Icc.exists_bound_of_continuousOn (continuous.continuousOn (s:=Icc observation (observation+2)))
  apply MemLp.of_bound (continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable bound
  filter_upwards [NativeWindowTraceEndpointWindow.average_interval] with shift support
  exact bounded (observation-shift) (by constructor <;> linarith [support.1,support.2])

def remainderEnergy (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : ℝ :=
  ∫ shift,‖coefficients (modes M) (remainder seed observation (modes M) F radius (modes_zero M) (modes_closed M)
    (value seed M (observation-shift)))‖^2 ∂averageMeasure

theorem remainder_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) :
    Integrable (fun shift => ‖coefficients (modes M) (remainder seed observation (modes M) F radius
      (modes_zero M) (modes_closed M) (value seed M (observation-shift)))‖^2) averageMeasure := by
  let op:=(coefficients (modes M)).comp (jointTest seed observation (modes M) F radius+
    nu.coeff • laplacian (modes M) (modes_zero M) (modes_closed M) nu)
  have continuous:= (LinearMap.toContinuousLinearMap op).continuous.comp (value_continuous seed M)
  exact (continuous_memLp observation _ continuous 2).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)

theorem remainder_nonnegative (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (M : ℕ)
    (F : Finset IntegerWavevector) (radius : ℕ) : 0≤remainderEnergy seed observation M F radius :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem heat_integrable (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (i : Coordinate) : Integrable (fun shift => NativeWindowStressHeatBalance.heatPair seed F i i (observation-shift)) averageMeasure := by
  have first:=NativeWindowStressHeatSource.product_integrable seed observation (viscousRead F i) (NativeWindowFiniteGramFourier.read F i)
  have last:=NativeWindowStressHeatSource.product_integrable seed observation (NativeWindowFiniteGramFourier.read F i) (viscousRead F i)
  have sum := Integrable.add (ε' := C(NativePhysicalFourier.Torus,ℝ)) first last
  simpa only [NativeWindowStressHeatBalance.heatPair,NativeWindowStressHeatTime.field_original,Pi.add_apply,Pi.smul_apply] using!
    sum.smul (-nu.coeff)

theorem heat_average (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (F : Finset IntegerWavevector)
    (closed : FiniteModeNegClosed F) (i : Coordinate) :
    (∫ shift,NativeWindowStressHeatBalance.heatPair seed F i i (observation-shift) ∂averageMeasure)=
      NativeWindowStressHeatSource.heat seed observation F i i := by
  rw [← NativeWindowStressHeatBalance.rawHeat_original seed observation F closed]
  simp only [NativeWindowStressHeatBalance.heatPair,NativeWindowStressHeatTime.field_original]
  rw [integral_smul,integral_add
    (NativeWindowStressHeatSource.product_integrable seed observation (viscousRead F i) (NativeWindowFiniteGramFourier.read F i))
    (NativeWindowStressHeatSource.product_integrable seed observation (NativeWindowFiniteGramFourier.read F i) (viscousRead F i))]
  rfl

theorem source_square (seed : GeneratedWholeRestartCurrent nu) (observation : ℝ) (nonnegative : 0≤observation)
    (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (closed : FiniteModeNegClosed F)
    (cover : ∀ k∈F,k≠0 →k∈modes M) : terminalEnergy seed observation M F radius=
      nu.coeff^2*NativeWindowAugmentedGradientSource.palinstrophyWindow seed M observation-
        heatRead seed observation F radius (∑ i : Coordinate,NativeWindowStressHeatSource.heat seed observation F i i)+
          remainderEnergy seed observation M F radius := by
  have same : terminalEnergy seed observation M F radius=
      ∫ shift,nu.coeff^2*‖NativeWindowAugmentedGradientSource.palinRead nu M
        (NativeUnheatedSourceQuadraticApprox.physicalSource seed (observation-shift))‖^2-
        (∑ i : Coordinate,heatRead seed observation F radius (NativeWindowStressHeatBalance.heatPair seed F i i (observation-shift)))+
        ‖coefficients (modes M) (remainder seed observation (modes M) F radius (modes_zero M) (modes_closed M)
          (value seed M (observation-shift)))‖^2 ∂averageMeasure := by
    apply integral_congr_ae
    filter_upwards [NativeWindowHistoryGNS.average_support] with shift support
    have sample0 : 0≤observation-shift := by linarith
    have spectral : ‖coefficients (modes M) (laplacian (modes M) (modes_zero M) (modes_closed M) nu
        (value seed M (observation-shift)))‖^2=‖NativeWindowAugmentedGradientSource.palinRead nu M
          (NativeUnheatedSourceQuadraticApprox.physicalSource seed (observation-shift))‖^2 := by
      rw [NativeWindowAugmentedGradientSource.palinRead_original,
        ← NativeWindowTraceDualWindow.value_load seed M (observation-shift) sample0]
      exact (real_inner_self_eq_norm_sq _).symm
    change ‖coefficients (modes M) (jointTest seed observation (modes M) F radius (value seed M (observation-shift)))‖^2=_
    rw [square_split,spectral,cross_original seed observation M F radius cover (observation-shift) sample0]
  have heatPaid (i : Coordinate):=(heatRead seed observation F radius).integrable_comp (heat_integrable seed observation F i)
  have palinPaid:=(NativeWindowAugmentedGradientSource.palinstrophy_integrable seed M observation).const_mul (nu.coeff^2)
  have differencePaid : Integrable (fun shift => nu.coeff^2*‖NativeWindowAugmentedGradientSource.palinRead nu M
      (NativeUnheatedSourceQuadraticApprox.physicalSource seed (observation-shift))‖^2-
      ∑ i : Coordinate,heatRead seed observation F radius (NativeWindowStressHeatBalance.heatPair seed F i i (observation-shift)))
      averageMeasure := palinPaid.sub (integrable_finsetSum Finset.univ (fun i _ => heatPaid i))
  rw [same,integral_add differencePaid
    (remainder_integrable seed observation M F radius),integral_sub palinPaid (integrable_finsetSum Finset.univ (fun i _ => heatPaid i)),
    integral_const_mul,integral_finsetSum Finset.univ (fun i _ => heatPaid i)]
  simp only [(heatRead seed observation F radius).integral_comp_comm (heat_integrable seed observation F _),
    heat_average seed observation F closed,← map_sum]
  rfl

end
end SaturationMonoid.NavierStokes.NativeWindowTraceTerminalGraph
