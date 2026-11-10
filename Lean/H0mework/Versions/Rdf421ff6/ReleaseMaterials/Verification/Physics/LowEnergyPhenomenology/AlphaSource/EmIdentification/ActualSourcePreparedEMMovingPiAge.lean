import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMMovingAge
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMTemporalFreeReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedStaticHalfPencil
import Mathlib.Analysis.SpecialFunctions.Exp
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedNoetherPi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalCausal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMMovingPiAge
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationPhysicalPhaseGaugeRealization
open SourcePropagationNoetherTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedEMTemporal ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedFiniteStaticRead ActualSourcePreparedNoetherPi
open ActualSourcePreparedEMMovingAge ActualSourcePreparedEMTemporalFreeReturn
open ActualSourcePreparedEMPhaseField PreparationVacuumPhysicalCharacteristic
open ActualDressedLeftFreeJet ActualDressedNumberField ActualDressedStaticResponse PreparationVacuumPhysicalHalfAxis
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open ActualSourcePreparedTemporalQuantumIR
open MeasureTheory Set Filter
open scoped Topology Interval BigOperators Matrix
attribute [local irreducible] dressedNoetherJet dressedNoetherKernel dressedEulerObserver
  dressedWindowPolarization dressedSignalMatrix noetherHistoryOperatorJet dressedKinematicPoint

private theorem constant_source_jets (force : Field289) (t : ℝ) :
    HasSourceJets (fun _ => (⟨force,0,0⟩ : SourceJet Field289)) t :=
  ⟨hasDerivAt_const t force,hasDerivAt_const t 0⟩

private theorem constant_source_jets_continuous (force : Field289) :
    ContinuousJets (fun _ => (⟨force,0,0⟩ : SourceJet Field289)) :=
  ⟨continuous_const,continuous_const,continuous_const⟩

private theorem jet_zero_force (event : DressedEvent) (transfer : PhysicalMomentum) (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event transfer (fun _ => ⟨0,0,0⟩) t i).value = 0 := by
  have actual := dressed_noether_action_derivative event transfer (0 : Field289) t i
  have stationary : HasDerivAt (fun r : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event transfer (fieldUnit i) t (r • (0 : Field289)))) 0 0 := by
    simpa only [smul_zero] using hasDerivAt_const 0
      (dressedEulerObserver event (dressedNoetherKernel event transfer (fieldUnit i) t 0))
  exact actual.unique stationary

private theorem signal_matrix_static_jet (event : DressedEvent) (transfer : PhysicalMomentum) (t : ℝ) (i j : Fin 289) :
    dressedSignalMatrix event transfer (0 : Fin 4 → ℂ) t i j =
      (dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j,0,0⟩) t i).value := by
  have actual := dressed_static_current event transfer (0 : Fin 4 → ℂ) rfl
    (Pi.single j (1 : ℂ)) t i
  have real_unit : (fun k : Fin 289 => ((Pi.single j (1 : ℂ) : Fin 289 → ℂ) k).re) = fieldUnit j := by
    funext k
    simp only [fieldUnit,Pi.single_apply]
    split_ifs <;> rfl
  have imaginary_unit : (fun k : Fin 289 => ((Pi.single j (1 : ℂ) : Fin 289 → ℂ) k).im) = 0 := by
    funext k
    simp only [Pi.single_apply,Pi.zero_apply]
    split_ifs <;> rfl
  let observe : Field289 → ℂ := fun force => dressedEulerObserver event
    (noetherHistoryOperatorJet (dressedKinematicPoint event transfer) (fieldUnit i)
      (fun _ => ⟨force,0,0⟩) t).value
  have re := congrArg observe real_unit
  have im := congrArg observe imaginary_unit
  have normalized : dressedSignalQuadrature event transfer (0 : Fin 4 → ℂ) t (Pi.single j 1) i =
      observe (fieldUnit j)+Complex.I*observe 0 :=
    actual.trans (congrArg₂ (fun x y : ℂ => x+Complex.I*y) re im)
  have real : (dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j,0,0⟩) t i).value = observe (fieldUnit j) :=
    dressed_noether_jet_original event transfer (fun _ => ⟨fieldUnit j,0,0⟩) t i
  have imaginary : (dressedNoetherJet event transfer (fun _ => ⟨0,0,0⟩) t i).value = observe 0 :=
    dressed_noether_jet_original event transfer (fun _ => ⟨0,0,0⟩) t i
  rw [←real,←imaginary,jet_zero_force,mul_zero,add_zero] at normalized
  simpa only [dressedSignalMatrix,dressed_signal_complex_original] using normalized

/-- This is the unchanged finite full289 polarization, contracted with the
original source EM row. No separate finite response is solved. -/
def sourceEMMovingPiWindow (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (j : Fin 289) : ℂ :=
  ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ) *
    dressedWindowPolarization event transfer (0 : Fin 4 → ℂ) lambda T i j

private theorem em_jet_continuous (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) :
    Continuous (fun t : ℝ => emTemporalJet event transfer force t) := by
  unfold emTemporalJet
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (dressed_noether_jet_continuous event transfer _
    (constant_source_jets_continuous force) i).1

private theorem em_jet_age_first (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) (t : ℝ) :
    dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer force t) =
      ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ) *
        (dressedNoetherJet event transfer (fun _ => ⟨force,0,0⟩) t i).first := by
  have each (i : Fin 289) := (dressed_noether_jet_generated event transfer _ continuous_const t
    (constant_source_jets force t) i).1.const_mul ((sourcePhaseGaugeField 0) i : ℂ)
  have original := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => each i)
  exact (source_em_moving_temporal_jet_age_derivative event transfer force t).unique original

/-- The original age jets generate the residual continuity needed by the
same finite-window integral; no integrability is supplied by a caller. -/
theorem source_em_moving_age_residual_continuous (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) :
    Continuous (fun t : ℝ => dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer force t)) := by
  simp_rw [em_jet_age_first]
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (dressed_noether_jet_continuous event transfer _
    (constant_source_jets_continuous force) i).2.1

private theorem weight_derivative (lambda : ℂ) (t : ℝ) :
    HasDerivAt (laplaceWeight lambda) (-lambda*laplaceWeight lambda t) t := by
  have real_time : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) t := by
    simpa only [id_eq,Complex.real_smul,mul_one,one_smul] using (hasDerivAt_id t).smul_const (1 : ℂ)
  have generated := ((real_time.const_mul (-lambda)).cexp)
  change HasDerivAt (laplaceWeight lambda) _ t at generated
  convert! generated using 1
  unfold laplaceWeight
  ring

private theorem weight_continuous (lambda : ℂ) : Continuous (laplaceWeight lambda) := by
  unfold laplaceWeight
  fun_prop

/-- The actual original finite polarization is the age integral of the
same original EM jet, across every forcing column. -/
theorem source_em_moving_pi_window_integral (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (j : Fin 289) :
    sourceEMMovingPiWindow event transfer lambda T j =
      ∫ t in (0 : ℝ)..T, laplaceWeight lambda t*emTemporalJet event transfer (fieldUnit j) t := by
  unfold sourceEMMovingPiWindow dressedWindowPolarization
  simp_rw [signal_matrix_static_jet]
  have each (i : Fin 289) : IntervalIntegrable (fun t : ℝ =>
      ((sourcePhaseGaugeField 0) i : ℂ)*(laplaceWeight lambda t*
        (dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j,0,0⟩) t i).value)) volume 0 T :=
    (continuous_const.mul ((weight_continuous lambda).mul
      (dressed_noether_jet_continuous event transfer _ (constant_source_jets_continuous (fieldUnit j)) i).1)).intervalIntegrable 0 T
  calc
    _ = ∑ i : Fin 289, ∫ t in (0 : ℝ)..T, ((sourcePhaseGaugeField 0) i : ℂ)*
        (laplaceWeight lambda t*(dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j,0,0⟩) t i).value) := by
      simp only [intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..T, ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ)*
        (laplaceWeight lambda t*(dressedNoetherJet event transfer (fun _ => ⟨fieldUnit j,0,0⟩) t i).value) :=
      (intervalIntegral.integral_finsetSum (fun i _ => each i)).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [emTemporalJet,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Exact source Laplace integration by parts retains both genuine
endpoints. It feeds the actual full finite Pi row, without an endpoint premise. -/
theorem source_em_moving_pi_window_boundary (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (j : Fin 289) :
    (∫ t in (0 : ℝ)..T, laplaceWeight lambda t*
      dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer (fieldUnit j) t)) =
      laplaceWeight lambda T*emTemporalJet event transfer (fieldUnit j) T-
        emTemporalJet event transfer (fieldUnit j) 0+lambda*sourceEMMovingPiWindow event transfer lambda T j := by
  let g := fun t : ℝ => emTemporalJet event transfer (fieldUnit j) t
  let a := fun t : ℝ => dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer (fieldUnit j) t)
  have derivative (t : ℝ) : HasDerivAt (fun s : ℝ => laplaceWeight lambda s*g s)
      (laplaceWeight lambda t*a t-lambda*(laplaceWeight lambda t*g t)) t := by
    have generated := (weight_derivative lambda t).mul
      (source_em_moving_temporal_jet_age_derivative event transfer (fieldUnit j) t)
    convert! generated using 1
    ring
  have first : IntervalIntegrable (fun t : ℝ => laplaceWeight lambda t*a t) volume 0 T :=
    ((weight_continuous lambda).mul (source_em_moving_age_residual_continuous event transfer (fieldUnit j))).intervalIntegrable 0 T
  have second : IntervalIntegrable (fun t : ℝ => lambda*(laplaceWeight lambda t*g t)) volume 0 T :=
    (continuous_const.mul ((weight_continuous lambda).mul (em_jet_continuous event transfer (fieldUnit j)))).intervalIntegrable 0 T
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => derivative t) (first.sub second)
  rw [intervalIntegral.integral_sub first second,intervalIntegral.integral_const_mul] at generated
  have zero : laplaceWeight lambda 0 = 1 := by simp [laplaceWeight]
  rw [zero,one_mul] at generated
  rw [source_em_moving_pi_window_integral]
  change _ = laplaceWeight lambda T*g T-g 0+lambda*(∫t in (0 : ℝ)..T,laplaceWeight lambda t*g t)
  linear_combination generated

/-- The same preparation return, not a surrogate Pi, prices the difference
between this finite EM row and every original infinite source Pi column. -/
theorem source_em_moving_pi_prepared_tail (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (j : Fin 289) :
    ‖(∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ)*sourcePreparedPiEntry event transfer lambda i j)-
      sourceEMMovingPiWindow event transfer lambda T j‖ ≤
      (∑ i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)‖)*
        dressedSignalTailPrice event transfer (0 : Fin 4 → ℂ) lambda T := by
  unfold sourceEMMovingPiWindow
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)*
        (sourcePreparedPiEntry event transfer lambda i j-
          dressedWindowPolarization event transfer (0 : Fin 4 → ℂ) lambda T i j)‖ := by
      simpa only [mul_sub] using norm_sum_le _ _
    _ ≤ ∑ i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)‖*
        dressedSignalTailPrice event transfer (0 : Fin 4 → ℂ) lambda T := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (source_prepared_pi_tail event transfer 0 rfl lambda positive T future i j) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

private theorem free_time_slope_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (force : Field289) : freeTimeSlope p F force 0=0 := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [abs_zero,zero_mul] using free_time_slope_price p F force 0)
    (norm_nonneg _)

/-- The two original inverse variations at age zero. The source reader,
compression current, energy and actual observer pair remain unchanged. -/
def sourceEMMovingInitialKernel (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) : H →L[ℂ] H :=
  let RL := jointCResolvent (event.momentum-transfer) event.frame event.energy 0
  let RR := jointCResolvent event.momentum event.frame event.energy 0
  let BL := freeCompressionCurrent (event.momentum-transfer) event.frame force
  let BR := freeCompressionCurrent event.momentum event.frame force
  let J := emTemporalReader event.momentum event.frame;
  -(RL*BL*RL)*J*RR+RL*J*(-(RR*BR*RR))

theorem source_em_moving_initial_jet (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) :
    emTemporalJet event transfer force 0=dressedEulerObserver event (sourceEMMovingInitialKernel event transfer force) := by
  rw [actual_em_temporal_jet_free]
  unfold emFreeSlope sourceEMMovingInitialKernel
  simp only [neg_zero,free_time_slope_zero,SourceFiniteUnitary.time_zero,
    zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero]

/-- The original all-age linear price makes the positive-frequency
terminal vanish. No asymptotic endpoint is supplied by a caller. -/
theorem source_em_moving_weighted_endpoint_limit (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (force : Field289) :
    Tendsto (fun t : ℝ => laplaceWeight lambda t*emTemporalJet event transfer force t)
      atTop (𝓝 0) := by
  have scaled := (tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop positive
  have decay : Tendsto (fun t : ℝ => Real.exp (-lambda.re*t)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,id_eq,neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp scaled
  have polynomial := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp scaled).const_mul lambda.re⁻¹
  have linear : Tendsto (fun t : ℝ => t*Real.exp (-lambda.re*t)) atTop (𝓝 0) := by
    have same : (fun t : ℝ => lambda.re⁻¹*((lambda.re*t)^1*Real.exp (-(lambda.re*t)))) =
        (fun t : ℝ => t*Real.exp (-lambda.re*t)) := by
      funext t
      rw [pow_one]
      field_simp
    simpa only [Function.comp_def,id_eq,same,mul_zero] using polynomial
  have majorant : Tendsto (fun t : ℝ => emTemporalPrice event transfer force*
      (Real.exp (-lambda.re*t)+t*Real.exp (-lambda.re*t))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (decay.add linear).const_mul (emTemporalPrice event transfer force)
  apply squeeze_zero_norm' _ majorant
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t future
  rw [norm_mul,laplace_norm]
  have source := mul_le_mul_of_nonneg_left
    (actual_em_temporal_jet_linear_price event transfer force t) (Real.exp_pos (-lambda.re*t)).le
  exact source.trans_eq (by rw [abs_of_nonneg future];ring)

/-- The unchanged static full289 window limit returns the same
preparation Pi, then the original source EM row reads that limit. -/
theorem source_em_moving_pi_window_limit (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (j : Fin 289) :
    Tendsto (fun T : ℝ => sourceEMMovingPiWindow event transfer lambda T j) atTop
      (𝓝 (sourcePreparedEMTemporalPi event transfer lambda j)) := by
  have whole := static_polarization_window_limit event transfer (0 : Fin 4 → ℂ) rfl lambda positive
  have each (i : Fin 289) : Tendsto
      (fun T : ℝ => ((sourcePhaseGaugeField 0) i : ℂ)*dressedWindowPolarization event transfer 0 lambda T i j)
      atTop (𝓝 (((sourcePhaseGaugeField 0) i : ℂ)*sourcePreparedPiEntry event transfer lambda i j)) := by
    have coordinate := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp whole i) j).const_mul
      (((sourcePhaseGaugeField 0) i : ℂ))
    rw [source_prepared_pi_actual event transfer lambda positive i j]
    exact coordinate
  unfold sourceEMMovingPiWindow sourcePreparedEMTemporalPi
  rw [source_temporal_force_phase]
  exact tendsto_finsetSum _ (fun i _ => each i)

/-- This is the finite integral of the original EM age residual,
already generated as the age derivative of the same Noether jet. -/
def sourceEMMovingResidualWindow (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (j : Fin 289) : ℂ :=
  ∫t in (0 : ℝ)..T, laplaceWeight lambda t*
    dressedEulerObserver event (Complex.I • sourceEMMovingAgeSlope event transfer (fieldUnit j) t)

/-- Positive frequency returns the original full Pi from its generated
initial term and residual improper integral, without deleting the residual. -/
theorem source_em_moving_residual_window_limit (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (j : Fin 289) :
    Tendsto (fun T : ℝ => sourceEMMovingResidualWindow event transfer lambda T j) atTop
      (𝓝 (-dressedEulerObserver event (sourceEMMovingInitialKernel event transfer (fieldUnit j))+
        lambda*sourcePreparedEMTemporalPi event transfer lambda j)) := by
  have source := ((source_em_moving_weighted_endpoint_limit event transfer lambda positive (fieldUnit j)).sub
    (tendsto_const_nhds (x:=emTemporalJet event transfer (fieldUnit j) 0))).add
    ((source_em_moving_pi_window_limit event transfer lambda positive j).const_mul lambda)
  have same : (fun T : ℝ => sourceEMMovingResidualWindow event transfer lambda T j) =
      (fun T : ℝ => laplaceWeight lambda T*emTemporalJet event transfer (fieldUnit j) T-
        emTemporalJet event transfer (fieldUnit j) 0+lambda*sourceEMMovingPiWindow event transfer lambda T j) := by
    funext T
    exact source_em_moving_pi_window_boundary event transfer lambda T j
  rw [same]
  simpa only [zero_sub,source_em_moving_initial_jet] using source

/-- A finite error price for that same infinite return retains the actual
terminal and the preparation tail, not an independently assigned remainder. -/
theorem source_em_moving_residual_window_price (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ)
    (positive : 0<lambda.re) (T : ℝ) (future : 0≤T) (j : Fin 289) :
    ‖sourceEMMovingResidualWindow event transfer lambda T j-
      (-dressedEulerObserver event (sourceEMMovingInitialKernel event transfer (fieldUnit j))+
        lambda*sourcePreparedEMTemporalPi event transfer lambda j)‖ ≤
      Real.exp (-lambda.re*T)*emTemporalPrice event transfer (fieldUnit j)*(1+T)+
        ‖lambda‖*(∑i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)‖)*
          dressedSignalTailPrice event transfer (0 : Fin 4 → ℂ) lambda T := by
  have same : sourcePreparedEMTemporalPi event transfer lambda j =
      ∑i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ)*sourcePreparedPiEntry event transfer lambda i j := by
    unfold sourcePreparedEMTemporalPi
    rw [source_temporal_force_phase]
  have tail := source_em_moving_pi_prepared_tail event transfer lambda positive T future j
  rw [←same,norm_sub_rev] at tail
  have terminal : ‖laplaceWeight lambda T*emTemporalJet event transfer (fieldUnit j) T‖ ≤
      Real.exp (-lambda.re*T)*emTemporalPrice event transfer (fieldUnit j)*(1+T) := by
    rw [norm_mul,laplace_norm]
    have price := mul_le_mul_of_nonneg_left
      (actual_em_temporal_jet_linear_price event transfer (fieldUnit j) T) (Real.exp_pos (-lambda.re*T)).le
    simpa only [abs_of_nonneg future,mul_assoc] using price
  unfold sourceEMMovingResidualWindow
  rw [source_em_moving_pi_window_boundary,source_em_moving_initial_jet]
  have equation : laplaceWeight lambda T*emTemporalJet event transfer (fieldUnit j) T-
      dressedEulerObserver event (sourceEMMovingInitialKernel event transfer (fieldUnit j))+
      lambda*sourceEMMovingPiWindow event transfer lambda T j-
      (-dressedEulerObserver event (sourceEMMovingInitialKernel event transfer (fieldUnit j))+
        lambda*sourcePreparedEMTemporalPi event transfer lambda j) =
      laplaceWeight lambda T*emTemporalJet event transfer (fieldUnit j) T+
        lambda*(sourceEMMovingPiWindow event transfer lambda T j-sourcePreparedEMTemporalPi event transfer lambda j) := by ring
  rw [equation]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul]
  have combined := add_le_add terminal (mul_le_mul_of_nonneg_left tail (norm_nonneg lambda))
  simpa only [norm_mul,mul_assoc] using combined



/-- Original Born plus full age residual, contracted with the actual
moving GE0 on all289 columns. The varying field is kept, without normalization. -/
def sourceEMMovingDriverWindow (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (T : ℝ) : ℂ :=
  ∑j : Fin 289,
    (dressedEulerObserver event (sourceEMMovingInitialKernel event (e.val^2 • n) (fieldUnit j))+
      sourceEMMovingResidualWindow event (e.val^2 • n) (sigma : ℂ) T j)*
      sourceTemporalCorrectedField event e.val sigma n j

/-- Every age-return entry is consumed at the driver's own epsilon-squared
transfer and same actual prepared field, yielding its original full quantum read. -/
theorem source_em_moving_actual_driver_window_limit (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0<sigma) :
    Tendsto (sourceEMMovingDriverWindow event e sigma n) atTop
      (𝓝 (dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n))) := by
  have paid : 0<(sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  have each (j : Fin 289) : Tendsto
      (fun T : ℝ =>
        (dressedEulerObserver event (sourceEMMovingInitialKernel event (e.val^2 • n) (fieldUnit j))+
          sourceEMMovingResidualWindow event (e.val^2 • n) (sigma : ℂ) T j)*
          sourceTemporalCorrectedField event e.val sigma n j) atTop
      (𝓝 ((sigma : ℂ)*sourcePreparedEMTemporalPi event (e.val^2 • n) (sigma : ℂ) j*
        sourceTemporalCorrectedField event e.val sigma n j)) := by
    have returned := (source_em_moving_residual_window_limit event (e.val^2 • n) (sigma : ℂ) paid j).const_add
      (dressedEulerObserver event (sourceEMMovingInitialKernel event (e.val^2 • n) (fieldUnit j)))
    simpa only [add_neg_cancel_left] using returned.mul_const (sourceTemporalCorrectedField event e.val sigma n j)
  have whole := tendsto_finsetSum Finset.univ (fun j _ => each j)
  rw [source_temporal_quantum_em_driver_return]
  unfold sourceEMMovingDriverWindow
  simpa only [Finset.mul_sum,mul_assoc] using whole

/-- The source endpoint and preparation tail price the full actual driver
window with every actual field component norm retained. -/
theorem source_em_moving_actual_driver_window_price (event : DressedEvent) (e : scaleDomain)
    (sigma : ℝ) (n : PhysicalMomentum) (positive : 0<sigma) (T : ℝ) (future : 0≤T) :
    ‖sourceEMMovingDriverWindow event e sigma n T-
      dotProduct sourceTemporalEMForce (sourceTemporalActualQuantumDriver event e sigma n)‖ ≤
      ∑j : Fin 289, (Real.exp (-sigma*T)*emTemporalPrice event (e.val^2 • n) (fieldUnit j)*(1+T)+
        ‖(sigma : ℂ)‖*(∑i : Fin 289,‖((sourcePhaseGaugeField 0) i : ℂ)‖)*
          dressedSignalTailPrice event (e.val^2 • n) (0 : Fin 4 → ℂ) (sigma : ℂ) T)*
        ‖sourceTemporalCorrectedField event e.val sigma n j‖ := by
  have paid : 0<(sigma : ℂ).re := by simpa only [Complex.ofReal_re] using positive
  rw [source_temporal_quantum_em_driver_return]
  unfold sourceEMMovingDriverWindow
  rw [Finset.mul_sum,←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  have price := source_em_moving_residual_window_price event (e.val^2 • n) (sigma : ℂ) paid T future j
  have equation :
      (dressedEulerObserver event (sourceEMMovingInitialKernel event (e.val^2 • n) (fieldUnit j))+
        sourceEMMovingResidualWindow event (e.val^2 • n) (sigma : ℂ) T j)*
        sourceTemporalCorrectedField event e.val sigma n j-
      (sigma : ℂ)*(sourcePreparedEMTemporalPi event (e.val^2 • n) (sigma : ℂ) j*
        sourceTemporalCorrectedField event e.val sigma n j) =
      (sourceEMMovingResidualWindow event (e.val^2 • n) (sigma : ℂ) T j-
        (-dressedEulerObserver event (sourceEMMovingInitialKernel event (e.val^2 • n) (fieldUnit j))+
          (sigma : ℂ)*sourcePreparedEMTemporalPi event (e.val^2 • n) (sigma : ℂ) j))*
        sourceTemporalCorrectedField event e.val sigma n j := by ring
  rw [equation,norm_mul]
  exact mul_le_mul_of_nonneg_right (by simpa only [Complex.ofReal_re] using price) (norm_nonneg _)

end LowEnergy.GaussComposite.ActualSourcePreparedEMMovingPiAge
