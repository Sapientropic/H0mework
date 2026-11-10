import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedEMMixedAgeRead
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedNoetherPi
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalCausal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedEMAgePiWindow
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationPhysicalPhaseGaugeRealization
open SourcePropagationNoetherTime
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedEMTemporal ActualDressedSignal ActualDressedPencil
open ActualDressedSylvester ActualDressedFiniteStaticRead ActualSourcePreparedNoetherPi
open ActualSourcePreparedEMMixedAgeRead ActualSourcePreparedEMAgeFieldReturn
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

private theorem jet_zero_force (event : DressedEvent) (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event 0 (fun _ => ⟨0,0,0⟩) t i).value = 0 := by
  have actual := dressed_noether_action_derivative event 0 (0 : Field289) t i
  have stationary : HasDerivAt (fun r : ℝ => dressedEulerObserver event
      (dressedNoetherKernel event 0 (fieldUnit i) t (r • (0 : Field289)))) 0 0 := by
    simpa only [smul_zero] using hasDerivAt_const 0
      (dressedEulerObserver event (dressedNoetherKernel event 0 (fieldUnit i) t 0))
  exact actual.unique stationary

private theorem signal_matrix_static_jet (event : DressedEvent) (t : ℝ) (i j : Fin 289) :
    dressedSignalMatrix event 0 (0 : Fin 4 → ℂ) t i j =
      (dressedNoetherJet event 0 (fun _ => ⟨fieldUnit j,0,0⟩) t i).value := by
  have actual := dressed_static_current event 0 (0 : Fin 4 → ℂ) rfl
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
    (noetherHistoryOperatorJet (dressedKinematicPoint event 0) (fieldUnit i)
      (fun _ => ⟨force,0,0⟩) t).value
  have re := congrArg observe real_unit
  have im := congrArg observe imaginary_unit
  have normalized : dressedSignalQuadrature event 0 (0 : Fin 4 → ℂ) t (Pi.single j 1) i =
      observe (fieldUnit j)+Complex.I*observe 0 :=
    actual.trans (congrArg₂ (fun x y : ℂ => x+Complex.I*y) re im)
  have real : (dressedNoetherJet event 0 (fun _ => ⟨fieldUnit j,0,0⟩) t i).value = observe (fieldUnit j) :=
    dressed_noether_jet_original event 0 (fun _ => ⟨fieldUnit j,0,0⟩) t i
  have imaginary : (dressedNoetherJet event 0 (fun _ => ⟨0,0,0⟩) t i).value = observe 0 :=
    dressed_noether_jet_original event 0 (fun _ => ⟨0,0,0⟩) t i
  rw [←real,←imaginary,jet_zero_force,mul_zero,add_zero] at normalized
  simpa only [dressedSignalMatrix,dressed_signal_complex_original] using normalized

/-- This is the unchanged finite full289 polarization, contracted with the
original source EM row. No separate finite response is solved. -/
def sourceEMAgePiWindow (event : DressedEvent) (lambda : ℂ) (T : ℝ) (j : Fin 289) : ℂ :=
  ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ) *
    dressedWindowPolarization event 0 (0 : Fin 4 → ℂ) lambda T i j

private theorem em_jet_continuous (event : DressedEvent) (force : Field289) :
    Continuous (fun t : ℝ => emTemporalJet event 0 force t) := by
  unfold emTemporalJet
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (dressed_noether_jet_continuous event 0 _
    (constant_source_jets_continuous force) i).1

private theorem em_jet_age_first (event : DressedEvent) (force : Field289) (t : ℝ) :
    dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event force t) =
      ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ) *
        (dressedNoetherJet event 0 (fun _ => ⟨force,0,0⟩) t i).first := by
  have each (i : Fin 289) := (dressed_noether_jet_generated event 0 _ continuous_const t
    (constant_source_jets force t) i).1.const_mul ((sourcePhaseGaugeField 0) i : ℂ)
  have original := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ => each i)
  exact (source_em_temporal_jet_age_derivative event force t).unique original

/-- The original age jets generate the residual continuity needed by the
same finite-window integral; no integrability is supplied by a caller. -/
theorem source_em_age_residual_continuous (event : DressedEvent) (force : Field289) :
    Continuous (fun t : ℝ => dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event force t)) := by
  simp_rw [em_jet_age_first]
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (dressed_noether_jet_continuous event 0 _
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
theorem source_em_age_pi_window_integral (event : DressedEvent) (lambda : ℂ) (T : ℝ) (j : Fin 289) :
    sourceEMAgePiWindow event lambda T j =
      ∫ t in (0 : ℝ)..T, laplaceWeight lambda t*emTemporalJet event 0 (fieldUnit j) t := by
  unfold sourceEMAgePiWindow dressedWindowPolarization
  simp_rw [signal_matrix_static_jet]
  have each (i : Fin 289) : IntervalIntegrable (fun t : ℝ =>
      ((sourcePhaseGaugeField 0) i : ℂ)*(laplaceWeight lambda t*
        (dressedNoetherJet event 0 (fun _ => ⟨fieldUnit j,0,0⟩) t i).value)) volume 0 T :=
    (continuous_const.mul ((weight_continuous lambda).mul
      (dressed_noether_jet_continuous event 0 _ (constant_source_jets_continuous (fieldUnit j)) i).1)).intervalIntegrable 0 T
  calc
    _ = ∑ i : Fin 289, ∫ t in (0 : ℝ)..T, ((sourcePhaseGaugeField 0) i : ℂ)*
        (laplaceWeight lambda t*(dressedNoetherJet event 0 (fun _ => ⟨fieldUnit j,0,0⟩) t i).value) := by
      simp only [intervalIntegral.integral_const_mul]
    _ = ∫ t in (0 : ℝ)..T, ∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ)*
        (laplaceWeight lambda t*(dressedNoetherJet event 0 (fun _ => ⟨fieldUnit j,0,0⟩) t i).value) :=
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
theorem source_em_age_pi_window_boundary (event : DressedEvent) (lambda : ℂ) (T : ℝ) (j : Fin 289) :
    (∫ t in (0 : ℝ)..T, laplaceWeight lambda t*
      dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event (fieldUnit j) t)) =
      laplaceWeight lambda T*emTemporalJet event 0 (fieldUnit j) T-
        emTemporalJet event 0 (fieldUnit j) 0+lambda*sourceEMAgePiWindow event lambda T j := by
  let g := fun t : ℝ => emTemporalJet event 0 (fieldUnit j) t
  let a := fun t : ℝ => dressedEulerObserver event (Complex.I • sourceEMAgeFieldSlope event (fieldUnit j) t)
  have derivative (t : ℝ) : HasDerivAt (fun s : ℝ => laplaceWeight lambda s*g s)
      (laplaceWeight lambda t*a t-lambda*(laplaceWeight lambda t*g t)) t := by
    have generated := (weight_derivative lambda t).mul
      (source_em_temporal_jet_age_derivative event (fieldUnit j) t)
    convert! generated using 1
    ring
  have first : IntervalIntegrable (fun t : ℝ => laplaceWeight lambda t*a t) volume 0 T :=
    ((weight_continuous lambda).mul (source_em_age_residual_continuous event (fieldUnit j))).intervalIntegrable 0 T
  have second : IntervalIntegrable (fun t : ℝ => lambda*(laplaceWeight lambda t*g t)) volume 0 T :=
    (continuous_const.mul ((weight_continuous lambda).mul (em_jet_continuous event (fieldUnit j)))).intervalIntegrable 0 T
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => derivative t) (first.sub second)
  rw [intervalIntegral.integral_sub first second,intervalIntegral.integral_const_mul] at generated
  have zero : laplaceWeight lambda 0 = 1 := by simp [laplaceWeight]
  rw [zero,one_mul] at generated
  rw [source_em_age_pi_window_integral]
  change _ = laplaceWeight lambda T*g T-g 0+lambda*(∫t in (0 : ℝ)..T,laplaceWeight lambda t*g t)
  linear_combination generated

/-- The same preparation return, not a surrogate Pi, prices the difference
between this finite EM row and every original infinite source Pi column. -/
theorem source_em_age_pi_prepared_tail (event : DressedEvent) (lambda : ℂ) (positive : 0<lambda.re)
    (T : ℝ) (future : 0≤T) (j : Fin 289) :
    ‖(∑ i : Fin 289, ((sourcePhaseGaugeField 0) i : ℂ)*sourcePreparedPiEntry event 0 lambda i j)-
      sourceEMAgePiWindow event lambda T j‖ ≤
      (∑ i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)‖)*
        dressedSignalTailPrice event 0 (0 : Fin 4 → ℂ) lambda T := by
  unfold sourceEMAgePiWindow
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)*
        (sourcePreparedPiEntry event 0 lambda i j-
          dressedWindowPolarization event 0 (0 : Fin 4 → ℂ) lambda T i j)‖ := by
      simpa only [mul_sub] using norm_sum_le _ _
    _ ≤ ∑ i : Fin 289, ‖((sourcePhaseGaugeField 0) i : ℂ)‖*
        dressedSignalTailPrice event 0 (0 : Fin 4 → ℂ) lambda T := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (source_prepared_pi_tail event 0 0 rfl lambda positive T future i j) (norm_nonneg _)
    _ = _ := by rw [Finset.sum_mul]

end LowEnergy.GaussComposite.ActualSourcePreparedEMAgePiWindow
