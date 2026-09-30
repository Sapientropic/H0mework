import H0mework.Physics.LowEnergy.FullQuantum.HistoryGreen.FreeIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-! Plancherel and genuine Fubini identify the source free spatial time integral with its Fourier Green. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
open FullSpace GaugeGreen Triangular YangMills.FullPairing MatterSpace.Response
noncomputable section

def freeTimeIntegrand (energy damping : ℝ) (initial : FullMatterL2) (time : ℝ) : FullMatterL2 :=
  temporalWeight energy damping time • GaugeHistory.momentumFree time initial

theorem freeTimeIntegrand_continuous (energy damping : ℝ) (initial : FullMatterL2) :
    Continuous (freeTimeIntegrand energy damping initial) :=
  (temporalWeight_continuous energy damping).smul (GaugeHistory.momentumFree_continuous initial)

theorem freeTimeIntegrand_bound (energy damping time : ℝ) (initial : FullMatterL2) :
    ‖freeTimeIntegrand energy damping initial time‖≤Retarded.envelope damping 0 time*‖initial‖ := by
  rw [freeTimeIntegrand,norm_smul,temporalWeight_norm]
  have estimate := ((GaugeHistory.momentumFree time).le_opNorm initial).trans
    (mul_le_mul_of_nonneg_right (GaugeHistory.momentumFree_norm time) (norm_nonneg initial))
  simpa only [Retarded.envelope,mul_zero,add_zero,mul_one,one_mul] using
    mul_le_mul_of_nonneg_left estimate (Real.exp_pos (-damping*time)).le

theorem freeTimeIntegrand_integrable (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    IntegrableOn (freeTimeIntegrand energy damping initial) (Ioi 0) := by
  apply ((Retarded.envelope_integrable damping 0 positive).mul_const ‖initial‖).mono'
    (freeTimeIntegrand_continuous energy damping initial).aestronglyMeasurable
  exact ae_of_all _ (fun t => freeTimeIntegrand_bound energy damping t initial)

theorem freeTimeIntegrand_ae (energy damping time : ℝ) (initial : FullMatterL2) :
    freeTimeIntegrand energy damping initial time=ᵐ[volume] fun frequency =>
      freeIntegrand (physicalMomentum frequency) energy damping time (initial frequency) := by
  filter_upwards [GaugeHistory.momentumFree_ae time initial,
    Lp.coeFn_smul (temporalWeight energy damping time) (GaugeHistory.momentumFree time initial)] with frequency flow scaled
  change (temporalWeight energy damping time • GaugeHistory.momentumFree time initial) frequency=_
  rw [scaled]
  simp only [Pi.smul_apply]
  rw [flow]
  rfl

def freePairIntegrand (energy damping : ℝ) (test initial : FullMatterL2) (time : ℝ) (frequency : Position) : ℂ :=
  inner ℂ (test frequency) (freeIntegrand (physicalMomentum frequency) energy damping time (initial frequency))

theorem freePairIntegrand_measurable (energy damping : ℝ) (test initial : FullMatterL2) :
    AEStronglyMeasurable (Function.uncurry (freePairIntegrand energy damping test initial))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Position)) := by
  have matrices : Continuous (fun tx : ℝ × Position => freeIntegrand (physicalMomentum tx.2) energy damping tx.1) :=
    ((temporalWeight_continuous energy damping).comp continuous_fst).smul GaugeHistory.freeMatrices_continuous
  have applied : AEStronglyMeasurable (fun tx : ℝ × Position =>
      freeIntegrand (physicalMomentum tx.2) energy damping tx.1 (initial tx.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Position)) :=
    (isBoundedBilinearMap_apply : IsBoundedBilinearMap ℂ (fun pair : FiberOperators × Hilbert => pair.1 pair.2)).continuous.comp_aestronglyMeasurable
      (matrices.aestronglyMeasurable.prodMk (Lp.memLp initial).aestronglyMeasurable.comp_snd)
  exact (Lp.memLp test).aestronglyMeasurable.comp_snd.inner applied

theorem freePairIntegrand_integrable (energy damping : ℝ) (positive : 0<damping) (test initial : FullMatterL2) :
    Integrable (Function.uncurry (freePairIntegrand energy damping test initial))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure Position)) := by
  have spatial : Integrable (fun x => ‖test x‖*‖initial x‖) volume :=
    (Lp.memLp test).norm.integrable_mul (Lp.memLp initial).norm
  apply ((Retarded.envelope_integrable damping 0 positive).mul_prod spatial).mono'
    (freePairIntegrand_measurable energy damping test initial)
  exact ae_of_all _ fun tx => by
    calc
      ‖freePairIntegrand energy damping test initial tx.1 tx.2‖≤
          ‖test tx.2‖*‖freeIntegrand (physicalMomentum tx.2) energy damping tx.1 (initial tx.2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖test tx.2‖*(Real.exp (-damping*tx.1)*‖initial tx.2‖) :=
        mul_le_mul_of_nonneg_left (((freeIntegrand (physicalMomentum tx.2) energy damping tx.1).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (freeIntegrand_norm _ _ _ _) (norm_nonneg _))) (norm_nonneg _)
      _ = _ := by simp [Retarded.envelope]; ring

theorem freeMomentumIntegral_pair (energy damping : ℝ) (positive : 0<damping) (test initial : FullMatterL2) :
    inner ℂ test (∫ t : ℝ in Ioi 0, freeTimeIntegrand energy damping initial t)=
      ∫ frequency, inner ℂ (test frequency)
        ((Complex.I • freeValue 0 (physicalMomentum frequency) energy damping) (initial frequency)) := by
  rw [← integral_inner (freeTimeIntegrand_integrable energy damping positive initial)]
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ frequency, freePairIntegrand energy damping test initial t frequency := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        change inner ℂ test (freeTimeIntegrand energy damping initial t)=_
        erw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [freeTimeIntegrand_ae energy damping t initial] with frequency read
        rw [read]
        rfl
    _ = ∫ frequency, ∫ t : ℝ in Ioi 0, freePairIntegrand energy damping test initial t frequency :=
      integral_integral_swap (freePairIntegrand_integrable energy damping positive test initial)
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun frequency => by
        have admissible := freeIntegrand_integrable (physicalMomentum frequency) energy damping positive
        have vector := (ContinuousLinearMap.apply ℂ Hilbert (initial frequency)).integrable_comp admissible
        change (∫ t : ℝ in Ioi 0, inner ℂ (test frequency)
          (freeIntegrand (physicalMomentum frequency) energy damping t (initial frequency)))=_
        erw [integral_inner vector]
        change inner ℂ (test frequency)
          (∫ t : ℝ in Ioi 0, freeIntegrand (physicalMomentum frequency) energy damping t (initial frequency))=_
        have applied := (ContinuousLinearMap.integral_apply admissible (initial frequency)).symm
        rw [applied,freeIntegral_original_resolvent _ _ _ positive]

theorem freeMomentumIntegral_original (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    (∫ t : ℝ in Ioi 0, freeTimeIntegrand energy damping initial t)=
      Complex.I • GaugeGreen.momentumFree 0 energy damping positive initial := by
  apply ext_inner_left ℂ
  intro test
  rw [freeMomentumIntegral_pair energy damping positive,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [GaugeGreen.momentumFree_ae 0 energy damping positive initial,
    Lp.coeFn_smul Complex.I (GaugeGreen.momentumFree 0 energy damping positive initial)] with frequency read scaled
  rw [scaled]
  simp only [Pi.smul_apply]
  rw [read]
  rfl

theorem freeSpatialIntegral_original (energy damping : ℝ) (positive : 0<damping) (initial : FullMatterL2) :
    (∫ t : ℝ in Ioi 0, temporalWeight energy damping t • GaugeHistory.spatialFree t initial)=
      Complex.I • freeR 0 energy damping positive initial := by
  have pull := fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (freeTimeIntegrand_integrable energy damping positive (fourier initial))
  calc
    _ = ∫ t : ℝ in Ioi 0, fourier.symm (freeTimeIntegrand energy damping (fourier initial) t) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        change temporalWeight energy damping t • fourier.symm (GaugeHistory.momentumFree t (fourier initial))=
          fourier.symm (temporalWeight energy damping t • GaugeHistory.momentumFree t (fourier initial))
        exact (map_smul fourier.symm _ _).symm
    _ = fourier.symm (∫ t : ℝ in Ioi 0, freeTimeIntegrand energy damping (fourier initial) t) := pull
    _ = fourier.symm (Complex.I • GaugeGreen.momentumFree 0 energy damping positive (fourier initial)) := by
      rw [freeMomentumIntegral_original energy damping positive]
    _ = _ := by rw [map_smul]; rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.HistoryGreen
