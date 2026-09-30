import H0mework.Versions.X.NavierStokes.SourceWindow.Pairing
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryGNS
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCofinalStressPositivity NativeEndpointVelocityCarrier
open NativeForwardWindowPairingReadout NativeForwardWindowPairingMoments
noncomputable section
variable {nu : Viscosity}

abbrev HistoryHilbert := Lp ScalarSequence 2 averageMeasure

def sample (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (shift : ℝ) : ScalarSequence :=
  shiftedRead index (NativeUnifiedCompleteSource.source seed (time-shift))

def mean (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) : ScalarSequence :=
  shiftedRead index (NativeForwardWindowSource.source seed time)

theorem sample_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (shift : ℝ) :
    sample seed time index shift = shiftedComponent (NativeUnifiedCompleteSource.source seed (time-shift)).fst index := rfl

theorem mean_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    mean seed time index = shiftedComponent (NativeForwardWindowPairing.data seed time).mean index := rfl

theorem sample_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    Integrable (sample seed time index) averageMeasure :=
  (shiftedRead index).integrable_comp (original_integrable seed time)

theorem sample_memLp (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    MemLp (sample seed time index) 2 averageMeasure :=
  (memLp_two_iff_integrable_sq_norm (sample_integrable seed time index).aestronglyMeasurable).mpr
    (NativeForwardWindowPairingMoments.square_integrable (shiftedRead index) seed time)

theorem sample_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (shift : ℝ) :
    ‖sample seed time index shift‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  change ‖NativePairedCarrierJets.shifted (wholeVelocity (NativeUnifiedCompleteSource.source seed (time-shift)).fst) index.1 index.2‖ ≤ _
  rw [NativePairedCarrierJets.shifted_norm]
  apply (lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (fun wave => norm_le_pi_norm (wholeVelocity (NativeUnifiedCompleteSource.source seed (time-shift)).fst wave) index.2)).trans
  exact (wholeVelocity_norm_le _).trans ((WithLp.norm_fst_le _ _).trans (NativeUnifiedCompleteSource.source_bound seed (time-shift)))

theorem sample_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    (∫ shift, sample seed time index shift ∂averageMeasure) = mean seed time index :=
  (linear_probability_integral (shiftedRead index) seed time).symm

def history (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) : HistoryHilbert :=
  (sample_memLp seed time index).toLp (sample seed time index)

def constant (value : ScalarSequence) : HistoryHilbert :=
  (memLp_const (μ := averageMeasure) (p := 2) value).toLp (fun _ : ℝ => value)

theorem history_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    history seed time index =ᵐ[averageMeasure] sample seed time index :=
  (sample_memLp seed time index).coeFn_toLp

theorem constant_ae (value : ScalarSequence) : constant value =ᵐ[averageMeasure] fun _ => value :=
  (memLp_const (μ := averageMeasure) (p := 2) value).coeFn_toLp

def vector (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) : HistoryHilbert :=
  history seed time index-constant (mean seed time index)

theorem vector_ae (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    vector seed time index =ᵐ[averageMeasure] fun shift =>
      shiftedComponent (NativeUnifiedCompleteSource.source seed (time-shift)).fst index-
        shiftedComponent (NativeForwardWindowPairing.data seed time).mean index := by
  filter_upwards [Lp.coeFn_sub (history seed time index) (constant (mean seed time index)),
    history_ae seed time index, constant_ae (mean seed time index)] with shift subtract original fixed
  change (history seed time index-constant (mean seed time index)) shift = _
  rw [subtract, Pi.sub_apply, original, fixed, sample_original, mean_original]

theorem constant_inner (first last : ScalarSequence) : inner ℂ (constant first) (constant last) = inner ℂ first last := by
  rw [L2.inner_def]
  calc
    _ = ∫ _ : ℝ, inner ℂ first last ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [constant_ae first, constant_ae last] with shift left right
      rw [left,right]
    _ = _ := by simp

theorem constant_add (first last : ScalarSequence) : constant (first+last) = constant first+constant last := by
  apply Lp.ext
  filter_upwards [constant_ae (first+last), Lp.coeFn_add (constant first) (constant last),
    constant_ae first, constant_ae last] with shift both split left right
  rw [both,split,Pi.add_apply,left,right]

theorem constant_smul (scalar : ℂ) (value : ScalarSequence) : constant (scalar • value) = scalar • constant value := by
  apply Lp.ext
  filter_upwards [constant_ae (scalar • value), Lp.coeFn_smul scalar (constant value), constant_ae value] with shift both split original
  rw [both,split,Pi.smul_apply,original]

def constantIsometry : ScalarSequence →ₗᵢ[ℂ] HistoryHilbert where
  toFun := constant
  map_add' := constant_add
  map_smul' := constant_smul
  norm_map' value := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖constant value‖^2 = ‖value‖^2
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ), constant_inner]

theorem history_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) :
    ‖history seed time index‖ ≤ NativeUnifiedCompleteSource.budget seed := by
  have budget0 := (norm_nonneg _).trans (sample_bound seed time index 0)
  have upper := Lp.norm_le_of_ae_bound budget0 (by
    filter_upwards [history_ae seed time index] with shift original
    rw [original]
    exact sample_bound seed time index shift)
  simpa [measureUnivNNReal] using upper

theorem constant_history (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (value : ScalarSequence) :
    inner ℂ (constant value) (history seed time index) = inner ℂ value (mean seed time index) := by
  rw [L2.inner_def]
  calc
    _ = ∫ shift, inner ℂ value (sample seed time index shift) ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [constant_ae value, history_ae seed time index] with shift fixed original
      rw [fixed,original]
    _ = _ := by rw [integral_inner (sample_integrable seed time index), sample_average]

theorem history_constant (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (value : ScalarSequence) :
    inner ℂ (history seed time index) (constant value) = inner ℂ (mean seed time index) value := by
  rw [← inner_conj_symm (history seed time index) (constant value), constant_history]
  exact inner_conj_symm _ _

theorem constant_vector (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (index : Index) (value : ScalarSequence) :
    inner ℂ (constant value) (vector seed time index) = 0 := by
  rw [vector, inner_sub_right, constant_history, constant_inner, sub_self]

theorem history_inner (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (left right : Index) :
    inner ℂ (history seed time left) (history seed time right) =
      -(NativeForwardWindowPairing.data seed time).stress (left.1-right.1) left.2 right.2 := by
  rw [L2.inner_def]
  have source := (Measure.measurePreserving_sub_left (volume : Measure ℝ) time).quasiMeasurePreserving.ae
    (NativeUnifiedGlobalStressSource.stress_ae seed)
  have sourceAverage := (withDensity_absolutelyContinuous volume (fun shift => (density shift : ℝ≥0∞))).ae_le source
  calc
    _ = ∫ shift, -stressRead (left.1-right.1) left.2 right.2
        (NativeUnifiedCompleteSource.source seed (time-shift)) ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [history_ae seed time left, history_ae seed time right, sourceAverage] with shift first last same
      have reality : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointReality
          (NativeUnifiedCompleteSource.source seed (time-shift)).fst := (NativeCompletePairedAction.source seed (time-shift)).reality
      rw [first,last,sample_original,sample_original, shiftedComponent_inner _ reality, NativeCofinalFluxPairing.bilinearFlux_diagonal]
      congr 1
      change NativeStressSource.quadraticFlux (wholeVelocity (NativeUnifiedCompleteSource.source seed (time-shift)).fst)
        (left.1-right.1) left.2 right.2 = NativeCompleteStressCarrier.read (NativeUnifiedCompleteSource.source seed (time-shift)).snd
          (left.1-right.1) left.2 right.2
      rw [NativeUnifiedCompleteSource.velocity_read, NativeUnifiedCompleteSource.stress_read, same]
    _ = _ := by
      rw [integral_neg, ← linear_probability_integral]
      rfl

theorem vector_inner (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (left right : Index) :
    inner ℂ (vector seed time left) (vector seed time right) =
      (NativeStressPairingCarrier.kernel (NativeForwardWindowPairing.data seed time)).matrix left right := by
  simp only [vector, inner_sub_left, inner_sub_right, history_inner, history_constant, constant_history, constant_inner]
  rw [mean_original, mean_original,
    shiftedComponent_inner _ (NativeForwardWindowPairing.data seed time).reality, NativeCofinalFluxPairing.bilinearFlux_diagonal]
  change -_ - -_ - (-_ - -_) = -(_-_)
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryGNS
