import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedCurrent
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedCurrentSeed

/-! Native temporal and spatial matter readers are generated from the original
full real-CAR action. The configuration force retains every H0 term on its core. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.CanonicalGradedCurrent
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussQuantumMultiplier GaussFockLabel
open GaussUnitaryHistory (HistorySpace reader)
open scoped Topology InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder

def boundedMatrix (A : Matrix Mode Mode ℂ) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (fun _ => quantized A) (fun _ => contDiffAt_const)
    (fun _ w => weight_commute w A) ‖quantized A‖ (norm_nonneg _)
    (fun _ f => (quantized A).le_opNorm f)

theorem boundedMatrix_core (A : Matrix Mode Mode ℂ) (f : QuantumTest) :
    boundedMatrix A (embed f) = embed (action (fun _ => A) (fun _ => contDiffAt_const) f) :=
  GaussBoundedMultiplier.extension_core (fun _ => quantized A) (fun _ => contDiffAt_const)
    (fun _ w => weight_commute w A) ‖quantized A‖ (norm_nonneg _)
    (fun _ f => (quantized A).le_opNorm f) f

theorem boundedMatrix_blocks (A : Matrix Mode Mode ℂ) (preserves : Preserves A)
    (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g) (boundedMatrix A) := by
  show NativeHistoryGrade.projection g * boundedMatrix A =
    boundedMatrix A * NativeHistoryGrade.projection g
  apply GaussYukawaGrade.core_ext
  intro f
  change NativeHistoryGrade.projection g (boundedMatrix A (embed f)) =
    boundedMatrix A (NativeHistoryGrade.projection g (embed f))
  rw [boundedMatrix_core, ← GaussCoreLabel.embed_project,
    ← GaussCoreLabel.embed_project, boundedMatrix_core]
  exact congrArg embed (GaussCoreLabel.commutes_matrix g (fun _ => A)
    (fun _ => contDiffAt_const) (fun _ => preserves) f)

inductive Component
  | temporal
  | spatial (i : Fin 3)

def gaugeMatrix (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) : Matrix Mode Mode ℂ :=
  match mu with
  | .temporal => Complex.I • GaussNativeMatter.nativeFull a
  | .spatial i => -∑ b : Fin 3,
      (GaussMatterCore.coefficient i b z : ℂ) • GaussMatterCore.matrixTerm b a

theorem gaugeMatrix_preserves (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    Preserves (gaugeMatrix z mu a) := by
  cases mu with
  | temporal => exact preserves_smul (native_preserves a) Complex.I
  | spatial i =>
    intro u v
    simp only [gaugeMatrix, Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, mul_neg, Finset.mul_sum]
    rw [Finset.sum_eq_zero (fun b _ => ?_), neg_zero]
    have h := preserves_smul (preserves_mul
      (preserves_smul (spin_preserves (Fin.castAdd 4 b)) Complex.I) (native_preserves a))
      (GaussMatterCore.coefficient i b z : ℂ) u v
    exact h

def gaugeReader (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) : H →L[ℂ] H :=
  boundedMatrix (gaugeMatrix z mu a)

theorem gaugeReader_blocks (z : SourceCoordinateSlice) (mu : Component) (a : NativeLie) :
    Commute historyProjection (reader (gaugeReader z mu a)) := by
  show reader sourceProjection * reader (gaugeReader z mu a) =
    reader (gaugeReader z mu a) * reader sourceProjection
  rw [← GaussUnitaryHistory.reader_mul, ← GaussUnitaryHistory.reader_mul]
  exact congrArg reader (boundedMatrix_blocks (gaugeMatrix z mu a)
    (gaugeMatrix_preserves z mu a) sourceLabel).eq

def sourceGaugeWord (z : SourceCoordinateSlice) (word : List (ℝ × Component × NativeLie)) :
    List (ℝ × (HistorySpace →L[ℂ] HistorySpace)) :=
  word.map (fun item => (item.1, reader (gaugeReader z item.2.1 item.2.2)))

theorem sourceGaugeWord_preserves (z : SourceCoordinateSlice) (word : List (ℝ × Component × NativeLie)) :
    ∀ item ∈ sourceGaugeWord z word, Commute historyProjection item.2 := by
  intro item hi
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hi
  exact gaugeReader_blocks z entry.2.1 entry.2.2

theorem source_gauge_word_return (z : SourceCoordinateSlice) (word : List (ℝ × Component × NativeLie))
    (cut : ℕ) (x y : HistorySpace) :
    cutoffObservation cut (sourceGaugeWord z word) x y =
      diagonalObservation (sourceGaugeWord z word) x y :=
  observable_return cut _ (sourceGaugeWord_preserves z word) x y

theorem source_gauge_cutoff_limit (z : SourceCoordinateSlice)
    (word : List (ℝ × Component × NativeLie)) (x y : HistorySpace) :
    Filter.Tendsto (fun cut : ℕ => cutoffObservation cut (sourceGaugeWord z word) x y)
      Filter.atTop (𝓝 (diagonalObservation (sourceGaugeWord z word) x y)) :=
  observable_cutoff_limit _ (sourceGaugeWord_preserves z word) x y

def twoCurrentWord (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (t s : ℝ) : List (ℝ × (HistorySpace →L[ℂ] HistorySpace)) :=
  [(-t, reader (gaugeReader z mu a)), (t-s, reader (gaugeReader z nu b)), (s, 1)]

theorem twoCurrentWord_preserves (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t s : ℝ) :
    ∀ item ∈ twoCurrentWord z mu nu a b t s, Commute historyProjection item.2 := by
  intro item hi
  simp only [twoCurrentWord, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact gaugeReader_blocks z mu a
  · exact gaugeReader_blocks z nu b
  · exact Commute.one_right historyProjection

def twoCurrent (cut : ℕ) (z : SourceCoordinateSlice) (mu nu : Component) (a b : NativeLie)
    (t s : ℝ) (x y : HistorySpace) : ℂ :=
  cutoffObservation cut (twoCurrentWord z mu nu a b t s) x y

theorem twoCurrent_cutoff_return (cut : ℕ) (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t s : ℝ) (x y : HistorySpace) :
    twoCurrent cut z mu nu a b t s x y =
      diagonalObservation (twoCurrentWord z mu nu a b t s) x y :=
  observable_return cut _ (twoCurrentWord_preserves z mu nu a b t s) x y

theorem twoCurrent_independent_dual (cut : ℕ) (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t s : ℝ) (x y : HistorySpace) :
    twoCurrent cut z mu nu a b t s x y =
      inner ℂ (FullYSourceCutoffVolterra.sourceSharpEvolution cut t (historyProjection x))
        (reader (gaugeReader z mu a)
          (FullYSourceCutoffVolterra.sourceEvolution cut (t-s)
            (reader (gaugeReader z nu b)
              (FullYSourceCutoffVolterra.sourceEvolution cut s (historyProjection y))))) := by
  rw [FullYSourceCutoffVolterra.source_evolution_sharp_pair]
  simp only [twoCurrent, cutoffObservation, twoCurrentWord, cutoffWord, List.foldr_cons,
    List.foldr_nil, mul_one, mul_apply_eq_comp]

theorem twoCurrent_cutoff_limit (z : SourceCoordinateSlice) (mu nu : Component)
    (a b : NativeLie) (t s : ℝ) (x y : HistorySpace) :
    Filter.Tendsto (fun cut : ℕ => twoCurrent cut z mu nu a b t s x y) Filter.atTop
      (𝓝 (diagonalObservation (twoCurrentWord z mu nu a b t s) x y)) :=
  observable_cutoff_limit _ (twoCurrentWord_preserves z mu nu a b t s) x y

/- The full source force is a core commutator. In particular, this is not the
finite matter matrix inside it. All native, coframe and normal-order terms of
the same H0 remain in `diagonalAction`. -/
def configurationForce (v : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] QuantumTest :=
  GaussDiagonalHistory.diagonalAction.comp (GaussCoframeCore.derivative v) -
    (GaussCoframeCore.derivative v).comp GaussDiagonalHistory.diagonalAction

def covariantForce (v : GaussLiveMomentum.Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  Complex.I • (GaussDiagonalHistory.diagonalAction.comp (covariantMomentum v) -
    (covariantMomentum v).comp GaussDiagonalHistory.diagonalAction)

theorem configurationForce_blocks (v : SourceCoordinateSlice) (g : NativeHistoryGrade.Label) :
    GaussCoreLabel.Commutes g (configurationForce v) := by
  unfold configurationForce
  rw [sub_eq_add_neg, ← neg_one_smul ℂ]
  exact GaussCoreLabel.commutes_add g
    (GaussCoreLabel.commutes_comp g (GaussDiagonalGrade.diagonal_action g)
      (GaussCoreLabel.commutes_derivative g v))
    (GaussCoreLabel.commutes_smul g
      (GaussCoreLabel.commutes_comp g (GaussCoreLabel.commutes_derivative g v)
        (GaussDiagonalGrade.diagonal_action g)) (-1))

theorem covariantForce_blocks (v : GaussLiveMomentum.Ambient) (g : NativeHistoryGrade.Label) :
    GaussCoreLabel.Commutes g (covariantForce v) := by
  unfold covariantForce
  apply GaussCoreLabel.commutes_smul g
  rw [sub_eq_add_neg, ← neg_one_smul ℂ]
  exact GaussCoreLabel.commutes_add g
    (GaussCoreLabel.commutes_comp g (GaussDiagonalGrade.diagonal_action g)
      (GaussDiagonalGrade.native_momentum g v))
    (GaussCoreLabel.commutes_smul g
      (GaussCoreLabel.commutes_comp g (GaussDiagonalGrade.native_momentum g v)
        (GaussDiagonalGrade.diagonal_action g)) (-1))

def gaugeDirection (i : Fin 3) (a : NativeLie) : GaussLiveMomentum.Ambient :=
  (0, SourceQuantumResidualGaugeSlice.gaugeCoordinates.symm (Pi.single i a))

def fullSpatialGaugeForce (i : Fin 3) (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  covariantForce (gaugeDirection i a)

theorem fullSpatialGaugeForce_blocks (i : Fin 3) (a : NativeLie) (g : NativeHistoryGrade.Label) :
    GaussCoreLabel.Commutes g (fullSpatialGaugeForce i a) :=
  covariantForce_blocks (gaugeDirection i a) g

#print axioms gaugeReader_blocks
#print axioms source_gauge_cutoff_limit
#print axioms twoCurrent_independent_dual
#print axioms twoCurrent_cutoff_return
#print axioms configurationForce_blocks
#print axioms fullSpatialGaugeForce_blocks
end LowEnergy.CanonicalGradedCurrent
