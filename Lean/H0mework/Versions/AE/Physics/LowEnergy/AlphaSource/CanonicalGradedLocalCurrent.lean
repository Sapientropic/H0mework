import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalGradedGaugeReturn
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! The original configuration-dependent native current is localized inside
its physical chart, then extended on the same Number-weighted completion.
The localizer generates the bound; no bounded current is supplied as data. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedLocalCurrent
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussQuantumMultiplier GaussFockLabel CanonicalGradedCurrent
open GaussHistoryHilbert (physicalChart)
open GaussUnitaryHistory (HistorySpace reader sourceFilter)
open Set Function MeasureTheory
open scoped Topology InnerProductSpace ContDiff Distributions Manifold
attribute [local instance] SourceRealScalarFock.branchOrder

abbrev Localizer := 𝓓(physicalChart, ℝ)
abbrev FiberMap := FockFiber →L[ℂ] FockFiber

/-- Every coframe coefficient is read at the integration configuration. -/
def sourceCurrent (mu : Component) (a : NativeLie) (z : SourceCoordinateSlice) : FiberMap :=
  quantized (gaugeMatrix z mu a)

theorem sourceCurrent_smooth (mu : Component) (a : NativeLie) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceCurrent mu a) z.val := by
  cases mu with
  | temporal =>
    change ContDiffAt ℝ ∞ (fun _ : SourceCoordinateSlice => quantized (Complex.I • GaussNativeMatter.nativeFull a)) z.val
    exact contDiffAt_const
  | spatial i =>
    have term (b : Fin 3) : ContDiffAt ℝ ∞
        (fun w => (GaussMatterCore.coefficient i b w : ℂ) • quantized (GaussMatterCore.matrixTerm b a)) z.val :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (GaussMatterCore.coefficient_smooth i b z)).smul contDiffAt_const
    have generated := (ContDiffAt.sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => term b)).neg
    convert generated using 1
    funext w
    change quantizer (-∑ b : Fin 3, (GaussMatterCore.coefficient i b w : ℂ) • GaussMatterCore.matrixTerm b a) = _
    rw [map_neg, map_sum]
    simp only [map_smul]
    rfl

def coefficient (phi : Localizer) (mu : Component) (a : NativeLie) (z : SourceCoordinateSlice) : FiberMap :=
  (phi z : ℂ) • sourceCurrent mu a z

theorem coefficient_zero_outside (phi : Localizer) (mu : Component) (a : NativeLie)
    (z : SourceCoordinateSlice) (outside : z ∉ tsupport phi) : coefficient phi mu a z = 0 := by
  rw [coefficient, image_eq_zero_of_notMem_tsupport outside, Complex.ofReal_zero]
  apply ContinuousLinearMap.ext
  intro v
  exact _root_.zero_smul ℂ (sourceCurrent mu a z v)

theorem coefficient_support (phi : Localizer) (mu : Component) (a : NativeLie) :
    tsupport (coefficient phi mu a) ⊆ tsupport phi := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra outside
  exact hz (coefficient_zero_outside phi mu a z outside)

theorem coefficient_smooth (phi : Localizer) (mu : Component) (a : NativeLie) :
    ContDiff ℝ ∞ (coefficient phi mu a) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport phi
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z phi.contDiff.contDiffAt).smul
      (sourceCurrent_smooth mu a ⟨z, phi.tsupport_subset hz⟩)
  · apply (contDiffAt_const (c := (0 : FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport phi).isOpen_compl.mem_nhds hz] with w hw
    exact coefficient_zero_outside phi mu a w hw

def coefficientTest (phi : Localizer) (mu : Component) (a : NativeLie) : 𝓓(physicalChart, FiberMap) where
  toFun := coefficient phi mu a
  contDiff' := coefficient_smooth phi mu a
  hasCompactSupport' := phi.hasCompactSupport.of_isClosed_subset isClosed_closure (coefficient_support phi mu a)
  tsupport_subset' := (coefficient_support phi mu a).trans phi.tsupport_subset

def bound (phi : Localizer) (mu : Component) (a : NativeLie) : ℝ :=
  ‖(coefficientTest phi mu a : BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

theorem bound_nonnegative (phi : Localizer) (mu : Component) (a : NativeLie) : 0 ≤ bound phi mu a := by
  exact norm_nonneg (coefficientTest phi mu a : BoundedContinuousFunction SourceCoordinateSlice FiberMap)

theorem coefficient_bound (phi : Localizer) (mu : Component) (a : NativeLie) (z : SourceCoordinateSlice)
    (v : FockFiber) : ‖coefficient phi mu a z v‖ ≤ bound phi mu a*‖v‖ := by
  have generated := (coefficientTest phi mu a : BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z
  exact ((coefficient phi mu a z).le_opNorm v).trans (mul_le_mul_of_nonneg_right generated (norm_nonneg v))

theorem coefficient_weights (phi : Localizer) (mu : Component) (a : NativeLie)
    (z : SourceCoordinateSlice) (w : ℕ → ℂ) : Commute (GaussFockWeights.weight w) (coefficient phi mu a z) :=
  (weight_commute w (gaugeMatrix z mu a)).smul_right (phi z : ℂ)

def localAction (phi : Localizer) (mu : Component) (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (coefficient phi mu a) (fun _ => (coefficient_smooth phi mu a).contDiffAt)

def localReader (phi : Localizer) (mu : Component) (a : NativeLie) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (coefficient phi mu a) (fun _ => (coefficient_smooth phi mu a).contDiffAt)
    (fun z w => coefficient_weights phi mu a z w) (bound phi mu a) (bound_nonnegative phi mu a)
    (fun z => coefficient_bound phi mu a z)

theorem localReader_core (phi : Localizer) (mu : Component) (a : NativeLie) (f : QuantumTest) :
    localReader phi mu a (embed f) = embed (localAction phi mu a f) :=
  GaussBoundedMultiplier.extension_core (coefficient phi mu a) (fun _ => (coefficient_smooth phi mu a).contDiffAt)
    (fun z w => coefficient_weights phi mu a z w) (bound phi mu a) (bound_nonnegative phi mu a)
    (fun z => coefficient_bound phi mu a z) f

theorem localReader_norm (phi : Localizer) (mu : Component) (a : NativeLie) :
    ‖localReader phi mu a‖ ≤ bound phi mu a :=
  GaussBoundedMultiplier.extension_norm (coefficient phi mu a) (fun _ => (coefficient_smooth phi mu a).contDiffAt)
    (fun z w => coefficient_weights phi mu a z w) (bound phi mu a) (bound_nonnegative phi mu a)
    (fun z => coefficient_bound phi mu a z)


def localMatrix (phi : Localizer) (mu : Component) (a : NativeLie) (z : SourceCoordinateSlice) :
    Matrix Mode Mode ℂ := (phi z : ℂ) • gaugeMatrix z mu a

theorem coefficient_quantized (phi : Localizer) (mu : Component) (a : NativeLie) (z : SourceCoordinateSlice) :
    coefficient phi mu a z = quantized (localMatrix phi mu a z) :=
  (quantizer.map_smul (phi z : ℂ) (gaugeMatrix z mu a)).symm

theorem localMatrix_hermitian (phi : Localizer) (mu : Component) (a : NativeLie) (z : SourceCoordinateSlice) :
    (localMatrix phi mu a z).conjTranspose = localMatrix phi mu a z := by
  rw [localMatrix, Matrix.conjTranspose_smul, CanonicalGradedGaugeVariation.gaugeMatrix_hermitian,
    Complex.star_def, Complex.conj_ofReal]

theorem localAction_blocks (phi : Localizer) (mu : Component) (a : NativeLie) (g : NativeHistoryGrade.Label) :
    GaussCoreLabel.Commutes g (localAction phi mu a) := by
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreLabel.fiberPiece g (coefficient phi mu a z (f z)) =
    coefficient phi mu a z (GaussCoreLabel.fiberPiece g (f z))
  rw [coefficient_quantized]
  exact congrArg (fun T : FiberMap => T (f z))
    (GaussFockLabel.blockWeight_quantized (fun l => if l=g then 1 else 0) (localMatrix phi mu a z)
      (preserves_smul (gaugeMatrix_preserves z mu a) (phi z : ℂ))).eq

theorem localReader_blocks (phi : Localizer) (mu : Component) (a : NativeLie) (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g) (localReader phi mu a) := by
  show NativeHistoryGrade.projection g*localReader phi mu a = localReader phi mu a*NativeHistoryGrade.projection g
  apply GaussYukawaGrade.core_ext
  intro f
  change NativeHistoryGrade.projection g (localReader phi mu a (embed f)) =
    localReader phi mu a (NativeHistoryGrade.projection g (embed f))
  rw [localReader_core, ← GaussCoreLabel.embed_project, ← GaussCoreLabel.embed_project, localReader_core]
  exact congrArg embed (localAction_blocks phi mu a g f)

theorem localAction_pair (phi : Localizer) (mu : Component) (a : NativeLie) (f g : QuantumTest) :
    GaussFockPair.sourcePair f (localAction phi mu a g) = GaussFockPair.sourcePair (localAction phi mu a f) g := by
  rw [GaussFockPair.sourcePair_integral, GaussFockPair.sourcePair_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    (coefficient phi mu a z (g z)) = inner ℂ
    (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (coefficient phi mu a z (f z))) (g z)
  rw [coefficient_quantized]
  exact weighted_pair _ (localMatrix phi mu a z) (localMatrix_hermitian phi mu a z) (f z) (g z)

theorem localReader_selfAdjoint (phi : Localizer) (mu : Component) (a : NativeLie) :
    IsSelfAdjoint (localReader phi mu a) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hx : Set.EqOn (fun x => inner ℂ (localReader phi mu a x) y)
      (fun x => inner ℂ x (localReader phi mu a y)) (Core : Set H) := by
    intro x hx
    obtain ⟨f,hf⟩ := embed_surjective_core ⟨x,hx⟩
    change embed f=x at hf
    rw [← hf]
    have hy : Set.EqOn (fun y => inner ℂ (localReader phi mu a (embed f)) y)
        (fun y => inner ℂ (embed f) (localReader phi mu a y)) (Core : Set H) := by
      intro y hy
      obtain ⟨g,hg⟩ := embed_surjective_core ⟨y,hy⟩
      change embed g=y at hg
      rw [← hg]
      dsimp only
      rw [localReader_core, localReader_core]
      exact (localAction_pair phi mu a f g).symm
    exact hy.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense y)
  exact hx.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense x)

/-- This is the unlocalized source current on its original smooth core. -/
def sourceAction (mu : Component) (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (sourceCurrent mu a) (sourceCurrent_smooth mu a)

theorem localAction_apply (phi : Localizer) (mu : Component) (a : NativeLie) (f : QuantumTest)
    (z : SourceCoordinateSlice) : localAction phi mu a f z = (phi z : ℂ) • sourceAction mu a f z := rfl

theorem localAction_exact (phi : Localizer) (mu : Component) (a : NativeLie) (f : QuantumTest)
    (covers : ∀ z ∈ tsupport f, phi z=1) : localAction phi mu a f = sourceAction mu a f := by
  apply DFunLike.ext
  intro z
  rw [localAction_apply]
  by_cases inside : z ∈ tsupport f
  · rw [covers z inside, Complex.ofReal_one, one_smul]
  · change (phi z : ℂ) • sourceCurrent mu a z (f z) = sourceCurrent mu a z (f z)
    rw [image_eq_zero_of_notMem_tsupport inside, map_zero, smul_zero]


/-- Any original core test generates a compact chart localizer that exactly
recovers the unlocalized current on that test. -/
theorem coreLocalizer_exists (f : QuantumTest) :
    ∃ phi : Localizer, (∀ z ∈ tsupport f, phi z=1) ∧ (∀ z, phi z ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨K, compact, covers, inside⟩ := exists_compact_between f.hasCompactSupport physicalChart.isOpen f.tsupport_subset
  obtain ⟨phi, one, zero, bounded⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ, SourceCoordinateSlice)) (n := (⊤ : ℕ∞)) (isClosed_tsupport f) covers
  have support : tsupport phi ⊆ K := by
    apply closure_minimal _ compact.isClosed
    intro z hz
    by_contra outside
    exact hz (zero z outside)
  refine ⟨⟨phi, phi.contMDiff.contDiff, compact.of_isClosed_subset isClosed_closure support,
    support.trans inside⟩, ?_, bounded⟩
  intro z hz
  exact one.self_of_nhdsSet z hz

def coreLocalizer (f : QuantumTest) : Localizer := (coreLocalizer_exists f).choose

theorem coreLocalizer_one (f : QuantumTest) : ∀ z ∈ tsupport f, coreLocalizer f z=1 :=
  (coreLocalizer_exists f).choose_spec.1

theorem localReader_original_core (mu : Component) (a : NativeLie) (f : QuantumTest) :
    localReader (coreLocalizer f) mu a (embed f) = embed (sourceAction mu a f) := by
  rw [localReader_core, localAction_exact _ _ _ f (coreLocalizer_one f)]


open SourceFamilyOperator
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _

def localTime (phi : Localizer) (mu : Component) (a : NativeLie) (parameter t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (CanonicalGradedVariation.timeFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (localReader phi mu a) (localReader_selfAdjoint phi mu a) parameter t)

def localVariation (phi : Localizer) (mu : Component) (a : NativeLie) (t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (CanonicalGradedVariation.variationFamily GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (localReader phi mu a) t)

theorem localTime_zero_parameter (phi : Localizer) (mu : Component) (a : NativeLie) (t : ℝ) :
    localTime phi mu a 0 t=GaussGradedUnitary.time t := by
  apply lift_congr sourceFilter
  intro F
  simp only [CanonicalGradedVariation.timeFamily, GaussGradedUnitary.finiteTime, zero_smul, add_zero]

theorem localTime_derivative (phi : Localizer) (mu : Component) (a : NativeLie) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => localTime phi mu a parameter t) (localVariation phi mu a t) 0 :=
  CanonicalGradedVariation.lifted_parameter_derivative sourceFilter GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (localReader phi mu a) (localReader_selfAdjoint phi mu a) t

theorem localTime_remainder (phi : Localizer) (mu : Component) (a : NativeLie) (parameter t : ℝ) :
    ‖localTime phi mu a parameter t-GaussGradedUnitary.time t-parameter • localVariation phi mu a t‖ ≤
      (|t| * bound phi mu a)^2*‖parameter‖^2 := by
  have generated := CanonicalGradedVariation.lifted_parameter_remainder sourceFilter GaussGradedCompression.compression
    GaussGradedCompression.compression_selfAdjoint (localReader phi mu a) (localReader_selfAdjoint phi mu a) parameter t
  rw [show lift sourceFilter (CanonicalGradedVariation.timeFamily GaussGradedCompression.compression
      GaussGradedCompression.compression_selfAdjoint (localReader phi mu a) (localReader_selfAdjoint phi mu a) 0 t) =
      GaussGradedUnitary.time t from localTime_zero_parameter phi mu a t] at generated
  apply generated.trans
  gcongr
  exact localReader_norm phi mu a

theorem localReader_history_blocks (phi : Localizer) (mu : Component) (a : NativeLie) :
    Commute historyProjection (reader (localReader phi mu a)) := by
  show reader sourceProjection*reader (localReader phi mu a) = reader (localReader phi mu a)*reader sourceProjection
  rw [← GaussUnitaryHistory.reader_mul, ← GaussUnitaryHistory.reader_mul]
  exact congrArg reader (localReader_blocks phi mu a sourceLabel).eq

private theorem perturbed_projection (phi : Localizer) (mu : Component) (a : NativeLie)
    (parameter : ℝ) (F : GaussUnitaryHistory.Index) :
    Commute sourceProjection (GaussGradedCompression.compression F+parameter • localReader phi mu a) := by
  apply ContinuousLinearMap.ext
  intro x
  have hc := congrArg (fun T : H →L[ℂ] H => T x) (GaussGradedCompression.compression_commutes F sourceLabel).eq
  have hb := congrArg (fun T : H →L[ℂ] H => T x) (localReader_blocks phi mu a sourceLabel).eq
  change sourceProjection (GaussGradedCompression.compression F x)=GaussGradedCompression.compression F (sourceProjection x) at hc
  change sourceProjection (localReader phi mu a x)=localReader phi mu a (sourceProjection x) at hb
  change sourceProjection (GaussGradedCompression.compression F x+parameter • localReader phi mu a x)=
    GaussGradedCompression.compression F (sourceProjection x)+parameter • localReader phi mu a (sourceProjection x)
  rw [map_add, LinearMapClass.map_smul_of_tower, hc, hb]

theorem full_finite_return (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) (F : GaussUnitaryHistory.Index) :
    sourceProjection*SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • localReader phi mu a+FullYSourceCutoffVolterra.cutoff cut) t =
    sourceProjection*SourceFiniteUnitary.time (GaussGradedCompression.compression F+parameter • localReader phi mu a) t :=
  CanonicalGradedGaugeReturn.left_time_return _ _ sourceProjection
    (perturbed_projection phi mu a parameter F) (CanonicalGradedGaugeReturn.cutoff_projection cut) t

/-- Every finite component retains the original literal Yukawa cutoff. -/
def fullProjectedFamily (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : Operator GaussUnitaryHistory.Index H where
  component F := sourceProjection*SourceFiniteUnitary.time
    (GaussGradedCompression.compression F+parameter • localReader phi mu a+FullYSourceCutoffVolterra.cutoff cut) t
  bounded := ⟨1, zero_le_one, fun F x => by
    rw [full_finite_return]
    change ‖sourceProjection (SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+parameter • localReader phi mu a) t x)‖ ≤ 1*‖x‖
    rw [one_mul]
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans_eq
      (SourceFiniteUnitary.time_norm _ ((GaussGradedCompression.compression_selfAdjoint F).add
        ((IsSelfAdjoint.all parameter).smul (localReader_selfAdjoint phi mu a))) t x)⟩

def fullProjectedTime (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullProjectedFamily phi mu a cut parameter t)

theorem fullProjectedTime_return (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (parameter t : ℝ) :
    fullProjectedTime phi mu a cut parameter t=historyProjection*localTime phi mu a parameter t := by
  change lift sourceFilter (fullProjectedFamily phi mu a cut parameter t) =
    lift sourceFilter (constant sourceProjection)*lift sourceFilter
      (CanonicalGradedVariation.timeFamily GaussGradedCompression.compression GaussGradedCompression.compression_selfAdjoint
        (localReader phi mu a) (localReader_selfAdjoint phi mu a) parameter t)
  exact (lift_congr sourceFilter _ _ (fun F => full_finite_return phi mu a cut parameter t F)).trans
    (lift_comp sourceFilter _ _)

theorem fullProjectedTime_original (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (t : ℝ) :
    fullProjectedTime phi mu a cut 0 t=historyProjection*FullYSourceCutoffVolterra.sourceEvolution cut t := by
  rw [fullProjectedTime_return, localTime_zero_parameter, cutoff_left_return]

theorem fullProjectedTime_derivative (phi : Localizer) (mu : Component) (a : NativeLie)
    (cut : ℕ) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => fullProjectedTime phi mu a cut parameter t)
      (historyProjection*localVariation phi mu a t) 0 := by
  simp only [fullProjectedTime_return]
  exact (localTime_derivative phi mu a t).const_mul historyProjection

def currentOperator (phi psi : Localizer) (mu nu : Component) (a b : NativeLie) (parameter t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  localTime psi nu b parameter (-t)*reader (localReader phi mu a)*localTime psi nu b parameter t

def currentDerivative (phi psi : Localizer) (mu nu : Component) (a b : NativeLie) (t : ℝ) :
    HistorySpace →L[ℂ] HistorySpace :=
  localVariation psi nu b (-t)*reader (localReader phi mu a)*GaussGradedUnitary.time t+
    GaussGradedUnitary.time (-t)*reader (localReader phi mu a)*localVariation psi nu b t

theorem currentOperator_derivative (phi psi : Localizer) (mu nu : Component) (a b : NativeLie) (t : ℝ) :
    HasDerivAt (fun parameter : ℝ => currentOperator phi psi mu nu a b parameter t)
      (currentDerivative phi psi mu nu a b t) 0 := by
  have generated := ((localTime_derivative psi nu b (-t)).mul_const (reader (localReader phi mu a))).mul
    (localTime_derivative psi nu b t)
  simp only [localTime_zero_parameter] at generated
  convert generated using 1 <;> rfl

def currentObservation (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (parameter t : ℝ) (x y : HistorySpace) : ℂ :=
  inner ℂ (historyProjection x) (currentOperator phi psi mu nu a b parameter t (historyProjection y))

theorem currentObservation_derivative (phi psi : Localizer) (mu nu : Component) (a b : NativeLie)
    (t : ℝ) (x y : HistorySpace) :
    HasDerivAt (fun parameter : ℝ => currentObservation phi psi mu nu a b parameter t x y)
      (inner ℂ (historyProjection x) (currentDerivative phi psi mu nu a b t (historyProjection y))) 0 := by
  have generated := ((ContinuousLinearMap.apply ℂ HistorySpace (historyProjection y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (currentOperator_derivative phi psi mu nu a b t)
  convert (hasDerivAt_const (0 : ℝ) (historyProjection x)).inner ℂ generated using 1
  all_goals first | rfl | (simp only [inner_zero_left, add_zero]; rfl)

end LowEnergy.CanonicalGradedLocalCurrent
