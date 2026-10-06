import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalGradedSpatialSource
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalGradedKernel

/-! The physical Fourier principal at the live Gauss coframe is localized by
an original chart test. Its bounded extension is added to the same finite
C_F. It does not replace any configuration CCR term or the source filter. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedSpatial
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussQuantumMultiplier GaussFockLabel CanonicalGradedCurrent CanonicalGradedSpatialSource
open GaussHistoryHilbert (physicalChart)
open GaussUnitaryHistory (HistorySpace reader sourceFilter)
open Set Function MeasureTheory
open scoped Topology InnerProductSpace ContDiff Distributions Manifold
attribute [local instance] SourceRealScalarFock.branchOrder

abbrev Localizer := CanonicalGradedLocalCurrent.Localizer
abbrev FiberMap := FockFiber →L[ℂ] FockFiber

/-- Every coframe coefficient is read at the integration configuration. -/
def sourceMomentum (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberMap :=
  quantized (momentumMatrix z p)

theorem sourceMomentum_smooth (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceMomentum p) z.val := by
  have term (i b : Fin 3) : ContDiffAt ℝ ∞
      (fun w => ((p i*GaussMatterCore.coefficient i b w : ℝ) : ℂ) •
        quantized (GaussCoframeSpin.full (Fin.castAdd 4 b))) z.val :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
      ((contDiffAt_const (c := p i)).mul (GaussMatterCore.coefficient_smooth i b z))).smul contDiffAt_const
  have generated := (ContDiffAt.sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    ContDiffAt.sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin 3))) => term i b))).neg
  convert generated using 1
  funext w
  change quantizer (-∑ i : Fin 3, ∑ b : Fin 3, ((p i*GaussMatterCore.coefficient i b w : ℝ) : ℂ) •
    GaussCoframeSpin.full (Fin.castAdd 4 b)) = _
  rw [map_neg, map_sum]
  simp only [map_sum, map_smul]
  rfl

def coefficient (phi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice) : FiberMap :=
  (phi z : ℂ) • sourceMomentum p z

theorem coefficient_zero_outside (phi : Localizer) (p : PhysicalMomentum)
    (z : SourceCoordinateSlice) (outside : z ∉ tsupport phi) : coefficient phi p z = 0 := by
  rw [coefficient, image_eq_zero_of_notMem_tsupport outside, Complex.ofReal_zero]
  apply ContinuousLinearMap.ext
  intro v
  exact _root_.zero_smul ℂ (sourceMomentum p z v)

theorem coefficient_support (phi : Localizer) (p : PhysicalMomentum) :
    tsupport (coefficient phi p) ⊆ tsupport phi := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra outside
  exact hz (coefficient_zero_outside phi p z outside)

theorem coefficient_smooth (phi : Localizer) (p : PhysicalMomentum) :
    ContDiff ℝ ∞ (coefficient phi p) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport phi
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z phi.contDiff.contDiffAt).smul
      (sourceMomentum_smooth p ⟨z, phi.tsupport_subset hz⟩)
  · apply (contDiffAt_const (c := (0 : FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport phi).isOpen_compl.mem_nhds hz] with w hw
    exact coefficient_zero_outside phi p w hw

def coefficientTest (phi : Localizer) (p : PhysicalMomentum) : 𝓓(physicalChart, FiberMap) where
  toFun := coefficient phi p
  contDiff' := coefficient_smooth phi p
  hasCompactSupport' := phi.hasCompactSupport.of_isClosed_subset isClosed_closure (coefficient_support phi p)
  tsupport_subset' := (coefficient_support phi p).trans phi.tsupport_subset

def bound (phi : Localizer) (p : PhysicalMomentum) : ℝ :=
  ‖(coefficientTest phi p : BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

theorem bound_nonnegative (phi : Localizer) (p : PhysicalMomentum) : 0 ≤ bound phi p := by
  exact norm_nonneg (coefficientTest phi p : BoundedContinuousFunction SourceCoordinateSlice FiberMap)

theorem coefficient_bound (phi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice)
    (v : FockFiber) : ‖coefficient phi p z v‖ ≤ bound phi p*‖v‖ := by
  have generated := (coefficientTest phi p : BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z
  exact ((coefficient phi p z).le_opNorm v).trans (mul_le_mul_of_nonneg_right generated (norm_nonneg v))

theorem coefficient_weights (phi : Localizer) (p : PhysicalMomentum)
    (z : SourceCoordinateSlice) (w : ℕ → ℂ) : Commute (GaussFockWeights.weight w) (coefficient phi p z) :=
  (weight_commute w (momentumMatrix z p)).smul_right (phi z : ℂ)

def localAction (phi : Localizer) (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (coefficient phi p) (fun _ => (coefficient_smooth phi p).contDiffAt)

def momentumReader (phi : Localizer) (p : PhysicalMomentum) : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (coefficient phi p) (fun _ => (coefficient_smooth phi p).contDiffAt)
    (fun z w => coefficient_weights phi p z w) (bound phi p) (bound_nonnegative phi p)
    (fun z => coefficient_bound phi p z)

theorem momentumReader_core (phi : Localizer) (p : PhysicalMomentum) (f : QuantumTest) :
    momentumReader phi p (embed f) = embed (localAction phi p f) :=
  GaussBoundedMultiplier.extension_core (coefficient phi p) (fun _ => (coefficient_smooth phi p).contDiffAt)
    (fun z w => coefficient_weights phi p z w) (bound phi p) (bound_nonnegative phi p)
    (fun z => coefficient_bound phi p z) f

theorem momentumReader_norm (phi : Localizer) (p : PhysicalMomentum) :
    ‖momentumReader phi p‖ ≤ bound phi p :=
  GaussBoundedMultiplier.extension_norm (coefficient phi p) (fun _ => (coefficient_smooth phi p).contDiffAt)
    (fun z w => coefficient_weights phi p z w) (bound phi p) (bound_nonnegative phi p)
    (fun z => coefficient_bound phi p z)


def localMatrix (phi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    Matrix Mode Mode ℂ := (phi z : ℂ) • momentumMatrix z p

theorem coefficient_quantized (phi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    coefficient phi p z = quantized (localMatrix phi p z) :=
  (quantizer.map_smul (phi z : ℂ) (momentumMatrix z p)).symm

theorem localMatrix_hermitian (phi : Localizer) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    (localMatrix phi p z).conjTranspose = localMatrix phi p z := by
  rw [localMatrix, Matrix.conjTranspose_smul, momentumMatrix_hermitian,
    Complex.star_def, Complex.conj_ofReal]

theorem localAction_blocks (phi : Localizer) (p : PhysicalMomentum) (g : NativeHistoryGrade.Label) :
    GaussCoreLabel.Commutes g (localAction phi p) := by
  intro f
  apply DFunLike.ext
  intro z
  change GaussCoreLabel.fiberPiece g (coefficient phi p z (f z)) =
    coefficient phi p z (GaussCoreLabel.fiberPiece g (f z))
  rw [coefficient_quantized]
  exact congrArg (fun T : FiberMap => T (f z))
    (GaussFockLabel.blockWeight_quantized (fun l => if l=g then 1 else 0) (localMatrix phi p z)
      (preserves_smul (momentumMatrix_preserves z p) (phi z : ℂ))).eq

theorem momentumReader_blocks (phi : Localizer) (p : PhysicalMomentum) (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g) (momentumReader phi p) := by
  show NativeHistoryGrade.projection g*momentumReader phi p = momentumReader phi p*NativeHistoryGrade.projection g
  apply GaussYukawaGrade.core_ext
  intro f
  change NativeHistoryGrade.projection g (momentumReader phi p (embed f)) =
    momentumReader phi p (NativeHistoryGrade.projection g (embed f))
  rw [momentumReader_core, ← GaussCoreLabel.embed_project, ← GaussCoreLabel.embed_project, momentumReader_core]
  exact congrArg embed (localAction_blocks phi p g f)

theorem localAction_pair (phi : Localizer) (p : PhysicalMomentum) (f g : QuantumTest) :
    GaussFockPair.sourcePair f (localAction phi p g) = GaussFockPair.sourcePair (localAction phi p f) g := by
  rw [GaussFockPair.sourcePair_integral, GaussFockPair.sourcePair_integral]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (f z))
    (coefficient phi p z (g z)) = inner ℂ
    (GaussFockWeights.weight (fun N => GaussDensityCore.complexDensity N z) (coefficient phi p z (f z))) (g z)
  rw [coefficient_quantized]
  exact weighted_pair _ (localMatrix phi p z) (localMatrix_hermitian phi p z) (f z) (g z)

theorem momentumReader_selfAdjoint (phi : Localizer) (p : PhysicalMomentum) :
    IsSelfAdjoint (momentumReader phi p) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hx : Set.EqOn (fun x => inner ℂ (momentumReader phi p x) y)
      (fun x => inner ℂ x (momentumReader phi p y)) (Core : Set H) := by
    intro x hx
    obtain ⟨f,hf⟩ := embed_surjective_core ⟨x,hx⟩
    change embed f=x at hf
    rw [← hf]
    have hy : Set.EqOn (fun y => inner ℂ (momentumReader phi p (embed f)) y)
        (fun y => inner ℂ (embed f) (momentumReader phi p y)) (Core : Set H) := by
      intro y hy
      obtain ⟨g,hg⟩ := embed_surjective_core ⟨y,hy⟩
      change embed g=y at hg
      rw [← hg]
      dsimp only
      rw [momentumReader_core, momentumReader_core]
      exact (localAction_pair phi p f g).symm
    exact hy.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense y)
  exact hx.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense x)

/-- The original physical gradient acts on the original configuration core. -/
def sourceAction (p : PhysicalMomentum) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (sourceMomentum p) (sourceMomentum_smooth p)

theorem localAction_apply (phi : Localizer) (p : PhysicalMomentum) (f : QuantumTest)
    (z : SourceCoordinateSlice) : localAction phi p f z = (phi z : ℂ) • sourceAction p f z := rfl

theorem localAction_exact (phi : Localizer) (p : PhysicalMomentum) (f : QuantumTest)
    (covers : ∀ z ∈ tsupport f, phi z=1) : localAction phi p f = sourceAction p f := by
  apply DFunLike.ext
  intro z
  rw [localAction_apply]
  by_cases inside : z ∈ tsupport f
  · rw [covers z inside, Complex.ofReal_one, one_smul]
  · change (phi z : ℂ) • sourceMomentum p z (f z) = sourceMomentum p z (f z)
    rw [image_eq_zero_of_notMem_tsupport inside, map_zero, smul_zero]


theorem momentumReader_original_core (p : PhysicalMomentum) (f : QuantumTest) :
    momentumReader (CanonicalGradedLocalCurrent.coreLocalizer f) p (embed f) =
      embed (sourceAction p f) := by
  rw [momentumReader_core, localAction_exact _ _ f (CanonicalGradedLocalCurrent.coreLocalizer_one f)]

theorem localAction_zero (phi : Localizer) : localAction phi 0=0 := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phi z : ℂ) • (quantizer (momentumMatrix z 0) (f z)) = 0
  rw [momentumMatrix_zero, map_zero]
  simp only [zero_apply, smul_zero]

theorem localAction_add (phi : Localizer) (p k : PhysicalMomentum) :
    localAction phi (p+k)=localAction phi p+localAction phi k := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (phi z : ℂ) • (quantizer (momentumMatrix z (p+k)) (f z)) =
    (phi z : ℂ) • (quantizer (momentumMatrix z p) (f z))+
      (phi z : ℂ) • (quantizer (momentumMatrix z k) (f z))
  rw [momentumMatrix_add, map_add, add_apply, smul_add]

theorem momentumReader_zero (phi : Localizer) : momentumReader phi 0=0 := by
  apply GaussYukawaGrade.core_ext
  intro f
  rw [momentumReader_core, localAction_zero]
  simp only [LinearMap.zero_apply, map_zero, zero_apply]

theorem momentumReader_add (phi : Localizer) (p k : PhysicalMomentum) :
    momentumReader phi (p+k)=momentumReader phi p+momentumReader phi k := by
  apply GaussYukawaGrade.core_ext
  intro f
  change momentumReader phi (p+k) (embed f)=momentumReader phi p (embed f)+momentumReader phi k (embed f)
  rw [momentumReader_core, momentumReader_core, momentumReader_core, localAction_add,
    LinearMap.add_apply, map_add]

open SourceFamilyOperator SourceFiniteUnitary
open GaussUnitaryHistory (Index)
local instance : NormedAlgebra ℝ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (HistorySpace →L[ℂ] HistorySpace) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The complete configuration Hamiltonian is retained at every physical momentum. -/
def finiteHamiltonian (phi : Localizer) (p : PhysicalMomentum) (F : Index) : H →L[ℂ] H :=
  GaussGradedCompression.compression F+momentumReader phi p

theorem finiteHamiltonian_selfAdjoint (phi : Localizer) (p : PhysicalMomentum) (F : Index) :
    IsSelfAdjoint (finiteHamiltonian phi p F) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (GaussGradedCompression.compression F x+momentumReader phi p x) y =
    inner ℂ x (GaussGradedCompression.compression F y+momentumReader phi p y)
  rw [inner_add_left, inner_add_right]
  exact congrArg₂ HAdd.hAdd (GaussGradedCompression.compression_pair F x y)
    ((momentumReader_selfAdjoint phi p).isSymmetric x y)

theorem finiteHamiltonian_blocks (phi : Localizer) (p : PhysicalMomentum)
    (F : Index) (g : NativeHistoryGrade.Label) :
    Commute (NativeHistoryGrade.projection g) (finiteHamiltonian phi p F) :=
  (GaussGradedCompression.compression_commutes F g).add_right (momentumReader_blocks phi p g)

theorem finiteHamiltonian_zero (phi : Localizer) (F : Index) :
    finiteHamiltonian phi 0 F=GaussGradedCompression.compression F := by
  rw [finiteHamiltonian, momentumReader_zero, add_zero]

theorem finiteHamiltonian_shift (phi : Localizer) (p k : PhysicalMomentum) (F : Index) :
    finiteHamiltonian phi (p+k) F=finiteHamiltonian phi p F+momentumReader phi k := by
  rw [finiteHamiltonian, finiteHamiltonian, momentumReader_add, add_assoc]

def timeFamily (phi : Localizer) (p : PhysicalMomentum) (t : ℝ) : Operator Index H where
  component F := time (finiteHamiltonian phi p F) t
  bounded := ⟨1, zero_le_one, fun F x => by
    rw [time_norm _ (finiteHamiltonian_selfAdjoint phi p F), one_mul]⟩

def spatialTime (phi : Localizer) (p : PhysicalMomentum) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (timeFamily phi p t)

theorem spatialTime_zero (phi : Localizer) (t : ℝ) :
    spatialTime phi 0 t=GaussGradedUnitary.time t := by
  apply lift_congr sourceFilter
  intro F
  exact congrArg (fun C : H →L[ℂ] H => time C t) (finiteHamiltonian_zero phi F)

theorem full_finite_return (phi : Localizer) (p : PhysicalMomentum)
    (cut : ℕ) (t : ℝ) (F : Index) :
    sourceProjection*time (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut) t =
      sourceProjection*time (finiteHamiltonian phi p F) t :=
  CanonicalGradedGaugeReturn.left_time_return _ _ sourceProjection
    (finiteHamiltonian_blocks phi p F sourceLabel) (CanonicalGradedGaugeReturn.cutoff_projection cut) t

/-- The Yukawa term is included before the original grade-zero observation. -/
def fullTimeFamily (phi : Localizer) (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) : Operator Index H where
  component F := sourceProjection*time (finiteHamiltonian phi p F+FullYSourceCutoffVolterra.cutoff cut) t
  bounded := ⟨1, zero_le_one, fun F x => by
    rw [full_finite_return]
    change ‖sourceProjection (time (finiteHamiltonian phi p F) t x)‖ ≤ 1*‖x‖
    rw [one_mul]
    exact (NativeHistoryGrade.piece_bound sourceLabel _).trans_eq
      (time_norm _ (finiteHamiltonian_selfAdjoint phi p F) t x)⟩

def fullSpatialTime (phi : Localizer) (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (fullTimeFamily phi p cut t)

theorem fullSpatialTime_return (phi : Localizer) (p : PhysicalMomentum) (cut : ℕ) (t : ℝ) :
    fullSpatialTime phi p cut t=historyProjection*spatialTime phi p t :=
  (lift_congr sourceFilter _ (comp (constant sourceProjection) (timeFamily phi p t))
    (fun F => full_finite_return phi p cut t F)).trans (lift_comp sourceFilter _ _)

theorem fullSpatialTime_original (phi : Localizer) (cut : ℕ) (t : ℝ) :
    fullSpatialTime phi 0 cut t=historyProjection*FullYSourceCutoffVolterra.sourceEvolution cut t := by
  rw [fullSpatialTime_return, spatialTime_zero, cutoff_left_return]

#print axioms momentumReader_original_core
#print axioms finiteHamiltonian_selfAdjoint
#print axioms finiteHamiltonian_shift
#print axioms spatialTime_zero
#print axioms fullSpatialTime_return
end LowEnergy.CanonicalGradedSpatial
