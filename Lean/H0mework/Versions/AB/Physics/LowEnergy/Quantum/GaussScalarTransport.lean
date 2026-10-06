import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussDensityCore

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussScalarTransport
open GaussDensityCore GaussHistoryHilbert GaussLiveMomentum GaussCoreDifferential
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open MeasureTheory Set
open scoped ContDiff Distributions

abbrev FrameIndex := Fin (Module.finrank ℝ SourceCoordinateSlice)
def frame : Module.Basis FrameIndex ℝ SourceCoordinateSlice := Module.finBasis ℝ SourceCoordinateSlice

def coefficient (v : Ambient) (i : FrameIndex) (z : SourceCoordinateSlice) : ℝ :=
  frame.coord i (direction v z)

theorem coefficient_smooth (v : Ambient) (i : FrameIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (fun w => (coefficient v i w : ℂ)) z.val :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp z.val
    ((frame.coord i).toContinuousLinearMap.contDiff.contDiffAt.comp z.val (direction_smooth v z))

def multiplyCoefficient (v : Ambient) (i : FrameIndex) : ScalarTest →ₗ[ℂ] ScalarTest :=
  multiply (fun z => (coefficient v i z : ℂ)) (coefficient_smooth v i)

def fieldDerivative (v : Ambient) : ScalarTest →ₗ[ℂ] ScalarTest :=
  ∑ i : FrameIndex, (multiplyCoefficient v i).comp (derivative (frame i))

def fieldTranspose (N : ℕ) (v : Ambient) : ScalarTest →ₗ[ℂ] ScalarTest :=
  ∑ i : FrameIndex, (weightedTranspose N (frame i)).comp (multiplyCoefficient v i)

private def evaluation (z : SourceCoordinateSlice) : ScalarTest →ₗ[ℂ] ℂ where
  toFun f := f z
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem fieldDerivative_apply (v : Ambient) (f : ScalarTest) (z : SourceCoordinateSlice) :
    fieldDerivative v f z = fderiv ℝ f z (direction v z) := by
  change evaluation z ((∑ i : FrameIndex, (multiplyCoefficient v i).comp (derivative (frame i))) f) = _
  rw [LinearMap.sum_apply, map_sum]
  change (∑ i : FrameIndex, (coefficient v i z : ℂ) * derivative (frame i) f z) = _
  simp only [derivative_apply]
  calc
    _ = ∑ i : FrameIndex, fderiv ℝ f z (coefficient v i z • frame i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, RCLike.real_smul_eq_coe_mul (K := ℂ)]
      rfl
    _ = fderiv ℝ f z (∑ i : FrameIndex, coefficient v i z • frame i) :=
      (map_sum (fderiv ℝ f z) _ _).symm
    _ = _ := congrArg (fderiv ℝ f z) (frame.sum_repr (direction v z))

def scalarEmbed (N : ℕ) : ScalarTest →ₗ[ℂ] GaussHistoryHilbert.SectorHilbert N where
  toFun := GaussCoreHilbert.scalarLp N
  map_add' f g := by
    apply Lp.ext
    filter_upwards [GaussCoreHilbert.scalarLp_ae N (f+g), GaussCoreHilbert.scalarLp_ae N f,
      GaussCoreHilbert.scalarLp_ae N g,
      Lp.coeFn_add (GaussCoreHilbert.scalarLp N f) (GaussCoreHilbert.scalarLp N g)]
      with z hsum hf hg hadd
    rw [hsum, hadd, Pi.add_apply, hf, hg]
    rfl
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [GaussCoreHilbert.scalarLp_ae N (c • f), GaussCoreHilbert.scalarLp_ae N f,
      Lp.coeFn_smul c (GaussCoreHilbert.scalarLp N f)] with z hsum hf hsmul
    change GaussCoreHilbert.scalarLp N (c • f) z = (c • GaussCoreHilbert.scalarLp N f) z
    rw [hsum, hsmul, Pi.smul_apply, hf]
    rfl

theorem pair_sum_right {ι : Type*} [Fintype ι] (N : ℕ) (f : ScalarTest) (g : ι → ScalarTest) :
    pair N f (∑ i, g i) = ∑ i, pair N f (g i) := by
  simp only [← hilbert_pair]
  change inner ℂ (scalarEmbed N f) (scalarEmbed N (∑ i, g i)) =
    ∑ i, inner ℂ (scalarEmbed N f) (scalarEmbed N (g i))
  rw [map_sum, inner_sum]

theorem pair_sum_left {ι : Type*} [Fintype ι] (N : ℕ) (f : ι → ScalarTest) (g : ScalarTest) :
    pair N (∑ i, f i) g = ∑ i, pair N (f i) g := by
  simp only [← hilbert_pair]
  change inner ℂ (scalarEmbed N (∑ i, f i)) (scalarEmbed N g) =
    ∑ i, inner ℂ (scalarEmbed N (f i)) (scalarEmbed N g)
  rw [map_sum, sum_inner]

theorem coefficient_pair (N : ℕ) (v : Ambient) (i : FrameIndex) (f g : ScalarTest) :
    pair N f (multiplyCoefficient v i g) = pair N (multiplyCoefficient v i f) g := by
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  change complexDensity N z * star (f z) * ((coefficient v i z : ℂ) * g z) =
    complexDensity N z * star ((coefficient v i z : ℂ) * f z) * g z
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem field_transpose_pair (N : ℕ) (v : Ambient) (f g : ScalarTest) :
    pair N f (fieldDerivative v g) = pair N (fieldTranspose N v f) g := by
  rw [fieldDerivative, LinearMap.sum_apply, pair_sum_right,
    fieldTranspose, LinearMap.sum_apply, pair_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  change pair N f (multiplyCoefficient v i (derivative (frame i) g)) =
    pair N (weightedTranspose N (frame i) (multiplyCoefficient v i f)) g
  rw [coefficient_pair, weighted_transpose_pair]

theorem field_transpose_hilbert (N : ℕ) (v : Ambient) (f g : ScalarTest) :
    inner ℂ (scalarEmbed N f) (scalarEmbed N (fieldDerivative v g)) =
      inner ℂ (scalarEmbed N (fieldTranspose N v f)) (scalarEmbed N g) := by
  change inner ℂ (GaussCoreHilbert.scalarLp N f) (GaussCoreHilbert.scalarLp N (fieldDerivative v g)) =
    inner ℂ (GaussCoreHilbert.scalarLp N (fieldTranspose N v f)) (GaussCoreHilbert.scalarLp N g)
  rw [hilbert_pair, hilbert_pair, field_transpose_pair]

#print axioms fieldDerivative_apply
#print axioms field_transpose_hilbert
end LowEnergy.GaussScalarTransport
