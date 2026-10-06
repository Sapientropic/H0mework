import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussFockLabel

/-! Actual Number/G projectors on the original complete smooth test core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussCoreLabel
open GaussFockLabel NativeHistoryGrade GaussCoreDifferential GaussCoreHilbert GaussFockPair
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert
open MeasureTheory
open scoped Distributions ContDiff

abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

def fiberPiece (g : Label) : FockFiber →L[ℂ] FockFiber :=
  blockWeight (fun l => if l = g then 1 else 0)

theorem fiberPiece_apply (g : Label) (f : FockFiber) (word : Occupation) :
    fiberPiece g f word = if sourceLabel word = g then f word else 0 := by
  by_cases h : sourceLabel word = g <;> simp [fiberPiece, blockWeight_apply, h]

def project (g : Label) : End := (TestFunction.postcompCLM (fiberPiece g)).toLinearMap

theorem project_apply (g : Label) (f : QuantumTest) (z : SourceCoordinateSlice) :
    project g f z = fiberPiece g (f z) := rfl

theorem embed_project (g : Label) (f : QuantumTest) :
    embed (project g f) = NativeHistoryGrade.projection g (embed f) := by
  apply PiLp.ext
  intro word
  apply Lp.ext
  filter_upwards [embed_ae (project g f) word, embed_ae f word,
    Lp.coeFn_zero ℂ 2 (GaussHistoryHilbert.numberMeasure word.card)] with z hp hf hz
  rw [hp, NativeHistoryGrade.projection_apply]
  change fiberPiece g (f z) word = _
  rw [fiberPiece_apply]
  by_cases h : sourceLabel word = g
  · simpa only [if_pos h] using hf.symm
  · simpa only [if_neg h, Pi.zero_apply] using hz.symm

theorem project_pair (g : Label) (f h : QuantumTest) :
    sourcePair f (project g h) = sourcePair (project g f) h := by
  simp only [sourcePair, embed_project]
  exact (projection_symmetric g (embed f) (embed h)).symm

theorem pair_separates (f g : QuantumTest) (equal : ∀ h, sourcePair h f = sourcePair h g) : f = g := by
  apply embed_injective
  have h := equal (f-g)
  change inner ℂ (embed (f-g)) (embed f) = inner ℂ (embed (f-g)) (embed g) at h
  rw [map_sub] at h
  have hz : inner ℂ (embed f-embed g) (embed f-embed g) = 0 := by
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℂ)).mp hz)

def Commutes (g : Label) (A : End) : Prop := ∀ f, project g (A f) = A (project g f)

theorem commutes_add (g : Label) {A B : End} (hA : Commutes g A) (hB : Commutes g B) :
    Commutes g (A+B) := by intro f; change project g (A f+B f) = _; rw [map_add, hA, hB]; rfl

theorem commutes_smul (g : Label) {A : End} (hA : Commutes g A) (c : ℂ) :
    Commutes g (c • A) := by intro f; change project g (c • A f) = _; rw [map_smul, hA]; rfl

theorem commutes_comp (g : Label) {A B : End} (hA : Commutes g A) (hB : Commutes g B) :
    Commutes g (A.comp B) := fun f => (hA (B f)).trans (congrArg A (hB f))

theorem commutes_sum {ι : Type*} [Fintype ι] (g : Label) {A : ι → End}
    (commutes : ∀ i, Commutes g (A i)) : Commutes g (∑ i, A i) := by
  intro f
  simp only [LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl (fun i _ => commutes i f)

theorem commutes_adjoint (g : Label) {A B : End} (hA : Commutes g A)
    (paired : ∀ f h, sourcePair f (B h) = sourcePair (A f) h) : Commutes g B := by
  intro f
  apply pair_separates
  intro h
  rw [project_pair, paired, ← hA, ← project_pair, ← paired]

theorem derivative_project (g : Label) (f : QuantumTest) (z v : SourceCoordinateSlice) :
    fderiv ℝ (project g f) z v = fiberPiece g (fderiv ℝ f z v) := by
  let P := (fiberPiece g).restrictScalars ℝ
  have h := P.hasFDerivAt.comp z ((f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt)
  change fderiv ℝ (P ∘ f) z v = _
  rw [h.fderiv]
  rfl

theorem commutes_directional (g : Label) (v : GaussLiveMomentum.Ambient) : Commutes g (directional v) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply, directional_apply, directional_apply, derivative_project]

theorem commutes_derivative (g : Label) (v : SourceCoordinateSlice) : Commutes g (GaussCoframeCore.derivative v) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply, GaussCoframeCore.derivative_apply, GaussCoframeCore.derivative_apply, derivative_project]

theorem commutes_real (g : Label) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) :
    Commutes g (GaussNativeForm.multiply c smooth) := by
  intro f
  apply DFunLike.ext
  intro z
  rw [project_apply, GaussNativeForm.multiply_apply, GaussNativeForm.multiply_apply, project_apply, map_smul]

theorem commutes_matrix (g : Label) (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => GaussQuantumMultiplier.quantized (A w)) z.val)
    (preserves : ∀ z, Preserves (A z)) : Commutes g (GaussQuantumMultiplier.action A smooth) := by
  intro f
  apply DFunLike.ext
  intro z
  exact congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (f z))
    (blockWeight_quantized (fun l => if l = g then 1 else 0) (A z) (preserves z)).eq

#print axioms embed_project
#print axioms commutes_adjoint
#print axioms commutes_matrix
end LowEnergy.GaussCoreLabel
