import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussNativeForm

/-! Ordinary coframe derivatives and their original Number-weighted adjoints. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussCoframeCore
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussDensityCore
open GaussScalarTransport GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates
open scoped ContDiff Distributions

def derivative (v : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v).toLinearMap

def transposeRows (v : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] H where
  toFun f := WithLp.toLp 2 (fun word => scalarEmbed word.card
    (weightedTranspose word.card v (component word f)))
  map_add' f g := by
    apply PiLp.ext
    intro word
    change scalarEmbed word.card (weightedTranspose word.card v (component word (f+g))) = _
    rw [map_add, map_add, map_add]
    rfl
  map_smul' c f := by
    apply PiLp.ext
    intro word
    change scalarEmbed word.card (weightedTranspose word.card v (component word (c • f))) = _
    rw [map_smul, map_smul, map_smul]
    rfl

theorem transposeRows_mem (v : SourceCoordinateSlice) (f : QuantumTest) : transposeRows v f ∈ Core := by
  intro word
  let test := weightedTranspose word.card v (component word f)
  exact ⟨test, scalarLp_ae word.card test, test.hasCompactSupport, test.contDiff, test.tsupport_subset⟩

def transpose (v : SourceCoordinateSlice) : QuantumTest →ₗ[ℂ] QuantumTest :=
  coreEquiv.symm.toLinearMap.comp ((transposeRows v).codRestrict Core (transposeRows_mem v))

theorem transpose_embed (v : SourceCoordinateSlice) (f : QuantumTest) :
    embed (transpose v f) = transposeRows v f :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply ⟨transposeRows v f, transposeRows_mem v f⟩)

theorem derivative_apply (v : SourceCoordinateSlice) (f : QuantumTest) (z : SourceCoordinateSlice) :
    derivative v f z = fderiv ℝ f z v := by
  change TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v f z = _
  rw [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le _ (by simp)]

theorem component_derivative (v : SourceCoordinateSlice) (f : QuantumTest) (word : Occupation) :
    component word (derivative v f) = GaussDensityCore.derivative v (component word f) := by
  apply DFunLike.ext
  intro z
  let P : FockFiber →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Occupation => ℂ) word
  let Q := P.restrictScalars ℝ
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
  have h := Q.hasFDerivAt.comp z hf
  rw [GaussDensityCore.derivative_apply]
  change derivative v f z word = _
  rw [derivative_apply]
  change (fderiv ℝ f z v) word = fderiv ℝ (Q ∘ f) z v
  rw [h.fderiv]
  rfl

theorem derivative_pair (v : SourceCoordinateSlice) (f g : QuantumTest) :
    sourcePair f (derivative v g) = sourcePair (transpose v f) g := by
  unfold sourcePair
  rw [transpose_embed, PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  change inner ℂ (scalarEmbed word.card (component word f))
      (scalarEmbed word.card (component word (derivative v g))) =
    inner ℂ (scalarEmbed word.card (weightedTranspose word.card v (component word f)))
      (scalarEmbed word.card (component word g))
  rw [component_derivative]
  exact weighted_transpose_hilbert word.card v (component word f) (component word g)

def coframeDirection (i : Fin 6) : SourceCoordinateSlice := (EuclideanSpace.single i 1,0)
def momentum (i : Fin 6) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (-Complex.I) • derivative (coframeDirection i)
def adjoint (i : Fin 6) : QuantumTest →ₗ[ℂ] QuantumTest :=
  Complex.I • transpose (coframeDirection i)

theorem momentum_pair (i : Fin 6) (f g : QuantumTest) :
    sourcePair f (momentum i g) = sourcePair (adjoint i f) g := by
  change inner ℂ (embed f) (embed ((-Complex.I) • derivative (coframeDirection i) g)) =
    inner ℂ (embed (Complex.I • transpose (coframeDirection i) f)) (embed g)
  rw [map_smul, map_smul, inner_smul_right, inner_smul_left]
  simp only [Complex.conj_I]
  congr 1
  exact derivative_pair _ f g

#print axioms component_derivative
#print axioms momentum_pair
end LowEnergy.GaussCoframeCore
