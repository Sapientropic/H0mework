import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussScalarTransport
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussFockPair
import H0mework.Physics.LowEnergy.Quantum.SymmetricGraphClosure

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussMomentumAdjoint
open GaussCoreHilbert GaussCoreDifferential GaussScalarTransport GaussFockPair GaussDensityCore
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussLiveMomentum
open MeasureTheory Set
open scoped ContDiff Distributions

def transposeRows (v : Ambient) : QuantumTest →ₗ[ℂ] H where
  toFun f := WithLp.toLp 2 (fun word => scalarEmbed word.card
    (fieldTranspose word.card v (component word f)))
  map_add' f g := by
    apply PiLp.ext
    intro word
    change scalarEmbed word.card (fieldTranspose word.card v (component word (f+g))) = _
    rw [map_add, map_add, map_add]
    rfl
  map_smul' c f := by
    apply PiLp.ext
    intro word
    change scalarEmbed word.card (fieldTranspose word.card v (component word (c • f))) = _
    rw [map_smul, map_smul, map_smul]
    rfl

theorem transposeRows_mem (v : Ambient) (f : QuantumTest) : transposeRows v f ∈ Core := by
  intro word
  let test := fieldTranspose word.card v (component word f)
  exact ⟨test, scalarLp_ae word.card test, test.hasCompactSupport, test.contDiff, test.tsupport_subset⟩

def derivativeTranspose (v : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  coreEquiv.symm.toLinearMap.comp ((transposeRows v).codRestrict Core (transposeRows_mem v))

theorem transpose_embed (v : Ambient) (f : QuantumTest) :
    embed (derivativeTranspose v f) = transposeRows v f :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply ⟨transposeRows v f, transposeRows_mem v f⟩)

theorem component_directional (v : Ambient) (f : QuantumTest) (word : Occupation) :
    component word (directional v f) = fieldDerivative v (component word f) := by
  apply DFunLike.ext
  intro z
  let P : FockFiber →L[ℂ] ℂ := PiLp.proj 2 (fun _ : Occupation => ℂ) word
  let Q := P.restrictScalars ℝ
  have hf := (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt (x := z)
  have h := Q.hasFDerivAt.comp z hf
  rw [fieldDerivative_apply]
  change (fderiv ℝ f z (direction v z)) word = fderiv ℝ (Q ∘ f) z (direction v z)
  rw [h.fderiv]
  rfl

theorem derivative_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (directional v g) = sourcePair (derivativeTranspose v f) g := by
  unfold sourcePair
  rw [transpose_embed, PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  change inner ℂ (scalarEmbed word.card (component word f))
      (scalarEmbed word.card (component word (directional v g))) =
    inner ℂ (scalarEmbed word.card (fieldTranspose word.card v (component word f)))
      (scalarEmbed word.card (component word g))
  rw [component_directional, field_transpose_hilbert]

def adjoint (v : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  Complex.I • (derivativeTranspose v - connectionAction v)

theorem momentum_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (covariantMomentum v g) = sourcePair (adjoint v f) g := by
  have hd := derivative_pair v f g
  have hc := connection_pair_skew v f g
  calc
    sourcePair f (covariantMomentum v g) = (-Complex.I) *
        (sourcePair f (directional v g) + sourcePair f (connectionAction v g)) := by
      change inner ℂ (embed f) (embed ((-Complex.I) • (directional v g + connectionAction v g))) = _
      rw [map_smul, map_add, inner_smul_right, inner_add_right]
      rfl
    _ = (-Complex.I) * (sourcePair (derivativeTranspose v f) g - sourcePair (connectionAction v f) g) := by
      rw [hd]
      have he := eq_neg_of_add_eq_zero_right hc
      rw [he, sub_eq_add_neg]
    _ = sourcePair (adjoint v f) g := by
      change _ = inner ℂ (embed (Complex.I • (derivativeTranspose v f - connectionAction v f))) (embed g)
      rw [map_smul, map_sub, inner_smul_left, inner_sub_left]
      simp only [Complex.conj_I]
      rfl

def realizedAdjoint (v : Ambient) : H →ₗ.[ℂ] H := realize (adjoint v)

theorem realized_pair (v : Ambient) (f g : Core) :
    inner ℂ (momentum v f) (g : H) = inner ℂ (f : H) (realizedAdjoint v g) := by
  obtain ⟨f, rfl⟩ := coreEquiv.surjective f
  obtain ⟨g, rfl⟩ := coreEquiv.surjective g
  have h := congrArg (starRingEnd ℂ) (momentum_pair v g f)
  change (starRingEnd ℂ) (inner ℂ (embed g) (embed (covariantMomentum v f))) =
    (starRingEnd ℂ) (inner ℂ (embed (adjoint v g)) (embed f)) at h
  rw [inner_conj_symm, inner_conj_symm] at h
  rw [momentum_on_test]
  change inner ℂ (embed (covariantMomentum v f)) (embed g) =
    inner ℂ (embed f) (embed (adjoint v (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply]
  exact h

theorem original_formal_adjoint (v : Ambient) :
    SymmetricGraphClosure.FormalAdjointPair (momentum v) (realizedAdjoint v) :=
  realized_pair v

#print axioms component_directional
#print axioms derivative_pair
#print axioms momentum_pair
#print axioms original_formal_adjoint
end LowEnergy.GaussMomentumAdjoint
