import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.SourceQuantum.Gauge
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.PhysicsCore.YangMills.Flat.Quantum.Ward.Pure.Commutation
import H0mework.Versions.R7e4da746.Physics.CompositeSpectrum.Action

/-! The original independent dual gives the full mother insertion action.
Its generator-wise product recovers the actual cubic response and supplies the
accepted positive-energy excitation on the original filtered feature. -/

set_option autoImplicit false
open scoped InnerProductSpace Matrix
namespace SaturationMonoid.PhysicsCore.YangMills.NativeCurvature
open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair Stage9DEF
open StageNineHolonomicField FullPairing NativeSource Stage10.GaugeSpectrum
noncomputable section

def dualAction (M : Mother) : Mother := flipMatter.comp M

theorem dualAction_response (p : BasePoint) (M : Mother) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer p)
      (Compatibility.responseMatrix M) =
      inner ℂ (prepared p) (operator (dualAction M) (prepared p)) := by
  have generated := Stage10.Recovery.stageOneThroughTenClosure.final.stageNine.quantumClosure.sourceResponse p M
  have dual := dual_flip p (flipMatter (M (actual.matter p)))
  rw [flipMatter_twice, ← inner_embed] at dual
  change actual.conjugateMatter p (M (actual.matter p)) =
    2 * (spinScale : ℂ) *
      inner ℂ (prepared p) (naturalCoordinates (dualAction M (actual.matter p))) at dual
  rw [← operator_coordinates, actual_eq_twice_prepared, map_smul, inner_smul_right] at dual
  have read :
      actual.conjugateMatter p (M (actual.matter p)) =
        4 * (spinScale : ℂ) *
          inner ℂ (prepared p) (operator (dualAction M) (prepared p)) := by
    rw [dual]
    ring
  rw [read, Runtime.firstQuantumTick_answer, Runtime.fieldAt_eq_vector] at generated
  rw [Stage10.Runtime.tick_vector]
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0)
    (Complex.ofReal_ne_zero.mpr spinScale_pos.ne')) generated.symm

def dualProduct (A B : Mother) : Mother := A.comp (flipMatter.comp B)

theorem dualAction_product (A B : Mother) :
    dualAction (dualProduct A B) = (dualAction A).comp (dualAction B) := rfl

theorem dualAction_unit : dualAction flipMatter = LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact flipMatter_twice v

def quantumEvaluate (configuration : StageNineHolonomicConfiguration) :
    Flat.Quantum.History.Polynomial →ₐ[ℂ] Mother :=
  FreeAlgebra.lift ℂ (fun label => dualAction (Flat.Quantum.History.field configuration label))

theorem quantumEvaluate_generator (configuration : StageNineHolonomicConfiguration)
    (label : Flat.Quantum.History.Label) :
    quantumEvaluate configuration (FreeAlgebra.ι ℂ label) =
      dualAction (Flat.Quantum.History.field configuration label) :=
  FreeAlgebra.lift_ι_apply _ _

theorem quantum_generator_response (configuration : StageNineHolonomicConfiguration)
    (p : BasePoint) (label : Flat.Quantum.History.Label) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer p)
      (Compatibility.responseMatrix (Flat.Quantum.History.field configuration label)) =
        inner ℂ (prepared p)
          (operator (quantumEvaluate configuration (FreeAlgebra.ι ℂ label)) (prepared p)) := by
  rw [quantumEvaluate_generator]
  exact dualAction_response p _

theorem dualAction_composite_embed (p : BasePoint) (values : Source.Index → ℂ) :
    dualAction (compositeAction p) (Compatibility.embed values) =
      singletAction p (Compatibility.embed values) := by
  have singlet : singletAction p = (curvatureScale : ℂ)^3 • flipMatter := by
    apply LinearMap.ext
    intro matter
    funext spin
    rw [singletAction, cubicSpinMatrix_normalForm]
    fin_cases spin <;>
      simp [diracMatrixMatterAction, exchange, flipMatter, Compatibility.spinFlip, Fin.sum_univ_four]
  change flipMatter (compositeAction p (Compatibility.embed values)) = _
  rw [compositeAction_embed, rawCubic_normalForm, Matrix.smul_mulVec, Matrix.one_mulVec,
    map_smul, map_smul, singlet, LinearMap.smul_apply]

theorem dualAction_composite_feature (p : BasePoint) :
    operator (dualAction (compositeAction p)) normalizedFeature = NativeReadout.excitation p := by
  change operator (dualAction (compositeAction p))
    ((‖groundFeature‖⁻¹ : ℂ) • naturalCoordinates
      (Compatibility.embed (groundProjector *ᵥ Source.vector 0))) =
      operator (singletAction p)
    ((‖groundFeature‖⁻¹ : ℂ) • naturalCoordinates
      (Compatibility.embed (groundProjector *ᵥ Source.vector 0)))
  rw [map_smul, map_smul, operator_coordinates, operator_coordinates,
    dualAction_composite_embed]

private theorem flipMatter_eq :
    flipMatter = diracMatrixMatterAction StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap := by
  apply LinearMap.ext
  exact flipMatter_source

private theorem field_flip (configuration : StageNineHolonomicConfiguration)
    (label : Flat.Quantum.History.Label) :
    Commute flipMatter (Flat.Quantum.History.field configuration label) := by
  rw [flipMatter_eq]
  have paid := Ward.Pure.source_word_spin configuration
    StageNineFullDiracAdjointMaterial.diracAdjointSpinSwap (FreeAlgebra.ι ℂ label)
  rwa [Flat.Quantum.History.evaluate_generator] at paid

private theorem dualAction_triple (A B C : Mother) (commutes : Commute flipMatter B) :
    dualAction A * dualAction B * dualAction C = dualAction (A * B * C) := by
  apply LinearMap.ext
  intro v
  change flipMatter (A (flipMatter (B (flipMatter (C v))))) = flipMatter (A (B (C v)))
  have middle := LinearMap.congr_fun commutes.eq (flipMatter (C v))
  change flipMatter (B (flipMatter (C v))) = B (flipMatter (flipMatter (C v))) at middle
  rw [flipMatter_twice] at middle
  rw [middle]

private theorem dualAction_alternating (fields : Fin 3 → Mother)
    (commutes : ∀ i, Commute flipMatter (fields i)) :
    alternatingProduct (fun i => dualAction (fields i)) =
      dualAction (alternatingProduct fields) := by
  have triple (a b c : Fin 3) := dualAction_triple (fields a) (fields b) (fields c) (commutes b)
  unfold alternatingProduct
  simp only [triple]
  apply LinearMap.ext
  intro v
  simp [dualAction]

def curvatureCubic (p : BasePoint) : Flat.Quantum.History.Polynomial :=
  alternatingProduct (fun axis => FreeAlgebra.ι ℂ (p, magneticPair axis))

theorem quantumEvaluate_cubic (p : BasePoint) :
    quantumEvaluate actual (curvatureCubic p) = dualAction (compositeAction p) := by
  have generators (axis : Fin 3) :
      Flat.Quantum.History.field actual (p, magneticPair axis) =
        incomingCurvatureAction p axis := by
    rw [incomingCurvatureAction, Stage10.Runtime.configuration_eq]
    rfl
  have mapped :
      quantumEvaluate actual (curvatureCubic p) =
        alternatingProduct (fun axis => dualAction (incomingCurvatureAction p axis)) := by
    simp only [curvatureCubic, alternatingProduct, map_smul, map_sub, map_add, map_mul,
      quantumEvaluate_generator, generators]
  rw [mapped]
  apply dualAction_alternating
  intro axis
  rw [← generators]
  exact field_flip actual _


theorem quantum_cubic_response (p : BasePoint) :
    inner ℂ (prepared p)
        (operator (quantumEvaluate actual (curvatureCubic p)) (prepared p)) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer p) (cubic p) := by
  rw [quantumEvaluate_cubic, ← dualAction_response, compositeAction_responseMatrix]

def sourceExcitation (p : BasePoint) : Hilbert :=
  operator (quantumEvaluate actual (curvatureCubic p)) normalizedFeature

theorem sourceExcitation_eq (p : BasePoint) :
    sourceExcitation p = NativeReadout.excitation p := by
  rw [sourceExcitation, quantumEvaluate_cubic, dualAction_composite_feature]

theorem sourceExcitation_ne_zero (p : BasePoint) : sourceExcitation p ≠ 0 := by
  rw [sourceExcitation_eq]
  exact NativeReadout.excitation_ne_zero p

theorem sourceExcitation_energy (p : BasePoint) :
    Quantum.Generator.hamiltonianOperator time (point (sourceExcitation p)) +
      (frequency : ℂ) • sourceExcitation p =
        ((2 * frequency : ℝ) : ℂ) • sourceExcitation p := by
  rw [sourceExcitation_eq]
  exact NativeReadout.positive_energy p

theorem sourceExcitation_source_pair (p : BasePoint) :
    featureWitness.full
      (star (motherFamily (quantumEvaluate actual (curvatureCubic p))) *
        motherFamily (quantumEvaluate actual (curvatureCubic p))) =
      inner ℂ (sourceExcitation p) (sourceExcitation p) := by
  rw [featureWitness_source_pair, feature_source_pair]
  rfl

private theorem flip_apply (v : Hilbert) (i : FullPairing.Index) :
    operator flipMatter v i = v (Compatibility.spinFlip i.1, i.2) := by
  have read := operator_coordinates flipMatter (naturalCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at read
  rw [read]
  conv_rhs => rw [← naturalCoordinates.apply_symm_apply v]
  rw [naturalCoordinates_apply, naturalCoordinates_apply]
  rfl

private theorem flip_clock (t : ℝ) (v : Hilbert) :
    operator flipMatter (clock t v) = clock (-t) (operator flipMatter v) := by
  apply PiLp.ext
  intro i
  rw [flip_apply, clock_apply, clock_apply, flip_apply, spinRate_flip]
  congr 1
  simp [phase, Dynamics.timeDisplacement]

private theorem dualAction_clock (t : ℝ) (M : Mother) (v : Hilbert) :
    operator (dualAction
      ((diracMatrixMatterAction (clockMatrix (Dynamics.timeDisplacement t))).comp
        (M.comp (diracMatrixMatterAction (clockMatrix (Dynamics.timeDisplacement t)))))) v =
      clock (-t) (operator (dualAction M) (clock t v)) := by
  have transported := flip_clock t (operator M (clock t v))
  simpa [operator, dualAction, clock] using transported

theorem dualAction_physicalTime (p : BasePoint) (t : ℝ) (M : Mother) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer (p + Dynamics.timeDisplacement t))
        (Compatibility.responseMatrix M) =
      State.vectorEvaluation (Stage10.Runtime.tick.answer p)
        (Compatibility.responseMatrix
          ((diracMatrixMatterAction (clockMatrix (Dynamics.timeDisplacement t))).comp
            (M.comp (diracMatrixMatterAction (clockMatrix (Dynamics.timeDisplacement t)))))) := by
  rw [dualAction_response, dualAction_response, dualAction_clock]
  rw [← time_prepared p t]
  change inner ℂ (clock t (prepared p)) (operator (dualAction M) (clock t (prepared p))) =
    inner ℂ (prepared p) (clock (-t) (operator (dualAction M) (clock t (prepared p))))
  have preserved := (time (Multiplicative.ofAdd t)).inner_map_map (prepared p)
    (clock (-t) (operator (dualAction M) (clock t (prepared p))))
  change inner ℂ (clock t (prepared p))
    (clock t (clock (-t) (operator (dualAction M) (clock t (prepared p))))) = _ at preserved
  rw [← clock_add, add_neg_cancel, clock_zero] at preserved
  exact preserved

end
end SaturationMonoid.PhysicsCore.YangMills.NativeCurvature
