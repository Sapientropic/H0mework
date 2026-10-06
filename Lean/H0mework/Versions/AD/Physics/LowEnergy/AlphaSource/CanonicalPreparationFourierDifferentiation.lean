import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationFourierMomentumJet
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
noncomputable section
namespace LowEnergy.PreparationVacuumFourierJets
open PreparationVacuumWeyl PreparationVacuumWeylDecay CanonicalPreparationSquareCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap FourierTransform RealInnerProductSpace
attribute [local irreducible] symbolSlice jointSymbol partialFourier

-- Use the operator-norm topology on the same derivative-map carrier.
local instance derivativeTopology (n : ℕ) : TopologicalSpace (PhysicalMomentum →L[ℝ] MomentumJet n) :=
  (inferInstance : NormedAddCommGroup (PhysicalMomentum →L[ℝ] MomentumJet n)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance derivativePseudoMetrizable (n : ℕ) :
    TopologicalSpace.PseudoMetrizableSpace (PhysicalMomentum →L[ℝ] MomentumJet n) := by
  infer_instance

def jetCurry (n : ℕ) : MomentumJet (n+1) ≃ₗᵢ[ℝ] (PhysicalMomentum →L[ℝ] MomentumJet n) :=
  continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => PhysicalMomentum) ℂ

theorem sourceMomentumJet_hasFDerivAt (n : ℕ) (x p : PhysicalMomentum) :
    HasFDerivAt (fun q : PhysicalMomentum => sourceMomentumJet n (x,q))
      (jetCurry n (sourceMomentumJet (n+1) (x,p))) p := by
  have smooth : ContDiff ℝ ∞ (fun q : PhysicalMomentum => symbolSlice q x) := by
    have same : (fun q : PhysicalMomentum => symbolSlice q x)=(fun q => jointSymbol (x,q)) := by
      funext q
      simp only [jointSymbol]
    rw [same]
    exact jointSymbol_smooth.comp (contDiff_const.prodMk contDiff_id)
  have differential := (smooth.differentiable_iteratedFDeriv
    (by exact_mod_cast ENat.natCast_lt_top n) p).hasFDerivAt
  simpa only [sourceMomentumJet,fderiv_iteratedFDeriv,Function.comp_apply,jetCurry] using differential

def phaseJet (n : ℕ) (k q x : PhysicalMomentum) : MomentumJet n :=
  𝐞 (-⟪x,k⟫) • sourceMomentumJet n (x,q)

def phaseJetDerivative (n : ℕ) (k q x : PhysicalMomentum) : PhysicalMomentum →L[ℝ] MomentumJet n :=
  𝐞 (-⟪x,k⟫) • jetCurry n (sourceMomentumJet (n+1) (x,q))

theorem phaseJet_hasFDerivAt (n : ℕ) (k x q : PhysicalMomentum) :
    HasFDerivAt (fun p => phaseJet n k p x) (phaseJetDerivative n k q x) q := by
  simpa only [phaseJet,phaseJetDerivative,Circle.smul_def] using!
    (sourceMomentumJet_hasFDerivAt n x q).const_smul (𝐞 (-⟪x,k⟫) : ℂ)

theorem jetCurry_circle (n : ℕ) (c : Circle) (f : MomentumJet (n+1)) :
    jetCurry n (c • f)=c • jetCurry n f := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousMultilinearMap.ext
  intro w
  simp only [jetCurry,continuousMultilinearCurryLeftEquiv_apply,Circle.smul_def,smul_apply]

theorem phaseJetDerivative_norm (n : ℕ) (k q x : PhysicalMomentum) :
    ‖phaseJetDerivative n k q x‖=‖sourceMomentumJet (n+1) (x,q)‖ := by
  calc
    _ = ‖jetCurry n (𝐞 (-⟪x,k⟫) • sourceMomentumJet (n+1) (x,q))‖ :=
      congrArg norm (jetCurry_circle n (𝐞 (-⟪x,k⟫)) (sourceMomentumJet (n+1) (x,q))).symm
    _ = ‖𝐞 (-⟪x,k⟫) • sourceMomentumJet (n+1) (x,q)‖ := (jetCurry n).norm_map _
    _ = _ := by
      with_unfolding_all
        exact Circle.norm_smul (𝐞 (-⟪x,k⟫)) (sourceMomentumJet (n+1) (x,q))

def localJetCompact (p : PhysicalMomentum) : Set (PhysicalMomentum × PhysicalMomentum) :=
  positionCompact ×ˢ Metric.closedBall p 1

theorem localJetCompact_compact (p : PhysicalMomentum) : IsCompact (localJetCompact p) :=
  positionCompact_compact.prod (isCompact_closedBall _ _)

theorem localJetBound_exists (n : ℕ) (p : PhysicalMomentum) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ xp∈localJetCompact p, ‖sourceMomentumJet (n+1) xp‖ ≤ bound := by
  have continuous : Continuous (fun xp => ‖sourceMomentumJet (n+1) xp‖) :=
    (sourceMomentumJet_smooth (n+1)).continuous.norm
  obtain ⟨bound,hbound⟩ := (localJetCompact_compact p).bddAbove_image continuous.continuousOn
  refine ⟨max bound 0,le_max_right _ _,?_⟩
  intro xp hx
  exact (hbound (mem_image_of_mem _ hx)).trans (le_max_left _ _)

def localJetBound (n : ℕ) (p : PhysicalMomentum) : ℝ := Classical.choose (localJetBound_exists n p)

theorem localJetBound_nonnegative (n : ℕ) (p : PhysicalMomentum) : 0 ≤ localJetBound n p :=
  (Classical.choose_spec (localJetBound_exists n p)).1

def localJetMajorant (n : ℕ) (p : PhysicalMomentum) : PhysicalMomentum → ℝ :=
  positionCompact.indicator (fun _ => localJetBound n p)

theorem localJetMajorant_integrable (n : ℕ) (p : PhysicalMomentum) :
    Integrable (localJetMajorant n p) (volume : Measure PhysicalMomentum) :=
  (integrableOn_const positionCompact_compact.measure_ne_top).integrable_indicator positionCompact_closed.measurableSet

theorem phaseJetDerivative_norm_bound (n : ℕ) (p k x q : PhysicalMomentum)
    (nearby : q∈Metric.closedBall p 1) : ‖phaseJetDerivative n k q x‖ ≤ localJetMajorant n p x := by
  by_cases inside : x∈positionCompact
  · rw [phaseJetDerivative_norm,localJetMajorant,indicator_of_mem inside]
    exact (Classical.choose_spec (localJetBound_exists n p)).2 (x,q) ⟨inside,nearby⟩
  · rw [phaseJetDerivative_norm,sourceMomentumJet_zero_outside (n+1) q x inside,norm_zero,
      localJetMajorant,indicator_of_notMem inside]

theorem phaseJetDerivative_continuous (n : ℕ) (p k : PhysicalMomentum) :
    Continuous (phaseJetDerivative n k p) := by
  have phase : Continuous (fun x : PhysicalMomentum => -⟪x,k⟫) :=
    (continuous_id.inner continuous_const).neg
  have whole : Continuous (fun x : PhysicalMomentum => phaseJet (n+1) k p x) :=
    (continuous_subtype_val.comp (Real.continuous_fourierChar.comp phase)).smul
      (sourceMomentumJet_x_smooth (n+1) p).continuous
  have same : phaseJetDerivative n k p=(fun x : PhysicalMomentum => jetCurry n (phaseJet (n+1) k p x)) := by
    funext x
    simp only [phaseJetDerivative,phaseJet,jetCurry_circle]
  rw [same]
  exact (jetCurry n).continuous.comp whole

theorem phaseJetDerivative_integral (n : ℕ) (p k : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,phaseJetDerivative n k p x)=jetCurry n (partialFourierJet (n+1) p k) := by
  rw [partialFourierJet_literal]
  have commute : (∫ x : PhysicalMomentum,jetCurry n (phaseJet (n+1) k p x))=
      jetCurry n (∫ x : PhysicalMomentum,phaseJet (n+1) k p x) := by
    with_unfolding_all
      exact (jetCurry n).toLinearIsometry.integral_comp_comm (𝕜 := ℝ)
        (E := MomentumJet (n+1)) (F := PhysicalMomentum →L[ℝ] MomentumJet n) (phaseJet (n+1) k p)
  calc
    _ = ∫ x : PhysicalMomentum,jetCurry n (phaseJet (n+1) k p x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [phaseJetDerivative,phaseJet,jetCurry_circle]
    _ = _ := commute

theorem partialFourierJet_hasFDerivAt (n : ℕ) (p k : PhysicalMomentum) :
    HasFDerivAt (fun q : PhysicalMomentum => partialFourierJet n q k)
      (jetCurry n (partialFourierJet (n+1) p k)) p := by
  have lower := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun q x => phaseJet n k q x) (F' := fun q x => phaseJetDerivative n k q x)
    (bound := localJetMajorant n p) (s := Metric.closedBall p 1)
    (Metric.closedBall_mem_nhds p (by norm_num))
    (Eventually.of_forall (fun q => (partialFourierJet_integrable n q k).aestronglyMeasurable))
    (partialFourierJet_integrable n p k)
    (phaseJetDerivative_continuous n p k).aestronglyMeasurable
    (Eventually.of_forall (fun x q hq => phaseJetDerivative_norm_bound n p k x q hq))
    (localJetMajorant_integrable n p)
    (Eventually.of_forall (fun x q _ => phaseJet_hasFDerivAt n k x q))
  rw [phaseJetDerivative_integral] at lower
  exact lower

end LowEnergy.PreparationVacuumFourierJets
