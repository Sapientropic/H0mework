import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiWholeVarianceGaussian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiDilationPrimitive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussDiagonalHistory
open SourceClockPhiCoframeForwardCore SourceClockPhiActualCovarianceStep SourceClockPhiCoframeForwardPair
open ClockPhiHeatCorrectedCovarianceSource ClockPhiConservativeHeatSource MeasureTheory Filter
open FirstCurrentClockPrimitiveSquare FirstCurrentDilationPrimitive SourceScalarDoubleCurrent
open ClockPhiHeatCorrectedHamiltonianSource PositiveClockGenerator
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev K(t:ℝ)(ht:0<t)(x:ℝ×ℝ):End:=correctedCompleteCore t ht x.1 x.2
private abbrev G(t:ℝ):End:=sourceGain (Real.sqrt t)
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev γ2:=γ.prod γ
attribute [local irreducible] sourcePair embed diagonalAction correctedCompleteCore
private theorem complete_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (K t ht x f) (K t ht x g)=sourcePair (G t f) (G t g):=by
  unfold K correctedCompleteCore correctedHeatCore
  change sourcePair (sourceForwardCore t ht.le (correctedProfileCore t ht x.1 x.2 (G t f)))
    (sourceForwardCore t ht.le (correctedProfileCore t ht x.1 x.2 (G t g)))=_
  rw [actual_forward_core_pair]
  exact clockProfileAction_pair _ _ _ _ _ _
private theorem pair_sub_l(f g h:QuantumTest):sourcePair (f-g) h=sourcePair f h-sourcePair g h:=by simp only[sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_r(f g h:QuantumTest):sourcePair f (g-h)=sourcePair f g-sourcePair f h:=by simp only[sourcePair,map_sub,inner_sub_right]

def actualClockDefect(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(w f:QuantumTest):QuantumTest:=
  diagonalAction (K t ht x w)-K t ht x f

def wholeSquaredMean(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∫x:ℝ×ℝ,sourcePair (G t (wholeVarianceColumn t ht x f)) (G t (wholeVarianceColumn t ht x g)) ∂γ2

def fullDefectMean(t:ℝ)(ht:0<t)(w f v g:QuantumTest):ℂ:=
  wholeSquaredMean t ht w v-wholePowerPair t ht w g-wholePowerPair t ht f v+
    sourcePair (G t f) (G t g)
private theorem H_square_mean(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair (diagonalAction (K t ht x f)) (diagonalAction (K t ht x g)) ∂γ2)=wholeSquaredMean t ht f g:=by
  unfold wholeSquaredMean
  apply integral_congr_ae
  exact Eventually.of_forall (fun x=>by dsimp only; rw [actual_whole_variance_column,actual_whole_variance_column,complete_pair])
private theorem H_mean(t:ℝ)(ht:0<t)(f g:QuantumTest):
    (∫x:ℝ×ℝ,sourcePair (K t ht x f) (diagonalAction (K t ht x g)) ∂γ2)=wholePowerPair t ht f g:=
  actual_corrected_hamiltonian_power_source t ht f g
private theorem defect_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(w f v g:QuantumTest):
    sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x v g)=
      sourcePair (diagonalAction (K t ht x w)) (diagonalAction (K t ht x v))-
      sourcePair (K t ht x w) (diagonalAction (K t ht x g))-
      sourcePair (K t ht x f) (diagonalAction (K t ht x v))+
      sourcePair (G t f) (G t g):=by
  unfold actualClockDefect
  rw [pair_sub_l,pair_sub_r,pair_sub_r,←diagonalAction_pair (K t ht x w) (K t ht x g),complete_pair]
  ring

/-- Both complete H0 legs and every original input defect have internally paid Gaussian L1;
the exact mean includes all ordered native/coframe covariance terms. -/
theorem actual_complete_source_defect_gaussian(t:ℝ)(ht:0<t)(w f v g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x v g)) γ2 ∧
    (∫x:ℝ×ℝ,sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x v g) ∂γ2)=
      fullDefectMean t ht w f v g:=by
  have hh:=actual_corrected_whole_H0_square_integrable t ht w v
  have hl:=(actual_corrected_hamiltonian_gaussian t ht w g).1
  have hr:=(actual_corrected_hamiltonian_gaussian t ht f v).1
  have hc:Integrable (fun _:ℝ×ℝ=>sourcePair (G t f) (G t g)) γ2:=integrable_const _
  refine ⟨(((hh.sub hl).sub hr).add hc).congr (Eventually.of_forall (fun x=>(defect_pair t ht x w f v g).symm)),?_⟩
  simp_rw [defect_pair]
  erw [integral_add ((hh.sub hl).sub hr) hc,integral_sub (hh.sub hl) hr,integral_sub hh hl]
  rw [H_square_mean,H_mean,H_mean,integral_const]
  simp only[MeasureTheory.probReal_univ,one_smul]
  rfl


/-- The full source variance is positive because it is the genuine Gaussian squared
forcing; positivity is produced after its integrability has been paid internally. -/
theorem actual_full_source_variance_nonnegative(t:ℝ)(ht:0<t)(w f:QuantumTest):
    0≤(fullDefectMean t ht w f w f).re:=by
  have h:=actual_complete_source_defect_gaussian t ht w f w f
  rw [←h.2]
  change 0≤RCLike.re (∫x:ℝ×ℝ,sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x w f) ∂γ2)
  rw [←integral_re h.1]
  apply integral_nonneg
  intro x
  change (0:ℝ)≤RCLike.re (sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x w f))
  simpa only[sourcePair] using inner_self_nonneg (𝕜:=ℂ) (x:=embed (actualClockDefect t ht x w f))

/-- The forcing is exactly the same full-H0 source transported through K, with its whole
commutator correction. The opposite pole is supplied by the same state, not a new occurrence. -/
theorem actual_full_source_clock_forcing(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(z:ℂ)(w f:QuantumTest)
    (he:diagonalAction w=f+z • w):
    actualClockDefect t ht x w (z • w)=K t ht x f+bracket diagonalAction (K t ht x) w ∧
    oppositeForcing z (K t ht x w) (actualClockDefect t ht x w (z • w))=
      actualClockDefect t ht x w (star z • w):=by
  constructor
  · unfold actualClockDefect bracket
    simp only[LinearMap.sub_apply,Module.End.mul_apply,he,map_add,map_smul]
    module
  · unfold oppositeForcing actualClockDefect
    simp only[map_smul]
    have hz:z-star z=2*(z.im:ℂ)*Complex.I:=by apply Complex.ext <;> simp;ring
    linear_combination (norm:=module) -(congrArg (fun c:ℂ=>c • K t ht x w) hz)

/-- The actual finite corrected-clock update of the whole squared source has an ordinary
Gaussian integral. No H0² generator or graph bound is supplied as a premise. -/
theorem actual_full_source_finite_variance_work(t:ℝ)(ht:0<t)(h:ℝ)(hh:0<h)(w f v g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>(h:ℂ)⁻¹*(
      sourcePair (actualClockDefect (t+h) (add_pos ht hh) x w f) (actualClockDefect (t+h) (add_pos ht hh) x v g)-
      sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x v g))) γ2 ∧
    (∫x:ℝ×ℝ,(h:ℂ)⁻¹*(
      sourcePair (actualClockDefect (t+h) (add_pos ht hh) x w f) (actualClockDefect (t+h) (add_pos ht hh) x v g)-
      sourcePair (actualClockDefect t ht x w f) (actualClockDefect t ht x v g)) ∂γ2)=
      (h:ℂ)⁻¹*(fullDefectMean (t+h) (add_pos ht hh) w f v g-fullDefectMean t ht w f v g):=by
  have h1:=actual_complete_source_defect_gaussian (t+h) (add_pos ht hh) w f v g
  have h0:=actual_complete_source_defect_gaussian t ht w f v g
  refine ⟨(h1.1.sub h0.1).const_mul _,?_⟩
  rw [integral_const_mul,integral_sub h1.1 h0.1,h1.2,h0.2]
end LowEnergy.FirstCurrentWholeVariance
