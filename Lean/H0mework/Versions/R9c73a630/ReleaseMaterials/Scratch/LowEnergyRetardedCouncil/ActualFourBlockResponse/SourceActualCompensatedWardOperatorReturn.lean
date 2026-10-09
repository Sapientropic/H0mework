import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualCompensatedQuadraticWardMoment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualShiftedQuadraticWardPayment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualCompensatedWardOperatorReturn
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPositiveBulkWard SourceScalarPairedTransport SourceScalarVirialBulk SourceScalarGaugeScale
open SourceNativeCutoffContact SourcePhysicalKineticSquare SourceHamiltonianScaleJet SourceScalarInverseBulk
open SourceResolventBandLimit ActualVectorJointCost ActualMixedCovarianceTail ActualMixedWindowGram SourceClockYukawaCubicCurrent
open ActualScalarPhaseJet ActualScalarPhaseFrequencyReturn ActualScalarPhaseQuadraticMoment
open ActualCompensatedQuadraticWardMoment ActualShiftedQuadraticWardPayment SourceInverseFullResponse
open FullYSourceResolventGraphSplice MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair coreWindow coreCovariance resolventCore phaseGenerator phaseJet phaseSecond
  thetaAction inverseVolumeAction phaseCoefficient momentMatrix pairMoment compensatedWardMoment mixedMoment
  SourceScalarAffineScaleTransport.generator SourceGaugeScaleTransport.generator SourceGaugeCoframeJets.K

private theorem phase_second_pair(A:End)(f h:QuantumTest):
    sourcePair f (phaseSecond A h)=
      sourcePair (phaseGenerator (phaseGenerator f)) (A h)+
        (2:ℂ)*sourcePair (phaseGenerator f) (A (phaseGenerator h))+
        sourcePair f (A (phaseGenerator (phaseGenerator h))) := by
  simp only [phaseSecond,LinearMap.comp_apply,phaseJet,LinearMap.coe_mk,AddHom.coe_mk,
    Module.End.mul_apply,LinearMap.sub_apply]
  have ps(g u v:QuantumTest):sourcePair g (u-v)=sourcePair g u-sourcePair g v := by
    simp only [sourcePair,map_sub,inner_sub_right]
  simp only [ps,(paid_quadratic_phase% phase_skew)]
  ring

private theorem window_covariance_pair(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    sourcePair (coreWindow m ell F z hz f) (coreWindow m ell F z hz h)=
      sourcePair f (coreCovariance m ell F z hz h) := by
  rw [actual_core_covariance_pair]
  simp only [coreWindow,Module.End.mul_apply,sourcePair,(paid_mixed_core% window_core)]

/-- The phase-polarized moment is the same original covariance occurrence,
read at its two fixed source inputs. -/
theorem actual_phase_pair_covariance(m ell:ℕ)(F:Index)(z:ℂ)(hz:z.im≠0)(f h:QuantumTest):
    phasePair m ell F z hz f h=sourcePair f (phaseSecond (coreCovariance m ell F z hz) h) := by
  rw [actual_phase_pair_fixed_jets]
  rw [window_covariance_pair,window_covariance_pair,window_covariance_pair,phase_second_pair]

private theorem causal_nonreal(advanced:Bool)(μ:ℝ)(hμ:0<μ)(w:ℝ):
    (causalFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa [causalFrequency,SourceResolventBandLimit.line_im] using hμ.ne'

/-- This is the already-paid compensated carrier as one original core
operator. The same cause's star escape pole stays with its actual charge. -/
def compensatedMomentOperator(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)(F:Index)(w:ℝ):End :=
  let z:=causalFrequency advanced μ w
  (z^2) • phaseSecond (coreCovariance m ell F z (causal_nonreal advanced μ hμ w))+
    ((-2*(phaseCoefficient:ℂ))*star (escapePole advanced μ w)) •
      (thetaAction m ell*inverseVolumeAction*thetaAction m ell)

theorem actual_pair_moment_operator(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)
    (F:Index)(f h:QuantumTest)(w:ℝ):
    pairMoment advanced μ hμ m ell F f h w=
      sourcePair f (compensatedMomentOperator advanced μ hμ m ell F w h) := by
  have ht:sourcePair f (thetaAction m ell (inverseVolumeAction (thetaAction m ell h)))=
      sourcePair (thetaAction m ell f) (inverseVolumeAction (thetaAction m ell h)) := by
    unfold thetaAction
    exact GaussNativeForm.multiply_pair _ _ _ _
  unfold pairMoment compensatedMomentOperator
  dsimp only
  rw [actual_phase_pair_covariance]
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply]
  have pa(x y:QuantumTest):sourcePair f (x+y)=sourcePair f x+sourcePair f y := by
    simp only [sourcePair,map_add,inner_add_right]
  have ps(c:ℂ)(x:QuantumTest):sourcePair f (c • x)=c*sourcePair f x := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [pa,ps,ps,ht]
  ring

/-- Whole fixed-input matrix identity; no RF leg or theta insertion moves. -/
theorem actual_moment_matrix_operator(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)
    (F:Index)(f h:QuantumTest)(w:ℝ):
    momentMatrix advanced μ hμ m ell F f h w=
      responseRead f h (compensatedMomentOperator advanced μ hμ m ell F w) := by
  funext A B
  unfold momentMatrix responseRead
  exact actual_pair_moment_operator advanced μ hμ m ell F (A f) (B h) w

/-- The original Ward acts after phase on this paid carrier. Its true gamma,
all three coframe jets and both original source legs are kept. -/
theorem actual_physical_ward_operator(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)
    (F:Index)(f h:QuantumTest)(w:ℝ):
    compensatedWardMoment false advanced μ hμ m ell F f h w=
      sourcePair f (inverseWeightedBulkJet (compensatedMomentOperator advanced μ hμ m ell F w) h) := by
  unfold compensatedWardMoment pairWardPhi
  simp only [Bool.false_eq_true,ite_false,zero_smul,add_zero]
  rw [actual_moment_matrix_operator]
  have hs:=original_response_ward f h (compensatedMomentOperator advanced μ hμ m ell F w) (1:End) (1:End)
  simpa only [Module.End.one_apply] using hs.symm

private theorem response_phi(f h:QuantumTest)(M:End):
    responseRead f h (deltaPhi M)=pairDelta Phi (responseRead f h M) := by
  rw [←SourceScalarAffineScaleTransport.generator_commutator]
  exact (paid_shifted_response% response_delta) Phi (paid_shifted_response% phi_pair) f h M
private theorem response_gauge(f h:QuantumTest)(M:End):
    responseRead f h (deltaGauge M)=pairDelta Gauge (responseRead f h M) := by
  rw [←SourceGaugeScaleTransport.generator_commutator]
  exact (paid_shifted_response% response_delta) Gauge (paid_shifted_response% gauge_pair) f h M

private theorem response_mixed(f h:QuantumTest)(M:End):
    responseRead f h (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge M)=
      InverseVolumeWardAlgebra.mixedPolynomial (pairDelta Phi) (pairDelta Gauge) (responseRead f h M) := by
  simp only [InverseVolumeWardAlgebra.mixedPolynomial,map_add,map_sub,map_smul,response_phi,response_gauge]

theorem actual_physical_mixed_operator(advanced:Bool)(μ:ℝ)(hμ:0<μ)(m ell:ℕ)
    (F:Index)(f h:QuantumTest)(w:ℝ):
    mixedMoment advanced μ hμ m ell F f h w=
      sourcePair f (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge
        (compensatedMomentOperator advanced μ hμ m ell F w) h) := by
  unfold mixedMoment
  rw [actual_moment_matrix_operator,←response_mixed]
  rfl

/-- Direct original operator consumer of the generated pure-mixed moment.
This readout preserves the norm-of-integral scope of its source payer. -/
theorem actual_physical_mixed_operator_tail(μ:ℝ)(hμ:0<μ)(f h:QuantumTest):
    ∀ε:ℝ,0 < ε → ∃N:ℕ,∀m,N ≤ m → ∀ell,m ≤ ell →
      ∀ᶠF in (sourceFilter:Filter Index),∀advanced:Bool,
        Integrable (fun w:ℝ=>sourcePair f (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge
          (compensatedMomentOperator advanced μ hμ m ell F w) h)) ∧
        ‖∫w:ℝ,sourcePair f (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge
          (compensatedMomentOperator advanced μ hμ m ell F w) h)‖≤ε := by
  intro ε hε
  obtain ⟨N,hN⟩:=actual_physical_mixed_moment_tail μ hμ f h ε hε
  refine ⟨N,fun m hm ell hml=>?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  intro advanced
  have he:mixedMoment advanced μ hμ m ell F f h=
      fun w:ℝ=>sourcePair f (InverseVolumeWardAlgebra.mixedPolynomial deltaPhi deltaGauge
        (compensatedMomentOperator advanced μ hμ m ell F w) h) :=
    funext (fun w=>actual_physical_mixed_operator advanced μ hμ m ell F f h w)
  have hf:=hF advanced
  rw [he] at hf
  exact hf

end LowEnergy.ActualCompensatedWardOperatorReturn
