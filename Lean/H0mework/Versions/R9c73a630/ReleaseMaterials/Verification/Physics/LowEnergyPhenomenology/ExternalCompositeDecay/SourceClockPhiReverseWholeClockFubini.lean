import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseWholeClockPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert SourceScalarShiftedBulk
open SourceScalarDoubleCurrent SourceClockPhiNormalizedScalarBudget SourceResolventBandLimit
open FirstCurrentJointBudget SourceLocalizedInverseFormPayment
open SourceJointResidualEnergy SourceFourPoleEnergyClosed FinitePhysicalSource FirstCurrentWholeCarrier
open ClockPhiHeatCorrectedCovarianceSource MeasureTheory Filter
open scoped InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
private abbrev B:End:=scalarBulkComplete
private abbrev Z:End:=reverseNativeClock
attribute [local irreducible] sourcePair embed correctedCompleteCore wholeSourceNext wholeSourceMap
private theorem frequency_positive(half:Bool):0<sourceNoetherFrequency half:=by
  have hn:0<sourceTime 0:=by
    rw [source_time_generated]
    exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
  linarith [actual_source_noether_gap half]
private def polePair(advanced:Bool)(μ a b q:ℝ):ℂ:=
  star (((a:ℂ)-actualFrequency advanced μ q)⁻¹)*((b:ℂ)-actualFrequency advanced μ q)⁻¹
private theorem pole_pair_integrable(advanced:Bool)(μ a b:ℝ)(hμ:0<μ):Integrable (polePair advanced μ a b):=by
  cases advanced
  · exact two_pole_integrable μ a b hμ
  · have h:=(RCLike.conjLIE (K:=ℂ)).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (two_pole_integrable μ a b hμ)
    apply h.congr
    exact Eventually.of_forall (fun q=>by
      change star (star (pole μ a q)*pole μ b q)=polePair true μ a b q
      simp only [polePair,actualFrequency,ite_true,pole,star_mul,star_inv₀,star_sub,
        Complex.star_def,Complex.conj_ofReal]
      ring)
def wholeClockWardKernel(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):ℂ:=
  let w:=(wholeSourceNext t ht half advanced m ell F g q).1
  sourcePair (bracket Z (correctedCompleteCore t ht x.1 x.2) w)
    (B (correctedCompleteCore t ht x.1 x.2 w))
private theorem kernel_columns(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    wholeClockWardKernel t ht half advanced m ell F g q x=
      ∑i:Channel F,∑j:Channel F,polePair advanced (sourceNoetherFrequency half) (channelValue F i) (channelValue F j) q*
        sourcePair (bracket Z (correctedCompleteCore t ht x.1 x.2)
          (sourceColumn (wholeSourceMap t ht half advanced m ell F g) m ell F g i))
          (B (correctedCompleteCore t ht x.1 x.2
            (sourceColumn (wholeSourceMap t ht half advanced m ell F g) m ell F g j))):=by
  have hw:=((actual_whole_electric_source_carrier t ht half advanced m ell F g).2 q).1
  unfold wholeClockWardKernel
  rw [hw]
  simp only [sourcePair,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro i _
  apply Finset.sum_congr rfl;intro j _
  simp only [polePair]
  ring

/-- Every finite and escape column of the actual whole source supplies the joint frequency/Gaussian integrability. The complete clock-Ward pair can therefore enter the original frequency Ward in either integral order. -/
theorem actual_whole_reverse_clock_Fubini(t:ℝ)(ht:0<t)(half advanced:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    Integrable (fun p:ℝ×(ℝ×ℝ)=>wholeClockWardKernel t ht half advanced m ell F g p.1 p.2)
      (volume.prod (γ.prod γ)) ∧
    (∫x:ℝ×ℝ,(∫q:ℝ,wholeClockWardKernel t ht half advanced m ell F g q x) ∂γ.prod γ)=
      ∫q:ℝ,wholeClockWardMean t ht half advanced m ell F g q:=by
  let c(j:Channel F):=sourceColumn (wholeSourceMap t ht half advanced m ell F g) m ell F g j
  have hi(i j:Channel F):Integrable (fun p:ℝ×(ℝ×ℝ)=>
      polePair advanced (sourceNoetherFrequency half) (channelValue F i) (channelValue F j) p.1*
        sourcePair (bracket Z (correctedCompleteCore t ht p.2.1 p.2.2) (c i))
          (B (correctedCompleteCore t ht p.2.1 p.2.2 (c j)))) (volume.prod (γ.prod γ)):=
    (pole_pair_integrable advanced _ _ _ (frequency_positive half)).mul_prod
      (actual_reverse_scalar_clock_payment t ht (c i) (c j)).1
  have h:Integrable (fun p:ℝ×(ℝ×ℝ)=>wholeClockWardKernel t ht half advanced m ell F g p.1 p.2)
      (volume.prod (γ.prod γ)):=by
    apply (integrable_finsetSum Finset.univ (fun i _=>integrable_finsetSum Finset.univ (fun j _=>hi i j))).congr
    exact Eventually.of_forall (fun p=>(kernel_columns t ht half advanced m ell F g p.1 p.2).symm)
  refine ⟨h,?_⟩
  exact (integral_integral_swap h).symm

/-- The source-generated common clock also pays the Gaussian average of the full original frequency Ward. Both causal branches use the same delta. -/
theorem actual_whole_reverse_clock_frequency_payment(ε:ℝ)(hε:0<ε)(half:Bool)(m ell:ℕ)(F:Index)(g:diagonal.domain):
    ∃δ:ℝ,0<δ ∧ δ≤1 ∧ ∀advanced:Bool,∀t:ℝ,∀ht:0<t,t≤δ→
      Integrable (fun p:ℝ×(ℝ×ℝ)=>wholeClockWardKernel t ht half advanced m ell F g p.1 p.2)
        (volume.prod (γ.prod γ)) ∧
      ‖∫x:ℝ×ℝ,(∫q:ℝ,wholeClockWardKernel t ht half advanced m ell F g q x) ∂γ.prod γ‖≤ε:=by
  obtain ⟨δ,hδ,hδ1,hpay⟩:=actual_whole_reverse_clock_common_payment ε hε half m ell F g
  refine ⟨δ,hδ,hδ1,?_⟩
  intro advanced t ht htδ
  have hf:=actual_whole_reverse_clock_Fubini t ht half advanced m ell F g
  refine ⟨hf.1,?_⟩
  rw [hf.2]
  exact (norm_integral_le_integral_norm _).trans (hpay advanced t ht htδ)
end LowEnergy.ReverseNativeClock
