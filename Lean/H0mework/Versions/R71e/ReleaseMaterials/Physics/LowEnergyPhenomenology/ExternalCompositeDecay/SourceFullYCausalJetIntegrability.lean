import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceFullYCausalJetHistory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.FullYDynamicCausalJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussDiagonalHistory
open GaussUnitaryHistory FullYDynamicSource FullYDynamicTimeJets CompositeFullYBorn FullYPairedParseval
open SourceScalarPairedTransport MeasureTheory Filter Set
open scoped Topology FourierTransform
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev HF(F:Index)(sharp:Bool):End := compressionCore F+sourceY sharp
private abbrev Tgen(F:Index)(sharp advanced:Bool)(μ:ℝ):End :=
  (-μ:ℂ) • (1:End)+((-Complex.I)*(direction advanced:ℂ)) • HF F sharp
attribute [local irreducible] embed literalCoreTime sourceReader sourceOrbit sourceSpace sourceWave

private theorem time_orbit(F:Index)(sharp:Bool)(q:QuantumTest)(t:ℝ):
    literalCoreTime F sharp q t∈sourceOrbit F sharp q := by
  unfold literalCoreTime
  exact ((sourceEquiv F sharp q).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp q) t
      (sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩))).property

/-- The actual source's finite invariant carrier pays every causal core-word
jet in L1; no bound on a globally unbounded word is supplied. -/
theorem actual_causal_jet_integrable(F:Index)(sharp:Bool)(q:QuantumTest)(A:End)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(n:ℕ):
    Integrable ((Ioi (0:ℝ)).indicator (dampedTimeJet F sharp q A advanced μ n)) := by
  let B := A*(Tgen F sharp advanced μ)^n
  let L := sourceReader F sharp q B
  have hi := L.integrable_comp (actual_source_wave_integrable F sharp q advanced μ hμ)
  apply hi.congr
  apply Eventually.of_forall
  intro t
  by_cases ht:t∈Ioi (0:ℝ)
  · simp only [sourceWave,causalWave,indicator_of_mem ht,map_smul]
    rw [source_reader_return F sharp q _ B (time_orbit F sharp q (direction advanced*t))]
    rfl
  · simp only [sourceWave,causalWave,indicator_of_notMem ht,map_zero]

/-- Complete relative causal jets keep the original two cutoff histories;
both individual source carriers generate their Bochner L1 payment. -/
theorem actual_relative_causal_jets_integrable(F G:Index)(sharp:Bool)(q:QuantumTest)(A:End)
    (advanced:Bool)(μ:ℝ)(hμ:0<μ)(n:ℕ):
    Integrable (causalRelativeJet F G sharp q A advanced μ n) := by
  have h := (actual_causal_jet_integrable F sharp q A advanced μ hμ n).sub
    (actual_causal_jet_integrable G sharp q A advanced μ hμ n)
  apply h.congr
  exact Eventually.of_forall (fun t=>by
    simp only [Pi.sub_apply,causalRelativeJet,indicator_sub])

private theorem relative_derivative_away(F G:Index)(sharp:Bool)(q:QuantumTest)(A:End)
    (advanced:Bool)(μ:ℝ)(n:ℕ)(t:ℝ)(ht:t≠0):
    HasDerivAt (causalRelativeJet F G sharp q A advanced μ n)
      (causalRelativeJet F G sharp q A advanced μ (n+1) t) t := by
  by_cases hp:0<t
  · change HasDerivAt ((Ioi (0:ℝ)).indicator _) ((Ioi (0:ℝ)).indicator _ t) t
    rw [indicator_of_mem (show t∈Ioi (0:ℝ) from hp)]
    apply ((actual_damped_time_jet_derivative F sharp q A advanced μ n t).sub
      (actual_damped_time_jet_derivative G sharp q A advanced μ n t)).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hp] with s hs
    exact indicator_of_mem hs _
  · have hn:t<0 := lt_of_le_of_ne (le_of_not_gt hp) ht
    change HasDerivAt ((Ioi (0:ℝ)).indicator _) ((Ioi (0:ℝ)).indicator _ t) t
    rw [indicator_of_notMem (show t∉Ioi (0:ℝ) from hp)]
    apply (hasDerivAt_const t (0:H)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hn] with s hs
    exact indicator_of_notMem (show s∉Ioi (0:ℝ) from not_lt_of_ge (le_of_lt (show s<0 from hs))) _

/-- Every prescribed derivative of the actual retarded correction is a
source-generated L1 function on the same cofinal event as its smooth history. -/
theorem actual_cofinal_causal_derivatives_integrable(B:Index)(q:QuantumTest)(N:ℕ):
    ∃K₀:Index,B⊆K₀ ∧ ∀F:Index,K₀⊆F → ∀G:Index,K₀⊆G →
      ∀sharp advanced:Bool,∀μ:ℝ,∀hμ:0<μ,∀A:End,
      ContDiff ℝ (N:ℕ) (causalRelativeJet F G sharp q A advanced μ 0) ∧
      ∀m:ℕ,m ≤ N → Integrable (iteratedDeriv m (causalRelativeJet F G sharp q A advanced μ 0)) := by
  obtain ⟨K₀,hB,hK₀⟩ := actual_cofinal_causal_history_smooth B q N
  refine ⟨K₀,hB,fun F hF G hG sharp advanced μ hμ A=>?_⟩
  have hs := hK₀ F hF G hG sharp advanced μ A
  have hj(j:ℕ)(h:j ≤ N):
      iteratedDeriv j (causalRelativeJet F G sharp q A advanced μ 0)=
        causalRelativeJet F G sharp q A advanced μ j := by
    induction j with
    | zero => exact iteratedDeriv_zero
    | succ j ih =>
      funext t
      by_cases ht:t=0
      · subst t
        rw [hs.2 (j+1) h]
        exact (indicator_of_notMem (show (0:ℝ)∉Ioi (0:ℝ) by simp) _).symm
      · rw [iteratedDeriv_succ,ih (le_trans (Nat.le_succ j) h)]
        exact (relative_derivative_away F G sharp q A advanced μ j t ht).deriv
  refine ⟨hs.1,?_⟩
  intro m hm
  rw [hj m hm]
  exact actual_relative_causal_jets_integrable F G sharp q A advanced μ hμ m

end LowEnergy.FullYDynamicCausalJets
