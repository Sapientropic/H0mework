import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualFourBlockRetarded

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualFourBlockCausalOnset
open GaussCoreHilbert GaussCoreDifferential GaussHistoryHilbert GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActualFourBlockSource ActualFourBlockRetarded FullYDynamicSource FullYPairedParseval CompositeFullYBorn
open MeasureTheory Filter Set
open scoped Topology
attribute [local irreducible] embed literalCoreTime sourceReader sourceOrbit sourceSpace

private theorem time_orbit (F : Index) (sharp : Bool) (q : QuantumTest) (t : ℝ) :
    literalCoreTime F sharp q t ∈ sourceOrbit F sharp q := by
  unfold literalCoreTime
  exact ((sourceEquiv F sharp q).symm
    (SourceFiniteUnitary.time (sourceGenerator F sharp q) t
      (sourceEquiv F sharp q ⟨q,sourceOrbit_input F sharp q⟩))).property

/-- The right causal trace returns the original coherent action on the input.
The bounded reader is generated on this source orbit, including either sharp. -/
theorem actual_causal_initial_return (F : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (advanced : Bool) (μ : ℝ) :
    Tendsto (causalOutput F sharp q p advanced μ) (𝓝[>] (0 : ℝ))
      (𝓝 (embed (coherentSource p q))) := by
  have ht : Continuous (fun t : ℝ => embed (literalCoreTime F sharp q t)) :=
    continuous_iff_continuousAt.mpr
      (fun t => (literal_core_time_derivative F sharp q t).continuousAt)
  have ha : Continuous (fun t : ℝ =>
      embed (coherentSource p (literalCoreTime F sharp q t))) := by
    apply ((sourceReader F sharp q (coherentSource p)).continuous.comp ht).congr
    intro t
    exact source_reader_return F sharp q _ (coherentSource p) (time_orbit F sharp q t)
  have hc : Continuous (fun t : ℝ => (Real.exp (-μ*t) : ℂ) •
      embed (coherentSource p (literalCoreTime F sharp q (direction advanced*t)))) :=
    (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).smul
        (ha.comp (continuous_const.mul continuous_id))
  have h := hc.tendsto 0
  simp only [mul_zero,literal_core_time_zero,Real.exp_zero,Complex.ofReal_one,one_smul] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [causalOutput,causalWave,indicator_of_mem ht]

theorem actual_causal_initial_nonzero (F : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (hq : coherentSource p q ≠ 0) (advanced : Bool) (μ : ℝ) :
    ∀ᶠt : ℝ in 𝓝[>] (0 : ℝ), causalOutput F sharp q p advanced μ t ≠ 0 := by
  have hn : embed (coherentSource p q) ≠ 0 := by
    intro h
    exact hq (embed_injective (h.trans (map_zero embed).symm))
  exact (actual_causal_initial_return F sharp q p advanced μ).eventually_ne hn

theorem actual_causal_nonpositive_zero (F : Index) (sharp : Bool) (q : QuantumTest)
    (p : Kinematics) (advanced : Bool) (μ t : ℝ) (ht : t ≤ 0) :
    causalOutput F sharp q p advanced μ t = 0 := by
  simp only [causalOutput,causalWave,indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr ht)]

end LowEnergy.ActualFourBlockCausalOnset
