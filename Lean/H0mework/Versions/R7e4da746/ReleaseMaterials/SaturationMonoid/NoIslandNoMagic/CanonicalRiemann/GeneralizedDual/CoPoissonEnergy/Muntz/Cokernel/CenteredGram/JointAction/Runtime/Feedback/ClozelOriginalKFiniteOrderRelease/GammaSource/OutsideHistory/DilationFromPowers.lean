import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Resolvent.ParameterJet
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Fourier.Inversion

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRSourceJointContact.OutsideHistory.DilationFromPowers

open Complex Filter FourierTransform MeasureTheory Set OriginalRResolventParameterJet
open scoped Topology InnerProductSpace

local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
local notation "W" => positiveMellinQuarterRightResolventWeight

private def strip : Set ℂ := {s | (1/2 : ℝ) < s.re ∧ s.re < 1}

private theorem strip_preconnected : IsPreconnected strip := by
  change IsPreconnected (Complex.reCLM ⁻¹' Ioo (1/2 : ℝ) 1)
  exact ((convex_Ioo (1/2 : ℝ) 1).linear_preimage Complex.reCLM.toLinearMap).isPreconnected

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem observed_analytic (Q : BurnolL2 →L[ℂ] E) (v : BurnolL2) :
    AnalyticOnNhd ℂ (fun s : ℂ => Q (burnolDirectRightResolvent (s / 2) v)) strip := by
  intro s hs
  let a : BurnolCompletedMellinCoordinate := ⟨s, hs.1, hs.2⟩
  exact (Q.analyticAt _).comp (parameter_analytic a v)

private theorem observed_jet (Q : BurnolL2 →L[ℂ] E) (c : BurnolCompletedMellinCoordinate)
    (v : BurnolL2) (n : ℕ) :
    iteratedDeriv n (fun s : ℂ => Q (burnolDirectRightResolvent (s / 2) v)) c.value =
      ((n.factorial : ℂ) / (2 : ℂ)^n) • Q (((R c)^(n+1)) v) := by
  have read : iteratedDeriv n (fun s : ℂ => Q (burnolDirectRightResolvent (s / 2) v)) c.value =
      Q (iteratedDeriv n (fun s : ℂ => burnolDirectRightResolvent (s / 2) v) c.value) := by
    rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
    change iteratedFDeriv ℂ n (Q ∘ (fun s : ℂ => burnolDirectRightResolvent (s / 2) v))
      c.value (fun _ => 1) = _
    rw [Q.iteratedFDeriv_comp_left (n := (n : WithTop ENat)) (parameter_analytic c v).contDiffAt le_rfl]
    rfl
  rw [read, parameter_jet, map_smul]

private theorem strip_zero [CompleteSpace E] (Q : BurnolL2 →L[ℂ] E) (c : BurnolCompletedMellinCoordinate)
    (v : BurnolL2) (silent : ∀ n : ℕ, Q (((R c)^(n+1)) v) = 0) :
    ∀ s ∈ strip, Q (burnolDirectRightResolvent (s / 2) v) = 0 := by
  have atC : c.value ∈ strip := ⟨c.rightHalf,c.belowOne⟩
  have analytic := observed_analytic Q v
  apply analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero strip_preconnected atC
  apply analyticOrderAt_eq_top.mp
  apply ENat.eq_top_iff_forall_ge.mpr
  intro n
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (analytic c.value atC)).mpr
  intro j _
  rw [observed_jet, silent, smul_zero]

private theorem damped_fourier_read [CompleteSpace E] (Q : BurnolL2 →L[ℂ] E) (v : BurnolL2) (y : ℝ) :
    let s : ℂ := (3/4 : ℂ) + (↑(4 * Real.pi * y) : ℂ) * I
    𝓕 ((Ioi (0 : ℝ)).indicator (fun h => Q (burnolDirectRightResolventIntegrand (3/8) v h))) y =
      -Q (burnolDirectRightResolvent (s/2) v) := by
  intro s
  have right : 1/4 < (s/2).re := by
    dsimp only [s]; rw [Complex.div_re]
    norm_num [Complex.add_re, Complex.mul_re]
  rw [Real.fourier_real_eq_integral_exp_smul, burnolDirectRightResolvent, map_neg, neg_neg,
    ← Q.integral_comp_comm (burnolDirectRightResolventIntegrand_integrableOn _ right v),
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards with h
  by_cases positive : 0 < h
  · have mem : h ∈ Ioi (0 : ℝ) := positive
    simp only [indicator_of_mem mem, burnolDirectRightResolventIntegrand, map_smul, smul_smul]
    congr 1
    unfold positiveMellinQuarterRightResolventWeight
    rw [← Complex.exp_add]
    congr 1
    dsimp only [s]
    push_cast
    ring
  · have mem : h ∉ Ioi (0 : ℝ) := positive
    simp only [indicator_of_notMem mem, smul_zero]

/-- The original nonnegative R powers determine the same observation on the inward dilation orbit. -/
theorem observed_inward_zero [CompleteSpace E] (Q : BurnolL2 →L[ℂ] E) (c : BurnolCompletedMellinCoordinate)
    (v : BurnolL2) (silent : ∀ n : ℕ, Q (((R c)^(n+1)) v) = 0) (h : ℝ) (positive : 0 < h) :
    Q (D (-h/2) v) = 0 := by
  let g : ℝ → E := fun t => Q (burnolDirectRightResolventIntegrand (3/8) v t)
  let f := (Ioi (0 : ℝ)).indicator g
  have ing : IntegrableOn g (Ioi (0 : ℝ)) :=
    Q.integrable_comp (burnolDirectRightResolventIntegrand_integrableOn _ (by norm_num) v)
  have int : Integrable f := ing.integrable_indicator measurableSet_Ioi
  have zero : 𝓕 f = 0 := by
    ext y
    let s : ℂ := (3/4 : ℂ) + (↑(4 * Real.pi * y) : ℂ) * I
    have inside : s ∈ strip := by
      change (1/2 : ℝ) < s.re ∧ s.re < 1
      norm_num [s, Complex.add_re, Complex.mul_re]
    change 𝓕 f y = 0
    rw [damped_fourier_read, strip_zero Q c v silent s inside, neg_zero]
  have hg : Continuous g := Q.continuous.comp
    ((positiveMellinQuarterRightResolventWeight_continuous (3/8)).smul
      ((burnolMultiplicativeDilation_stronglyContinuous v).comp (by fun_prop)))
  have atH : ContinuousAt f h := hg.continuousAt.congr
    (by filter_upwards [Ioi_mem_nhds positive] with t ht; exact (indicator_of_mem ht g).symm)
  have ifourier : Integrable (𝓕 f) := by rw [zero]; exact integrable_zero ℝ E volume
  have reverse := int.fourierInv_fourier_eq ifourier atH
  rw [zero] at reverse
  have gh : g h = 0 := by
    simpa [Real.fourierInv_eq, f, indicator_of_mem (show h ∈ Ioi (0 : ℝ) from positive)] using reverse.symm
  change Q (W (3/8) h • D (-h/2) v) = 0 at gh
  rw [map_smul] at gh
  exact (smul_eq_zero.mp gh).resolve_left (Complex.exp_ne_zero _)

end OriginalRSourceJointContact.OutsideHistory.DilationFromPowers
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
