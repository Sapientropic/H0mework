import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Sequences
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.FiniteLogCountingSource
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.LogPairClosure
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalGamma.Source.FiniteLogCounting
noncomputable section

theorem logPair_of_tendsto (u v : ℕ → BurnolL2) (a b : BurnolL2)
    (hua : Tendsto u atTop (𝓝 a)) (hvb : Tendsto v atTop (𝓝 b))
    (source : ∀ n, LogPair (u n) (v n)) : LogPair a b := by
  obtain ⟨ns, nsMono, first⟩ := (tendstoInMeasure_of_tendsto_Lp hua).exists_seq_tendsto_ae
  obtain ⟨ms, msMono, second⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hvb.comp nsMono.tendsto_atTop)).exists_seq_tendsto_ae
  have words : ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ,
      v (ns (ms n)) x = (Real.log |x| : ℂ) * u (ns (ms n)) x :=
    ae_all_iff.mpr (fun n => source (ns (ms n)))
  filter_upwards [first, second, words] with x hu hv hw
  have multiplied := (hu.comp msMono.tendsto_atTop).const_mul (Real.log |x| : ℂ)
  have same : Tendsto (fun n : ℕ => v (ns (ms n)) x) atTop
      (𝓝 ((Real.log |x| : ℂ) * a x)) := by
    apply multiplied.congr'
    exact Eventually.of_forall (fun n => (hw n).symm)
  exact tendsto_nhds_unique hv same

private def logGraph : Submodule ℂ (BurnolL2 × BurnolL2) where
  carrier := {w | LogPair w.1 w.2}
  zero_mem' := by
    change LogPair 0 0
    simp only [LogPair]
    filter_upwards [Lp.coeFn_zero (α := ℝ) (E := ℂ) (p := 2) (μ := volume)] with x zero
    have actual : (0 : BurnolL2) x = (0 : ℂ) := by simpa only [Pi.zero_apply] using zero
    rw [actual, mul_zero]
  add_mem' := by
    intro a b ha hb
    change LogPair (a.1 + b.1) (a.2 + b.2)
    filter_upwards [ha, hb, Lp.coeFn_add a.1 b.1, Lp.coeFn_add a.2 b.2] with x ax bx first second
    rw [first, second]
    simp only [Pi.add_apply]
    rw [ax, bx, mul_add]
  smul_mem' := by
    intro scalar a ha
    change LogPair (scalar • a.1) (scalar • a.2)
    filter_upwards [ha, Lp.coeFn_smul scalar a.1, Lp.coeFn_smul scalar a.2] with x ax first second
    rw [first, second]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ax]
    ring

private theorem log_graph_closed : IsClosed (logGraph : Set (BurnolL2 × BurnolL2)) := by
  apply IsSeqClosed.isClosed
  intro w limit belongs converges
  exact logPair_of_tendsto (fun n => (w n).1) (fun n => (w n).2) limit.1 limit.2
    ((continuous_fst.tendsto limit).comp converges)
    ((continuous_snd.tendsto limit).comp converges) belongs

theorem logPair_integral {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u v : α → BurnolL2) (hu : Integrable u μ) (hv : Integrable v μ)
    (source : ∀ᵐ t ∂μ, LogPair (u t) (v t)) :
    LogPair (∫ t, u t ∂μ) (∫ t, v t ∂μ) := by
  have : IsClosed (logGraph : Set (BurnolL2 × BurnolL2)) := log_graph_closed
  have joint := hu.prodMk hv
  have generated : (∫ t, (u t, v t) ∂μ) ∈ logGraph := by
    apply (Submodule.Quotient.mk_eq_zero logGraph).mp
    have read := logGraph.mkQL.integral_comp_comm joint
    change logGraph.mkQL (∫ t, (u t, v t) ∂μ) = 0
    rw [← read]
    apply integral_eq_zero_of_ae
    filter_upwards [source] with t ht
    exact (Submodule.Quotient.mk_eq_zero logGraph).mpr ht
  rw [integral_pair hu hv] at generated
  exact generated

end
end OriginalGamma.Source.LogPairClosure
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
