import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Covariancesource
import H0mework.Versions.AD.Checks.Physics.IndependentBell.NistReal.NominalReplay.ObservableClosure.FullStatisticalFiber.Phaseconsumer

/-! Primitive covariance tuples generate same-source local means and complete N5 readouts. -/

set_option autoImplicit false

namespace P23.ObservableClosure.CovarianceSource.Consumer

open PhaseFiber
open TrainingChart
open P23.ObservableClosure.Consumer

noncomputable section

def tupleMean (input : Primitive) (a : ℝ) : ℝ :=
  input.m-input.z*cosDouble a-input.x*sinDouble a

def tupleMirrorMean (input : Primitive) (a : ℝ) : ℝ :=
  input.m-input.z*cosDouble a+input.x*sinDouble a

theorem generated_means (input : Primitive) (k : ℝ) (hk : PhaseDomain input k)
    (a b : ℝ) :
    meanA (CovarianceSource.generatedSnapshot input k hk) a=tupleMean input a ∧
    meanB (CovarianceSource.generatedSnapshot input k hk) b=tupleMean input b/input.r := by
  have hc := generated_coordinates input k hk
  rw [native_mean_A_covariance,native_mean_B_covariance]
  dsimp only [covarianceMean,tupleMean]
  rw [hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq]
  exact ⟨rfl,rfl⟩

structure TuplePolytope (input : Primitive) (a0 a1 : ℝ) (bounds : MeanIntervals) : Prop where
  alpha0 : bounds.alpha0lo ≤ tupleMean input a0 ∧ tupleMean input a0 ≤ bounds.alpha0hi
  alpha1 : bounds.alpha1lo ≤ tupleMean input a1 ∧ tupleMean input a1 ≤ bounds.alpha1hi
  beta0 : bounds.beta0lo*input.r ≤ tupleMirrorMean input a0 ∧
    tupleMirrorMean input a0 ≤ bounds.beta0hi*input.r
  beta1 : bounds.beta1lo*input.r ≤ tupleMirrorMean input a1 ∧
    tupleMirrorMean input a1 ≤ bounds.beta1hi*input.r

theorem generated_polytope_iff_tuple (input : Primitive) (k : ℝ) (hk : PhaseDomain input k)
    (a0 a1 : ℝ) (bounds : MeanIntervals) :
    SourcePolytope (CovarianceSource.generatedSnapshot input k hk) a0 a1 bounds ↔
      TuplePolytope input a0 a1 bounds := by
  have hc := generated_coordinates input k hk
  constructor
  · intro hs
    constructor
    · simpa only [covarianceMean,tupleMean,hc.m_eq,hc.z_eq,hc.x_eq] using hs.alpha0
    · simpa only [covarianceMean,tupleMean,hc.m_eq,hc.z_eq,hc.x_eq] using hs.alpha1
    · simpa only [mirrorCovarianceMean,tupleMirrorMean,hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq]
        using hs.beta0
    · simpa only [mirrorCovarianceMean,tupleMirrorMean,hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq]
        using hs.beta1
  · intro ht
    constructor
    · simpa only [covarianceMean,tupleMean,hc.m_eq,hc.z_eq,hc.x_eq] using ht.alpha0
    · simpa only [covarianceMean,tupleMean,hc.m_eq,hc.z_eq,hc.x_eq] using ht.alpha1
    · simpa only [mirrorCovarianceMean,tupleMirrorMean,hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq]
        using ht.beta0
    · simpa only [mirrorCovarianceMean,tupleMirrorMean,hc.m_eq,hc.z_eq,hc.x_eq,hc.ratio_eq]
        using ht.beta1

/-- The tuple's complete halfspaces generate exactly the source's four local intervals. -/
theorem generated_single_intervals_iff_tuple (input : Primitive) (k : ℝ)
    (hk : PhaseDomain input k) (a0 a1 : ℝ) (bounds : MeanIntervals) :
    SingleMembership (CovarianceSource.generatedSnapshot input k hk) a0 a1 bounds ↔
      TuplePolytope input a0 a1 bounds :=
  (single_membership_iff_polytope _ a0 a1 bounds).trans
    (generated_polytope_iff_tuple input k hk a0 a1 bounds)

theorem generated_window_readback (input : Primitive) (k : ℝ) (hk : PhaseDomain input k)
    (cell : Cell) (bgA bgB : ℝ) :
    generatedWindow (CovarianceSource.generatedSnapshot input k hk) cell bgA bgB=
      PhaseFiber.Consumer.phaseWindow (rawSource input) k cell bgA bgB :=
  PhaseFiber.Consumer.generated_window_readback (rawSource input) k
    (generated_phase_physical input k hk) cell bgA bgB

theorem generated_shared_phase (input : Primitive) (k : ℝ) (hk : PhaseDomain input k)
    (cell0 cell1 : Cell) :
    g (rawSource input).baseline cell1*
      (pulse00 (CovarianceSource.generatedSnapshot input k hk) cell0*
        E (rawSource input).baseline cell0 (e (rawSource input).baseline)-
        L (rawSource input).baseline cell0 (e (rawSource input).baseline))=
    g (rawSource input).baseline cell0*
      (pulse00 (CovarianceSource.generatedSnapshot input k hk) cell1*
        E (rawSource input).baseline cell1 (e (rawSource input).baseline)-
        L (rawSource input).baseline cell1 (e (rawSource input).baseline)) :=
  PhaseFiber.Consumer.shared_phase_relation (rawSource input) k
    (generated_phase_physical input k hk) cell0 cell1

structure GeneratedSourceReadout (input : Primitive) (k : ℝ) (hk : PhaseDomain input k)
    (bgA bgB : ℝ) : Prop where
  coordinates : CoordinatesReadback (CovarianceSource.generatedSnapshot input k hk) input
  interference : PhaseFiber.interference (CovarianceSource.generatedSnapshot input k hk)=k
  means : ∀ a b,
    meanA (CovarianceSource.generatedSnapshot input k hk) a=tupleMean input a ∧
      meanB (CovarianceSource.generatedSnapshot input k hk) b=tupleMean input b/input.r
  cells : ∀ cell,
    pulse00 (CovarianceSource.generatedSnapshot input k hk) cell=affinePulse (rawSource input) cell k
  windows : ∀ cell,
    generatedWindow (CovarianceSource.generatedSnapshot input k hk) cell bgA bgB=
      PhaseFiber.Consumer.phaseWindow (rawSource input) k cell bgA bgB

/-- Every lawful regular tuple generates its exact source, common phase and all N5/OR cells. -/
theorem primitive_generates_source_and_readouts (input : Primitive) (k : ℝ)
    (hk : PhaseDomain input k) (bgA bgB : ℝ) : GeneratedSourceReadout input k hk bgA bgB :=
  ⟨generated_coordinates input k hk,CovarianceSource.generated_interference input k hk,
    fun a b => generated_means input k hk a b,
    CovarianceSource.generated_all_cells input k hk,
    fun cell => generated_window_readback input k hk cell bgA bgB⟩

end
end P23.ObservableClosure.CovarianceSource.Consumer
