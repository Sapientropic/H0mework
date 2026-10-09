import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedObservedPolePrice
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Matrix.Normed

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedIRReturn
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn
open SourcePropagationAlgebraicResponse SourcePropagationResolvent SourcePropagationSpectralAxis
open PreparationVacuumPropagationPencil
open ActualDressedStaticPole ActualDressedFullCoulomb ActualDressedNoether
open PreparationVacuumActionFieldLift
open Filter Polynomial
open scoped Topology BigOperators Matrix.Norms.Elementwise
attribute [local irreducible] propagationNumerator sourcePoleRegularOperator staticPoleRegularOperator
  dressedStaticPoleRegular dressedEulerObserver dressedKinematicPoint

private theorem numerator_sum {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (z : ℂ) :
    aeval T (P/ₘ(X-C z))=
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree,z^(j-(n+1))*P.coeff j) • T^n := by
  have degree : (P/ₘ(X-C z)).natDegree<P.natDegree+1 := by
    rw [natDegree_divByMonic P (monic_X_sub_C z)]
    exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_self _)
  rw [aeval_eq_sum_range' degree]
  apply Finset.sum_congr rfl
  intro n _
  rw [coeff_divByMonic_X_sub_C]

private theorem numerator_analytic {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    (T : A) (P : ℂ[X]) (z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ=>aeval T (P/ₘ(X-C w))) z := by
  have polynomial : AnalyticAt ℂ (fun w : ℂ=>
      ∑n∈Finset.range (P.natDegree+1),
        (∑j∈Finset.Icc (n+1) P.natDegree,w^(j-(n+1))*P.coeff j) • T^n) z := by
    fun_prop
  exact polynomial.congr (Eventually.of_forall (fun w=>(numerator_sum T P w).symm))

theorem original_propagation_numerator_analytic (q : PhysicalResponsePoint) (z : ℂ) :
    AnalyticAt ℂ (propagationNumerator q) z := by
  have source:=numerator_analytic (A:=SourcePropagationResolvent.TransferOp)
    (evolutionGenerator q) (propagationPolynomial q) z
  unfold propagationNumerator
  exact source

private theorem inverse_scaled_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d : ℂ→ℂ) (N : ℂ→E) (a : ℂ) (hd : AnalyticAt ℂ d a) (hn : AnalyticAt ℂ N a) (nonzero : d a≠0) :
    AnalyticAt ℂ (fun z=> (d z)⁻¹ • N z) a :=
  (hd.inv nonzero).smul hn

theorem original_source_regular_analytic (q : PhysicalResponsePoint) (a : ℂ) :
    AnalyticAt ℂ (sourcePoleRegularOperator q a) a := by
  have denominator : AnalyticAt ℂ (fun z : ℂ=>(sourcePoleDenominator q a).eval z) a :=
    AnalyticOnNhd.eval_polynomial (𝕜:=ℂ) (sourcePoleDenominator q a) a (Set.mem_univ a)
  unfold sourcePoleRegularOperator
  exact inverse_scaled_analytic _ _ a denominator (original_propagation_numerator_analytic q a) (sourcePole_regular q a)

private theorem analytic_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : ℂ→E→L[ℂ]E) (v : ℂ→E) (z : ℂ)
    (hr : AnalyticAt ℂ R z) (hv : AnalyticAt ℂ v z) :
    AnalyticAt ℂ (fun w=>R w (v w)) z := by
  exact ((ContinuousLinearMap.id ℂ (E→L[ℂ]E)).analyticAt_bilinear (R z,v z)).comp₂ hr hv

private theorem regular_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : ℂ→E→L[ℂ]E) (D : E→L[ℂ]E) (V W : E) (n : ℕ)
    (hr : AnalyticAt ℂ R 0) :
    AnalyticAt ℂ (fun z : ℂ=>z^n • R z V+R z (D (R z W))) 0 := by
  have first:=analytic_apply R (fun _ : ℂ=>V) 0 hr (analyticAt_const ..)
  have inner:=analytic_apply R (fun _ : ℂ=>W) 0 hr (analyticAt_const ..)
  have drive:=(D.analyticAt _).comp inner
  exact ((analyticAt_id.pow n).smul first).add (analytic_apply R _ 0 hr drive)

theorem original_static_regular_operator_analytic (q : PhysicalResponsePoint) (reader force : Field289) :
    AnalyticAt ℂ (staticPoleRegularOperator q reader force) 0 := by
  unfold staticPoleRegularOperator
  exact regular_analytic _ _ _ _ _ (original_source_regular_analytic q 0)

/-- Analyticity is generated on the original full regularized matrix, before any IR factor is selected. -/
theorem actual_regular_matrix_analytic (event : DressedEvent) :
    AnalyticAt ℂ (dressedStaticPoleRegular event) 0 := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  unfold dressedStaticPoleRegular
  exact ((dressedEulerObserver event).analyticAt _).comp
    (original_static_regular_operator_analytic (dressedKinematicPoint event 0) (fieldUnit i) (fieldUnit j))

end LowEnergy.GaussComposite.ActualDressedIRReturn
