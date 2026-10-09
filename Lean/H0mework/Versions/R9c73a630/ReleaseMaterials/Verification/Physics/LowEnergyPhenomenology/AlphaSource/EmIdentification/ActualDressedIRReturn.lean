import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedIRFactor

set_option autoImplicit false
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedIRReturn
open CanonicalGradedSpatialSource GaussCoreHilbert
open ActualDressedStaticPole ActualDressedFullCoulomb ActualDressedSylvester
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
attribute [local irreducible] dressedStaticPoleOrder dressedStaticPoleRegular dressedStaticPolarization

private theorem cancel_sixth {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z : ℂ) (nonzero : z≠0) (n : ℕ) (P G : E)
    (equation : z^(n+6) • P=z^n • G) : z^6 • P=G := by
  have scalar : (z^n)⁻¹*z^(n+6)=z^6 := by
    rw [pow_add,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero n nonzero),one_mul]
  calc
    _=((z^n)⁻¹*z^(n+6)) • P:=congrArg (fun c : ℂ => c • P) scalar.symm
    _=(z^n)⁻¹ • (z^(n+6) • P):=(smul_smul _ _ _).symm
    _=(z^n)⁻¹ • (z^n • G):=congrArg (fun X : E => (z^n)⁻¹ • X) equation
    _=G:=by rw [smul_smul,inv_mul_cancel₀ (pow_ne_zero n nonzero),one_smul]

private theorem supplement_sixth {E : Type*} [AddCommGroup E] [Module ℂ E]
    (z : ℂ) (q : ℕ) (small : q ≤ 6) (P R : E) (equation : z^q • P=R) :
    z^6 • P=z^(6-q) • R := by
  have split : 6=(6-q)+q:=by omega
  calc
    _=z^((6-q)+q) • P:=congrArg (fun n : ℕ => z^n • P) split
    _=z^(6-q) • (z^q • P):=by rw [pow_add,smul_smul]
    _=_:=congrArg (fun X : E => z^(6-q) • X) equation

private theorem actual_matrix_regularized (event : DressedEvent) (z : ℂ) (positive : 0<z.re) :
    z^(2*dressedStaticPoleOrder event) • dressedStaticPolarization event 0 z=dressedStaticPoleRegular event z := by
  funext i j
  exact dressed_static_polarization_regularized event z positive i j

private theorem analytic_scaled {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : ℂ→E) (n : ℕ) (h : AnalyticAt ℂ R 0) : AnalyticAt ℂ (fun z : ℂ => z^n • R z) 0 :=
  (analyticAt_id.pow n).smul h

/-- The same full actual matrix has a source-generated analytic sixth regularization, in every operator-order branch. -/
theorem actual_sixth_ir_regularization (event : DressedEvent) :
    ∃G : ℂ→Matrix (Fin 289) (Fin 289) ℂ,AnalyticAt ℂ G 0 ∧
      ∀ᶠz : ℂ in 𝓝 0,0<z.re→z^6 • dressedStaticPolarization event 0 z=G z := by
  by_cases high : 6 ≤ 2*dressedStaticPoleOrder event
  · obtain ⟨G,analytic,factor⟩:=actual_regular_matrix_factor event
    refine ⟨G,analytic,?_⟩
    filter_upwards [factor] with z generated
    intro positive
    have nonzero : z≠0 := by
      intro zero
      have impossible : (0:ℝ)<0:=by simpa only [zero,Complex.zero_re] using positive
      exact (lt_irrefl (0:ℝ)) impossible
    have split : 2*dressedStaticPoleOrder event=(2*dressedStaticPoleOrder event-6)+6:=by omega
    have same : z^((2*dressedStaticPoleOrder event-6)+6) • dressedStaticPolarization event 0 z=
        z^(2*dressedStaticPoleOrder event-6) • G z := by
      rw [←split]
      exact (actual_matrix_regularized event z positive).trans generated
    exact cancel_sixth z nonzero _ _ _ same
  · have small : 2*dressedStaticPoleOrder event ≤ 6:=by omega
    refine ⟨fun z : ℂ => z^(6-2*dressedStaticPoleOrder event) • dressedStaticPoleRegular event z,
      analytic_scaled _ _ (actual_regular_matrix_analytic event),?_⟩
    exact Eventually.of_forall (fun z positive => supplement_sixth z _ small _ _ (actual_matrix_regularized event z positive))

/-- The actual zero-transfer sixth-normalized response returns a finite source matrix at zero damping. -/
theorem actual_sixth_ir_return (event : DressedEvent) :
    ∃L : Matrix (Fin 289) (Fin 289) ℂ,
      Tendsto (fun z : ℂ => z^6 • dressedStaticPolarization event 0 z)
        (nhdsWithin 0 {z : ℂ|0<z.re}) (𝓝 L) := by
  obtain ⟨G,analytic,source⟩:=actual_sixth_ir_regularization event
  refine ⟨G 0,?_⟩
  apply Tendsto.congr' _ (analytic.continuousAt.tendsto.mono_left inf_le_left)
  filter_upwards [self_mem_nhdsWithin,source.filter_mono inf_le_left] with z positive actual
  exact (actual positive).symm

theorem actual_sixth_ir_real_return (event : DressedEvent) :
    ∃L : Matrix (Fin 289) (Fin 289) ℂ,
      Tendsto (fun s : ℝ => (s:ℂ)^6 • dressedStaticPolarization event 0 (s:ℂ))
        (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 L) := by
  obtain ⟨G,analytic,source⟩:=actual_sixth_ir_regularization event
  have embedding : Tendsto (fun s : ℝ => (s:ℂ)) (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 (0:ℂ)):=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left inf_le_left
  refine ⟨G 0,?_⟩
  apply Tendsto.congr' _ (analytic.continuousAt.tendsto.comp embedding)
  filter_upwards [self_mem_nhdsWithin,embedding.eventually source] with s positive actual
  exact (actual positive).symm

end LowEnergy.GaussComposite.ActualDressedIRReturn
