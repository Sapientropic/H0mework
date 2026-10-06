import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceFiniteTimeIntegral

/-! The original simplex estimate acts on finite time families before taking the same filter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.FullYSourceTimeFamilyGraph
open SourceFamilyHilbert SourceFamilyOperator Filter MeasureTheory
open FullYSourceCutoffNorm FullYSourceCutoffTimeGraph FullYSourceCutoffVolterra
open FullYSourceFiniteTimeIntegral
open scoped Topology InnerProductSpace

section Family
variable {I E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  (u : Ultrafilter I)

theorem lifted_distance (A : ℕ → E →L[ℂ] E)
    (hA : ∀ x m n, m ≤ n → ‖A n x-A m x‖^2 ≤ ‖A n x‖^2-‖A m x‖^2)
    (x : Hilbert E u) {m n : ℕ} (hmn : m ≤ n) :
    ‖lift u (SourceFamilyOperator.constant (A n)) x-
      lift u (SourceFamilyOperator.constant (A m)) x‖^2 ≤
      ‖lift u (SourceFamilyOperator.constant (A n)) x‖^2-
        ‖lift u (SourceFamilyOperator.constant (A m)) x‖^2 := by
  refine UniformSpace.Completion.induction_on x (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,lift_coe,←UniformSpace.Completion.coe_sub]
  simp only [UniformSpace.Completion.norm_coe]
  apply le_of_tendsto_of_tendsto (square_tendsto u _)
    ((square_tendsto u _).sub (square_tendsto u _))
  exact Filter.Eventually.of_forall (fun i => hA (value f i) m n hmn)

theorem lifted_residual (S B : E →L[ℂ] E) (A : ℕ → E →L[ℂ] E)
    (hA : ∀ n x, S (A n x)=B x-(A (n+1) x-A n x))
    (x : Hilbert E u) (n : ℕ) :
    lift u (SourceFamilyOperator.constant S) (lift u (SourceFamilyOperator.constant (A n)) x)=
      lift u (SourceFamilyOperator.constant B) x-
        (lift u (SourceFamilyOperator.constant (A (n+1))) x-
          lift u (SourceFamilyOperator.constant (A n)) x) := by
  refine UniformSpace.Completion.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  rw [lift_coe,lift_coe,lift_coe,lift_coe,←UniformSpace.Completion.coe_sub,
    ←UniformSpace.Completion.coe_sub]
  congr 1
  apply Family.ext
  funext i
  exact hA n (value f i)

end Family

open GaussCoreHilbert
open GaussUnitaryHistory (HistorySpace sourceFilter reader inclusion)
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

def familyReader (A : H →L[ℂ] H) : TimeSpace μ →L[ℂ] TimeSpace μ :=
  lift sourceFilter (SourceFamilyOperator.constant (A.compLpL 2 μ))

def familyCutoff (n : ℕ) : TimeSpace μ →L[ℂ] TimeSpace μ := familyReader μ (cutoff n)

theorem original_cutoff_distance (x : H) {m n : ℕ} (hmn : m ≤ n) :
    ‖cutoff n x-cutoff m x‖^2 ≤ ‖cutoff n x‖^2-‖cutoff m x‖^2 := by
  have h := source_cutoff_distance (inclusion x) hmn
  simpa only [GaussUnitaryHistory.reader_inclusion,←map_sub,LinearIsometry.norm_map] using h

theorem original_cutoff_residual (n : ℕ) (x : H) :
    GaussRadialDomain.inverseRadius (cutoff n x)=GaussYukawaOperator.bounded x-
      (cutoff (n+1) x-cutoff n x) :=
  congrArg (fun T : H →L[ℂ] H => T x) (cutoff_graph_residual n)

theorem family_cutoff_distance (ψ : TimeSpace μ) {m n : ℕ} (hmn : m ≤ n) :
    ‖familyCutoff μ n ψ-familyCutoff μ m ψ‖^2 ≤
      ‖familyCutoff μ n ψ‖^2-‖familyCutoff μ m ψ‖^2 :=
  lifted_distance sourceFilter (fun n => (cutoff n).compLpL 2 μ)
    (fun ψ _ _ h => mapped_l2_distance μ cutoff (fun x _ _ hj => original_cutoff_distance x hj) ψ h)
    ψ hmn

theorem family_cutoff_residual (ψ : TimeSpace μ) (n : ℕ) :
    familyReader μ GaussRadialDomain.inverseRadius (familyCutoff μ n ψ)=
      familyReader μ GaussYukawaOperator.bounded ψ-
        (familyCutoff μ (n+1) ψ-familyCutoff μ n ψ) :=
  lifted_residual sourceFilter (GaussRadialDomain.inverseRadius.compLpL 2 μ)
    (GaussYukawaOperator.bounded.compLpL 2 μ) (fun n => (cutoff n).compLpL 2 μ)
    (fun n ψ => mapped_l2_residual μ GaussRadialDomain.inverseRadius
      GaussYukawaOperator.bounded cutoff original_cutoff_residual ψ n) ψ n

theorem family_strong_limit (ψ : TimeSpace μ)
    (bounded : ∃ C : ℝ, ∀ n, ‖familyCutoff μ n ψ‖ ≤ C) :
    ∃ y : TimeSpace μ, Tendsto (fun n => familyCutoff μ n ψ) atTop (𝓝 y) :=
  squared_distance_strong_limit (fun n => familyCutoff μ n ψ)
    (fun _ _ h => family_cutoff_distance μ ψ h) bounded

theorem family_graph_limit (ψ y : TimeSpace μ)
    (h : Tendsto (fun n => familyCutoff μ n ψ) atTop (𝓝 y)) :
    familyReader μ GaussRadialDomain.inverseRadius y=familyReader μ GaussYukawaOperator.bounded ψ :=
  telescoping_limit (familyReader μ GaussRadialDomain.inverseRadius)
    (fun n => familyCutoff μ n ψ) _ y (family_cutoff_residual μ ψ) h

variable [IsFiniteMeasure μ]

theorem retarded_limit_of_bounded (τ : α → ℝ) (hτ : Measurable τ) (ψ : TimeSpace μ)
    (bounded : ∃ C : ℝ, ∀ n, ‖familyCutoff μ n ψ‖ ≤ C) :
    ∃ y : TimeSpace μ,
      Tendsto (fun n => familyCutoff μ n ψ) atTop (𝓝 y) ∧
      familyReader μ GaussRadialDomain.inverseRadius y=familyReader μ GaussYukawaOperator.bounded ψ ∧
      Tendsto (fun n => sourceIntegral μ τ hτ (familyCutoff μ n ψ)) atTop
        (𝓝 (sourceIntegral μ τ hτ y)) :=
  (family_strong_limit μ ψ bounded).imp (fun y hy =>
    ⟨hy,family_graph_limit μ ψ y hy,source_integral_limit μ τ hτ _ y hy⟩)

#print axioms family_cutoff_distance
#print axioms retarded_limit_of_bounded
end LowEnergy.FullYSourceTimeFamilyGraph
