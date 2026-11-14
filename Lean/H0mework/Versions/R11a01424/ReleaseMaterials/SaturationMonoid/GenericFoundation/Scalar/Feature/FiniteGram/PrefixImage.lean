import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixReadback

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedFiniteGram.PrefixImage

open scoped InnerProductSpace Topology
open Filter Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A source stream reads the original covectors in their given order. -/
def read (source : Nat → H) (value : H) (i : Nat) : ℂ := inner ℂ (source i) value

def sample (data : Nat → ℂ) (n : Nat) : Coordinates (Fin n) :=
  WithLp.toLp 2 fun i : Fin n => data i.val

def approximate (source : Nat → H) (data : Nat → ℂ) (n : Nat) : H :=
  PrefixReadback.inverse (fun i : Fin n => source i.val) (sample data n)

/-- Rejected finite data retain their actual discrepancy against the synthesized field. -/
def residual (source : Nat → H) (data : Nat → ℂ) (n : Nat) : Coordinates (Fin n) :=
  Projection.rhs (fun i : Fin n => source i.val) (approximate source data n) - sample data n

theorem residual_original (source : Nat → H) (value : H) (n : Nat) :
    residual source (read source value) n = 0 := by
  let tests := fun i : Fin n => source i.val
  let values := Projection.rhs tests value
  have compatible : values ∈ (Kernel (Projection.gram tests))ᗮ :=
    (Submodule.mem_orthogonal _ _).mpr (Projection.compatible tests value)
  have exactImage : (Kernel (Projection.gram tests))ᗮ.starProjection values = values :=
    Submodule.starProjection_eq_self_iff.mpr compatible
  exact sub_eq_zero.mpr ((PrefixReadback.inverse_equation tests values).trans exactImage)

def energy (source : Nat → H) (data : Nat → ℂ) (n : Nat) : ℝ :=
  ‖approximate source data n‖^2

abbrev Admitted (source : Nat → H) :=
  {data : Nat → ℂ // (∀ n, residual source data n = 0) ∧ BddAbove (range (energy source data))}

private theorem prefix_projection (source : Nat → H) (data : Nat → ℂ)
    {m n : Nat} (within : m ≤ n) (exactRead : residual source data n = 0) :
    approximate source data m =
      (Projection.sourceSpan (fun i : Fin m => source i.val)).starProjection (approximate source data n) := by
  let atOld := fun i : Fin m => source i.val
  let atNew := fun i : Fin n => source i.val
  let current := approximate source data n
  have all : Projection.rhs atNew current = sample data n := sub_eq_zero.mp exactRead
  have first : Projection.rhs atOld current = sample data m := by
    ext i
    exact congrArg (fun x : Coordinates (Fin n) => x (i.castLE within)) all
  exact (congrArg (PrefixReadback.inverse atOld) first.symm).trans
    (PrefixReadback.inverse_actual_rhs atOld current)

/-- The cost of a new compatible prefix is the squared norm of its actual innovation. -/
theorem energy_increment (source : Nat → H) (data : Nat → ℂ) {m n : Nat}
    (within : m ≤ n) (exactRead : residual source data n = 0) :
    energy source data n = energy source data m + ‖approximate source data n-approximate source data m‖^2 := by
  let S := Projection.sourceSpan (fun i : Fin m => source i.val)
  let current := approximate source data n
  have earlier : approximate source data m = S.starProjection current :=
    prefix_projection source data within exactRead
  change ‖current‖^2 = ‖approximate source data m‖^2 + ‖current-approximate source data m‖^2
  rw [earlier,← Submodule.starProjection_orthogonal_val]
  exact S.norm_sq_eq_add_norm_sq_starProjection current

theorem cauchy_from_budget (source : Nat → H) (data : Admitted source) :
    CauchySeq (approximate source data.val) := by
  let cost := energy source data.val
  let total := sSup (range cost)
  have ceiling (n : Nat) : cost n ≤ total := le_csSup data.property.2 ⟨n,rfl⟩
  refine Metric.cauchySeq_iff'.mpr ?_
  intro ε positive
  have tolerance : total-ε^2 < total := sub_lt_self total (pow_pos positive 2)
  obtain ⟨_,⟨N,rfl⟩,close⟩ := exists_lt_of_lt_csSup (Set.range_nonempty cost) tolerance
  refine ⟨N,fun n after => ?_⟩
  rw [dist_eq_norm]
  apply (sq_lt_sq₀ (norm_nonneg _) positive.le).mp
  have paid := energy_increment source data.val after (data.property.1 n)
  change cost n = cost N + ‖approximate source data.val n - approximate source data.val N‖^2 at paid
  linarith only [ceiling n,close,paid]

/-- Actual source data pay the exact finite equations and the bound on all generated fields. -/
def capture (source : Nat → H) (value : H) : Admitted source :=
  ⟨read source value, residual_original source value, ⟨‖value‖^2,by
    rintro _ ⟨n,rfl⟩
    let frame := fun i : Fin n => source i.val
    have observed : approximate source (read source value) n =
        (Projection.sourceSpan frame).starProjection value :=
      PrefixReadback.inverse_actual_rhs frame value
    change ‖approximate source (read source value) n‖^2 ≤ _
    rw [observed]
    exact pow_le_pow_left₀ (norm_nonneg _) (Submodule.norm_starProjection_apply_le _ _) 2⟩⟩

variable [CompleteSpace H]

/-- The readback is the limit of the existing finite inverses applied to the actual stream. -/
def realize (source : Nat → H) (data : Admitted source) : H :=
  limUnder atTop (approximate source data.val)

theorem realize_captured (source : Nat → H)
    (separates : ∀ x : H, (∀ i, read source x i = 0) → x = 0) (value : H) :
    realize source (capture source value) = value :=
  (PrefixReadback.inverse_tendsto source separates value).limUnder_eq

omit [CompleteSpace H] in
private theorem coordinate_exact (source : Nat → H) (data : Admitted source) (i : Nat) :
    (fun n => read source (approximate source data.val n) i) =ᶠ[atTop] fun _ => data.val i := by
  filter_upwards [eventually_ge_atTop (i+1)] with n after
  let index : Fin n := ⟨i,Nat.lt_of_succ_le after⟩
  have vector : Projection.rhs (fun j : Fin n => source j.val) (approximate source data.val n) =
      sample data.val n :=
    sub_eq_zero.mp (data.property.1 n)
  exact congrArg (fun coordinates : Coordinates (Fin n) => coordinates index) vector

theorem read_realized (source : Nat → H) (data : Admitted source) :
    read source (realize source data) = data.val := by
  funext i
  have converges : Tendsto (approximate source data.val) atTop (𝓝 (realize source data)) :=
    (cauchy_from_budget source data).tendsto_limUnder
  have measured : Tendsto (fun n => read source (approximate source data.val n) i) atTop
      (𝓝 (read source (realize source data) i)) :=
    ((innerSL ℂ (source i)).continuous.tendsto _).comp converges
  have fixed : Tendsto (fun n => read source (approximate source data.val n) i) atTop (𝓝 (data.val i)) :=
    (tendsto_congr' (coordinate_exact source data i)).2 tendsto_const_nhds
  exact tendsto_nhds_unique measured fixed

/-- Finite exact readback and bounded generated energy characterize the actual image. -/
theorem admitted_iff_image (source : Nat → H) (data : Nat → ℂ) :
    ((∀ n, residual source data n = 0) ∧ BddAbove (range (energy source data))) ↔
      ∃ x : H, read source x = data := by
  constructor
  · intro valid
    exact ⟨realize source ⟨data,valid⟩,read_realized source ⟨data,valid⟩⟩
  · rintro ⟨x,rfl⟩
    exact (capture source x).property

end SourceGeneratedFiniteGram.PrefixImage
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
