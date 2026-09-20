/-
  Lemma 3 (contraction skeleton): fading-memory observational agreement.

  This is the first machine-checkable slice of the dynamical Lemma 3. It does
  not prove a spectral-radius theorem. Instead it proves the stable core that
  the spectral / Lyapunov certificates should feed:

    contraction + eventual shared observation cell
      -> eventual observational equality.

  Agent-memory reading:
  - `T` is one common future recall/update step.
  - `obs` is the routing / ranking observation.
  - An observation cell is a region that does not cross an argmax tie boundary;
    inside the cell, `obs` is constant.
  - A fixed-point margin ball is a concrete observation cell around a stable
    route attractor.
-/

import Mathlib

open scoped BigOperators

/-! ## Observation cells -/

/-- `obs` is constant on a region. For argmax routing, this is a single
    no-tie cell where the top route does not change. -/
def ObsConstantOn {X Y : Type*} (obs : X → Y) (C : Set X) : Prop :=
  ∀ ⦃x y : X⦄, x ∈ C → y ∈ C → obs x = obs y

/-- If both trajectories are eventually in the same observation cell, their
    observations eventually agree. This is the topological/routing part of
    Lemma 3, separated from the contraction proof that gets them into the cell. -/
theorem eventual_obs_eq_of_eventually_in_constant_cell
    {X Y : Type*} {T : X → X} {obs : X → Y} {C : Set X} {x y : X}
    (hobs : ObsConstantOn obs C)
    (hxin : ∃ N, ∀ n, N ≤ n → (T^[n]) x ∈ C)
    (hyin : ∃ N, ∀ n, N ≤ n → (T^[n]) y ∈ C) :
    ∃ N, ∀ n, N ≤ n → obs ((T^[n]) x) = obs ((T^[n]) y) := by
  rcases hxin with ⟨Nx, hx⟩
  rcases hyin with ⟨Ny, hy⟩
  refine ⟨max Nx Ny, ?_⟩
  intro n hn
  exact hobs (hx n (le_trans (le_max_left Nx Ny) hn))
    (hy n (le_trans (le_max_right Nx Ny) hn))

/-! ## Contraction toward a fixed route attractor -/

/-- Iterating a contraction toward a fixed point shrinks distance by `q^n`.

    This is the formal fading-memory inequality. It is deliberately stated
    with an explicit fixed point rather than invoking a Banach fixed-point
    theorem; runtime certificates can provide the stable route attractor or
    local cell separately. -/
theorem dist_iterate_fixed_le_geometric
    {X : Type*} [PseudoMetricSpace X]
    (T : X → X) {q : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hcontract : ∀ x y : X, dist (T x) (T y) ≤ q * dist x y)
    {z : X} (hz : T z = z) :
    ∀ n x, dist ((T^[n]) x) z ≤ q ^ n * dist x z := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        dist ((T^[n.succ]) x) z = dist (T ((T^[n]) x)) (T z) := by
          rw [hz]
          simp [Function.iterate_succ_apply']
        _ ≤ q * dist ((T^[n]) x) z := hcontract ((T^[n]) x) z
        _ ≤ q * (q ^ n * dist x z) :=
          mul_le_mul_of_nonneg_left (ih x) hq_nonneg
        _ = q ^ n.succ * dist x z := by
          rw [pow_succ]
          ring

/-! ## Margin ball: local-constant observation near an attractor -/

/-- If a contraction eventually puts both trajectories inside the same
    no-tie margin ball around a fixed point, observations eventually agree.

    The `hxtail` / `hytail` hypotheses are the explicit runtime certificate
    that the geometric tails are below the margin. A later spectral/Lyapunov
    harness should produce these bounds. -/
theorem eventual_obs_eq_of_fixed_point_margin
    {X Y : Type*} [PseudoMetricSpace X]
    {T : X → X} {q ε : ℝ} {z x y : X} {obs : X → Y}
    (hq_nonneg : 0 ≤ q)
    (hcontract : ∀ a b : X, dist (T a) (T b) ≤ q * dist a b)
    (hz : T z = z)
    (hobs_margin : ∀ a : X, dist a z < ε → obs a = obs z)
    (hxtail : ∃ Nx, ∀ n, Nx ≤ n → q ^ n * dist x z < ε)
    (hytail : ∃ Ny, ∀ n, Ny ≤ n → q ^ n * dist y z < ε) :
    ∃ N, ∀ n, N ≤ n → obs ((T^[n]) x) = obs ((T^[n]) y) := by
  rcases hxtail with ⟨Nx, hx_tail⟩
  rcases hytail with ⟨Ny, hy_tail⟩
  refine ⟨max Nx Ny, ?_⟩
  intro n hn
  have hx_bound := dist_iterate_fixed_le_geometric T hq_nonneg hcontract hz n x
  have hy_bound := dist_iterate_fixed_le_geometric T hq_nonneg hcontract hz n y
  have hx_close : dist ((T^[n]) x) z < ε :=
    lt_of_le_of_lt hx_bound (hx_tail n (le_trans (le_max_left Nx Ny) hn))
  have hy_close : dist ((T^[n]) y) z < ε :=
    lt_of_le_of_lt hy_bound (hy_tail n (le_trans (le_max_right Nx Ny) hn))
  calc
    obs ((T^[n]) x) = obs z := hobs_margin ((T^[n]) x) hx_close
    _ = obs ((T^[n]) y) := (hobs_margin ((T^[n]) y) hy_close).symm

/-! ## Lyapunov certificate bridge -/

/-- A Lyapunov-style contraction over an arbitrary nonnegative energy/distance
    witness `V`. Runtime certificates should instantiate `V` with a quadratic
    form such as `vᵀ P v`. -/
def LyapunovContraction {X : Type*} (V : X → X → ℝ) (T : X → X) (r : ℝ) : Prop :=
  ∀ x y : X, V (T x) (T y) ≤ r * V x y

/-- Lyapunov contraction toward a fixed point gives the same geometric tail as
    the metric contraction theorem above, but in the certified energy `V`.

    For a matrix certificate `Jᵀ P J ≤ q² P`, instantiate `r = q²` and
    `V x y = (x-y)ᵀ P (x-y)`. -/
theorem lyapunov_iterate_fixed_le_geometric
    {X : Type*} (V : X → X → ℝ) (T : X → X) {r : ℝ}
    (hr_nonneg : 0 ≤ r)
    (hcontract : LyapunovContraction V T r)
    {z : X} (hz : T z = z) :
    ∀ n x, V ((T^[n]) x) z ≤ r ^ n * V x z := by
  intro n
  induction n with
  | zero =>
      intro x
      simp
  | succ n ih =>
      intro x
      calc
        V ((T^[n.succ]) x) z = V (T ((T^[n]) x)) (T z) := by
          rw [hz]
          simp [Function.iterate_succ_apply']
        _ ≤ r * V ((T^[n]) x) z := hcontract ((T^[n]) x) z
        _ ≤ r * (r ^ n * V x z) :=
          mul_le_mul_of_nonneg_left (ih x) hr_nonneg
        _ = r ^ n.succ * V x z := by
          rw [pow_succ]
          ring

/-- If a Lyapunov certificate eventually puts both trajectories inside the
    same observation-safe energy ball, observations eventually agree. -/
theorem eventual_obs_eq_of_lyapunov_margin
    {X Y : Type*} {V : X → X → ℝ}
    {T : X → X} {r ε : ℝ} {z x y : X} {obs : X → Y}
    (hr_nonneg : 0 ≤ r)
    (hcontract : LyapunovContraction V T r)
    (hz : T z = z)
    (hobs_margin : ∀ a : X, V a z < ε → obs a = obs z)
    (hxtail : ∃ Nx, ∀ n, Nx ≤ n → r ^ n * V x z < ε)
    (hytail : ∃ Ny, ∀ n, Ny ≤ n → r ^ n * V y z < ε) :
    ∃ N, ∀ n, N ≤ n → obs ((T^[n]) x) = obs ((T^[n]) y) := by
  rcases hxtail with ⟨Nx, hx_tail⟩
  rcases hytail with ⟨Ny, hy_tail⟩
  refine ⟨max Nx Ny, ?_⟩
  intro n hn
  have hx_bound := lyapunov_iterate_fixed_le_geometric V T hr_nonneg hcontract hz n x
  have hy_bound := lyapunov_iterate_fixed_le_geometric V T hr_nonneg hcontract hz n y
  have hx_close : V ((T^[n]) x) z < ε :=
    lt_of_le_of_lt hx_bound (hx_tail n (le_trans (le_max_left Nx Ny) hn))
  have hy_close : V ((T^[n]) y) z < ε :=
    lt_of_le_of_lt hy_bound (hy_tail n (le_trans (le_max_right Nx Ny) hn))
  calc
    obs ((T^[n]) x) = obs z := hobs_margin ((T^[n]) x) hx_close
    _ = obs ((T^[n]) y) := (hobs_margin ((T^[n]) y) hy_close).symm

/-! ## Quadratic-form semantics for `Jᵀ P J ≤ q² P` -/

variable {ι : Type*} [Fintype ι]

/-- Quadratic form `vᵀ P v`. -/
def quadraticForm (P : Matrix ι ι ℝ) (v : ι → ℝ) : ℝ :=
  v ⬝ᵥ (Matrix.mulVec P v)

/-- Quadratic-form semantics of the Lyapunov matrix inequality
    `Jᵀ P J ≤ q² P`: every direction loses at least a `q²` factor in
    `P`-energy after one linearized reducer step. -/
def QuadraticLyapunovCertificate (J P : Matrix ι ι ℝ) (q : ℝ) : Prop :=
  ∀ v : ι → ℝ, quadraticForm P (Matrix.mulVec J v) ≤ q ^ 2 * quadraticForm P v

/-- The certified quadratic energy between two states. -/
def quadraticVDistance (P : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ :=
  quadraticForm P (x - y)

/-- A quadratic Lyapunov certificate makes the linearized reducer
    `x ↦ J *ᵥ x` a Lyapunov contraction with rate `q²`. -/
theorem quadratic_lyapunov_certificate_to_contraction
    (J P : Matrix ι ι ℝ) (q : ℝ)
    (hcert : QuadraticLyapunovCertificate J P q) :
    LyapunovContraction (quadraticVDistance P) (fun x : ι → ℝ => Matrix.mulVec J x) (q ^ 2) := by
  intro x y
  unfold quadraticVDistance
  rw [← Matrix.mulVec_sub]
  exact hcert (x - y)

/-! ## Diagonal / polarity-separated spectral slice -/

/-- Coordinate energy used by the diagonal active-subspace certificate. -/
def coordinateEnergy (x : ι → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- A diagonal linearized reducer represented by its coordinate gains. -/
def diagonalStep (d : ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => d i * x i

/-- If every coordinate gain is bounded by `q` in squared magnitude, then the
    diagonal / polarity-separated active subspace contracts in coordinate
    energy by `q²`.

    This is the Lean version of the runtime `P=I` active-subspace certificate.
    It is not the general matrix spectral-radius theorem. -/
theorem diagonal_energy_contracts_of_sq_le
    (d : ι → ℝ) {q : ℝ}
    (hbound : ∀ i, d i ^ 2 ≤ q ^ 2) :
    ∀ x : ι → ℝ, coordinateEnergy (diagonalStep d x) ≤ q ^ 2 * coordinateEnergy x := by
  intro x
  unfold coordinateEnergy diagonalStep
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i _
  have hx_nonneg : 0 ≤ x i ^ 2 := sq_nonneg (x i)
  have hmul := mul_le_mul_of_nonneg_right (hbound i) hx_nonneg
  nlinarith [hmul]

/-!
  Summary of Lemma 3 Lean status:
  - `eventual_obs_eq_of_eventually_in_constant_cell` proves the routing-cell
    part: eventual membership in one no-tie cell gives eventual equality.
  - `dist_iterate_fixed_le_geometric` proves the contraction/fading-memory
    distance bound.
  - `eventual_obs_eq_of_fixed_point_margin` composes them with an explicit
    margin-tail certificate.
  - `lyapunov_iterate_fixed_le_geometric` and
    `eventual_obs_eq_of_lyapunov_margin` prove the same bridge for an arbitrary
    Lyapunov energy `V`.
  - `quadratic_lyapunov_certificate_to_contraction` connects the quadratic-form
    semantics of `Jᵀ P J ≤ q² P` to that Lyapunov bridge.
  - `diagonal_energy_contracts_of_sq_le` proves the active diagonal /
    polarity-separated spectral slice consumed by the current `P=I` runtime
    certificate.

  Not yet proven here:
  - spectral-radius ⇒ contraction;
  - Lyapunov / interval certificate generation for a concrete reducer;
  - nonlinear gauge non-leakage for the true router.
-/
