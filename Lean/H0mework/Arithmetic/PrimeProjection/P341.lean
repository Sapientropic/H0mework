import H0mework.Realization.Relations.P295
import H0mework.Arithmetic.PrimeSearch.P340

/-!
# Proposition 341: special-fiber deformation boundary

The saturation family gives a genuine deformation parameter.  In the chain
complex face, `saturate σ K` rescales the differential by the keep-rate
`1 - σ`: nonzero keep-rate is the general fiber, while `σ = 1` is the special
fiber where the differential collapses to zero.

In the arithmetic sigma-carrier face, the same boundary appears sharply:
`σ = 1` collapses all positive exponents to the absorbing rate `1`, so the
special-fiber Goldbach statement is trivially true but not exponent-faithful.
On every general fiber `0 < σ < 1`, P308 says sigma-Goldbach is exactly ordinary
Goldbach.

Thus special-fiber unification constrains the general fiber only through an
explicit specialization-transfer certificate.  Supplying that certificate has
ordinary Goldbach strength; without it, the special fiber is too collapsed to
prove the general-fiber statement.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid

/-! ## Chain-complex deformation: general and special fibers -/

namespace SaturatedChainComplex

variable {R : Type*} [Field R]
variable {C : ℕ → Type*}
variable [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]

/-- A nonzero keep-rate is the algebraic general-fiber condition for the
saturation-rescaled chain complex. -/
def IsGeneralFiber (σ : R) : Prop :=
  1 - σ ≠ 0

/-- Full saturation is the special fiber. -/
def IsSpecialFiber (σ : R) : Prop :=
  σ = 1

/-- THEOREM 1: on the general fiber, cycles are exactly the original cycles. -/
theorem generalFiber_cycles_preserved
    {σ : R} (hσ : IsGeneralFiber σ)
    (K : SequentialChainComplex R C) (n : ℕ) (x : C n) :
    IsCycle (saturate σ K) n x ↔ IsCycle K n x :=
  isCycle_saturate_iff_of_keep_ne hσ K n x

/-- THEOREM 2: on the general fiber, boundaries are exactly the original
boundaries. -/
theorem generalFiber_boundaries_preserved
    {σ : R} (hσ : IsGeneralFiber σ)
    (K : SequentialChainComplex R C) (n : ℕ) (x : C (n + 1)) :
    IsBoundary (saturate σ K) n x ↔ IsBoundary K n x :=
  isBoundary_saturate_iff_of_keep_ne hσ K n x

/-- THEOREM 3: on the special fiber, every chain is a cycle. -/
theorem specialFiber_all_cycles
    {σ : R} (hσ : IsSpecialFiber σ)
    (K : SequentialChainComplex R C) (n : ℕ) (x : C n) :
    IsCycle (saturate σ K) n x := by
  subst hσ
  exact isCycle_saturate_one K n x

/-- THEOREM 4: on the special fiber, boundaries are exactly zero. -/
theorem specialFiber_boundaries_zero_iff
    {σ : R} (hσ : IsSpecialFiber σ)
    (K : SequentialChainComplex R C) (n : ℕ) (x : C (n + 1)) :
    IsBoundary (saturate σ K) n x ↔ x = 0 := by
  subst hσ
  exact isBoundary_saturate_one_iff K n x

/-- A specialization-transfer certificate is the extra datum needed to push a
property from the collapsed special fiber back to nonzero-keep general fibers.
It is not automatic from saturation alone. -/
structure SpecializationTransfer (PropertyAt : R → Prop) : Prop where
  transfer :
    PropertyAt 1 -> ∀ ⦃σ : R⦄, IsGeneralFiber σ -> PropertyAt σ

/-- THEOREM 5: special-fiber truth controls a general fiber exactly when a
specialization-transfer certificate has been supplied. -/
theorem specialFiber_controls_general_of_transfer
    {PropertyAt : R → Prop}
    (T : SpecializationTransfer (R := R) PropertyAt)
    (hspecial : PropertyAt 1)
    {σ : R} (hσ : IsGeneralFiber σ) :
    PropertyAt σ :=
  T.transfer hspecial hσ

/-- A compact certificate for the chain-complex deformation boundary. -/
structure SaturationDeformationBoundaryCertificate
    (K : SequentialChainComplex R C) : Prop where
  general_cycles :
    ∀ {σ : R}, IsGeneralFiber σ ->
      ∀ n x, IsCycle (saturate σ K) n x ↔ IsCycle K n x
  general_boundaries :
    ∀ {σ : R}, IsGeneralFiber σ ->
      ∀ n x, IsBoundary (saturate σ K) n x ↔ IsBoundary K n x
  special_cycles :
    ∀ {σ : R}, IsSpecialFiber σ ->
      ∀ n x, IsCycle (saturate σ K) n x
  special_boundaries :
    ∀ {σ : R}, IsSpecialFiber σ ->
      ∀ n x, IsBoundary (saturate σ K) n x ↔ x = 0
  transfer_gate :
    ∀ {PropertyAt : R → Prop},
      SpecializationTransfer (R := R) PropertyAt ->
        PropertyAt 1 ->
          ∀ {σ : R}, IsGeneralFiber σ -> PropertyAt σ

/-- THEOREM 6: every sequential chain complex carries the canonical
general/special-fiber deformation boundary certificate. -/
theorem saturationDeformationBoundaryCertificate
    (K : SequentialChainComplex R C) :
    SaturationDeformationBoundaryCertificate K where
  general_cycles := by
    intro σ hσ n x
    exact generalFiber_cycles_preserved hσ K n x
  general_boundaries := by
    intro σ hσ n x
    exact generalFiber_boundaries_preserved hσ K n x
  special_cycles := by
    intro σ hσ n x
    exact specialFiber_all_cycles hσ K n x
  special_boundaries := by
    intro σ hσ n x
    exact specialFiber_boundaries_zero_iff hσ K n x
  transfer_gate := by
    intro PropertyAt T hspecial σ hσ
    exact specialFiber_controls_general_of_transfer T hspecial hσ

end SaturatedChainComplex

/-! ## Arithmetic special fiber: collapsed truth versus faithful general fiber -/

namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- THEOREM 7: at the absorbing special fiber `σ = 1`, every positive
iteration exponent has effective rate `1`. -/
theorem iteratedRate_specialFiber_one_of_pos
    {n : ℕ} (hn : 0 < n) :
    iteratedRate (1 : K) n = 1 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  simp [iteratedRate, hn0]

/-- THEOREM 8: the special fiber is not exponent-faithful: positive exponents
collapse to the same effective rate. -/
theorem specialFiber_iteratedRate_not_injective :
    Not (Function.Injective (fun n : ℕ => iteratedRate (1 : K) n)) := by
  intro hinj
  have hcollapse :
      iteratedRate (1 : K) 1 = iteratedRate (1 : K) 2 := by
    simp [iteratedRate]
  have hnat : (1 : ℕ) = 2 := hinj hcollapse
  norm_num at hnat

/-- THEOREM 9: special-fiber sigma-Goldbach is trivially true for every
positive exponent, because both sides have collapsed to the absorbing rate. -/
theorem specialFiber_sigmaGoldbachDecomposition_of_pos
    {n : ℕ} (hn : 0 < n) :
    SigmaGoldbachDecomposition (1 : K) n := by
  let p : PrimeExponent := ⟨2, by norm_num⟩
  refine ⟨p, p, ?_⟩
  have hnrate : iteratedRate (1 : K) n = 1 :=
    iteratedRate_specialFiber_one_of_pos hn
  have hprate : iteratedRate (1 : K) p.1 = 1 := by
    have hp : 0 < p.1 := by
      norm_num [p]
    exact iteratedRate_specialFiber_one_of_pos hp
  calc
    iteratedRate (1 : K) n = 1 := hnrate
    _ = satOrField (iteratedRate (1 : K) p.1)
          (iteratedRate (1 : K) p.1) := by
      simp [hprate, satOrField]

/-- THEOREM 10: the special fiber satisfies the even sigma-Goldbach statement
vacuously/trivially. -/
theorem specialFiber_sigmaEvenGoldbachStatement :
    SigmaEvenGoldbachStatement (1 : K) := by
  intro n hn
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hpos : 0 < 2 * n := Nat.mul_pos (by norm_num) hnpos
  exact specialFiber_sigmaGoldbachDecomposition_of_pos hpos

/-- A specialization-transfer principle for sigma-Goldbach: special-fiber
truth is allowed to constrain a nondegenerate general fiber only if this
additional transfer datum is supplied. -/
def SigmaGoldbachSpecializationTransfer (K : Type*)
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] : Prop :=
  ∀ ⦃σ : K⦄, 0 < σ -> σ < 1 ->
    SigmaEvenGoldbachStatement (1 : K) -> SigmaEvenGoldbachStatement σ

/-- THEOREM 11: if a specialization-transfer certificate pushes the collapsed
special-fiber Goldbach statement to any nondegenerate general fiber, ordinary
Goldbach follows.  This is the precise strength of the proposed special-fiber
method. -/
theorem specialFiber_transfer_implies_evenGoldbach
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (T : SigmaGoldbachSpecializationTransfer K) :
    EvenGoldbachStatement := by
  have hgeneral : SigmaEvenGoldbachStatement σ :=
    T hσ0 hσ1 specialFiber_sigmaEvenGoldbachStatement
  exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mp hgeneral

/-- THEOREM 12: conversely, ordinary Goldbach supplies the general-fiber
Goldbach statement on every nondegenerate fiber; the special fiber itself
supplies no exponent-faithful information. -/
theorem evenGoldbach_gives_generalFiber_sigmaGoldbach
    (hG : EvenGoldbachStatement)
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaEvenGoldbachStatement σ :=
  (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mpr hG

/-- A compact arithmetic certificate for the special/general fiber boundary. -/
structure P341ArithmeticSpecialFiberBoundaryCertificate : Prop where
  special_positive_collapse :
    ∀ n : ℕ, 0 < n -> iteratedRate (1 : K) n = 1
  special_not_faithful :
    Not (Function.Injective (fun n : ℕ => iteratedRate (1 : K) n))
  special_goldbach_trivial :
    ∀ n : ℕ, 0 < n -> SigmaGoldbachDecomposition (1 : K) n
  special_even_goldbach :
    SigmaEvenGoldbachStatement (1 : K)
  general_fiber_iff_ordinary :
    ∀ {σ : K}, 0 < σ -> σ < 1 ->
      (SigmaEvenGoldbachStatement σ ↔ EvenGoldbachStatement)
  transfer_implies_ordinary :
    ∀ {σ : K}, 0 < σ -> σ < 1 ->
      SigmaGoldbachSpecializationTransfer K -> EvenGoldbachStatement
  ordinary_gives_general :
    EvenGoldbachStatement ->
      ∀ {σ : K}, 0 < σ -> σ < 1 -> SigmaEvenGoldbachStatement σ

/-- THEOREM 13: the canonical arithmetic special-fiber boundary certificate. -/
theorem p341ArithmeticSpecialFiberBoundaryCertificate :
    P341ArithmeticSpecialFiberBoundaryCertificate (K := K) where
  special_positive_collapse := by
    intro n hn
    exact iteratedRate_specialFiber_one_of_pos hn
  special_not_faithful := specialFiber_iteratedRate_not_injective
  special_goldbach_trivial := by
    intro n hn
    exact specialFiber_sigmaGoldbachDecomposition_of_pos hn
  special_even_goldbach := specialFiber_sigmaEvenGoldbachStatement
  general_fiber_iff_ordinary := by
    exact fun {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) =>
      sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo (K := K) hσ0 hσ1
  transfer_implies_ordinary := by
    exact fun {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) T =>
      specialFiber_transfer_implies_evenGoldbach (K := K) hσ0 hσ1 T
  ordinary_gives_general := by
    exact fun hG {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) =>
      evenGoldbach_gives_generalFiber_sigmaGoldbach (K := K) hG hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
