import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Heat
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Terms
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Integrals

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction
open LAlanine40K2025 UnifiedOrbitals BasinRefinement GaussianPrimitive SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource Polynomial MeasureTheory Set
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Laplace
open BasinRefinement.SourceCoulomb
open scoped BigOperators intervalIntegral Topology
noncomputable section

private theorem pairExponent_cast (s t : Term) :
    ((pairExponent s t : ℚ) : ℝ) = (s.exponent:ℝ) + (t.exponent:ℝ) := by
  rw [pairExponent]
  push_cast
  ring

/-- Penalty factorisation: the axis penalties sum to `pairPenalty`. -/
private theorem penalty_sum (s t : Term) :
    (∑ k : Fin 3, productPenalty (s.exponent:ℝ) (t.exponent:ℝ)
      (s.centre k : ℝ) (t.centre k : ℝ)) = (pairPenalty s t : ℝ) := by
  unfold pairPenalty productPenalty pairExponent
  push_cast
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The second-stage penalty sum is the Boys argument times `σ = τ/(γ+τ)`. -/
private theorem penalty2_sum (s t : Term) (C : Fin 3 → ℚ) (τ : ℝ) :
    (∑ k : Fin 3,
      (((s.exponent:ℝ)+(t.exponent:ℝ))*τ/(((s.exponent:ℝ)+(t.exponent:ℝ))+τ)) *
        ((pairAxisCentre s t k : ℝ) - (C k : ℝ))^2) =
      (boysArgument s t C : ℝ) *
        (τ/(((s.exponent:ℝ)+(t.exponent:ℝ))+τ)) := by
  have hγq : (↑(pairExponent s t) : ℝ) = (s.exponent:ℝ)+(t.exponent:ℝ) :=
    pairExponent_cast s t
  rw [← hγq]
  unfold boysArgument
  push_cast
  rw [← Finset.mul_sum]
  ring

/-- Product of per-axis eval₂'s is the eval₂ of the product polynomial. -/
private theorem axis_eval₂_prod (s t : Term) (C : Fin 3 → ℚ) (σ : ℝ) :
    (∏ k : Fin 3, (axisPolynomial s t C k).eval₂ (Rat.castHom ℝ) σ) =
      (attractionPolynomial s t C).eval₂ (Rat.castHom ℝ) σ := by
  unfold attractionPolynomial
  exact (map_prod (Polynomial.eval₂RingHom (Rat.castHom ℝ) σ) _ Finset.univ).symm

/-- For each heat parameter `tt > 0` the spatial integral factorises axis by axis. -/
theorem axis_split (s t : Term) (hs : 0 < s.exponent) (ht : 0 < t.exponent)
    (C : Fin 3 → ℚ) (tt : ℝ) (htt : 0 < tt) :
    ∫ x : Point, (value s zeroJet x * value t zeroJet x) *
        Real.exp (-(distance (x - fun k => (C k : ℝ)))^2 * tt^2) =
    (s.weight : ℝ) * t.weight * Real.exp (-(pairPenalty s t : ℝ)) *
      (Real.exp (-(boysArgument s t C : ℝ) *
          (tt^2/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))) *
        ((Real.sqrt (Real.pi/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)))^3 *
          (attractionPolynomial s t C).eval₂ (Rat.castHom ℝ)
            (tt^2/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)))) := by
  set Cv : Point := fun k => (C k : ℝ) with hCv
  have hτp : 0 < tt^2 := pow_pos htt 2
  have hγ : (0:ℝ) < (s.exponent:ℝ)+(t.exponent:ℝ) :=
    add_pos (by exact_mod_cast hs) (by exact_mod_cast ht)
  have hγτ : (0:ℝ) < (s.exponent:ℝ)+(t.exponent:ℝ)+tt^2 := add_pos hγ hτp
  have hDs : ∀ x : Point, (distance (x - Cv))^2 =
      ∑ k : Fin 3, (x k - Cv k)^2 := by
    intro x
    rw [distance, Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    simp only [Pi.sub_apply]
  have hexp : ∀ x : Point, Real.exp (-(distance (x - Cv))^2 * tt^2) =
      ∏ k : Fin 3, Real.exp (-tt^2 * (x k - Cv k)^2) := by
    intro x
    rw [hDs]
    rw [show -(∑ k : Fin 3, (x k - Cv k)^2) * tt^2 =
        ∑ k : Fin 3, -tt^2 * (x k - Cv k)^2 by
      rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring]
    exact Real.exp_sum Finset.univ _
  have hax : ∀ k : Fin 3, ∫ x : ℝ,
      shiftedGaussian (s.exponent:ℝ) (s.centre k) (s.powers k) x *
        shiftedGaussian (t.exponent:ℝ) (t.centre k) (t.powers k) x *
        Real.exp (-tt^2*(x-((C k : ℚ):ℝ))^2) =
      Real.exp (-productPenalty (s.exponent:ℝ) (t.exponent:ℝ)
          (s.centre k) (t.centre k)) *
        (Real.exp (-(((s.exponent:ℝ)+(t.exponent:ℝ))*tt^2/
            ((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))*
            ((pairAxisCentre s t k : ℝ)-(C k : ℝ))^2) *
          Real.sqrt (Real.pi/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)) *
          (axisPolynomial s t C k).eval₂ (Rat.castHom ℝ)
            (tt^2/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))) := by
    intro k
    exact axis_attraction_integral s.exponent t.exponent hs ht
      (s.centre k) (t.centre k) (C k) (s.powers k) (t.powers k) (tt^2) hτp
  calc ∫ x : Point, (value s zeroJet x * value t zeroJet x) *
          Real.exp (-(distance (x - Cv))^2 * tt^2)
      = ∫ x : Point, (s.weight : ℝ) * t.weight *
          ∏ k : Fin 3, (shiftedGaussian (s.exponent:ℝ) (s.centre k)
              (s.powers k) (x k) *
            shiftedGaussian (t.exponent:ℝ) (t.centre k) (t.powers k) (x k) *
            Real.exp (-tt^2 * (x k - Cv k)^2)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [term_product_form s t x, hexp x]
        rw [mul_assoc, ← Finset.prod_mul_distrib]
    _ = (s.weight : ℝ) * t.weight *
          ∏ k : Fin 3, ∫ x : ℝ,
            shiftedGaussian (s.exponent:ℝ) (s.centre k) (s.powers k) x *
            shiftedGaussian (t.exponent:ℝ) (t.centre k) (t.powers k) x *
            Real.exp (-tt^2 * (x - Cv k)^2) := by
        rw [integral_const_mul]
        congr 1
        simpa only [] using
          integral_fin_nat_prod_volume_eq_prod (fun a : Fin 3 => fun x : ℝ =>
            shiftedGaussian (s.exponent:ℝ) (s.centre a) (s.powers a) x *
              shiftedGaussian (t.exponent:ℝ) (t.centre a) (t.powers a) x *
              Real.exp (-tt^2 * (x - Cv a)^2))
    _ = (s.weight : ℝ) * t.weight *
          ∏ k : Fin 3, (Real.exp (-productPenalty (s.exponent:ℝ) (t.exponent:ℝ)
              (s.centre k) (t.centre k)) *
            (Real.exp (-(((s.exponent:ℝ)+(t.exponent:ℝ))*tt^2/
                ((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))*
                ((pairAxisCentre s t k : ℝ)-(C k : ℝ))^2) *
              Real.sqrt (Real.pi/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)) *
              (axisPolynomial s t C k).eval₂ (Rat.castHom ℝ)
                (tt^2/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)))) := by
        congr 1
        apply Finset.prod_congr rfl
        intro k _
        exact hax k
    _ = (s.weight : ℝ) * t.weight * Real.exp (-(pairPenalty s t : ℝ)) *
          (Real.exp (-(boysArgument s t C : ℝ) *
              (tt^2/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))) *
            ((Real.sqrt (Real.pi/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)))^3 *
              (attractionPolynomial s t C).eval₂ (Rat.castHom ℝ)
                (tt^2/((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2)))) := by
        rw [Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib,
          penalty_sum]
        rw [Finset.prod_mul_distrib]
        rw [Finset.prod_mul_distrib, ← Real.exp_sum]
        rw [show (∑ x : Fin 3,
            -(((s.exponent:ℝ)+(t.exponent:ℝ))*tt^2/
                ((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))*
              ((pairAxisCentre s t x:ℝ)-(C x:ℝ))^2) =
          -(∑ x : Fin 3,
            (((s.exponent:ℝ)+(t.exponent:ℝ))*tt^2/
                ((s.exponent:ℝ)+(t.exponent:ℝ)+tt^2))*
              ((pairAxisCentre s t x:ℝ)-(C x:ℝ))^2) by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring]
        rw [penalty2_sum]
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [axis_eval₂_prod]
        ring

/-- The primitive attraction integral in Boys form (computable coefficients). -/
noncomputable def primitiveAttraction (s t : Term) (C : Fin 3 → ℚ) : ℝ :=
  (s.weight : ℝ) * t.weight * (2 * Real.pi / (pairExponent s t : ℝ)) *
    Real.exp (-(pairPenalty s t : ℝ)) *
    ∑ j ∈ Finset.range (attractionOrder s t + 1),
      (attractionCoefficientQ s t C j : ℝ) * boys j (boysArgument s t C)

/-- Closed form: the primitive nuclear-attraction integral equals the Boys sum. -/
theorem primitive_attraction_closed (s t : Term)
    (hs : 0 < s.exponent) (ht : 0 < t.exponent) (C : Fin 3 → ℚ) :
    ∫ x : Point, value s zeroJet x * value t zeroJet x *
        kernel (x - fun k => (C k : ℝ)) =
      primitiveAttraction s t C := by
  set γ : ℝ := (s.exponent:ℝ) + (t.exponent:ℝ) with hγdef
  have hγ : 0 < γ := add_pos (by exact_mod_cast hs) (by exact_mod_cast ht)
  set T : ℝ := (boysArgument s t C : ℝ) with hTdef
  set AP : Polynomial ℚ := attractionPolynomial s t C with hAPdef
  set g : ℝ → ℝ := fun τ =>
      Real.exp (-T * (τ^2/(γ+τ^2))) *
        ((Real.sqrt (Real.pi/(γ+τ^2)))^3 *
          AP.eval₂ (Rat.castHom ℝ) (τ^2/(γ+τ^2))) with hgdef
  rw [attraction_heat_swap s t hs ht C]
  have inner : ∀ tt ∈ Ioi (0:ℝ),
      (∫ x : Point, (value s zeroJet x * value t zeroJet x) *
          Real.exp (-(distance (x - fun k => (C k : ℝ)))^2 * tt^2)) =
        ((s.weight:ℝ) * t.weight * Real.exp (-(pairPenalty s t : ℝ))) * g tt := by
    intro tt htt
    rw [axis_split s t hs ht C tt htt]
  rw [setIntegral_congr_fun measurableSet_Ioi inner]
  rw [integral_const_mul]
  have hgf : ∀ u ∈ Ioo (0:ℝ) 1,
      g (substMap γ u) * substDeriv γ u =
        (Real.pi*Real.sqrt Real.pi/γ) *
          (Real.exp (-T*u^2) * AP.eval₂ (Rat.castHom ℝ) (u^2)) := by
    intro u hu
    rw [hgdef]
    show (Real.exp (-T * ((substMap γ u)^2/(γ + (substMap γ u)^2))) *
        ((Real.sqrt (Real.pi/(γ + (substMap γ u)^2)))^3 *
          AP.eval₂ (Rat.castHom ℝ) ((substMap γ u)^2/(γ + (substMap γ u)^2)))) *
        substDeriv γ u =
      _
    rw [substMap_ratio γ hγ u hu]
    rw [show Real.exp (-T * u^2) * ((Real.sqrt (Real.pi/(γ+(substMap γ u)^2)))^3 *
          AP.eval₂ (Rat.castHom ℝ) (u^2)) * substDeriv γ u =
        Real.exp (-T * u^2) * AP.eval₂ (Rat.castHom ℝ) (u^2) *
          ((Real.sqrt (Real.pi/(γ+(substMap γ u)^2)))^3 * substDeriv γ u) by ring]
    rw [subst_density γ hγ u hu]
    ring
  rw [subst_integral γ hγ g]
  rw [setIntegral_congr_fun measurableSet_Ioo hgf]
  rw [integral_const_mul]
  have hAPeval : ∀ u : ℝ,
      AP.eval₂ (Rat.castHom ℝ) (u^2) =
      ∑ j ∈ Finset.range (attractionOrder s t + 1),
        (attractionCoefficientQ s t C j:ℝ) * (u^2)^j := by
    intro u
    rw [hAPdef, eval₂_eq_sum]
    rw [sum_over_range _ (fun n => by simp)]
    have hsub : Finset.range (attractionDegree s t C + 1) ⊆
        Finset.range (attractionOrder s t + 1) :=
      Finset.range_subset.mpr (fun x hx => Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le hx
          (Nat.add_le_add_right (attraction_degree_le s t C) 1)))
    have hq : ∀ j : ℕ,
        (Rat.castHom ℝ) ((attractionPolynomial s t C).coeff j) =
          (attractionCoefficientQ s t C j:ℝ) := by
      intro j
      rw [Rat.coe_castHom]
      rw [show (attractionPolynomial s t C).coeff j =
          attractionCoefficientQ s t C j from
        attraction_coefficient_evaluated s t C j]
    simp only [hq]
    have hzero : ∀ j ∈ Finset.range (attractionOrder s t + 1),
        j ∉ Finset.range (attractionDegree s t C + 1) →
        (attractionCoefficientQ s t C j:ℝ) * (u^2)^j = 0 := by
      intro j _ hj
      rw [Finset.mem_range] at hj
      simp only [attractionDegree] at hj
      rw [show attractionCoefficientQ s t C j = 0 by
        rw [← attraction_coefficient_evaluated]
        exact coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
    exact Finset.sum_subset hsub hzero
  have hboys : ∫ u in Ioo (0:ℝ) 1,
        Real.exp (-T*u^2) * AP.eval₂ (Rat.castHom ℝ) (u^2) =
      ∑ j ∈ Finset.range (attractionOrder s t + 1),
        (attractionCoefficientQ s t C j:ℝ) * boys j T := by
    have hconv : (∫ u in Ioo (0:ℝ) 1,
        Real.exp (-T*u^2) * AP.eval₂ (Rat.castHom ℝ) (u^2)) =
        ∫ u in (0:ℝ)..1,
          Real.exp (-T*u^2) * AP.eval₂ (Rat.castHom ℝ) (u^2) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact setIntegral_congr_set Ioo_ae_eq_Ioc
    rw [hconv]
    have hev : ∀ u : ℝ, Real.exp (-T*u^2) * AP.eval₂ (Rat.castHom ℝ) (u^2) =
        ∑ j ∈ Finset.range (attractionOrder s t + 1),
          (attractionCoefficientQ s t C j:ℝ) *
            (u^(2*j) * Real.exp (-T*u^2)) := by
      intro u
      rw [hAPeval u, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [pow_mul]
      ring
    rw [intervalIntegral.integral_congr (fun u _ => hev u)]
    have hii : ∀ j ∈ Finset.range (attractionOrder s t + 1),
        IntervalIntegrable
          (fun u : ℝ => (attractionCoefficientQ s t C j:ℝ) *
            (u^(2*j) * Real.exp (-T*u^2))) volume (0:ℝ) 1 :=
      fun j _ => ((continuous_const.mul
        ((continuous_pow _).mul
          (Real.continuous_exp.comp
            (continuous_const.mul (continuous_pow 2)))))).intervalIntegrable 0 1
    rw [intervalIntegral.integral_finsetSum hii]
    apply Finset.sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul]
    rfl
  rw [hboys]
  unfold primitiveAttraction
  rw [hγdef, hTdef, ← pairExponent_cast]
  have hconst : (2/Real.sqrt Real.pi) *
      (Real.pi*Real.sqrt Real.pi/(pairExponent s t:ℝ)) =
      2*Real.pi/(pairExponent s t:ℝ) := by
    field_simp [Real.sqrt_ne_zero'.mpr Real.pi_pos,
      ne_of_gt (by exact_mod_cast add_pos hs ht : (0:ℝ) < (pairExponent s t:ℝ))]
  rw [show (2/Real.sqrt Real.pi) *
        ((s.weight:ℝ)*t.weight*Real.exp (-(pairPenalty s t:ℝ)) *
          (Real.pi*Real.sqrt Real.pi/(pairExponent s t:ℝ) *
            ∑ j ∈ Finset.range (attractionOrder s t + 1),
              (attractionCoefficientQ s t C j:ℝ) * boys j T)) =
      ((2/Real.sqrt Real.pi)*(Real.pi*Real.sqrt Real.pi/(pairExponent s t:ℝ))) *
        ((s.weight:ℝ)*t.weight*Real.exp (-(pairPenalty s t:ℝ)) *
          ∑ j ∈ Finset.range (attractionOrder s t + 1),
            (attractionCoefficientQ s t C j:ℝ) * boys j T) by ring]
  rw [hconst]
  ring

/-- Sanity control: same-centre s-type pair reduces to `w_s w_t·2π/γ`. -/
theorem primitive_s_type_same_centre (s t : Term) (C : Fin 3 → ℚ)
    (hs : 0 < s.exponent) (ht : 0 < t.exponent)
    (hps : s.powers = fun _ => 0) (hpt : t.powers = fun _ => 0)
    (hcs : s.centre = C) (hct : t.centre = C) :
    primitiveAttraction s t C =
      (s.weight:ℝ) * t.weight * (2*Real.pi/(pairExponent s t:ℝ)) := by
  have hγq : 0 < pairExponent s t := add_pos hs ht
  unfold primitiveAttraction
  have horder : attractionOrder s t = 0 := by
    unfold attractionOrder
    simp [hps, hpt]
  rw [horder, Finset.sum_range_one]
  have hpen : pairPenalty s t = 0 := by
    unfold pairPenalty
    simp [hcs, hct]
  have harg : boysArgument s t C = 0 := by
    unfold boysArgument pairAxisCentre
    have hrp : ∀ k : Fin 3,
        rationalProductCentre s.exponent t.exponent (s.centre k) (t.centre k) =
          C k := by
      intro k
      rw [hcs, hct]
      unfold rationalProductCentre
      field_simp [ne_of_gt (add_pos hs ht)]
    simp only [hrp]
    simp [sub_self]
  rw [harg, hpen]
  have hp0 : ∀ k : Fin 3, s.powers k = 0 := fun k => congrFun hps k
  have hq0 : ∀ k : Fin 3, t.powers k = 0 := fun k => congrFun hpt k
  have hax0 : ∀ k : Fin 3, axisCoeffQ s t C k 0 = 1 := by
    intro k
    simp only [axisCoeffQ, axisScaledCoeffQ, hp0 k, hq0 k]
    simp only [axisInnerCoeff, linearPowCoeff, oneMinusCoeff]
    simp [rationalMoment]
  have hQ0 : attractionCoefficientQ s t C 0 = 1 := by
    unfold attractionCoefficientQ
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
    rw [hax0 0, hax0 1, hax0 2]
    norm_num
  rw [hQ0]
  simp [boys_zero_arg]

end
end LAlanine40K2025.UnifiedOrbitals.Attraction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
