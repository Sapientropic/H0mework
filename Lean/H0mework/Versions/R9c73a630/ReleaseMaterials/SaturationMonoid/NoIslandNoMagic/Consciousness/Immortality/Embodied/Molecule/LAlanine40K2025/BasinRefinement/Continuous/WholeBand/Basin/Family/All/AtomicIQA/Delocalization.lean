import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.Population
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.Normalize

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
open SourceGaussianModel SourceFiniteData SourceCoulomb GlobalSource ContinuousGradient Set MeasureTheory Function
open LAlanine40K2025.UnifiedOrbitals
open LAlanine40K2025.UnifiedOrbitals.Frame
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree
open scoped BigOperators Topology
noncomputable section

/-- Exchange-hole (Fermi-hole) density of an ordered point pair:
    `|⟪v(z₂), v(z₁)⟫|²` for the occupied orbital vector `v`. -/
def holeDensity (z : Point × Point) : ℝ :=
  ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖^2

theorem hole_density_nonnegative (z : Point × Point) : 0 ≤ holeDensity z :=
  sq_nonneg _

theorem hole_density_swap (z : Point × Point) : holeDensity z.swap = holeDensity z := by
  unfold holeDensity Prod.swap
  have h : inner ℂ (occupiedVector z.1) (occupiedVector z.2) =
      star (inner ℂ (occupiedVector z.2) (occupiedVector z.1)) :=
    (inner_conj_symm _ _).symm
  rw [h,norm_star]

theorem normalized_orbital_continuous (b : Basis) :
    Continuous (normalizedOrbital b) := by
  unfold normalizedOrbital expansion
  exact continuous_finsetSum _ fun c _ =>
    ((orbital_contDiff (sourceTerms c) zeroJet 0).continuous).const_mul _

theorem oneBodyKernel_pair_continuous :
    Continuous (fun z : Point × Point => oneBodyKernel z.1 z.2) := by
  unfold oneBodyKernel
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => ?_
  exact (continuous_const.mul
    (Complex.continuous_ofReal.comp ((normalized_orbital_continuous i).comp
      continuous_fst))).mul
    (Complex.continuous_ofReal.comp ((normalized_orbital_continuous k).comp
      continuous_snd))

theorem hole_density_continuous : Continuous holeDensity := by
  have h : Continuous fun z : Point × Point =>
      inner ℂ (occupiedVector z.2) (occupiedVector z.1) := by
    convert oneBodyKernel_pair_continuous using 1
    funext z
    exact (kernel_inner z.1 z.2).symm
  exact h.norm.pow 2

theorem hole_density_integrable : Integrable holeDensity := by
  have onedim : Integrable (fun x : Point => ‖occupiedVector x‖^2) := by
    convert projected_density_integrable.const_mul (1/2 : ℝ) using 1
    funext x
    rw [projected_density_norm]
    ring
  have gint : Integrable (fun z : Point × Point =>
      ‖occupiedVector z.1‖^2 * ‖occupiedVector z.2‖^2) :=
    onedim.mul_prod onedim
  apply gint.mono' hole_density_continuous.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have cs : ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖ ≤
      ‖occupiedVector z.2‖ * ‖occupiedVector z.1‖ := norm_inner_le_norm _ _
  have sq := pow_le_pow_left₀ (norm_nonneg _) cs 2
  rw [Real.norm_of_nonneg (hole_density_nonnegative z)]
  calc holeDensity z
      = ‖inner ℂ (occupiedVector z.2) (occupiedVector z.1)‖^2 := rfl
    _ ≤ (‖occupiedVector z.2‖ * ‖occupiedVector z.1‖)^2 := sq
    _ = ‖occupiedVector z.1‖^2 * ‖occupiedVector z.2‖^2 := by
        rw [mul_pow]; ring

/-- Expansion of `star (occupiedValue a y) * occupiedValue b y` over the basis. -/
private theorem occupiedPair_expand (y : Point) (a b : OccupiedSlot) :
    star (occupiedValue a y) * occupiedValue b y =
      ∑ i : Basis, ∑ k : Basis, star (normalizedFactor i a) * normalizedFactor k b *
        ((normalizedOrbital i y : ℂ) * normalizedOrbital k y) := by
  simp only [occupiedValue]
  rw [star_sum]
  simp_rw [star_mul]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [show star ((normalizedOrbital i y : ℂ)) = (normalizedOrbital i y : ℂ) from
    by simp]
  ring

/-- Complex orbital products of the hole integrand are integrable in `y`. -/
private theorem hole_term_integrable (a b : OccupiedSlot) :
    Integrable fun y : Point => star (occupiedValue a y) * occupiedValue b y := by
  have eachInt : ∀ i k : Basis, Integrable (fun y : Point =>
      star (normalizedFactor i a) * normalizedFactor k b *
        ((normalizedOrbital i y : ℂ) * normalizedOrbital k y)) := by
    intro i k
    have h : Integrable fun y : Point =>
        (((normalizedOrbital i y * normalizedOrbital k y : ℝ)) : ℂ) :=
      (normalized_pair_integrable i k).ofReal
    have hc := h.const_mul (star (normalizedFactor i a) * normalizedFactor k b)
    refine hc.congr (Filter.Eventually.of_forall fun y => ?_)
    push_cast
    ring
  have hsum : Integrable fun y : Point => ∑ i : Basis, ∑ k : Basis,
      star (normalizedFactor i a) * normalizedFactor k b *
        ((normalizedOrbital i y : ℂ) * normalizedOrbital k y) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => eachInt i k
  exact hsum.congr (Filter.Eventually.of_forall fun y => (occupiedPair_expand y a b).symm)

/-- Occupied orbitals are orthonormal with respect to the L² pairing. -/
theorem occupied_orthonormal (a b : OccupiedSlot) :
    (∫ y : Point, star (occupiedValue a y) * occupiedValue b y) =
      if a = b then (1 : ℂ) else 0 := by
  classical
  have eachInt : ∀ i k : Basis, Integrable (fun y : Point =>
      star (normalizedFactor i a) * normalizedFactor k b *
        ((normalizedOrbital i y : ℂ) * normalizedOrbital k y)) := by
    intro i k
    have h : Integrable fun y : Point =>
        (((normalizedOrbital i y * normalizedOrbital k y : ℝ)) : ℂ) :=
      (normalized_pair_integrable i k).ofReal
    have hc := h.const_mul (star (normalizedFactor i a) * normalizedFactor k b)
    refine hc.congr (Filter.Eventually.of_forall fun y => ?_)
    push_cast
    ring
  calc (∫ y : Point, star (occupiedValue a y) * occupiedValue b y)
      = ∑ i : Basis, ∑ k : Basis,
          star (normalizedFactor i a) * normalizedFactor k b *
            (((∫ y : Point,
                normalizedOrbital i y * normalizedOrbital k y) : ℝ) : ℂ) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall
          fun y => occupiedPair_expand y a b)]
        rw [integral_finsetSum _ fun i _ =>
          integrable_finsetSum _ fun k _ => eachInt i k]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ fun k _ => eachInt i k]
        apply Finset.sum_congr rfl
        intro k _
        rw [integral_const_mul]
        congr 1
        rw [show (fun y : Point =>
            (normalizedOrbital i y : ℂ) * normalizedOrbital k y) =
            fun y : Point =>
              (((normalizedOrbital i y * normalizedOrbital k y : ℝ)) : ℂ) from
          funext fun y => by push_cast; ring]
        exact integral_complex_ofReal
    _ = ∑ i : Basis, star (normalizedFactor i a) * normalizedFactor i b := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · rw [normalized_pair actual_gram_positive i i]
          simp
        · intro k _ hki
          have hik : i ≠ k := fun h => hki h.symm
          rw [normalized_pair actual_gram_positive i k]
          simp [hik]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
    _ = (normalizedFactor.conjTranspose * normalizedFactor) a b := by
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro i _
        rfl
    _ = if a = b then (1 : ℂ) else 0 := by
        rw [normalized_isometry]
        exact Matrix.one_apply

/-- Reproducing property of the exchange hole: integrating the hole density over
    the second point returns the squared norm of the occupied vector. -/
theorem hole_reproducing (x : Point) :
    (∫ y : Point, holeDensity (x,y)) = ‖occupiedVector x‖^2 := by
  classical
  have innerValue : ∀ y : Point, inner ℂ (occupiedVector y) (occupiedVector x) =
      ∑ a : OccupiedSlot, occupiedValue a x * star (occupiedValue a y) := by
    intro y
    rw [← kernel_inner x y]
    exact kernel_factor x y
  have sqnorm : ∀ c : ℂ, ‖c‖^2 = (star c * c).re := by
    intro c
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self]
    simp
  have pointwise : ∀ y : Point, holeDensity (x,y) =
      (∑ a : OccupiedSlot, ∑ b : OccupiedSlot,
        occupiedValue b x * star (occupiedValue a x) *
          (star (occupiedValue b y) * occupiedValue a y)).re := by
    intro y
    unfold holeDensity
    rw [innerValue y,sqnorm]
    congr 1
    rw [star_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [star_mul,star_star]
    ring
  have outerIntegrable : Integrable fun y : Point =>
      ∑ a : OccupiedSlot, ∑ b : OccupiedSlot,
        occupiedValue b x * star (occupiedValue a x) *
          (star (occupiedValue b y) * occupiedValue a y) :=
    integrable_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ =>
        (hole_term_integrable b a).const_mul _
  have htotal : (∫ y : Point, ∑ a : OccupiedSlot, ∑ b : OccupiedSlot,
      occupiedValue b x * star (occupiedValue a x) *
        (star (occupiedValue b y) * occupiedValue a y)) =
      ((‖occupiedVector x‖^2 : ℝ) : ℂ) := by
    rw [integral_finsetSum _ fun a _ =>
      integrable_finsetSum _ fun b _ => (hole_term_integrable b a).const_mul _]
    have entry : ∀ a b : OccupiedSlot,
        (∫ y : Point, occupiedValue b x * star (occupiedValue a x) *
            (star (occupiedValue b y) * occupiedValue a y)) =
          occupiedValue b x * star (occupiedValue a x) *
            (if b = a then (1 : ℂ) else 0) := by
      intro a b
      rw [integral_const_mul,occupied_orthonormal]
    have entry' : ∀ a : OccupiedSlot,
        (∫ y : Point, ∑ b : OccupiedSlot,
            occupiedValue b x * star (occupiedValue a x) *
              (star (occupiedValue b y) * occupiedValue a y)) =
          ((‖occupiedValue a x‖^2 : ℝ) : ℂ) := by
      intro a
      rw [integral_finsetSum _ fun b _ => (hole_term_integrable b a).const_mul _]
      simp_rw [entry a]
      rw [Finset.sum_eq_single a]
      · simp
        exact RCLike.mul_conj _
      · intro b _ hba
        simp [hba]
      · intro ha
        exact absurd (Finset.mem_univ a) ha
    rw [Finset.sum_congr rfl fun a _ => entry' a]
    rw [show (∑ a : OccupiedSlot, ((‖occupiedValue a x‖^2 : ℝ) : ℂ)) =
        ((∑ a : OccupiedSlot, ‖occupiedValue a x‖^2 : ℝ) : ℂ) from by
      simp]
    congr 1
    rw [EuclideanSpace.norm_eq,Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro a _
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall pointwise)]
  show (∫ y : Point, RCLike.re (∑ a : OccupiedSlot, ∑ b : OccupiedSlot,
      occupiedValue b x * star (occupiedValue a x) *
        (star (occupiedValue b y) * occupiedValue a y))) = ‖occupiedVector x‖^2
  rw [integral_re outerIntegrable,htotal]
  exact Complex.ofReal_re _

/-- Shared-pair (exchange-hole overlap) mass of pair cell `ij`; the `2 ×` factor
    is the spin-degeneracy weight so that rows sum to projected populations. -/
def sharedPairs (ij : Option (Fin 13) × Option (Fin 13)) : ℝ :=
  2 * ∫ z in pairCell ij, holeDensity z

/-- P24-projected electron population of zone `i`. -/
def projectedPopulation (i : Option (Fin 13)) : ℝ :=
  ∫ x in region i, projectedDensity x

theorem shared_pairs_nonnegative (ij : Option (Fin 13) × Option (Fin 13)) :
    0 ≤ sharedPairs ij :=
  mul_nonneg (by norm_num)
    (setIntegral_nonneg (all_pair_cells_measurable ij)
      (fun z _ => hole_density_nonnegative z))

theorem shared_pairs_symmetric (i j : Option (Fin 13)) :
    sharedPairs (i,j) = sharedPairs (j,i) := by
  have h := setIntegral_prod_swap (μ := volume) (ν := volume)
    (region i) (region j) holeDensity
  rw [← Measure.volume_eq_prod] at h
  simp_rw [hole_density_swap] at h
  unfold sharedPairs
  rw [show pairCell (i,j) = region i ×ˢ region j from
      Partition.Finite.pairCell_prod label (i,j),
    show pairCell (j,i) = region j ×ˢ region i from
      Partition.Finite.pairCell_prod label (j,i)]
  rw [h]

theorem shared_pairs_row (i : Option (Fin 13)) :
    (∑ j : Option (Fin 13), sharedPairs (i,j)) = projectedPopulation i := by
  have hdisj : Pairwise (Disjoint on fun j : Option (Fin 13) => pairCell (i,j)) := by
    intro a b hab
    apply all_pair_cells_disjoint
    exact fun h => hab (congrArg Prod.snd h)
  have hp (j : Option (Fin 13)) : pairCell (i,j) = region i ×ˢ region j :=
    Partition.Finite.pairCell_prod label (i,j)
  have hunion : (⋃ j : Option (Fin 13), pairCell (i,j)) = region i ×ˢ Set.univ := by
    simp_rw [hp]
    rw [← Set.prod_iUnion,OneBody.regions_cover]
  have hsum := integral_iUnion_fintype (s := fun j => pairCell (i,j))
    (fun j => all_pair_cells_measurable (i,j)) hdisj
    (fun _ => hole_density_integrable.integrableOn)
  rw [hunion] at hsum
  have hprod : (∫ z in region i ×ˢ Set.univ, holeDensity z) =
      ∫ x in region i, ∫ y in (Set.univ : Set Point), holeDensity (x,y) := by
    have h := setIntegral_prod holeDensity (μ := volume) (ν := volume)
      (s := region i) (t := Set.univ)
      (by rw [← Measure.volume_eq_prod Point Point]
          exact hole_density_integrable.integrableOn)
    rw [← Measure.volume_eq_prod Point Point] at h
    exact h
  rw [hprod] at hsum
  simp_rw [setIntegral_univ] at hsum
  simp_rw [hole_reproducing] at hsum
  calc (∑ j : Option (Fin 13), sharedPairs (i,j))
      = ∑ j, 2 * ∫ z in pairCell (i,j), holeDensity z := rfl
    _ = 2 * ∑ j, ∫ z in pairCell (i,j), holeDensity z := by rw [← Finset.mul_sum]
    _ = 2 * ∫ x in region i, ‖occupiedVector x‖^2 := by rw [← hsum]
    _ = ∫ x in region i, projectedDensity x := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun (all_regions_measurable i)
        intro x _
        rw [projected_density_norm]
    _ = projectedPopulation i := rfl

theorem projected_population_total :
    (∑ i : Option (Fin 13), projectedPopulation i) = 48 := by
  have h := integral_iUnion_fintype (s := region) all_regions_measurable
    OneBody.regions_disjoint (fun _ => projected_density_integrable.integrableOn)
  rw [OneBody.regions_cover] at h
  rw [setIntegral_univ] at h
  calc (∑ i : Option (Fin 13), projectedPopulation i)
      = ∫ x : Point, projectedDensity x := h.symm
    _ = 48 := projected_charge

theorem shared_pairs_total :
    (∑ ij : Option (Fin 13) × Option (Fin 13), sharedPairs ij) = 48 := by
  calc (∑ ij : Option (Fin 13) × Option (Fin 13), sharedPairs ij)
      = ∑ i, ∑ j, sharedPairs (i,j) := Fintype.sum_prod_type _
    _ = ∑ i, projectedPopulation i :=
        Finset.sum_congr rfl fun i _ => shared_pairs_row i
    _ = 48 := projected_population_total

/-- Localization index λ_i: electrons shared with themselves (atomic part). -/
def localization (i : Option (Fin 13)) : ℝ := sharedPairs (i,i)

/-- Delocalization index δ(i,j): electrons shared between zones i and j. -/
def delocalization (i j : Option (Fin 13)) : ℝ :=
  sharedPairs (i,j) + sharedPairs (j,i)

theorem population_localization_delocalization (i : Option (Fin 13)) :
    projectedPopulation i =
      localization i + (1/2) * ∑ j ∈ Finset.univ.erase i, delocalization i j := by
  unfold localization delocalization
  rw [← shared_pairs_row i]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [shared_pairs_symmetric i j]
  ring

theorem localization_delocalization_sum_rule :
    (∑ i : Option (Fin 13), localization i) +
      (1/2) * ∑ i, ∑ j ∈ Finset.univ.erase i, delocalization i j = 48 := by
  calc (∑ i : Option (Fin 13), localization i) +
      (1/2) * ∑ i, ∑ j ∈ Finset.univ.erase i, delocalization i j
      = ∑ i, (localization i +
          (1/2) * ∑ j ∈ Finset.univ.erase i, delocalization i j) := by
        rw [Finset.mul_sum,← Finset.sum_add_distrib]
    _ = ∑ i, projectedPopulation i :=
        Finset.sum_congr rfl fun i _ =>
          (population_localization_delocalization i).symm
    _ = 48 := projected_population_total

/-- The D3 zone population splits into the P24-projected population plus the
    residual zone integral. -/
theorem zone_population_projected (i : Option (Fin 13)) :
    OneBody.zonePopulation i =
      projectedPopulation i + ∫ x in region i, densityResidual x := by
  show (∫ x in region i, sourceDensity x) =
    (∫ x in region i, projectedDensity x) + ∫ x in region i, densityResidual x
  rw [← integral_add projected_density_integrable.integrableOn
    density_residual_integrable.integrableOn]
  apply setIntegral_congr_fun (all_regions_measurable i)
  intro x _
  simp only [densityResidual]
  ring

theorem zone_residual_total :
    |∑ i : Option (Fin 13), ∫ x in region i, densityResidual x| ≤ 1/10^9 := by
  have h := integral_iUnion_fintype (s := region) all_regions_measurable
    OneBody.regions_disjoint (fun _ => density_residual_integrable.integrableOn)
  rw [OneBody.regions_cover,setIntegral_univ] at h
  rw [← h]
  exact original_D3_charge_residual

end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
