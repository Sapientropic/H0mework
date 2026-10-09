import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.FullU
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.OneBody.Population
import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Metric.Charge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Symmetry
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
open LAlanine40K2025.UnifiedOrbitals LAlanine40K2025.UnifiedAction
open LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SourceGaussianModel SourceFiniteData ContinuousGradient GlobalSource
open Set MeasureTheory Function
open scoped BigOperators InnerProductSpace
noncomputable section

/-- The point with coordinate `a` set to `t` and the other coordinates read
from `v`. -/
private abbrev linePt (a : Fin 3) (t : ℝ) (v : Fin 2 → ℝ) : Point :=
  Fin.insertNth a t v

/-- Updating the inserted coordinate of `insertNth` shifts the inserted value. -/
private theorem update_eq_insertNth (a : Fin 3) (v : Fin 2 → ℝ) (t s : ℝ) :
    Function.update (linePt a t v) a s = linePt a s v := by
  simp only [linePt]
  funext k
  rcases Fin.eq_self_or_eq_succAbove a k with rfl | ⟨j, rfl⟩
  · rw [Function.update_self, Fin.insertNth_apply_same]
  · rw [Function.update_of_ne (Fin.succAbove_ne a j), Fin.insertNth_apply_succAbove,
      Fin.insertNth_apply_succAbove]

/-- A single source term restricted to a coordinate line is integrable. -/
private theorem value_line_integrable (term : Term) (positive : 0 < term.exponent)
    (d : MultiIndex) (a : Fin 3) (v : Fin 2 → ℝ) :
    Integrable fun t : ℝ => value term d (linePt a t v) := by
  have hfac (k : Fin 3) : Integrable fun t : ℝ =>
      factor term.exponent (term.powers k) (d k) (t - (term.centre k : ℝ)) :=
    (factor_integrable term.exponent positive (term.powers k) (d k)).comp_sub_right _
  fin_cases a
  · have hval : ∀ t : ℝ,
        value term d (linePt (0 : Fin 3) t v) =
          ((term.weight : ℝ) *
            factor term.exponent (term.powers 1) (d 1) (v 0 - term.centre 1) *
            factor term.exponent (term.powers 2) (d 2) (v 1 - term.centre 2)) *
          factor term.exponent (term.powers 0) (d 0) (t - term.centre 0) := by
      intro t
      have h0 : linePt (0 : Fin 3) t v 0 = t := Fin.insertNth_apply_same _ _ _
      have h1 : linePt (0 : Fin 3) t v 1 = v 0 := by
        show linePt (0 : Fin 3) t v ((0 : Fin 3).succAbove 0) = v 0
        rw [show linePt _ _ _ = Fin.insertNth _ _ _ from rfl,Fin.insertNth_apply_succAbove]
      have h2 : linePt (0 : Fin 3) t v 2 = v 1 := by
        show linePt (0 : Fin 3) t v ((0 : Fin 3).succAbove 1) = v 1
        rw [show linePt _ _ _ = Fin.insertNth _ _ _ from rfl,Fin.insertNth_apply_succAbove]
      simp only [value, h0, h1, h2]
      ring
    show Integrable (fun t => value term d (linePt (0 : Fin 3) t v))
    rw [funext hval]
    exact (hfac 0).const_mul _
  · have hval : ∀ t : ℝ,
        value term d (linePt (1 : Fin 3) t v) =
          ((term.weight : ℝ) *
            factor term.exponent (term.powers 0) (d 0) (v 0 - term.centre 0) *
            factor term.exponent (term.powers 2) (d 2) (v 1 - term.centre 2)) *
          factor term.exponent (term.powers 1) (d 1) (t - term.centre 1) := by
      intro t
      have h0 : linePt (1 : Fin 3) t v 0 = v 0 := by
        show linePt (1 : Fin 3) t v ((1 : Fin 3).succAbove 0) = v 0
        rw [show linePt _ _ _ = Fin.insertNth _ _ _ from rfl,Fin.insertNth_apply_succAbove]
      have h1 : linePt (1 : Fin 3) t v 1 = t := Fin.insertNth_apply_same _ _ _
      have h2 : linePt (1 : Fin 3) t v 2 = v 1 := by
        show linePt (1 : Fin 3) t v ((1 : Fin 3).succAbove 1) = v 1
        rw [show linePt _ _ _ = Fin.insertNth _ _ _ from rfl,Fin.insertNth_apply_succAbove]
      simp only [value, h0, h1, h2]
      ring
    show Integrable (fun t => value term d (linePt (1 : Fin 3) t v))
    rw [funext hval]
    exact (hfac 1).const_mul _
  · have hval : ∀ t : ℝ,
        value term d (linePt (2 : Fin 3) t v) =
          ((term.weight : ℝ) *
            factor term.exponent (term.powers 0) (d 0) (v 0 - term.centre 0) *
            factor term.exponent (term.powers 1) (d 1) (v 1 - term.centre 1)) *
          factor term.exponent (term.powers 2) (d 2) (t - term.centre 2) := by
      intro t
      have h0 : linePt (2 : Fin 3) t v 0 = v 0 := by
        show linePt (2 : Fin 3) t v ((2 : Fin 3).succAbove 0) = v 0
        rw [show linePt _ _ _ = Fin.insertNth _ _ _ from rfl,Fin.insertNth_apply_succAbove]
      have h1 : linePt (2 : Fin 3) t v 1 = v 1 := by
        show linePt (2 : Fin 3) t v ((2 : Fin 3).succAbove 1) = v 1
        rw [show linePt _ _ _ = Fin.insertNth _ _ _ from rfl,Fin.insertNth_apply_succAbove]
      have h2 : linePt (2 : Fin 3) t v 2 = t := Fin.insertNth_apply_same _ _ _
      simp only [value, h0, h1, h2]
    show Integrable (fun t => value term d (linePt (2 : Fin 3) t v))
    simp only [hval]
    exact (hfac 2).const_mul _

/-- A source orbital restricted to a coordinate line is integrable. -/
private theorem orbital_line_integrable (terms : List Term)
    (positive : ∀ term ∈ terms, 0 < term.exponent) (d : MultiIndex)
    (a : Fin 3) (v : Fin 2 → ℝ) :
    Integrable fun t : ℝ => orbital terms d (linePt a t v) := by
  induction terms with
  | nil => simp [orbital]
  | cons term rest ih =>
    have hint : Integrable fun t => value term d (linePt a t v) :=
      value_line_integrable term (positive term (List.mem_cons_self)) d a v
    have hrest : Integrable fun t => orbital rest d (linePt a t v) :=
      ih fun s hs => positive s (List.mem_cons_of_mem _ hs)
    have hfun : (fun t => orbital (term :: rest) d (linePt a t v)) =
        fun t => value term d (linePt a t v) +
          orbital rest d (linePt a t v) := by
      funext t
      simp only [orbital, List.map_cons, List.sum_cons]
    rw [hfun]
    exact hint.add hrest

/-- A source orbital restricted to a coordinate line is continuous. -/
private theorem orbital_line_continuous (terms : List Term) (d : MultiIndex)
    (a : Fin 3) (v : Fin 2 → ℝ) :
    Continuous fun t : ℝ => orbital terms d (linePt a t v) :=
  (orbital_contDiff _ _ 0).continuous.comp
    (show Continuous (fun t : ℝ => linePt a t v) from
      Continuous.finInsertNth a continuous_id continuous_const)

/-- A product of two source orbitals on a coordinate line is integrable. -/
private theorem orbital_product_line_integrable (i j : Basis) (d e : MultiIndex)
    (a : Fin 3) (v : Fin 2 → ℝ) :
    Integrable fun t : ℝ => orbital (sourceTerms i) d (linePt a t v) *
      orbital (sourceTerms j) e (linePt a t v) :=
  (orbital_line_integrable (sourceTerms j) (source_exponents_positive j) e a v).bdd_mul
    (orbital_line_continuous (sourceTerms i) d a v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact source_orbital_uniform_bound d i (linePt a t v))

/-- The coordinate-line derivative of `ao i · ao j`. -/
private theorem product_line_hasDerivAt (i j : Basis) (a : Fin 3) (v : Fin 2 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ao i (linePt a s v) * ao j (linePt a s v))
      (derivative i a (linePt a t v) * ao j (linePt a t v) +
        ao i (linePt a t v) * derivative j a (linePt a t v)) t := by
  have hi : HasDerivAt (fun s : ℝ => ao i (linePt a s v))
      (derivative i a (linePt a t v)) t := by
    have h := orbital_coordinate_derivative (sourceTerms i) zeroJet
      (linePt a t v) a
    simp only [linePt] at h
    rw [Fin.insertNth_apply_same] at h
    convert h using 1
    · funext s
      show orbital (sourceTerms i) zeroJet (linePt a s v) =
          orbital (sourceTerms i) zeroJet
            (Function.update (linePt a t v) a s)
      rw [update_eq_insertNth]
    · rfl
  have hj : HasDerivAt (fun s : ℝ => ao j (linePt a s v))
      (derivative j a (linePt a t v)) t := by
    have h := orbital_coordinate_derivative (sourceTerms j) zeroJet
      (linePt a t v) a
    simp only [linePt] at h
    rw [Fin.insertNth_apply_same] at h
    convert h using 1
    · funext s
      show orbital (sourceTerms j) zeroJet (linePt a s v) =
          orbital (sourceTerms j) zeroJet
            (Function.update (linePt a t v) a s)
      rw [update_eq_insertNth]
    · rfl
  exact hi.mul hj

/-- The first derivative matrix is antisymmetric: the linear form
`∫ ∂_a (φ_i φ_j)` vanishes because `φ_i φ_j` and its line derivatives are
integrable on every coordinate line. -/
theorem first_derivative_antisymmetric (a : Fin 3) (i j : Basis) :
    UnifiedOrbitals.firstDerivative a i j +
      UnifiedOrbitals.firstDerivative a j i = 0 := by
  set g : Point → ℝ := fun x => ao i x * ao j x with hg
  set g' : Point → ℝ := fun x =>
    derivative i a x * ao j x + ao i x * derivative j a x with hg'
  have gint : Integrable g' := by
    apply ((source_product_integrable i j (raise zeroJet a) zeroJet).add
      (source_product_integrable i j zeroJet (raise zeroJet a))).congr
    filter_upwards with x
    simp only [hg', ao, derivative, Pi.add_apply]
  have hprod : Integrable g := source_product_integrable i j zeroJet zeroJet
  -- reduce the space integral to line integrals through `piFinSuccAbove`
  have hp : MeasurePreserving ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a) volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) a
  have hps : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm (volume.prod volume) volume := hp.symm _
  have gintP : Integrable (fun z : ℝ × (Fin 2 → ℝ) => g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm z))
      (volume.prod volume) := by
    have h2 : Integrable g' (Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm (volume.prod volume)) := by
      rw [hps.map_eq]
      exact gint
    exact (MeasureTheory.integrable_map_equiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm g').mp h2
  have swap1 : (∫ x : Point, g' x) =
      ∫ z : ℝ × (Fin 2 → ℝ), g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm z) ∂(volume.prod volume) := by
    have this := MeasureTheory.integral_map_equiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm g' (μ := volume.prod volume)
    rw [hps.map_eq] at this
    exact this
  have gintS : Integrable (fun w : (Fin 2 → ℝ) × ℝ => g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm w.swap))
      (volume.prod volume) := by
    have h2 : Integrable (fun z : ℝ × (Fin 2 → ℝ) => g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm z))
        (Measure.map ((MeasurableEquiv.prodComm : (Fin 2 → ℝ) × ℝ ≃ᵐ ℝ × (Fin 2 → ℝ)))
          ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ))) := by
      rw [show Measure.map ((MeasurableEquiv.prodComm : (Fin 2 → ℝ) × ℝ ≃ᵐ ℝ × (Fin 2 → ℝ)))
            ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) =
          Measure.map Prod.swap
            ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) from rfl,
        Measure.prod_swap]
      exact gintP
    exact (MeasureTheory.integrable_map_equiv ((MeasurableEquiv.prodComm : (Fin 2 → ℝ) × ℝ ≃ᵐ ℝ × (Fin 2 → ℝ)))
      fun z : ℝ × (Fin 2 → ℝ) => g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm z)).mp h2
  have swap2 : (∫ z : ℝ × (Fin 2 → ℝ), g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm z) ∂(volume.prod volume)) =
      ∫ v : Fin 2 → ℝ, ∫ t : ℝ, g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm (t, v)) := by
    have step : (∫ z : ℝ × (Fin 2 → ℝ), g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm z) ∂(volume.prod volume)) =
        ∫ w : (Fin 2 → ℝ) × ℝ, g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm w.swap) ∂(volume.prod volume) := by
      conv_lhs => rw [← Measure.prod_swap]
      rw [show Measure.map Prod.swap
            ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) =
          Measure.map
            (MeasurableEquiv.prodComm : (Fin 2 → ℝ) × ℝ ≃ᵐ ℝ × (Fin 2 → ℝ))
            ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) from rfl]
      rw [MeasureTheory.integral_map_equiv]
      rfl
    rw [step]
    exact MeasureTheory.integral_prod _ gintS
  have inner : ∀ v : Fin 2 → ℝ, (∫ t : ℝ, g' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) a).symm (t, v))) = 0 := by
    intro v
    have hder : ∀ t : ℝ,
        HasDerivAt (fun s : ℝ => ao i (linePt a s v) *
            ao j (linePt a s v))
          (g' (linePt a t v)) t := fun t => by
      have := product_line_hasDerivAt i j a v t
      simpa [hg'] using this
    have hf' : Integrable fun t : ℝ => g' (linePt a t v) := by
      refine ((orbital_product_line_integrable i j (raise zeroJet a) zeroJet a v).add
        (orbital_product_line_integrable i j zeroJet (raise zeroJet a) a v)).congr ?_
      filter_upwards with t
      simp only [hg', ao, derivative, Pi.add_apply]
    have hf : Integrable fun t : ℝ =>
        ao i (linePt a t v) * ao j (linePt a t v) :=
      orbital_product_line_integrable i j zeroJet zeroJet a v
    have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hder hf' hf
    convert hzero using 2
    funext t
    congr 1
  have hzero : (∫ x : Point, g' x) = 0 := by
    rw [swap1, swap2]
    simp only [inner, integral_const, smul_zero]
  unfold UnifiedOrbitals.firstDerivative
  simp only [ao, derivative]
  rw [← integral_add (source_product_integrable i j zeroJet (raise zeroJet a))
    (source_product_integrable j i zeroJet (raise zeroJet a))]
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun x => by
      show orbital (sourceTerms i) zeroJet x *
            orbital (sourceTerms j) (raise zeroJet a) x +
          orbital (sourceTerms j) zeroJet x *
            orbital (sourceTerms i) (raise zeroJet a) x = g' x
      rw [hg']
      simp only [ao, derivative]
      ring)]
  exact hzero
/-- The connection square is the squared norm of the connection vector. -/
theorem connection_square_norm (p : BasePoint) (d : LorentzianIndex) :
    connectionSquare p d = ((‖connectionVector p d‖^2 : ℝ) : ℂ) := by
  unfold connectionSquare
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

/-- The full `U` kinetic channel: the `D·F` linear-connection terms cancel by
D3 symmetry of the density matrix against the antisymmetry of
`firstDerivative` (`∫ ∂_a (φ_iφ_j) = 0` line by line), leaving exactly the
zone kinetic sum plus `N/2·Σ‖C_kψ‖²`. -/
theorem full_U_kinetic_shift (uTime : ℝ) :
    (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        spatialCovariantForm uTime i j) =
      (((∑ z : Option (Fin 13), OneBody.zoneKinetic z) +
        (1/2) * (∑ z : Option (Fin 13), OneBody.zonePopulation z) *
          ∑ axis : Fin 3,
            ‖connectionVector (spatialSlice uTime 0) axis.succ‖^2 : ℝ) : ℂ) := by
  classical
  have Fanti : ∀ axis : Fin 3, ∀ u v : Basis,
      (firstDerivative axis u v : ℂ) = -(firstDerivative axis v u : ℂ) := by
    intro axis u v
    have h := first_derivative_antisymmetric axis u v
    have hC : (firstDerivative axis u v : ℂ) + firstDerivative axis v u = 0 := by
      exact_mod_cast h
    exact eq_neg_of_add_eq_zero_left hC
  have Tzero : ∀ axis : Fin 3,
      (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) = 0 := by
    intro axis
    have hself : (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) =
        -(∑ i : Basis, ∑ j : Basis,
          (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) := by
      calc ∑ i : Basis, ∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)
          = ∑ i : Basis, ∑ j : Basis,
              (densityMatrix j i : ℂ) * (firstDerivative axis j i : ℂ) :=
            Finset.sum_comm
        _ = ∑ i : Basis, ∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis j i : ℂ) := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            rw [original_D3_AO_symmetric i j]
        _ = ∑ i : Basis, ∑ j : Basis,
              (densityMatrix i j : ℂ) * (-(firstDerivative axis i j : ℂ)) := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            rw [Fanti axis j i]
        _ = -(∑ i : Basis, ∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) := by
            simp only [mul_neg, Finset.sum_neg_distrib]
    have h2 : (2 : ℂ) * (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) = 0 := by
      linear_combination hself
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  set p0 := spatialSlice uTime 0 with hp0
  have perAxis : ∀ axis : Fin 3,
      (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
         (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
         (overlap i j : ℂ) * connectionSquare p0 axis.succ)) =
      ((∫ x : Point, sourceDensity x : ℝ) : ℂ) *
        connectionSquare p0 axis.succ := by
    intro axis
    have L1 : (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) * (firstDerivative axis j i : ℂ)) = 0 := by
      calc ∑ i : Basis, ∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis j i : ℂ)
          = ∑ i : Basis, ∑ j : Basis,
              (densityMatrix j i : ℂ) * (firstDerivative axis i j : ℂ) :=
            Finset.sum_comm
        _ = ∑ i : Basis, ∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ) := by
            apply Finset.sum_congr rfl; intro i _
            apply Finset.sum_congr rfl; intro j _
            rw [original_D3_AO_symmetric j i]
        _ = 0 := Tzero axis
    have L2 : (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) = 0 :=
      Tzero axis
    have overlapC : (∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) * (overlap i j : ℂ)) =
        ((∫ x : Point, sourceDensity x : ℝ) : ℂ) := by
      rw [Metric.actual_charge_overlap]
      push_cast
      rfl
    have split : (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
         (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
         (overlap i j : ℂ) * connectionSquare p0 axis.succ)) =
        (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
            ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ)) +
        (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
            ((firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ))) +
        ∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
          ((overlap i j : ℂ) * connectionSquare p0 axis.succ) := by
      simp_rw [mul_add, Finset.sum_add_distrib]
    have e1 : (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ)) = 0 := by
      calc (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
            ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ))
          = ∑ i : Basis, ∑ j : Basis,
              ((densityMatrix i j : ℂ) * (firstDerivative axis j i : ℂ)) *
                connectionPair p0 axis.succ :=
            Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
        _ = ∑ i : Basis, (∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis j i : ℂ)) *
                connectionPair p0 axis.succ :=
            Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
        _ = (∑ i : Basis, ∑ j : Basis,
            (densityMatrix i j : ℂ) * (firstDerivative axis j i : ℂ)) *
              connectionPair p0 axis.succ := (Finset.sum_mul _ _ _).symm
        _ = 0 := by rw [L1, zero_mul]
    have e2 : (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        ((firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ))) = 0 := by
      calc (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
            ((firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ)))
          = ∑ i : Basis, ∑ j : Basis,
              ((densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) *
                star (connectionPair p0 axis.succ) :=
            Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
        _ = ∑ i : Basis, (∑ j : Basis,
              (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) *
                star (connectionPair p0 axis.succ) :=
            Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
        _ = (∑ i : Basis, ∑ j : Basis,
            (densityMatrix i j : ℂ) * (firstDerivative axis i j : ℂ)) *
              star (connectionPair p0 axis.succ) := (Finset.sum_mul _ _ _).symm
        _ = 0 := by rw [L2, zero_mul]
    have e3 : (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
        ((overlap i j : ℂ) * connectionSquare p0 axis.succ)) =
        ((∫ x : Point, sourceDensity x : ℝ) : ℂ) *
          connectionSquare p0 axis.succ := by
      calc (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
            ((overlap i j : ℂ) * connectionSquare p0 axis.succ))
          = ∑ i : Basis, ∑ j : Basis,
              ((densityMatrix i j : ℂ) * (overlap i j : ℂ)) *
                connectionSquare p0 axis.succ :=
            Finset.sum_congr rfl fun i _ =>
              Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
        _ = ∑ i : Basis, (∑ j : Basis,
              (densityMatrix i j : ℂ) * (overlap i j : ℂ)) *
                connectionSquare p0 axis.succ :=
            Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
        _ = (∑ i : Basis, ∑ j : Basis,
            (densityMatrix i j : ℂ) * (overlap i j : ℂ)) *
              connectionSquare p0 axis.succ := (Finset.sum_mul _ _ _).symm
        _ = ((∫ x : Point, sourceDensity x : ℝ) : ℂ) *
              connectionSquare p0 axis.succ := by rw [overlapC]
    rw [split, e1, e2, e3, zero_add, zero_add]
  have hcomm : (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
      ((1/2 : ℂ) * ∑ axis : Fin 3,
        ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
         (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
         (overlap i j : ℂ) * connectionSquare p0 axis.succ))) =
      (1/2 : ℂ) * ∑ axis : Fin 3, ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) *
          ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
           (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
           (overlap i j : ℂ) * connectionSquare p0 axis.succ) := by
    calc (∑ i : Basis, ∑ j : Basis, (densityMatrix i j : ℂ) *
          ((1/2 : ℂ) * ∑ axis : Fin 3,
            ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
             (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
             (overlap i j : ℂ) * connectionSquare p0 axis.succ)))
        = ∑ i : Basis, ∑ j : Basis, (1/2 : ℂ) * ∑ axis : Fin 3,
            (densityMatrix i j : ℂ) *
              ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
               (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
               (overlap i j : ℂ) * connectionSquare p0 axis.succ) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j _
          rw [mul_left_comm, Finset.mul_sum]
      _ = (1/2 : ℂ) * ∑ i : Basis, ∑ j : Basis, ∑ axis : Fin 3,
            (densityMatrix i j : ℂ) *
              ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
               (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
               (overlap i j : ℂ) * connectionSquare p0 axis.succ) := by
          calc ∑ i : Basis, ∑ j : Basis, (1/2 : ℂ) * ∑ axis : Fin 3,
                (densityMatrix i j : ℂ) *
                  ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
                   (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
                   (overlap i j : ℂ) * connectionSquare p0 axis.succ)
              = ∑ i : Basis, (1/2 : ℂ) * ∑ j : Basis, ∑ axis : Fin 3,
                  (densityMatrix i j : ℂ) *
                    ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
                     (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
                     (overlap i j : ℂ) * connectionSquare p0 axis.succ) :=
                Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
            _ = (1/2 : ℂ) * ∑ i : Basis, ∑ j : Basis, ∑ axis : Fin 3,
                  (densityMatrix i j : ℂ) *
                    ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
                     (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
                     (overlap i j : ℂ) * connectionSquare p0 axis.succ) :=
                (Finset.mul_sum _ _ _).symm
      _ = (1/2 : ℂ) * ∑ axis : Fin 3, ∑ i : Basis, ∑ j : Basis,
            (densityMatrix i j : ℂ) *
              ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
               (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
               (overlap i j : ℂ) * connectionSquare p0 axis.succ) := by
          congr 1
          calc ∑ i : Basis, ∑ j : Basis, ∑ a2 : Fin 3,
                (densityMatrix i j : ℂ) *
                  ((firstDerivative a2 j i : ℂ) * connectionPair p0 a2.succ +
                   (firstDerivative a2 i j : ℂ) * star (connectionPair p0 a2.succ) +
                   (overlap i j : ℂ) * connectionSquare p0 a2.succ)
              = ∑ i : Basis, ∑ a2 : Fin 3, ∑ j : Basis,
                  (densityMatrix i j : ℂ) *
                    ((firstDerivative a2 j i : ℂ) * connectionPair p0 a2.succ +
                     (firstDerivative a2 i j : ℂ) * star (connectionPair p0 a2.succ) +
                     (overlap i j : ℂ) * connectionSquare p0 a2.succ) :=
                Finset.sum_congr rfl fun i _ => Finset.sum_comm
            _ = ∑ a2 : Fin 3, ∑ i : Basis, ∑ j : Basis,
                  (densityMatrix i j : ℂ) *
                    ((firstDerivative a2 j i : ℂ) * connectionPair p0 a2.succ +
                     (firstDerivative a2 i j : ℂ) * star (connectionPair p0 a2.succ) +
                     (overlap i j : ℂ) * connectionSquare p0 a2.succ) :=
                Finset.sum_comm
  rw [Nuclear.full_U_kinetic_zone_join uTime]
  rw [hcomm]
  have axisDone :
      (∑ axis : Fin 3, ∑ i : Basis, ∑ j : Basis,
        (densityMatrix i j : ℂ) *
          ((firstDerivative axis j i : ℂ) * connectionPair p0 axis.succ +
           (firstDerivative axis i j : ℂ) * star (connectionPair p0 axis.succ) +
           (overlap i j : ℂ) * connectionSquare p0 axis.succ)) =
      ∑ axis : Fin 3, ((∫ x : Point, sourceDensity x : ℝ) : ℂ) *
        connectionSquare p0 axis.succ :=
    Finset.sum_congr rfl fun axis _ => perAxis axis
  rw [axisDone]
  have sqDone :
      (∑ axis : Fin 3, ((∫ x : Point, sourceDensity x : ℝ) : ℂ) *
          connectionSquare p0 axis.succ) =
      ∑ axis : Fin 3, ((∫ x : Point, sourceDensity x : ℝ) : ℂ) *
        ((‖connectionVector p0 axis.succ‖^2 : ℝ) : ℂ) :=
    Finset.sum_congr rfl fun axis _ =>
      congrArg _ (connection_square_norm p0 axis.succ)
  rw [sqDone]
  have hpop : (∑ z : Option (Fin 13), OneBody.zonePopulation z) =
      ∫ x : Point, sourceDensity x := OneBody.zone_population_sum
  rw [hpop]
  push_cast
  rw [← Finset.mul_sum]
  congr 1
  ring
end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.AtomicIQA
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
