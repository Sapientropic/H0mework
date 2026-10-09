import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Coulomb
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Integral
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.ERIFTC

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel ReceiverBody.NuclearBasis ReceiverBody.NuclearCoulomb

def centredDerivative (term : Term) (jet : MultiIndex) (centre x : Point) : Point →L[ℝ] ℝ :=
  -(∑ axis : Fin 3, (ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).smulRight
    (centredValue term (raise jet axis) centre x))

theorem centred_derivative_apply (term : Term) (jet : MultiIndex) (centre x velocity : Point) :
    centredDerivative term jet centre x velocity = jetRate term jet centre velocity x := by
  simp only [centredDerivative,neg_apply,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,jetRate]

theorem centred_hasFDerivAt (term : Term) (jet : MultiIndex) (centre x : Point) :
    HasFDerivAt (fun c => centredValue term jet c x) (centredDerivative term jet centre x) centre := by
  have smooth : DifferentiableAt ℝ (fun c => centredValue term jet c x) centre := by
    unfold centredValue
    apply ((value_contDiff term jet 1).differentiable (by norm_num) _).comp centre
    fun_prop
  apply smooth.hasFDerivAt.congr_fderiv
  ext velocity
  let curve : ℝ → Point := fun t => centre+t • velocity
  have motion : HasDerivAt curve velocity 0 := by
    simpa only [curve,id_eq,one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const velocity).const_add centre
  have coordinate (axis : Fin 3) : HasDerivAt (fun t => curve t axis) (velocity axis) 0 := by
    simpa only [curve,Pi.add_apply,Pi.smul_apply,smul_eq_mul,id_eq,one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (velocity axis)).const_add (centre axis)
  have atCurve : HasFDerivAt (fun c => centredValue term jet c x)
      (fderiv ℝ (fun c => centredValue term jet c x) centre) (curve 0) := by
    simpa only [curve,zero_smul,add_zero] using smooth.hasFDerivAt
  have measured := atCurve.comp_hasDerivAt 0 motion
  have generated := centred_value_derivative term jet curve velocity 0 x coordinate
  simpa only [curve,zero_smul,add_zero,centred_derivative_apply,jetRate] using measured.unique generated


abbrev AttractionConfiguration := Fin 2 → Point

def attractionIntegrandDerivative (left right : Term) (l r : MultiIndex)
    (centres : AttractionConfiguration) (x : Point) : AttractionConfiguration →L[ℝ] ℝ :=
  -(∑ axis : Fin 3,
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp (ContinuousLinearMap.proj 0)).smulRight
      (attractionIntegrand left right (raise l axis) r (centres 0) (centres 1) x)) +
  -(∑ axis : Fin 3,
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp (ContinuousLinearMap.proj 1)).smulRight
      (attractionIntegrand right left (raise r axis) l (centres 1) (centres 0) x))

theorem attraction_integrand_derivative_apply (left right : Term) (l r : MultiIndex)
    (centres speeds : AttractionConfiguration) (x : Point) :
    attractionIntegrandDerivative left right l r centres x speeds =
      attractionRate left right l r (centres 0) (centres 1) (speeds 0) (speeds 1) x := by
  simp only [attractionIntegrandDerivative,add_apply,neg_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,attractionRate,jetRate,attractionIntegrand,
    neg_mul,mul_neg,Fin.sum_univ_three]
  ring


theorem attraction_integrand_hasFDerivAt (left right : Term) (l r : MultiIndex)
    (centres : AttractionConfiguration) (x : Point) :
    HasFDerivAt (fun c => attractionIntegrand left right l r (c 0) (c 1) x)
      (attractionIntegrandDerivative left right l r centres x) centres := by
  have leftMotion := (centred_hasFDerivAt left l (centres 0) x).comp centres
    (ContinuousLinearMap.proj 0 : AttractionConfiguration →L[ℝ] Point).hasFDerivAt
  have rightMotion := (centred_hasFDerivAt right r (centres 1) x).comp centres
    (ContinuousLinearMap.proj 1 : AttractionConfiguration →L[ℝ] Point).hasFDerivAt
  have generated := (leftMotion.mul rightMotion).mul_const (SourceCoulomb.kernel x)
  apply generated.congr_fderiv
  ext speeds
  simp only [attraction_integrand_derivative_apply,attractionRate,
    add_apply,
    smul_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,
    smul_eq_mul,centred_derivative_apply,Function.comp_def]
  ring


def attractionDerivative (left right : Term) (l r : MultiIndex) (centres : AttractionConfiguration) :
    AttractionConfiguration →L[ℝ] ℝ :=
  -(∑ axis : Fin 3,
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp (ContinuousLinearMap.proj 0)).smulRight
      (primitiveAttraction left right (raise l axis) r (centres 0) (centres 1))) +
  -(∑ axis : Fin 3,
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp (ContinuousLinearMap.proj 1)).smulRight
      (primitiveAttraction right left (raise r axis) l (centres 1) (centres 0)))

theorem attraction_derivative_apply (left right : Term) (l r : MultiIndex)
    (centres speeds : AttractionConfiguration) :
    attractionDerivative left right l r centres speeds =
      primitiveAttractionRate left right l r (centres 0) (centres 1) (speeds 0) (speeds 1) := by
  simp only [attractionDerivative,add_apply,neg_apply,
    sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,primitiveAttractionRate]

def pairIntegrandDerivative (terms : Quartet → Term) (jets : Quartet → MultiIndex)
    (centres : Quartet → Point) (z : Point × Point) : (Quartet → Point) →L[ℝ] ℝ :=
  -(∑ slot : Quartet, ∑ axis : Fin 3,
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp (ContinuousLinearMap.proj slot)).smulRight
      (eriIntegrand terms (raiseSlot jets slot axis) centres z))

theorem pair_integrand_derivative_apply (terms : Quartet → Term) (jets : Quartet → MultiIndex)
    (centres speeds : Quartet → Point) (z : Point × Point) :
    pairIntegrandDerivative terms jets centres z speeds = eriRate terms jets centres speeds z := by
  simp only [pairIntegrandDerivative,neg_apply,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,eriRate]

theorem pair_integrand_hasFDerivAt (terms : Quartet → Term) (jets : Quartet → MultiIndex)
    (centres : Quartet → Point) (z : Point × Point) :
    HasFDerivAt (fun c => eriIntegrand terms jets c z) (pairIntegrandDerivative terms jets centres z) centres := by
  have each (slot : Quartet) (x : Point) :=
    (centred_hasFDerivAt (terms slot) (jets slot) (centres slot) x).comp centres
      (ContinuousLinearMap.proj slot : (Quartet → Point) →L[ℝ] Point).hasFDerivAt
  have smooth : DifferentiableAt ℝ (fun c => eriIntegrand terms jets c z) centres :=
    ((((each 0 z.1).mul (each 1 z.1)).mul ((each 2 z.2).mul (each 3 z.2))).mul_const
      (SourceCoulomb.kernel (z.2-z.1))).differentiableAt
  apply smooth.hasFDerivAt.congr_fderiv
  ext speeds
  let curve : ℝ → Quartet → Point := fun t => centres+t • speeds
  have motion : HasDerivAt curve speeds 0 := by
    simpa only [curve,id_eq,one_smul] using! ((hasDerivAt_id (0 : ℝ)).smul_const speeds).const_add centres
  have coordinate (slot : Quartet) (axis : Fin 3) :
      HasDerivAt (fun t => curve t slot axis) (speeds slot axis) 0 := by
    simpa only [curve,Pi.add_apply,Pi.smul_apply,smul_eq_mul,id_eq,one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const (speeds slot axis)).const_add (centres slot axis)
  have atCurve : HasFDerivAt (fun c => eriIntegrand terms jets c z)
      (fderiv ℝ (fun c => eriIntegrand terms jets c z) centres) (curve 0) := by
    simpa only [curve,zero_smul,add_zero] using smooth.hasFDerivAt
  have measured := atCurve.comp_hasDerivAt 0 motion
  have generated := eri_integrand_derivative terms jets curve speeds 0 z coordinate
  simpa only [curve,zero_smul,add_zero,pair_integrand_derivative_apply] using measured.unique generated


def pairDerivative (terms : Quartet → Term) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    (Quartet → Point) →L[ℝ] ℝ :=
  -(∑ slot : Quartet, ∑ axis : Fin 3,
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp (ContinuousLinearMap.proj slot)).smulRight
      (primitiveERI terms (raiseSlot jets slot axis) centres))

theorem pair_derivative_apply (terms : Quartet → Term) (jets : Quartet → MultiIndex)
    (centres speeds : Quartet → Point) :
    pairDerivative terms jets centres speeds = primitiveERIRate terms jets centres speeds := by
  simp only [pairDerivative,neg_apply,sum_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,primitiveERIRate]

private theorem coordinate_projection_norm {I : Type} [Fintype I] (slot : I) (axis : Fin 3) :
    ‖((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj slot : (I → Point) →L[ℝ] Point))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,one_mul] using
    (norm_le_pi_norm (v slot) axis).trans (norm_le_pi_norm v slot)

private theorem scalar_dual_integrable {X D : Type} [MeasurableSpace X]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {μ : Measure X} (field : X → ℝ) (integrable : Integrable field μ) (dual : D →L[ℝ] ℝ) :
    Integrable (fun x => dual.smulRight (field x)) μ := by
  apply (integrable.smul_const dual).congr
  apply Filter.Eventually.of_forall
  intro x
  ext v
  simp only [ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul,mul_comm]


theorem attraction_integrand_derivative_integrable (left right : Term)
    (hl : 0 < left.exponent) (hr : 0 < right.exponent) (l r : MultiIndex)
    (centres : AttractionConfiguration) : Integrable (attractionIntegrandDerivative left right l r centres) := by
  have first (axis : Fin 3) := scalar_dual_integrable (X := Point) (D := AttractionConfiguration)
    (μ := (volume : Measure Point))
    (fun x => attractionIntegrand left right (raise l axis) r (centres 0) (centres 1) x)
    (attraction_integrand_integrable left right hl hr (raise l axis) r (centres 0) (centres 1))
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj (0 : Fin 2) : AttractionConfiguration →L[ℝ] Point))
  have second (axis : Fin 3) := scalar_dual_integrable (X := Point) (D := AttractionConfiguration)
    (μ := (volume : Measure Point))
    (fun x => attractionIntegrand right left (raise r axis) l (centres 1) (centres 0) x)
    (attraction_integrand_integrable right left hr hl (raise r axis) l (centres 1) (centres 0))
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj (1 : Fin 2) : AttractionConfiguration →L[ℝ] Point))
  have firstTotal := Integrable.add (ε' := AttractionConfiguration →L[ℝ] ℝ) (μ := (volume : Measure Point))
    (Integrable.add (ε' := AttractionConfiguration →L[ℝ] ℝ) (μ := (volume : Measure Point))
      (first 0) (first 1)) (first 2)
  have secondTotal := Integrable.add (ε' := AttractionConfiguration →L[ℝ] ℝ) (μ := (volume : Measure Point))
    (Integrable.add (ε' := AttractionConfiguration →L[ℝ] ℝ) (μ := (volume : Measure Point))
      (second 0) (second 1)) (second 2)
  have total := Integrable.add (ε' := AttractionConfiguration →L[ℝ] ℝ) (μ := (volume : Measure Point))
    (firstTotal.neg) (secondTotal.neg)
  apply total.congr
  filter_upwards [] with x
  simp only [attractionIntegrandDerivative,Fin.sum_univ_three,Pi.add_apply,Pi.neg_apply]

theorem attraction_integrand_derivative_integral (left right : Term)
    (hl : 0 < left.exponent) (hr : 0 < right.exponent) (l r : MultiIndex)
    (centres : AttractionConfiguration) :
    (∫ x : Point, attractionIntegrandDerivative left right l r centres x) =
      attractionDerivative left right l r centres := by
  ext speeds
  rw [ContinuousLinearMap.integral_apply
    (attraction_integrand_derivative_integrable left right hl hr l r centres)]
  simp only [attraction_integrand_derivative_apply,attraction_derivative_apply]
  exact integrated_attraction_rate left right hl hr l r (centres 0) (centres 1) (speeds 0) (speeds 1)

def attractionDerivativeEnvelope (left right : Term) (l r : MultiIndex) (C : ℝ) (x : Point) : ℝ :=
  (∑ axis : Fin 3, attractionEnvelope left right (raise l axis) r C x) +
    ∑ axis : Fin 3, attractionEnvelope right left (raise r axis) l C x

theorem attraction_derivative_envelope_integrable (left right : Term)
    (hl : 0 < left.exponent) (hr : 0 < right.exponent) (l r : MultiIndex) (C : ℝ) :
    Integrable (attractionDerivativeEnvelope left right l r C) :=
  (integrable_finsetSum _ (fun axis _ => attraction_envelope_integrable left right hl hr (raise l axis) r C)).add
    (integrable_finsetSum _ (fun axis _ => attraction_envelope_integrable right left hr hl (raise r axis) l C))

theorem attraction_derivative_uniform_bound (left right : Term)
    (hl : 0 < left.exponent) (hr : 0 < right.exponent) (l r : MultiIndex)
    (centres : AttractionConfiguration) (C : ℝ) (bounded : ∀ slot, ‖centres slot‖ ≤ C) (x : Point) :
    ‖attractionIntegrandDerivative left right l r centres x‖ ≤ attractionDerivativeEnvelope left right l r C x := by
  have first (axis : Fin 3) :
      ‖((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj 0 : AttractionConfiguration →L[ℝ] Point)).smulRight
        (attractionIntegrand left right (raise l axis) r (centres 0) (centres 1) x)‖ ≤
        attractionEnvelope left right (raise l axis) r C x := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul (coordinate_projection_norm 0 axis)
      (attraction_uniform_bound left right hl hr (raise l axis) r C (centres 0) (centres 1) x
        (bounded 0) (bounded 1)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have second (axis : Fin 3) :
      ‖((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj 1 : AttractionConfiguration →L[ℝ] Point)).smulRight
        (attractionIntegrand right left (raise r axis) l (centres 1) (centres 0) x)‖ ≤
        attractionEnvelope right left (raise r axis) l C x := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact (mul_le_mul (coordinate_projection_norm 1 axis)
      (attraction_uniform_bound right left hr hl (raise r axis) l C (centres 1) (centres 0) x
        (bounded 1) (bounded 0)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  unfold attractionIntegrandDerivative attractionDerivativeEnvelope
  exact (norm_add_le _ _).trans (add_le_add
    (by rw [norm_neg]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun axis _ => first axis)))
    (by rw [norm_neg]; exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun axis _ => second axis))))

theorem primitive_attraction_hasFDerivAt (left right : Term)
    (hl : 0 < left.exponent) (hr : 0 < right.exponent) (l r : MultiIndex)
    (centres : AttractionConfiguration) :
    HasFDerivAt (fun c => primitiveAttraction left right l r (c 0) (c 1))
      (attractionDerivative left right l r centres) centres := by
  let C := ‖centres‖+1
  let s : Set AttractionConfiguration := {c | ‖c‖ < C}
  have near : s ∈ 𝓝 centres :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have actual := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (c : AttractionConfiguration) (x : Point) => attractionIntegrand left right l r (c 0) (c 1) x)
    (F' := fun (c : AttractionConfiguration) (x : Point) => attractionIntegrandDerivative left right l r c x)
    (bound := attractionDerivativeEnvelope left right l r C) near
    (Filter.Eventually.of_forall fun c => attraction_integrand_measurable left right l r (c 0) (c 1))
    (attraction_integrand_integrable left right hl hr l r (centres 0) (centres 1))
    (attraction_integrand_derivative_integrable left right hl hr l r centres).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x c bound =>
      attraction_derivative_uniform_bound left right hl hr l r c C
        (fun slot => (norm_le_pi_norm c slot).trans bound.le) x)
    (attraction_derivative_envelope_integrable left right hl hr l r C)
    (Filter.Eventually.of_forall fun x c _ => attraction_integrand_hasFDerivAt left right l r c x)
  rw [attraction_integrand_derivative_integral left right hl hr l r centres] at actual
  exact actual

theorem pair_integrand_derivative_integrable (terms : Quartet → Term)
    (positive : ∀ slot, 0 < (terms slot).exponent) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    Integrable (pairIntegrandDerivative terms jets centres) := by
  have each (slot : Quartet) (axis : Fin 3) := scalar_dual_integrable _
    (eri_integrand_integrable terms positive (raiseSlot jets slot axis) centres)
    ((ContinuousLinearMap.proj axis : Point →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj slot : (Quartet → Point) →L[ℝ] Point))
  simpa only [pairIntegrandDerivative] using!
    (integrable_finsetSum _ (fun slot _ => integrable_finsetSum _ (fun axis _ => each slot axis))).neg

theorem pair_integrand_derivative_integral (terms : Quartet → Term)
    (positive : ∀ slot, 0 < (terms slot).exponent) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    (∫ z : Point × Point, pairIntegrandDerivative terms jets centres z) = pairDerivative terms jets centres := by
  ext speeds
  rw [ContinuousLinearMap.integral_apply (pair_integrand_derivative_integrable terms positive jets centres)]
  simp only [pair_integrand_derivative_apply,pair_derivative_apply]
  exact integrated_eri_rate terms positive jets centres speeds

def pairDerivativeEnvelope (terms : Quartet → Term) (jets : Quartet → MultiIndex) (C : ℝ) (z : Point × Point) : ℝ :=
  ∑ slot : Quartet, ∑ axis : Fin 3, eriEnvelope terms (raiseSlot jets slot axis) C z

theorem pair_derivative_envelope_integrable (terms : Quartet → Term)
    (positive : ∀ slot, 0 < (terms slot).exponent) (jets : Quartet → MultiIndex) (C : ℝ) :
    Integrable (pairDerivativeEnvelope terms jets C) :=
  integrable_finsetSum _ (fun slot _ => integrable_finsetSum _ (fun axis _ =>
    eri_envelope_integrable terms positive (raiseSlot jets slot axis) C))

theorem pair_derivative_uniform_bound (terms : Quartet → Term)
    (positive : ∀ slot, 0 < (terms slot).exponent) (jets : Quartet → MultiIndex)
    (centres : Quartet → Point) (C : ℝ) (bounded : ∀ slot, ‖centres slot‖ ≤ C) (z : Point × Point) :
    ‖pairIntegrandDerivative terms jets centres z‖ ≤ pairDerivativeEnvelope terms jets C z := by
  unfold pairIntegrandDerivative pairDerivativeEnvelope
  rw [norm_neg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro slot _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro axis _
  rw [ContinuousLinearMap.norm_smulRight_apply]
  exact (mul_le_mul (coordinate_projection_norm slot axis)
    (eri_uniform_bound terms positive (raiseSlot jets slot axis) centres C bounded z)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem primitive_pair_hasFDerivAt (terms : Quartet → Term)
    (positive : ∀ slot, 0 < (terms slot).exponent) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    HasFDerivAt (primitiveERI terms jets) (pairDerivative terms jets centres) centres := by
  let C := ‖centres‖+1
  let s : Set (Quartet → Point) := {c | ‖c‖ < C}
  have near : s ∈ 𝓝 centres :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have actual := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun (c : Quartet → Point) (z : Point × Point) => eriIntegrand terms jets c z)
    (F' := fun (c : Quartet → Point) (z : Point × Point) => pairIntegrandDerivative terms jets c z)
    (bound := pairDerivativeEnvelope terms jets C) near
    (Filter.Eventually.of_forall fun c => eri_integrand_measurable terms jets c)
    (eri_integrand_integrable terms positive jets centres)
    (pair_integrand_derivative_integrable terms positive jets centres).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z c bound => pair_derivative_uniform_bound terms positive jets c C
      (fun slot => (norm_le_pi_norm c slot).trans bound.le) z)
    (pair_derivative_envelope_integrable terms positive jets C)
    (Filter.Eventually.of_forall fun z c _ => pair_integrand_hasFDerivAt terms jets c z)
  rw [pair_integrand_derivative_integral terms positive jets centres] at actual
  exact actual

theorem multicentre_nuclear_relative (left right nuclear : Point) (i j : Nat) (l r : MultiIndex) :
    CPS1MolecularFrame.primitiveNuclearIntegral left right i j nuclear l r =
      (primitiveAttraction (CPS1ElectronicSource.primitive i) (CPS1ElectronicSource.primitive j)
        l r (left-nuclear) (right-nuclear) : ℂ) := by
  let field : Point → ℝ := fun x =>
    centredValue (CPS1ElectronicSource.primitive i) l left x*
      centredValue (CPS1ElectronicSource.primitive j) r right x*SourceCoulomb.kernel (x-nuclear)
  have same : (fun x : Point => (SourceCoulomb.kernel (x-nuclear) : ℂ)*
      star (CPS1ElectronicSource.orbitalValue left i l x)*CPS1ElectronicSource.orbitalValue right j r x) =
      fun x => (field x : ℂ) := by
    funext x
    rw [CPS1QuantumNuclear.orbital_centred,CPS1QuantumNuclear.orbital_centred]
    simp only [field,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  have rebased : (fun x => field (x+nuclear)) =
      attractionIntegrand (CPS1ElectronicSource.primitive i) (CPS1ElectronicSource.primitive j)
        l r (left-nuclear) (right-nuclear) := by
    funext x
    simp only [field,attractionIntegrand,CPS1QuantumNuclear.centred_translate,add_sub_cancel_right]
  have translated : (∫ x : Point, field (x+nuclear)) = ∫ x : Point, field x := by
    simpa only [sub_neg_eq_add] using integral_sub_right_eq_self (μ := (volume : Measure Point)) field (-nuclear)
  unfold CPS1MolecularFrame.primitiveNuclearIntegral
  rw [same,integral_complex_ofReal]
  exact congrArg (fun z : ℝ => (z : ℂ))
    (translated.symm.trans (congrArg (fun f : Point → ℝ => ∫ x : Point, f x) rebased))

def nuclearRelative : (Fin 3 → Point) →L[ℝ] AttractionConfiguration :=
  ContinuousLinearMap.pi (fun slot : Fin 2 => if slot = 0 then
    (ContinuousLinearMap.proj (0 : Fin 3) : (Fin 3 → Point) →L[ℝ] Point)-ContinuousLinearMap.proj 2
    else (ContinuousLinearMap.proj (1 : Fin 3) : (Fin 3 → Point) →L[ℝ] Point)-ContinuousLinearMap.proj 2)

theorem nuclear_relative_zero (centres : Fin 3 → Point) : nuclearRelative centres 0 = centres 0-centres 2 := rfl
theorem nuclear_relative_one (centres : Fin 3 → Point) : nuclearRelative centres 1 = centres 1-centres 2 := rfl

def complexNuclearDerivative (i j : Nat) (l r : MultiIndex) (centres : Fin 3 → Point) :
    (Fin 3 → Point) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((attractionDerivative (CPS1ElectronicSource.primitive i) (CPS1ElectronicSource.primitive j)
    l r (nuclearRelative centres)).comp nuclearRelative)

theorem multicentre_nuclear_hasFDerivAt (i j : Nat) (l r : MultiIndex) (centres : Fin 3 → Point) :
    HasFDerivAt (fun c : Fin 3 → Point => CPS1MolecularFrame.primitiveNuclearIntegral (c 0) (c 1) i j (c 2) l r)
      (complexNuclearDerivative i j l r centres) centres := by
  have positive (mode : Nat) : 0 < (CPS1ElectronicSource.primitive mode).exponent := by
    norm_num [CPS1ElectronicSource.primitive]
  have attraction := primitive_attraction_hasFDerivAt (CPS1ElectronicSource.primitive i)
    (CPS1ElectronicSource.primitive j) (positive i) (positive j) l r (nuclearRelative centres)
  have shifted := attraction.comp centres nuclearRelative.hasFDerivAt
  have generated := Complex.ofRealCLM.hasFDerivAt.comp centres shifted
  have same : (fun c : Fin 3 → Point => CPS1MolecularFrame.primitiveNuclearIntegral (c 0) (c 1) i j (c 2) l r) =
      fun c => (primitiveAttraction (CPS1ElectronicSource.primitive i) (CPS1ElectronicSource.primitive j)
        l r (nuclearRelative c 0) (nuclearRelative c 1) : ℂ) := by
    funext c
    rw [nuclear_relative_zero,nuclear_relative_one]
    exact multicentre_nuclear_relative (c 0) (c 1) (c 2) i j l r
  rw [same]
  exact generated

theorem multicentre_pair_relative (modes : Quartet → Nat) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    CPS1MolecularFrame.primitivePairIntegral (centres 0) (centres 1) (centres 2) (centres 3)
      (modes 0) (modes 1) (modes 2) (modes 3) (jets 0) (jets 1) (jets 2) (jets 3) =
      (primitiveERI (fun slot => CPS1ElectronicSource.primitive (modes slot)) jets centres : ℂ) := by
  have same : (fun z : Point × Point => (SourceCoulomb.kernel (z.1-z.2) : ℂ)*
      star (CPS1ElectronicSource.orbitalValue (centres 0) (modes 0) (jets 0) z.1)*
      CPS1ElectronicSource.orbitalValue (centres 1) (modes 1) (jets 1) z.1*
      star (CPS1ElectronicSource.orbitalValue (centres 2) (modes 2) (jets 2) z.2)*
      CPS1ElectronicSource.orbitalValue (centres 3) (modes 3) (jets 3) z.2) =
      fun z => (eriIntegrand (fun slot => CPS1ElectronicSource.primitive (modes slot)) jets centres z : ℂ) := by
    funext z
    rw [CPS1ElectronicSource.coulomb_kernel_sub_comm z.1 z.2]
    simp only [CPS1QuantumNuclear.orbital_centred,Complex.star_def,Complex.conj_ofReal,
      eriIntegrand,Complex.ofReal_mul]
    ring
  unfold CPS1MolecularFrame.primitivePairIntegral
  rw [same,integral_complex_ofReal]
  rfl

def complexPairDerivative (modes : Quartet → Nat) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    (Quartet → Point) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (pairDerivative (fun slot => CPS1ElectronicSource.primitive (modes slot)) jets centres)

theorem multicentre_pair_hasFDerivAt (modes : Quartet → Nat) (jets : Quartet → MultiIndex) (centres : Quartet → Point) :
    HasFDerivAt (fun c : Quartet → Point => CPS1MolecularFrame.primitivePairIntegral (c 0) (c 1) (c 2) (c 3)
      (modes 0) (modes 1) (modes 2) (modes 3) (jets 0) (jets 1) (jets 2) (jets 3))
      (complexPairDerivative modes jets centres) centres := by
  have positive (slot : Quartet) : 0 < (CPS1ElectronicSource.primitive (modes slot)).exponent := by
    norm_num [CPS1ElectronicSource.primitive]
  have real := primitive_pair_hasFDerivAt (fun slot => CPS1ElectronicSource.primitive (modes slot)) positive jets centres
  have generated := Complex.ofRealCLM.hasFDerivAt.comp centres real
  have same : (fun c : Quartet → Point => CPS1MolecularFrame.primitivePairIntegral (c 0) (c 1) (c 2) (c 3)
      (modes 0) (modes 1) (modes 2) (modes 3) (jets 0) (jets 1) (jets 2) (jets 3)) =
      fun c => (primitiveERI (fun slot => CPS1ElectronicSource.primitive (modes slot)) jets c : ℂ) :=
    funext (multicentre_pair_relative modes jets)
  rw [same]
  exact generated

end
end CPS1Deformation
