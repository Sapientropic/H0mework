import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousOrbit

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalRieszSource OriginalPaPhysicalGreen
open OriginalKSourceResolventReconstruction
open scoped Topology ENNReal

open private centreLimit centre_integrable homogeneous_tail_read homogeneous_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.WeakLimit

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "r₀" => ((1/4 : ℝ)/2)
local notation "box" => symmetricInterval r₀
local notation "raw" => fun (z : L¹ × BurnolL2) (x : ℝ) => Prod.fst z x+Prod.snd z x
local notation "Hraw" => fun c (x : ℝ) =>
  ((|x| : ℝ) : ℂ)^(-star (BurnolCompletedMellinCoordinate.value c))*(1/2 : ℂ)
local notation "positiveLine" => Measure.restrict (volume : Measure ℝ) (Ioi (0 : ℝ))

local instance positiveLineNonzero : NeZero positiveLine := ⟨by
  intro zero
  have whole := congrArg (fun m : Measure ℝ => m univ) zero
  rw [Measure.restrict_apply_univ, Real.volume_Ioi, Measure.coe_zero, Pi.zero_apply] at whole
  exact ENNReal.top_ne_zero whole⟩

private theorem positive_scaling_constant (g : ℝ → ℂ) (measured : Measurable g)
    (action : ∀ a : ℝ, 0 < a → ∀ᵐ x : ℝ ∂volume, g (a*x) = g x) :
    ∃ coefficient : ℂ, ∀ᵐ x : ℝ ∂positiveLine, g x = coefficient := by
  have fibre : ∀ᵐ a : ℝ ∂positiveLine, ∀ᵐ x : ℝ ∂positiveLine, g (a*x) = g x :=
    (ae_restrict_mem measurableSet_Ioi).mono fun a positive =>
      ae_restrict_of_ae (action a positive)
  have relation : MeasurableSet {z : ℝ × ℝ | g (z.1*z.2) = g z.2} :=
    measurableSet_eq_fun (measured.comp (measurable_fst.mul measurable_snd))
      (measured.comp measurable_snd)
  obtain ⟨base, read, positive⟩ := (((Measure.ae_ae_comm (μ := positiveLine) (ν := positiveLine) relation).mp fibre).and
    (ae_restrict_mem measurableSet_Ioi)).exists
  have basePositive : 0 < base := positive
  have full := (ae_restrict_iff' measurableSet_Ioi).mp read
  have pull : Measure.QuasiMeasurePreserving (fun a : ℝ => base⁻¹*a) volume volume := by
    simpa only [smul_eq_mul] using
      Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ)) (inv_ne_zero basePositive.ne')
  refine ⟨g base, ?_⟩
  filter_upwards [ae_restrict_of_ae (pull.ae full), ae_restrict_mem measurableSet_Ioi] with x atx live
  change 0 < base⁻¹*x → g ((base⁻¹*x)*base) = g base at atx
  have moved := atx (mul_pos (inv_pos.mpr basePositive) live)
  simpa only [mul_comm (base⁻¹*x) base, ← mul_assoc, mul_inv_cancel₀ basePositive.ne', one_mul] using moved

private theorem even_scaling_constant (g : ℝ → ℂ) (measured : Measurable g)
    (action : ∀ a : ℝ, 0 < a → ∀ᵐ x : ℝ ∂volume, g (a*x) = g x)
    (even : ∀ᵐ x : ℝ ∂volume, g (-x) = g x) :
    ∃ coefficient : ℂ, ∀ᵐ x : ℝ ∂volume, g x = coefficient := by
  obtain ⟨a, positive⟩ := positive_scaling_constant g measured action
  have first := (ae_restrict_iff' measurableSet_Ioi).mp positive
  refine ⟨a, ?_⟩
  filter_upwards [first, negMeasurePreserving.quasiMeasurePreserving.ae first, even, volume.ae_ne (0 : ℝ)]
    with x direct reflected parity nonzero
  by_cases live : 0 < x
  · exact direct live
  · have negative := lt_of_le_of_ne (le_of_not_gt live) nonzero
    exact parity.symm.trans (reflected (neg_pos.mpr negative))

private theorem homogeneous_raw_coefficient (c : BurnolCompletedMellinCoordinate) (z : L¹ × BurnolL2)
    (even : ∀ᵐ x : ℝ ∂volume, raw z (-x) = raw z x)
    (law : GapEuler.euler (distributionOfSplit z)+(star c.value-1/2) • distributionOfSplit z = 0) :
    ∃ a : ℂ, (raw z) =ᵐ[volume] fun x => a*Hraw c x := by
  let s := star c.value
  let weight := fun x : ℝ => ((|x| : ℝ) : ℂ)^s
  let g := fun x : ℝ => weight x*raw z x
  have powerMeasurable : Measurable weight := by
    apply measurable_of_continuousOn_compl_singleton 0
    intro x hx
    have live : x ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
    exact ((Complex.continuousAt_ofReal_cpow_const |x| s (Or.inr (abs_ne_zero.mpr live))).comp
      continuous_abs.continuousAt).continuousWithinAt
  have rawMeasurable : Measurable (raw z) := (Lp.stronglyMeasurable z.1).measurable.add (Lp.stronglyMeasurable z.2).measurable
  have measured : Measurable g := powerMeasurable.mul rawMeasurable
  have parity : ∀ᵐ x : ℝ ∂volume, g (-x) = g x := by
    filter_upwards [even] with x read
    dsimp only [g, weight]
    rw [abs_neg, read]
  have act (a : ℝ) (positive : 0 < a) : ∀ᵐ x : ℝ ∂volume, g (a*x) = g x := by
    let h := Real.log a
    have scale : Real.exp h = a := Real.exp_log positive
    have phase : Complex.exp (-(s-1/2)*(h : ℂ)) =
        (Real.exp (h/2) : ℂ)*Complex.exp (-s*(h : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    have power (x : ℝ) : weight (a*x) = Complex.exp (s*(h : ℂ))*weight x := by
      dsimp only [weight]
      rw [abs_mul, abs_of_pos positive, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg positive.le (abs_nonneg x),
        Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr positive.ne'),
        ← Complex.ofReal_log positive.le]
      dsimp only [h]
      ring
    have source := homogeneous_split_raw_dilation z (s-1/2) law h
    filter_upwards [source] with x value
    rw [scale, phase, mul_assoc] at value
    have rawScale := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (h/2))) value
    have cancel : Complex.exp (s*(h : ℂ))*Complex.exp (-s*(h : ℂ)) = 1 := by
      rw [← Complex.exp_add, show s*(h : ℂ)+ -s*(h : ℂ)=0 by ring, Complex.exp_zero]
    dsimp only [g]
    rw [power, rawScale]
    calc
      _ = (Complex.exp (s*(h : ℂ))*Complex.exp (-s*(h : ℂ)))*(weight x*raw z x) := by ring
      _ = _ := by rw [cancel, one_mul]
  obtain ⟨a, constant⟩ := even_scaling_constant g measured act parity
  refine ⟨2*a, ?_⟩
  filter_upwards [constant, volume.ae_ne (0 : ℝ)] with x actual nonzero
  have live : weight x ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)))
  apply mul_left_cancel₀ live
  change g x = weight x*((2*a)*(((|x| : ℝ) : ℂ)^(-s)*(1/2 : ℂ)))
  rw [actual, Complex.cpow_neg]
  change a = weight x*((2*a)*((weight x)⁻¹*(1/2 : ℂ)))
  field_simp [live]

/-- Support and parity of the actual two pieces of the same half-gap cutoff. -/
structure IsEvenPhysicalSplit (z : L¹ × BurnolL2) : Prop where
  centre : ∀ᵐ x : ℝ ∂volume, x ∉ box → z.1 x = 0
  exterior : ∀ᵐ x : ℝ ∂volume, x ∈ box → z.2 x = 0
  even : ∀ᵐ x : ℝ ∂volume, raw z (-x) = raw z x

private theorem cutoff_split_read (radius : ℝ) (value : BurnolL2) :
    ∀ᵐ x : ℝ ∂volume,
      (splitAtPhysicalCutoff radius value).1 x = (symmetricInterval radius).indicator (value : ℝ → ℂ) x ∧
      (splitAtPhysicalCutoff radius value).2 x =
        value x-(symmetricInterval radius).indicator (value : ℝ → ℂ) x := by
  let cut := originalPhysicalCutoff radius value
  have centre := (originalPhysicalCutoff_integrable radius value).coeFn_toL1
  filter_upwards [centre, Lp.coeFn_sub value cut, originalPhysicalCutoff_coeFn radius value]
    with x inner outer atx
  constructor
  · exact inner.trans atx
  · change (value-cut : BurnolL2) x = _
    rw [outer, Pi.sub_apply, atx]

private theorem cutoff_split_whole (radius : ℝ) (value : BurnolL2) :
    (raw (splitAtPhysicalCutoff radius value)) =ᵐ[volume] (value : ℝ → ℂ) := by
  filter_upwards [cutoff_split_read radius value] with x parts
  rw [parts.1, parts.2]
  abel

theorem actual_even_physical_split (value : BurnolL2) (even : reflectL2 value = value) :
    IsEvenPhysicalSplit (splitAtPhysicalCutoff r₀ value) := by
  have full := cutoff_split_whole r₀ value
  have reflected := Lp.coeFn_compMeasurePreserving value negMeasurePreserving
  change ∀ᵐ x : ℝ ∂volume, reflectL2 value x = value (-x) at reflected
  rw [even] at reflected
  constructor
  · filter_upwards [cutoff_split_read r₀ value] with x actual outside
    rw [actual.1, indicator_of_notMem outside]
  · filter_upwards [cutoff_split_read r₀ value] with x actual inside
    rw [actual.2, indicator_of_mem inside, sub_self]
  · filter_upwards [full, negMeasurePreserving.quasiMeasurePreserving.ae full, reflected]
      with x direct opposite parity
    change raw (splitAtPhysicalCutoff r₀ value) (-x) = value (-x) at opposite
    exact opposite.trans (parity.symm.trans direct.symm)

theorem counted_homogeneous_even_physical_split (c : BurnolCompletedMellinCoordinate) :
    IsEvenPhysicalSplit (countedHomogeneousSplit c) := by
  let z := countedHomogeneousSplit c
  have core := (centre_integrable c).coeFn_toL1
  have outside := homogeneous_tail_read c
  have whole : (raw z) =ᵐ[volume] Hraw c := by
    filter_upwards [core, outside] with x insideRead outsideRead
    change z.1 x = _ at insideRead
    change z.2 x = _ at outsideRead
    rw [insideRead, outsideRead]
    by_cases inside : x ∈ box
    · rw [indicator_of_mem inside, if_neg (not_lt_of_ge (abs_le.mpr inside)), add_zero]
    · rw [indicator_of_notMem inside, if_pos (lt_of_not_ge (fun h => inside (abs_le.mp h))), zero_add]
  constructor
  · filter_upwards [core] with x read missing
    change z.1 x = _ at read
    rw [read, indicator_of_notMem missing]
  · filter_upwards [outside] with x read member
    change z.2 x = _ at read
    rw [read, if_neg (not_lt_of_ge (abs_le.mpr member))]
  · filter_upwards [whole, negMeasurePreserving.quasiMeasurePreserving.ae whole] with x read reflected
    change raw z (-x) = Hraw c (-x) at reflected
    exact reflected.trans ((homogeneous_even c x).trans read.symm)

theorem distributionOfSplit_from_cutoff (radius : ℝ) (value : BurnolL2) :
    distributionOfSplit (splitAtPhysicalCutoff radius value) = (value : S') := by
  ext test
  rw [distributionOfSplit_apply, Lp.toTemperedDistribution_apply]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [cutoff_split_whole radius value] with x read
  rw [read]

/-- The original Euler action on the complete mixed source. -/
def eulerOfPhysicalSplit (c : BurnolCompletedMellinCoordinate) :
    (L¹ × BurnolL2) →L[ℂ] S' :=
  (GapEuler.euler+(star c.value-1/2) • ContinuousLinearMap.id ℂ S').comp distributionOfSplit

/-- The literal R source generates the Euler observation on the exact split. -/
theorem actual_split_R_equation (c : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
    eulerOfPhysicalSplit c (splitAtPhysicalCutoff r₀ (sourceResolvent c input)) =
      -(2 : ℂ) • (input : S') := by
  change GapEuler.euler (distributionOfSplit (splitAtPhysicalCutoff r₀ (sourceResolvent c input)))+
    (star c.value-1/2) • distributionOfSplit (splitAtPhysicalCutoff r₀ (sourceResolvent c input)) = _
  rw [distributionOfSplit_from_cutoff]
  exact sourceResolvent_euler c input

/-- The entire homogeneous fibre on the actual even split consists of the
one original homogeneous line. The two supports recover both components. -/
theorem original_split_homogeneous_fibre (c : BurnolCompletedMellinCoordinate)
    (z : L¹ × BurnolL2) (supported : IsEvenPhysicalSplit z) :
    eulerOfPhysicalSplit c z = 0 ↔ ∃ a : ℂ, z = a • countedHomogeneousSplit c := by
  constructor
  · intro zero
    have law : GapEuler.euler (distributionOfSplit z)+(star c.value-1/2) • distributionOfSplit z = 0 := zero
    obtain ⟨a, actual⟩ := homogeneous_raw_coefficient c z supported.even law
    refine ⟨a, Prod.ext ?_ ?_⟩
    · apply Lp.ext
      let core := centreLimit c
      have read := (centre_integrable c).coeFn_toL1
      filter_upwards [actual, supported.centre, supported.exterior, read,
        Lp.coeFn_smul a core] with x value centre exterior face scalar
      change core x = _ at face
      change z.1 x = (a • core : L¹) x
      rw [scalar, Pi.smul_apply, smul_eq_mul, face]
      change z.1 x+z.2 x = _ at value
      by_cases inside : x ∈ box
      · rw [indicator_of_mem inside]
        rwa [exterior inside, add_zero] at value
      · rw [indicator_of_notMem inside, mul_zero]
        exact centre inside
    · apply Lp.ext
      let tail := (countedHomogeneousSplit c).2
      filter_upwards [actual, supported.centre, supported.exterior, homogeneous_tail_read c,
        Lp.coeFn_smul a tail] with x value centre exterior face scalar
      change tail x = _ at face
      change z.2 x = (a • tail : BurnolL2) x
      rw [scalar, Pi.smul_apply, smul_eq_mul, face]
      change z.1 x+z.2 x = _ at value
      by_cases inside : x ∈ box
      · rw [if_neg (not_lt_of_ge (abs_le.mpr inside)), mul_zero]
        exact exterior inside
      · rw [if_pos (lt_of_not_ge (fun h => inside (abs_le.mp h)))]
        rwa [centre inside, zero_add] at value
  · rintro ⟨a, rfl⟩
    have law : eulerOfPhysicalSplit c (countedHomogeneousSplit c) = 0 := counted_homogeneous_euler c
    rw [map_smul, law]
    ext test
    simp [smul_apply]

private theorem split_difference_raw (left right : L¹ × BurnolL2) :
    ∀ᵐ x : ℝ ∂volume, raw (left-right) x = raw left x-raw right x := by
  filter_upwards [Lp.coeFn_sub left.1 right.1, Lp.coeFn_sub left.2 right.2] with x centre exterior
  change (left.1-right.1 : L¹) x+(left.2-right.2 : BurnolL2) x = _
  rw [centre, exterior, Pi.sub_apply, Pi.sub_apply]
  abel

private theorem even_split_sub {left right : L¹ × BurnolL2}
    (first : IsEvenPhysicalSplit left) (second : IsEvenPhysicalSplit right) :
    IsEvenPhysicalSplit (left-right) := by
  constructor
  · filter_upwards [first.centre, second.centre, Lp.coeFn_sub left.1 right.1] with x one two subtracted outside
    change (left.1-right.1 : L¹) x = _
    rw [subtracted, Pi.sub_apply, one outside, two outside, sub_self]
  · filter_upwards [first.exterior, second.exterior, Lp.coeFn_sub left.2 right.2] with x one two subtracted inside
    change (left.2-right.2 : BurnolL2) x = _
    rw [subtracted, Pi.sub_apply, one inside, two inside, sub_self]
  · have rawSub := split_difference_raw left right
    filter_upwards [rawSub, negMeasurePreserving.quasiMeasurePreserving.ae rawSub, first.even, second.even]
      with x direct reflected one two
    exact reflected.trans ((congrArg₂ (· - ·) one two).trans direct.symm)

/-- The same weak Euler and physical observations determine the complete
original even split at the exact zero. -/
theorem original_split_euler_physical_injective (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) {left right : L¹ × BurnolL2}
    (first : IsEvenPhysicalSplit left) (second : IsEvenPhysicalSplit right)
    (sameSource : eulerOfPhysicalSplit c left = eulerOfPhysicalSplit c right)
    (samePhysical : physicalProjectionFromCentre left = physicalProjectionFromCentre right) :
    left = right := by
  have source : eulerOfPhysicalSplit c (left-right) = 0 := by
    rw [map_sub, sameSource, sub_self]
  obtain ⟨a, line⟩ := (original_split_homogeneous_fibre c (left-right) (even_split_sub first second)).mp source
  have physical : physicalProjectionFromCentre (left-right) = 0 := by
    rw [map_sub, samePhysical, sub_self]
  rw [line] at physical
  have coefficient : a = 0 := (actual_homogeneous_coefficient_recovery c zero a 0).mp (by
    rw [physical, zero_smul, map_zero])
  rw [coefficient, zero_smul] at line
  exact sub_eq_zero.mp line

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
