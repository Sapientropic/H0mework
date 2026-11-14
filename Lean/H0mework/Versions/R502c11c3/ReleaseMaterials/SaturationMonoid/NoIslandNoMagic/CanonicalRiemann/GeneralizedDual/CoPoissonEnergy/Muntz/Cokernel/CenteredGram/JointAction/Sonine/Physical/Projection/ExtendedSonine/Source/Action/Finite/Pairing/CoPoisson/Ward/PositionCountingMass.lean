import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionCountedEuler

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionCountingMass
open Complex Filter MeasureTheory Set OriginalRieszSource
open scoped Topology BigOperators
local notation "q" => (1/4:ℝ)
local notation "box" => Ioc (0:ℝ) q
local notation "seed" => PositionCounting.seedRaw
open private seed_bound regularBound regular_nonnegative scaleBound scale_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionChannel
open private evenSeed evenSeed_split evenSeed_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionEuler

private theorem box_power (r:ℝ) (hr:-1<r) : IntegrableOn (fun x:ℝ => x^r) box := by
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤q)).mp
    (intervalIntegral.intervalIntegrable_rpow' hr)

private theorem product_mem (a b:ℝ) :
    ∀ᵐz:ℝ×ℝ ∂((volume.restrict (Ioc 0 a)).prod (volume.restrict (Ioc 0 b))),
      z.1∈Ioc 0 a ∧ z.2∈Ioc 0 b := by
  apply (Measure.ae_prod_iff_ae_ae
    (((measurableSet_Ioc.preimage measurable_fst).inter
      (measurableSet_Ioc.preimage measurable_snd)))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  exact ⟨hx,hy⟩

private theorem box_joint (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    Integrable (fun z:ℝ×ℝ => seed c (z.1*z.2))
      ((volume.restrict (Ioc 0 (N:ℝ))).prod (volume.restrict box)) := by
  have constant : IntegrableOn (fun _:ℝ => (1:ℝ)) box := integrableOn_const (by simp)
  have xpos : IntegrableOn (fun x:ℝ => x^(-c.value.re)+1) box :=
    (box_power (-c.value.re) (by linarith [c.belowOne])).add constant
  apply ((scale_integrable c N).mul_prod xpos).mono'
    (((PositionCounting.seed_measurable c).comp (by fun_prop)).aestronglyMeasurable)
  have located : ∀ᵐz:ℝ×ℝ ∂((volume.restrict (Ioc 0 (N:ℝ))).prod (volume.restrict box)),
      z.1∈Ioc 0 (N:ℝ) ∧ z.2∈box := by
    exact product_mem (N:ℝ) q
  filter_upwards [located] with z hz
  have actual := seed_bound c (z.1*z.2) (mul_ne_zero hz.1.1.ne' hz.2.1.ne')
  rw [abs_mul,abs_of_pos hz.1.1,abs_of_pos hz.2.1,Real.mul_rpow hz.1.1.le hz.2.1.le] at actual
  change ‖seed c (z.1*z.2)‖≤scaleBound c z.1*(z.2^(-c.value.re)+1)
  unfold scaleBound
  nlinarith [regular_nonnegative c,Real.rpow_nonneg hz.1.1.le (-c.value.re),
    Real.rpow_nonneg hz.2.1.le (-c.value.re)]

private def triangle (c:BurnolCompletedMellinCoordinate) (x y:ℝ) : ℂ :=
  if y≤x then (x:ℂ)⁻¹*seed c y else 0

private theorem triangle_joint (c:BurnolCompletedMellinCoordinate) :
    Integrable (fun z:ℝ×ℝ => triangle c z.1 z.2)
      ((volume.restrict box).prod (volume.restrict box)) := by
  let d:ℝ := (1-c.value.re)/2
  let C:ℝ := 1/2+regularBound c
  have hd:0<d := by dsimp [d];linarith [c.belowOne]
  have hc:0≤C := by dsimp [C];linarith [regular_nonnegative c]
  have first := box_power (d-1) (by linarith)
  have second := (box_power (-c.value.re-d) (by dsimp [d];linarith [c.belowOne])).const_mul C
  have measured : Measurable (fun z:ℝ×ℝ => triangle c z.1 z.2) := by
    unfold triangle
    have inverse : Measurable (fun z:ℝ×ℝ => (z.1:ℂ)⁻¹) := by fun_prop
    exact (inverse.mul ((PositionCounting.seed_measurable c).comp measurable_snd)).ite
      (measurableSet_le measurable_snd measurable_fst) measurable_const
  apply (first.mul_prod second).mono' measured.aestronglyMeasurable
  have located : ∀ᵐz:ℝ×ℝ ∂((volume.restrict box).prod (volume.restrict box)),
      z.1∈box ∧ z.2∈box := by
    exact product_mem q q
  filter_upwards [located] with z hz
  by_cases order:z.2≤z.1
  · have raw := seed_bound c z.2 hz.2.1.ne'
    rw [abs_of_pos hz.2.1] at raw
    have lower:1≤z.2^(-c.value.re) := by
      have h:=Real.rpow_le_rpow_of_nonpos hz.2.1 (show z.2≤1 by linarith [hz.2.2])
        (show -c.value.re≤0 by linarith [c.rightHalf])
      simpa only [Real.one_rpow] using h
    have bounded:‖seed c z.2‖≤C*z.2^(-c.value.re) := by
      dsimp [C]
      nlinarith [regular_nonnegative c]
    have growth:=Real.rpow_le_rpow hz.2.1.le order hd.le
    have yp:z.2^(-c.value.re)=z.2^(-c.value.re-d)*z.2^d := by
      rw [←Real.rpow_add hz.2.1]
      congr 1
      ring
    have xp:z.1^(d-1)=z.1^d*z.1⁻¹ := by
      rw [sub_eq_add_neg,Real.rpow_add hz.1.1,Real.rpow_neg_one]
    change ‖triangle c z.1 z.2‖≤z.1^(d-1)*(C*z.2^(-c.value.re-d))
    rw [triangle,if_pos order,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz.1.1]
    calc
      _≤z.1⁻¹*(C*z.2^(-c.value.re)) := mul_le_mul_of_nonneg_left bounded (inv_nonneg.mpr hz.1.1.le)
      _=C*z.2^(-c.value.re-d)*z.2^d*z.1⁻¹ := by rw [yp];ring
      _≤C*z.2^(-c.value.re-d)*z.1^d*z.1⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left growth (mul_nonneg hc (Real.rpow_nonneg hz.2.1.le _)))
          (inv_nonneg.mpr hz.1.1.le)
      _=_ := by rw [xp];ring
  · rw [triangle,if_neg order,norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hz.1.1.le _)
      (mul_nonneg hc (Real.rpow_nonneg hz.2.1.le _))

private theorem seed_scaled_integrable (c:BurnolCompletedMellinCoordinate) (a:ℝ) (ha:0<a) :
    IntegrableOn (fun x:ℝ => seed c (a*x)) box :=
  ((integrable_comp_mul_left_iff (seed c) ha.ne').mpr (PositionEuler.seed_integrable c)).mono_measure Measure.restrict_le_self

private theorem seed_scale (c:BurnolCompletedMellinCoordinate) (a:ℝ) (ha:0<a) :
    (∫x:ℝ in box,seed c (a*x))=(a:ℂ)⁻¹*(∫t:ℝ in Ioc 0 (a*q),seed c t) := by
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),
    intervalIntegral.integral_comp_mul_left _ ha.ne',mul_zero,
    intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤a*q)]
  simp only [Complex.real_smul,Complex.ofReal_inv]

private theorem seed_prefix_zero (c:BurnolCompletedMellinCoordinate) (b:ℝ) (hb:q≤b) :
    (∫t:ℝ in Ioc 0 b,seed c t)=0 := by
  have pointwise : EqOn (seed c) ((Ioc 0 q).indicator (positionSource c)) (Ioc 0 b) := by
    intro t ht
    simp only [PositionCounting.seedRaw,abs_of_pos ht.1,indicator_apply,mem_Ioc,ht.1,true_and]
  rw [setIntegral_congr_fun measurableSet_Ioc pointwise,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr (Ioc_subset_Ioc le_rfl hb),
    PositionSource.positive_mass_zero]

private theorem seed_scaled_mass_zero (c:BurnolCompletedMellinCoordinate) (a:ℝ) (ha:1≤a) :
    (∫x:ℝ in box,seed c (a*x))=0 := by
  rw [seed_scale c a (by linarith),seed_prefix_zero c (a*q) (by nlinarith)]
  simp

private theorem small_channel (c:BurnolCompletedMellinCoordinate) (x:ℝ) (hx:0<x) :
    (∫a:ℝ in Ioc 0 1,seed c (a*x))=
      (x:ℂ)⁻¹*(∫y:ℝ in Ioc 0 x,seed c y) := by
  rw [←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_comp_mul_right _ hx.ne',zero_mul,one_mul,
    intervalIntegral.integral_of_le hx.le]
  simp only [Complex.real_smul,Complex.ofReal_inv]

private theorem triangle_lower (c:BurnolCompletedMellinCoordinate) (x:ℝ) (hx:x∈box) :
    (∫y:ℝ in box,triangle c x y)=(x:ℂ)⁻¹*(∫y:ℝ in Ioc 0 x,seed c y) := by
  have same : (fun y:ℝ => triangle c x y)=(Iic x).indicator (fun y => (x:ℂ)⁻¹*seed c y) := by
    funext y
    simp only [triangle,indicator_apply,mem_Iic]
  rw [same,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have region:Iic x∩box=Ioc 0 x := by
    ext y
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · exact fun h => ⟨h.2.1,h.1⟩
    · exact fun h => ⟨h.2,⟨h.1,h.2.trans hx.2⟩⟩
  rw [region,integral_const_mul]

private theorem triangle_upper (c:BurnolCompletedMellinCoordinate) (y:ℝ) (hy:y∈box) :
    (∫x:ℝ in box,triangle c x y)=seed c y*(Real.log (q/y):ℂ) := by
  have same : (fun x:ℝ => triangle c x y)=(Ici y).indicator (fun x => (x:ℂ)⁻¹*seed c y) := by
    funext x
    simp only [triangle,indicator_apply,mem_Ici]
  rw [same,integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have region:Ici y∩box=Icc y q := by
    ext x
    simp only [mem_inter_iff,mem_Ici,mem_Ioc,mem_Icc]
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,⟨hy.1.trans_le h.1,h.2⟩⟩
  rw [region,integral_mul_const,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hy.2]
  simp_rw [←Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal,integral_inv_of_pos hy.1 (by norm_num : (0:ℝ)<q)]
  ring

/-- Both coordinate singularities are paid on the original fixed source box before Fubini. -/
theorem log_source_integrable (c:BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun y:ℝ => positionSource c y*(Real.log (q/y):ℂ)) box := by
  apply (triangle_joint c).integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  rw [triangle_upper c y hy,PositionCounting.seedRaw,abs_of_pos hy.1,if_pos hy.2]

private theorem continuous_mass_one (c:BurnolCompletedMellinCoordinate) :
    (∫x:ℝ in box,∫a:ℝ in Ioc 0 1,seed c (a*x))=
      ∫y:ℝ in box,positionSource c y*(Real.log (q/y):ℂ) := by
  calc
    _=∫x:ℝ in box,∫y:ℝ in box,triangle c x y := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      rw [small_channel c x hx.1,triangle_lower c x hx]
    _=∫y:ℝ in box,∫x:ℝ in box,triangle c x y := integral_integral_swap (triangle_joint c)
    _=_ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only
      rw [triangle_upper c y hy,PositionCounting.seedRaw,abs_of_pos hy.1,if_pos hy.2]

private theorem continuous_mass (c:BurnolCompletedMellinCoordinate) (N:ℕ) (hN:1≤N) :
    (∫x:ℝ in box,∫a:ℝ in Ioc 0 (N:ℝ),seed c (a*x))=
      ∫y:ℝ in box,positionSource c y*(Real.log (q/y):ℂ) := by
  have hn:(1:ℝ)≤N := by exact_mod_cast hN
  let f:ℝ→ℂ := fun a => ∫x:ℝ in box,seed c (a*x)
  have hf:IntegrableOn f (Ioc 0 (N:ℝ)) := (box_joint c N).integral_prod_left
  have small:IntegrableOn f (Ioc 0 1) := hf.mono_set (Ioc_subset_Ioc le_rfl hn)
  have large:IntegrableOn f (Ioc 1 (N:ℝ)) := hf.mono_set (Ioc_subset_Ioc (by norm_num) le_rfl)
  have split := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr small)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hn).mpr large)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    intervalIntegral.integral_of_le hn,intervalIntegral.integral_of_le (Nat.cast_nonneg N)] at split
  have after:(∫a:ℝ in Ioc 1 (N:ℝ),f a)=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro a ha
    exact seed_scaled_mass_zero c a ha.1.le
  rw [after,add_zero] at split
  rw [←integral_integral_swap (box_joint c N)]
  change (∫a:ℝ in Ioc 0 (N:ℝ),f a)=_
  rw [←split]
  have one := box_joint c 1
  norm_num only [Nat.cast_one] at one
  exact (integral_integral_swap one).trans (continuous_mass_one c)

private theorem positive_integrable (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    IntegrableOn (PositionCounting.raw c N) box := by
  have discrete : IntegrableOn (fun x:ℝ => ∑n∈Finset.Ico 1 N,seed c ((n:ℝ)*x)) box :=
    integrable_finsetSum _ (fun n hn => seed_scaled_integrable c n (by exact_mod_cast (Finset.mem_Ico.mp hn).1))
  exact discrete.sub (box_joint c N).integral_prod_right

private theorem positive_mass (c:BurnolCompletedMellinCoordinate) (N:ℕ) (hN:1≤N) :
    (∫x:ℝ in box,PositionCounting.raw c N x)=
      -(∫y:ℝ in box,positionSource c y*(Real.log (q/y):ℂ)) := by
  have term : ∀n∈Finset.Ico 1 N,IntegrableOn (fun x:ℝ => seed c ((n:ℝ)*x)) box :=
    fun n hn => seed_scaled_integrable c n (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
  change (∫x:ℝ in box, (∑n∈Finset.Ico 1 N,seed c ((n:ℝ)*x))-
    ∫a:ℝ in Ioc 0 (N:ℝ),seed c (a*x))=_
  rw [integral_sub (integrable_finsetSum _ term) (box_joint c N).integral_prod_right,
    integral_finsetSum _ term,continuous_mass c N hN]
  have zero:(∑n∈Finset.Ico 1 N,∫x:ℝ in box,seed c ((n:ℝ)*x))=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact seed_scaled_mass_zero c n (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
  rw [zero,zero_sub]

private theorem seed_even (c:BurnolCompletedMellinCoordinate) (x:ℝ) : seed c (-x)=seed c x := by
  simp only [PositionCounting.seedRaw,abs_neg]

private theorem raw_even (c:BurnolCompletedMellinCoordinate) (N:ℕ) (x:ℝ) :
    PositionCounting.raw c N (-x)=PositionCounting.raw c N x := by
  unfold PositionCounting.raw
  simp_rw [mul_neg,seed_even]

private theorem raw_even_seed (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    PositionCounting.raw c N=evenSeed (PositionCounting.raw c N) := by
  funext x
  unfold evenSeed
  by_cases inside:|x|≤q
  · rw [if_pos inside]
    by_cases positive:0≤x
    · rw [abs_of_nonneg positive]
    · rw [abs_of_neg (lt_of_not_ge positive),raw_even]
  · rw [if_neg inside,PositionCountedEuler.raw_outside c N x (lt_of_not_ge inside)]

theorem raw_integrable (c:BurnolCompletedMellinCoordinate) (N:ℕ) :
    Integrable (PositionCounting.raw c N) :=
  (evenSeed_integrable _ (positive_integrable c N)).congr
    (ae_of_all _ (fun x => congrFun (raw_even_seed c N).symm x))

/-- The whole finite source keeps the logarithmic contact of the small-scale continuous channel. -/
theorem mass_of_one_le (c:BurnolCompletedMellinCoordinate) (N:ℕ) (hN:1≤N) :
    (∫x:ℝ,PositionCounting.raw c N x)=
      -2*(∫y:ℝ in box,positionSource c y*(Real.log (q/y):ℂ)) := by
  let f := PositionCounting.raw c N
  let positive := (box).indicator f
  have hp:Integrable positive := (integrable_indicator_iff measurableSet_Ioc).mpr (positive_integrable c N)
  have hn:Integrable (fun x:ℝ => positive (-x)) :=
    (Measure.measurePreserving_neg (volume:Measure ℝ)).integrable_comp_of_integrable hp
  have reflected := (Measure.measurePreserving_neg (volume:Measure ℝ)).integral_comp
    measurableEmbedding_neg positive
  have split : (∫x:ℝ,f x)=(∫x:ℝ,positive x)+(∫x:ℝ,positive (-x)) := by
    change (∫x:ℝ,PositionCounting.raw c N x)=_
    rw [raw_even_seed c N,integral_congr_ae (evenSeed_split _),integral_add hp hn]
  rw [reflected] at split
  dsimp only [positive,f] at split
  rw [integral_indicator measurableSet_Ioc,positive_mass c N hN] at split
  rw [split]
  ring

theorem mass_zero (c:BurnolCompletedMellinCoordinate) : (∫x:ℝ,PositionCounting.raw c 0 x)=0 := by
  simp [PositionCounting.raw]
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionCountingMass
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
