import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.ConstantFourier
import Mathlib.Analysis.MellinTransform

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalUnitMellinSource.Sawtooth
open Complex Filter MeasureTheory Set
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped Topology InnerProductSpace
local notation "q" => (1/4:ℝ)

macro "sawtoothEulerPaid% " field:ident : term => do
  let owner := Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient 0
  let scope := `SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward.DirichletCoefficient
  return Lean.mkIdent (owner.append (scope.append field.getId))

def actualSawtoothIntegrand (s : ℂ) (x : ℝ) : ℂ :=
  -((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)

theorem actual_sawtooth_tail_one (s : ℂ) (positive : 0 < s.re) (notOne : s ≠ 1) :
    IntegrableOn (actualSawtoothIntegrand s) (Ioi 1) ∧
      (∫ x : ℝ in Ioi 1, actualSawtoothIntegrand s x) = riemannZeta s / s + 1 / (1 - s) := by
  have nonzero : s ≠ 0 := by intro same; simp [same] at positive
  have integrable := ((sawtoothEulerPaid% error_integrable) s positive).neg
  have same : (fun x : ℝ => -((sawtoothEulerPaid% errorIntegrand) s x)) = actualSawtoothIntegrand s := by
    funext x
    unfold actualSawtoothIntegrand
    change -(((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = _
    rw [neg_mul]
  change IntegrableOn (fun x : ℝ => -((sawtoothEulerPaid% errorIntegrand) s x)) (Ioi 1) at integrable
  rw [same] at integrable
  have original := (sawtoothEulerPaid% source_mellin_eq_zeta) s positive notOne
  rw [sawtoothEulerPaid% defect_mellin_eq] at original
  refine ⟨integrable, ?_⟩
  rw [← same, integral_neg]
  calc
    -(∫ x : ℝ in Ioi 1, (sawtoothEulerPaid% errorIntegrand) s x) =
        (s / (s - 1) - s * (∫ x : ℝ in Ioi 1, (sawtoothEulerPaid% errorIntegrand) s x)) / s -
          1 / (s - 1) := by field_simp [nonzero]; ring
    _ = riemannZeta s / s - 1 / (s - 1) := by rw [original]
    _ = riemannZeta s / s + 1 / (1 - s) := by
      rw [show 1 - s = -(s - 1) by ring, div_neg, sub_eq_add_neg]

private theorem actual_sawtooth_window (a : ℝ) (s : ℂ) (positiveA : 0 < a)
    (bounded : a ≤ 1) (below : s.re < 1) :
    IntegrableOn (actualSawtoothIntegrand s) (Ioc a 1) ∧
      (∫ x : ℝ in Ioc a 1, actualSawtoothIntegrand s x) =
        ((a : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  have exponent : -1 < (-s).re := by simp; linarith
  have power : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s)) (Ioc a 1) :=
    (intervalIntegral.intervalIntegrable_cpow' (a := a) (b := 1) exponent).1
  have same : (fun x : ℝ => -(x : ℂ) ^ (-s)) =ᵐ[volume.restrict (Ioc a 1)]
      actualSawtoothIntegrand s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (s := Ioc a 1) (volume.ae_ne (1 : ℝ))] with x inside notOneX
    have positiveX : 0 < x := positiveA.trans inside.1
    have belowX : x < 1 := lt_of_le_of_ne inside.2 notOneX
    unfold actualSawtoothIntegrand
    rw [Int.fract_eq_self.mpr ⟨positiveX.le, belowX⟩, neg_mul]
    congr 1
    calc
      (x : ℂ) ^ (-s) = (x : ℂ) ^ (1 + (-s - 1)) := by congr 1; ring
      _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-s - 1) :=
        Complex.cpow_add _ _ (by exact_mod_cast positiveX.ne' : (x : ℂ) ≠ 0)
      _ = (x : ℂ) * (x : ℂ) ^ (-s - 1) := by rw [Complex.cpow_one]
  refine ⟨power.neg.congr same, ?_⟩
  rw [← integral_congr_ae same, integral_neg, ← intervalIntegral.integral_of_le bounded,
    integral_cpow (Or.inl exponent), ofReal_one, one_cpow]
  have exponentEq : -s + 1 = 1 - s := by ring
  rw [exponentEq]
  ring

theorem actual_sawtooth_tail_scalar (a : ℝ) (s : ℂ) (positiveA : 0 < a) (bounded : a ≤ 1)
    (positive : 0 < s.re) (below : s.re < 1) :
    IntegrableOn (actualSawtoothIntegrand s) (Ioi a) ∧
      (∫ x : ℝ in Ioi a, actualSawtoothIntegrand s x) =
        riemannZeta s / s + (a : ℂ) ^ (1 - s) / (1 - s) := by
  have notOne : s ≠ 1 := by intro same; simp [same] at below
  have first := actual_sawtooth_window a s positiveA bounded below
  have tail := actual_sawtooth_tail_one s positive notOne
  have integrable : IntegrableOn (actualSawtoothIntegrand s) (Ioi a) := by
    rw [← Ioc_union_Ioi_eq_Ioi bounded]
    exact first.1.union tail.1
  refine ⟨integrable, ?_⟩
  rw [← Ioc_union_Ioi_eq_Ioi bounded,
    setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi first.1 tail.1, first.2, tail.2]
  ring


private theorem inverse_scaled_mellin (f : ℝ → ℂ) (s value : ℂ) (source : HasMellin f (-s) value) :
    HasMellin (fun x : ℝ => f ((1 / 4 : ℝ) / x)) s ((1 / 4 : ℂ) ^ s * value) := by
  have scaled := (MellinConvergent.comp_mul_left (f := f)
    (by norm_num : (0 : ℝ) < 1 / 4)).mpr source.1
  have inverse := (MellinConvergent.comp_rpow (f := fun y => f ((1 / 4 : ℝ) * y))
    (s := s) (by norm_num : (-1 : ℝ) ≠ 0)).mpr
      (by simpa only [ofReal_neg, ofReal_one, div_neg, div_one] using scaled)
  refine ⟨by simpa only [Real.rpow_neg_one, div_eq_mul_inv] using inverse, ?_⟩
  change mellin (fun x : ℝ => (fun y => f ((1 / 4 : ℝ) * y)) x⁻¹) s = _
  calc
    _ = mellin (fun y => f ((1 / 4 : ℝ) * y)) (-s) :=
      mellin_comp_inv (fun y => f ((1 / 4 : ℝ) * y)) s
    _ = _ := by
      rw [mellin_comp_mul_left _ _ (by norm_num : (0 : ℝ) < 1 / 4), neg_neg, source.2]
      norm_num [smul_eq_mul]


private theorem original_sawtooth_head (z : ℂ) (below : z.re<1) :
    IntegrableOn (actualSawtoothIntegrand z) (Ioc 0 1) ∧
      (∫ x : ℝ in Ioc 0 1,actualSawtoothIntegrand z x)= -1/(1-z) := by
  have exponent : -1<(-z).re := by simp only [neg_re];linarith
  have power:= (intervalIntegral.intervalIntegrable_cpow' (a:=0) (b:=1) exponent).1
  have same : (fun x : ℝ=>-(x:ℂ)^(-z))=ᵐ[volume.restrict (Ioc 0 1)] actualSawtoothIntegrand z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (s:=Ioc (0:ℝ) 1) (volume.ae_ne (1:ℝ))] with x inside notOne
    have belowX : x<1 := lt_of_le_of_ne inside.2 notOne
    unfold actualSawtoothIntegrand
    rw [Int.fract_eq_self.mpr ⟨inside.1.le,belowX⟩,neg_mul]
    have identity:=Complex.cpow_add 1 (-z-1) (Complex.ofReal_ne_zero.mpr inside.1.ne')
    rw [Complex.cpow_one,show (1:ℂ)+(-z-1)= -z by ring] at identity
    exact congrArg Neg.neg identity
  refine ⟨power.neg.congr same,?_⟩
  rw [← integral_congr_ae same,integral_neg,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_cpow (Or.inl exponent)]
  have nonzero : -z+1≠0 := by intro vanishing;have re:=congrArg Complex.re vanishing;simp at re;linarith
  simp only [Complex.ofReal_one,one_cpow,Complex.ofReal_zero,zero_cpow nonzero,sub_zero]
  rw [show -z+1=1-z by ring]
  ring

theorem actual_whole_fractional_mellin (z : ℂ) (positive : 0<z.re) (below : z.re<1) :
    HasMellin (fun x : ℝ=>-((Int.fract x:ℝ):ℂ)) (-z) (riemannZeta z/z) := by
  have notOne : z≠1 := by intro vanishing;rw [vanishing] at below;norm_num at below
  have head:=original_sawtooth_head z below
  have tail:=actual_sawtooth_tail_one z positive notOne
  have whole : IntegrableOn (actualSawtoothIntegrand z) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1)]
    exact head.1.union tail.1
  have value : (∫ x : ℝ in Ioi 0,actualSawtoothIntegrand z x)=riemannZeta z/z := by
    rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),setIntegral_union Ioc_disjoint_Ioi_same
      measurableSet_Ioi head.1 tail.1,head.2,tail.2]
    ring
  have same : (fun x : ℝ=>(x:ℂ)^(-z-1)*(-((Int.fract x:ℝ):ℂ)))=actualSawtoothIntegrand z := by
    funext x
    unfold actualSawtoothIntegrand
    ring
  change IntegrableOn (fun x : ℝ=>(x:ℂ)^(-z-1)*(-((Int.fract x:ℝ):ℂ))) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0,(x:ℂ)^(-z-1)*(-((Int.fract x:ℝ):ℂ)))=riemannZeta z/z
  rw [same]
  exact ⟨whole,value⟩

theorem actual_original_d_mellin (z : ℂ) (positive : 0<z.re) (below : z.re<1) :
    HasMellin (ConstantDual.value:ℝ→ℂ) z ((q:ℂ)^z*(riemannZeta z/z)) := by
  have source:=inverse_scaled_mellin _ z _ (actual_whole_fractional_mellin z positive below)
  have raw : (ConstantDual.value:ℝ→ℂ)=ᵐ[volume.restrict (Ioi 0)] fun x : ℝ=>-((Int.fract (q/x):ℝ):ℂ) := by
    filter_upwards [ae_restrict_of_ae ConstantDual.value_coeFn,ae_restrict_mem measurableSet_Ioi] with x native inside
    rw [native,ConstantDual.sawtoothRaw,abs_of_pos inside]
  have weighted : (fun x : ℝ=>(x:ℂ)^(z-1)*(ConstantDual.value x))=ᵐ[volume.restrict (Ioi 0)]
      fun x : ℝ=>(x:ℂ)^(z-1)*(-((Int.fract (q/x):ℝ):ℂ)) := by
    filter_upwards [raw] with x actual
    rw [actual]
  refine ⟨source.1.congr weighted.symm,?_⟩
  change (∫ x : ℝ in Ioi 0,(x:ℂ)^(z-1)*ConstantDual.value x)=_
  have read : (∫ x : ℝ in Ioi 0,(x:ℂ)^(z-1)*(-((Int.fract (q/x):ℝ):ℂ)))=
      (q:ℂ)^z*(riemannZeta z/z) := by
    simpa only [mellin,smul_eq_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using source.2
  exact (integral_congr_ae weighted).trans read


end OriginalUnitMellinSource.Sawtooth
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
