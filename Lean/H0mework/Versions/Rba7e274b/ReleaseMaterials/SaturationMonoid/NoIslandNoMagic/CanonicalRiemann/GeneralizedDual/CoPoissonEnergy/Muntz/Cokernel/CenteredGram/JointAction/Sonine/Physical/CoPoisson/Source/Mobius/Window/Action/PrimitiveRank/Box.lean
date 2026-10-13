import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Window
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Contraction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace

def boxSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  (2/(1-coordinate.value):ℂ) • Paid.box 4+
  (2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value)) • Paid.interiorBase coordinate

 theorem box_source_even : reflectL2 (Paid.box 4)=Paid.box 4 := by
  apply Lp.ext
  have reflected := negMeasurePreserving.quasiMeasurePreserving.ae_eq (FiniteMobiusResolventFlux.box_read 4)
  filter_upwards [Lp.coeFn_compMeasurePreserving (Paid.box 4) negMeasurePreserving,
    reflected,FiniteMobiusResolventFlux.box_read 4] with x moved negative direct
  rw [show reflectL2 (Paid.box 4) x=Paid.box 4 (-x) from moved,direct]
  simp only [Function.comp_def] at negative
  rw [negative]
  have membership : -x∈symmetricInterval 4 ↔ x∈symmetricInterval 4 := by
    change -4≤-x ∧ -x≤4 ↔ -4≤x ∧ x≤4
    constructor <;> rintro ⟨lower,upper⟩ <;> constructor <;> linarith
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside,indicator_of_mem (membership.mpr inside)]
  · rw [indicator_of_notMem inside,indicator_of_notMem (fun h=>inside (membership.mp h))]

 theorem box_source_read (coordinate : BurnolCompletedMellinCoordinate) :
    (boxSource coordinate : ℝ→ℂ)=ᵐ[volume] fun x=>
      if |x| < (4:ℝ) then (2/(1-coordinate.value):ℂ)-
        (2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value))*((|x|:ℝ):ℂ)^(coordinate.value-1) else 0 := by
  filter_upwards [Lp.coeFn_add ((2/(1-coordinate.value):ℂ) • Paid.box 4)
      ((2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value)) • Paid.interiorBase coordinate),
    Lp.coeFn_smul (2/(1-coordinate.value):ℂ) (Paid.box 4),
    Lp.coeFn_smul (2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value)) (Paid.interiorBase coordinate),
    FiniteMobiusResolventFlux.box_read 4,Paid.interior_base_read coordinate,volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x add boxScalar powerScalar boxRead powerRead notFour notNegativeFour
  change ((2/(1-coordinate.value):ℂ) • Paid.box 4+
    (2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value)) • Paid.interiorBase coordinate : BurnolL2) x=_
  rw [add,Pi.add_apply,boxScalar,powerScalar]
  change (2/(1-coordinate.value):ℂ)*Paid.box 4 x+
    (2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value))*Paid.interiorBase coordinate x=_
  rw [boxRead,powerRead]
  by_cases inside : |x| < (4:ℝ)
  · simp only [indicator_of_mem (show x∈symmetricInterval 4 from abs_le.mp inside.le),if_pos inside]
    ring
  · have outside : x∉symmetricInterval 4 := by
      intro bound
      have same : |x|=4 := le_antisymm (abs_le.mpr bound) (le_of_not_gt inside)
      rcases eq_or_eq_neg_of_abs_eq same with equal | equal
      · exact notFour equal
      · exact notNegativeFour equal
    simp only [indicator_of_notMem outside,if_neg inside,mul_zero,add_zero]

 theorem box_Rplus_source (coordinate : BurnolCompletedMellinCoordinate) :
    Paid.Rplus (coordinate.value/2) (Paid.box 4)=boxSource coordinate := by
  let field := Paid.Rplus (coordinate.value/2) (Paid.box 4)
  have even : reflectL2 field=field := FiniteMobiusResolventFlux.Rplus_even coordinate _ box_source_even
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have supported : Cut.cutoff 4 field=field := by
    have source := cutoff_Rplus_source 4 (by norm_num) (coordinate.value/2) right (Paid.box 4)
    rw [FiniteMobiusResolventFlux.cutoff_box 4 4 (by norm_num) (le_refl _)] at source
    exact source
  have supportRead := Cut.cutoff_read 4 field
  rw [supported] at supportRead
  have parity := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
  change (reflectL2 field : ℝ→ℂ)=ᵐ[volume] (field : ℝ→ℂ) ∘ (fun x=>-x) at parity
  rw [even] at parity
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae (box_Rplus_positive coordinate)
  apply Lp.ext
  filter_upwards [box_Rplus_positive coordinate,negative,parity,supportRead,box_source_read coordinate,
    volume.ae_ne (0:ℝ),volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)] with x positiveRead negativeRead reflected support target nonzero notFour notNegativeFour
  change field x=boxSource coordinate x
  rw [target]
  by_cases inside : |x| < (4:ℝ)
  · rw [if_pos inside]
    have source : field x= -(2:ℂ)*((|x|:ℝ):ℂ)^(coordinate.value-1)*
        ((4:ℂ)^(1-coordinate.value)-((|x|:ℝ):ℂ)^(1-coordinate.value))/(1-coordinate.value) := by
      rcases lt_or_gt_of_ne nonzero with neg | pos
      · have actual : field x=field (-x) := reflected
        rw [actual,abs_of_neg neg]
        exact negativeRead (by linarith) (by simpa only [abs_of_neg neg] using inside.le)
      · rw [abs_of_pos pos]
        exact positiveRead pos (by simpa only [abs_of_pos pos] using inside.le)
    rw [source]
    have unit : ((|x|:ℝ):ℂ)^(coordinate.value-1)*((|x|:ℝ):ℂ)^(1-coordinate.value)=1 := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)),show coordinate.value-1+(1-coordinate.value)=0 by ring,Complex.cpow_zero]
    calc
      _ = 2/(1-coordinate.value)*
        (((|x|:ℝ):ℂ)^(coordinate.value-1)*((|x|:ℝ):ℂ)^(1-coordinate.value))-
        (2*(4:ℂ)^(1-coordinate.value)/(1-coordinate.value))*((|x|:ℝ):ℂ)^(coordinate.value-1) := by ring
      _ = _ := by rw [unit,mul_one]
  · rw [if_neg inside,support,indicator_of_notMem]
    intro bound
    have equal : |x|=4 := le_antisymm (abs_le.mpr bound) (le_of_not_gt inside)
    rcases eq_or_eq_neg_of_abs_eq equal with same | same
    · exact notFour same
    · exact notNegativeFour same

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
