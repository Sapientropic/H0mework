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

-- Coefficient multiplication consumes the interval source law even at the exact resonance.
theorem inverse_interior_positive (coordinate parameter : BurnolCompletedMellinCoordinate) :
    ∀ᵐ x : ℝ ∂volume, ∀ _positive : 0<x, ∀ _bounded : x<4,
    inverseAction (coordinate.value/2) (parameter.value/2) (Paid.interiorBase coordinate) x=
      -((4:ℂ)^(coordinate.value-parameter.value))*Paid.interiorBase parameter x := by
  filter_upwards [Lp.coeFn_sub (-(Paid.interiorBase coordinate))
    ((parameter.value/2-coordinate.value/2) • Paid.Rplus (parameter.value/2) (Paid.interiorBase coordinate)),
    Lp.coeFn_neg (Paid.interiorBase coordinate),Lp.coeFn_smul (parameter.value/2-coordinate.value/2)
      (Paid.Rplus (parameter.value/2) (Paid.interiorBase coordinate)),Paid.interior_base_read coordinate,
    Paid.interior_base_read parameter,interior_Rplus_positive coordinate parameter] with x difference negative scalar source target response positive bounded
  change (-(Paid.interiorBase coordinate)-(parameter.value/2-coordinate.value/2) •
    Paid.Rplus (parameter.value/2) (Paid.interiorBase coordinate) : BurnolL2) x=_
  rw [difference,Pi.sub_apply,negative,Pi.neg_apply,scalar]
  change -(Paid.interiorBase coordinate : BurnolL2) x-(parameter.value/2-coordinate.value/2)*
    Paid.Rplus (parameter.value/2) (Paid.interiorBase coordinate) x=_
  rw [source,target,abs_of_pos positive,response positive bounded.le]
  simp only [if_pos bounded]
  have changePower : (x:ℂ)^(coordinate.value-1)=(x:ℂ)^(parameter.value-1)*(x:ℂ)^(coordinate.value-parameter.value) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
    congr 1
    ring
  rw [changePower]
  have sourceDifference := source_power_difference (coordinate.value-parameter.value) x 4 positive bounded.le
  calc
    _ = (x:ℂ)^(parameter.value-1)*
        ((x:ℂ)^(coordinate.value-parameter.value)+(coordinate.value-parameter.value)*
          (∫ t:ℝ in x..(4:ℝ),(t:ℂ)^(coordinate.value-parameter.value-1))) := by ring
    _ = _ := by
      rw [sourceDifference]
      norm_num only [Complex.ofReal_ofNat]
      ring

 theorem interior_source_even (coordinate : BurnolCompletedMellinCoordinate) :
    reflectL2 (Paid.interiorBase coordinate)=Paid.interiorBase coordinate := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving (Paid.interiorBase coordinate) negMeasurePreserving,
    Paid.interior_base_read coordinate,negMeasurePreserving.quasiMeasurePreserving.ae_eq (Paid.interior_base_read coordinate)]
    with x reflection direct negative
  simp only [Function.comp_def] at negative
  rw [show reflectL2 (Paid.interiorBase coordinate) x=Paid.interiorBase coordinate (-x) from reflection,direct]
  rw [negative,abs_neg]

 theorem interior_source_supported (coordinate : BurnolCompletedMellinCoordinate) :
    Cut.cutoff 4 (Paid.interiorBase coordinate)=Paid.interiorBase coordinate := by
  apply Lp.ext
  filter_upwards [Cut.cutoff_read 4 (Paid.interiorBase coordinate),Paid.interior_base_read coordinate] with x cutRead source
  rw [cutRead]
  by_cases inside : x∈symmetricInterval 4
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside,source,if_neg]
    intro bound
    exact inside (abs_le.mp bound.le)

-- Full actual source action, not a caller-selected return equality.
theorem inverse_interior_source (coordinate parameter : BurnolCompletedMellinCoordinate) :
    inverseAction (coordinate.value/2) (parameter.value/2) (Paid.interiorBase coordinate)=
      -((4:ℂ)^(coordinate.value-parameter.value)) • Paid.interiorBase parameter := by
  let field := inverseAction (coordinate.value/2) (parameter.value/2) (Paid.interiorBase coordinate)
  have right : 1/4<(parameter.value/2).re := by rw [Complex.div_re];norm_num;linarith [parameter.rightHalf]
  have even : reflectL2 field=field := by
    unfold field inverseAction
    rw [map_sub,map_neg,map_smul,interior_source_even,FiniteMobiusResolventFlux.Rplus_even parameter _ (interior_source_even coordinate)]
  have supported : Cut.cutoff 4 field=field := by
    unfold field inverseAction
    rw [map_sub,map_neg,map_smul,interior_source_supported]
    have source := cutoff_Rplus_source 4 (by norm_num) (parameter.value/2) right (Paid.interiorBase coordinate)
    rw [interior_source_supported] at source
    rw [source]
  have supportRead := Cut.cutoff_read 4 field
  rw [supported] at supportRead
  have parity := Lp.coeFn_compMeasurePreserving field negMeasurePreserving
  change (reflectL2 field : ℝ→ℂ)=ᵐ[volume] (field : ℝ→ℂ) ∘ (fun x=>-x) at parity
  rw [even] at parity
  have negative := negMeasurePreserving.quasiMeasurePreserving.ae (inverse_interior_positive coordinate parameter)
  apply Lp.ext
  filter_upwards [inverse_interior_positive coordinate parameter,negative,parity,supportRead,
    Lp.coeFn_smul (-((4:ℂ)^(coordinate.value-parameter.value))) (Paid.interiorBase parameter),
    Paid.interior_base_read parameter,negMeasurePreserving.quasiMeasurePreserving.ae_eq (Paid.interior_base_read parameter),volume.ae_ne (0:ℝ),volume.ae_ne (4:ℝ),volume.ae_ne (-4:ℝ)]
    with x direct reverse reflected support scalar basis negativeBasis nonzero notFour notNegativeFour
  change field x=(-(4:ℂ)^(coordinate.value-parameter.value) • Paid.interiorBase parameter : BurnolL2) x
  rw [scalar]
  change field x=(-(4:ℂ)^(coordinate.value-parameter.value))*Paid.interiorBase parameter x
  by_cases inside : |x| < (4:ℝ)
  · rcases lt_or_gt_of_ne nonzero with neg | pos
    · have actual : field x=field (-x) := reflected
      rw [actual,reverse (by linarith) (by simpa only [abs_of_neg neg] using inside)]
      simp only [Function.comp_def] at negativeBasis
      rw [negativeBasis,basis,abs_neg]
    · exact direct pos (by simpa only [abs_of_pos pos] using inside)
  · have outside : x∉symmetricInterval 4 := by
      intro bound
      have same : |x|=4 := le_antisymm (abs_le.mpr bound) (le_of_not_gt inside)
      rcases eq_or_eq_neg_of_abs_eq same with equal | equal
      · exact notFour equal
      · exact notNegativeFour equal
    rw [support,indicator_of_notMem outside,basis,if_neg inside,mul_zero]

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
