import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatQuarticOrder
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.HeatPacket
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.FiveRows

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeQuarticStartKernel
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open NativeUnheatedTreeQuarticStart NativeUnheatedTreeHeatCoefficient
open NativeUnheatedTreeHeatTopology (Tree)
open NativeUnheatedTreeHeatGrowth
open NativeUnheatedTreeRieszKernel (Wave)
open NativeUnheatedStressPairEvolution NativeUnheatedTriadKernel NativeUnheatedTriadChannels
noncomputable section

theorem triad_bound (nu : Viscosity) (k : Wave) (index : Wave × Wave) (i j response : Coordinate) :
    ‖NativeUnheatedTriadChannelWrite.normalizer nu index.2 (k-index.1-index.2) index.1 i j response‖ ≤
      rootCoefficient nu triad k (triadIndices k index) := by
  have pair := original_pair nu k (k-index.1)
  have original : ‖(((decay nu (k-index.1) index.1)⁻¹ : ℝ) : ℂ)‖ ≤
      rootCoefficient nu (.fork .leaf .leaf) k (k-index.1,(PUnit.unit,PUnit.unit)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (NativeUnheatedTreeLocalHeat.decay_nonnegative nu _ _))]
    simpa only [sub_sub_cancel] using pair
  have lower : decay nu index.2 (k-index.1-index.2) ≤ triadDecay nu index.2 (k-index.1-index.2) index.1 := by
    unfold decay triadDecay
    nlinarith only [mul_nonneg nu.coeff_pos.le (multiplier_nonnegative index.1)]
  have generated := original_step nu (.fork .leaf .leaf) (.inl PUnit.unit) k
    (k-index.1,(PUnit.unit,PUnit.unit)) index.2 (((decay nu (k-index.1) index.1)⁻¹ : ℝ) : ℂ)
    (triadDecay nu index.2 (k-index.1-index.2) index.1) i j response original lower
  change ‖(triadDecay nu index.2 (k-index.1-index.2) index.1)⁻¹ •
    ((((decay nu (k-index.1) index.1)⁻¹ : ℝ) : ℂ)*pressure (k-index.1) i j response)‖ ≤
      rootCoefficient nu triad k (triadIndices k index) at generated
  apply le_trans _ generated
  apply le_of_eq
  congr 1
  unfold NativeUnheatedTriadChannelWrite.normalizer
  rw [show index.2+(k-index.1-index.2) = k-index.1 by abel]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

def parentSlots (k : Wave) (index : Wave × Wave) (i j outside : Coordinate) : Fin 3 → NativeUnheatedTreeTime.Slot :=
  ![(index.2,i),(k-index.1-index.2,j),(index.1,outside)]

theorem split_rate (nu : Viscosity) (slot : Fin 3) (k : Wave) (index : NativeUnheatedQuarticAllSlots.Index)
    (i j outside l m : Coordinate) :
    NativeUnheatedTreeTime.sumRate nu (NativeUnheatedTreeLeaf.slots (parentSlots k index.1 i j outside) slot l m index.2) =
      NativeUnheatedQuarticPrimitiveKernel.rate nu slot k i j outside l m index := by
  change nu.coeff*(∑ number : Fin 4, integerWaveViscousMultiplier
    (NativeUnheatedTreeLeaf.slots (parentSlots k index.1 i j outside) slot l m index.2 number).1) = _
  rw [Fin.sum_univ_four]
  fin_cases slot
  · rfl
  · rfl
  · change nu.coeff*(integerWaveViscousMultiplier index.2+integerWaveViscousMultiplier (index.1.1-index.2)+
      integerWaveViscousMultiplier index.1.2+integerWaveViscousMultiplier (k-index.1.1-index.1.2)) =
      nu.coeff*(integerWaveViscousMultiplier index.1.2+integerWaveViscousMultiplier (k-index.1.1-index.1.2)+
        integerWaveViscousMultiplier index.2+integerWaveViscousMultiplier (index.1.1-index.2))
    ring

theorem parent_wave (k : Wave) (index : Wave × Wave) (i j outside : Coordinate) (slot : Fin 3) :
    wave triad k (triadIndices k index) (triadOrder slot) = (parentSlots k index i j outside slot).1 := by
  rw [triad_wave]
  fin_cases slot <;> rfl

theorem base_recognition (nu : Viscosity) (slot : Fin 3) (k : Wave) (index : NativeUnheatedQuarticAllSlots.Index)
    (i j response outside l m : Coordinate) :
    NativeUnheatedQuinticFiveRows.base nu slot k i j response outside l m index =
      (NativeUnheatedQuarticPrimitiveKernel.rate nu slot k i j outside l m index)⁻¹ •
        (NativeUnheatedTriadChannelWrite.normalizer nu index.1.2 (k-index.1.1-index.1.2) index.1.1 i j response *
          pressure (parentSlots k index.1 i j outside slot).1 l m (parentSlots k index.1 i j outside slot).2) := by
  fin_cases slot <;> rfl

theorem coefficient_bound (nu : Viscosity) (slot : Fin 3) (k : Wave) (index : NativeUnheatedQuarticAllSlots.Index)
    (i j response outside l m : Coordinate) :
    ‖NativeUnheatedQuinticFiveRows.base nu slot k i j response outside l m index‖ ≤
      rootCoefficient nu (tree slot) k (indices slot k index) := by
  have lower := NativeUnheatedTreeLocalHeat.split_rate_lower nu (parentSlots k index.1 i j outside) slot l m index.2
  rw [split_rate, ← parent_wave k index.1 i j outside slot] at lower
  have generated := original_step nu triad (triadOrder slot) k (triadIndices k index.1) index.2
    (NativeUnheatedTriadChannelWrite.normalizer nu index.1.2 (k-index.1.1-index.1.2) index.1.1 i j response)
    (NativeUnheatedQuarticPrimitiveKernel.rate nu slot k i j outside l m index) l m
    (parentSlots k index.1 i j outside slot).2 (triad_bound nu k index.1 i j response) lower
  rw [parent_wave] at generated
  rw [base_recognition]
  exact generated

def alignment (nu : Viscosity) (slot : Fin 3) (i j response outside l m : Coordinate) :
    NativeUnheatedTreeHeatPacket.Alignment nu
      (fun k index => NativeUnheatedQuarticAllSlots.slots slot k i j outside l m index)
      (fun k index => NativeUnheatedQuinticFiveRows.base nu slot k i j response outside l m index) where
  tree := tree slot
  count := count slot
  order := order slot
  indices := indices slot
  wave_at k index number := wave_at slot k index i j outside l m number
  coefficient_bound k index := coefficient_bound nu slot k index i j response outside l m

theorem primitive_original {nu : Viscosity}
    (seed : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent nu)
    (slot : Fin 3) (k : Wave) (index : NativeUnheatedQuarticAllSlots.Index)
    (i j response outside l m : Coordinate) (time : ℝ) :
    NativeUnheatedQuarticAllSlots.primitiveTerm seed slot k i j response outside l m index time =
      NativeUnheatedQuinticFiveRows.base nu slot k i j response outside l m index*
        NativeUnheatedTreeTime.product seed (NativeUnheatedQuarticAllSlots.slots slot k i j outside l m index) time := by
  simp only [NativeUnheatedTreeTime.product, Fin.prod_univ_four, NativeUnheatedQuarticAllSlots.primitiveTerm,
    NativeUnheatedQuarticNormalForm.primitive, NativeUnheatedQuinticFiveRows.base, NativeUnheatedQuarticTime.product]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeQuarticStartKernel
