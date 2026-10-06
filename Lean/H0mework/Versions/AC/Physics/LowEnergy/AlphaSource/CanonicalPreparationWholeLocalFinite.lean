import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationLocalizedHeadTail

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWholeTail
open PreparationVacuumLocalizedTail PreparationVacuumOriginalRadii PreparationVacuumCanonicalMoyal
open PreparationVacuumConicComposition PreparationVacuumConicBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol
abbrev ArrayBound := ℕ → ℝ

def energyTailFor (B : ℕ → Fin 5 → ArrayBound) : Symbol :=
  fun x=>∑' j : ℕ,energyTailTerm B (j+2) x

theorem energyTailTerm_low (B : ℕ → Fin 5 → ArrayBound) (k : ℕ) (x : Phase)
    (low : ‖x.2‖<sourceRadiusFor B k) : energyTailTerm B k x=0 := by
  have positive : 0<sourceRadiusFor B k:=originalRadius_positive _ _
  have ratio : rho x/sourceRadiusFor B k≤1 := (div_le_one positive).mpr low.le
  simp only [energyTailTerm,localizedEnergy,sourceRadialChi,Function.comp_def,sourceChi,if_pos ratio,mul_zero]

def nearbyHead (x : Phase) : ℕ := ⌈‖x.2‖⌉₊+2

theorem nearbyHead_positive (x : Phase) : 0<nearbyHead x := by unfold nearbyHead;omega

theorem nearbyHead_above (x : Phase) : ‖x.2‖<(nearbyHead x : ℝ) := by
  have bound:=Nat.le_ceil ‖x.2‖
  unfold nearbyHead
  push_cast
  linarith

theorem same_radius_locally_finite (B : ℕ → Fin 5 → ArrayBound) (x : Phase) :
    ∀ᶠ y : Phase in 𝓝 x,∀ j : ℕ,nearbyHead x≤j → energyTailTerm B (j+2) y=0 := by
  have near : ∀ᶠ y : Phase in 𝓝 x,‖y.2‖<(nearbyHead x : ℝ) :=
    continuous_snd.norm.continuousAt.eventually (gt_mem_nhds (nearbyHead_above x))
  filter_upwards [near] with y hy
  intro j later
  apply energyTailTerm_low B (j+2) y
  have bound:=originalRadius_at_least_linear (originalCutoff B) (j+2)
  have index : (nearbyHead x : ℝ)≤(j : ℝ):=by exact_mod_cast later
  push_cast at bound
  change ‖y.2‖<originalRadius (originalCutoff B) (j+2)
  linarith

theorem energyTailFor_finite_germ (B : ℕ → Fin 5 → ArrayBound) (x : Phase) :
    energyTailFor B=ᶠ[𝓝 x]
      (fun y=>∑ j∈Finset.range (nearbyHead x),energyTailTerm B (j+2) y) := by
  filter_upwards [same_radius_locally_finite B x] with y hy
  exact tsum_eq_sum (s:=Finset.range (nearbyHead x)) (fun j hj=>hy j (by simpa only [Finset.mem_range,not_lt] using hj))

end LowEnergy.PreparationVacuumWholeTail
