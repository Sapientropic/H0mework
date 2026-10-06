import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationWholeLocalFinite

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumWholeTail
open PreparationVacuumLocalizedTail PreparationVacuumOriginalRadii PreparationVacuumCanonicalMoyal
open PreparationVacuumConicComposition PreparationVacuumConicBudget PreparationVacuumClockSymbol
open PreparationVacuumEngineSmooth PreparationVacuumEngineBudget PreparationVacuumMoyalBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

theorem energyTailFor_finite_germ_extended (B : ℕ → Fin 5 → ArrayBound) (x : Phase) (N : ℕ)
    (more : nearbyHead x≤N) : energyTailFor B=ᶠ[𝓝 x]
      (fun y=>∑ j∈Finset.range N,energyTailTerm B (j+2) y) := by
  filter_upwards [same_radius_locally_finite B x] with y hy
  exact tsum_eq_sum (s:=Finset.range N) (fun j hj=>hy j (more.trans (by simpa only [Finset.mem_range,not_lt] using hj)))

theorem energyTailFor_smooth (B : ℕ → Fin 5 → ArrayBound) (x : Phase) (hx : x∈poleDomain) :
    ContDiffAt ℝ ∞ (energyTailFor B) x := by
  have finite : ContDiffAt ℝ ∞
      (fun y=>∑ j∈Finset.range (nearbyHead x),energyTailTerm B (j+2) y) x := by
    apply ContDiffAt.sum
    intro j _
    exact (localizedEnergy_smooth (sourceRadiusFor B (j+2)) (j+2) x hx).contDiffAt (poleDomain_open.mem_nhds hx)
  exact finite.congr_of_eventuallyEq (energyTailFor_finite_germ B x)

theorem energyTailFor_jet_readback (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) (w : Word m)
    (x : Phase) (hx : x∈poleDomain) (N : ℕ) (more : nearbyHead x≤N) :
    jet m (energyTailFor B) w x=∑ j∈Finset.range N,jet m (energyTailTerm B (j+2)) w x := by
  have germ:=energyTailFor_finite_germ_extended B x N more
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  change iteratedFDeriv ℝ m (energyTailFor B) x (slotDirection∘w)=_
  rw [read]
  exact jet_sum poleDomain_open (Finset.range N) (fun j=>energyTailTerm B (j+2))
    (fun j _=>localizedEnergy_smooth (sourceRadiusFor B (j+2)) (j+2)) m w x hx

theorem energyTailFor_low_germ (B : ℕ → Fin 5 → ArrayBound) (x : Phase) (low : ‖x.2‖<1) :
    energyTailFor B=ᶠ[𝓝 x] (fun _=>0) := by
  have near : ∀ᶠ y : Phase in 𝓝 x,‖y.2‖<1:=
    continuous_snd.norm.continuousAt.eventually (gt_mem_nhds low)
  filter_upwards [near] with y hy
  have vanish : ∀ j : ℕ,energyTailTerm B (j+2) y=0 := by
    intro j
    apply energyTailTerm_low
    have lower:=originalRadius_at_least_linear (originalCutoff B) (j+2)
    change ‖y.2‖<originalRadius (originalCutoff B) (j+2)
    push_cast at lower
    linarith
  unfold energyTailFor
  simp_rw [vanish]
  simp

end LowEnergy.PreparationVacuumWholeTail
