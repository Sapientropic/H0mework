import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineActualRadial
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationConicCutoffs
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationUniformEnergyFeed
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalTailScale

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLocalizedTail
open PreparationVacuumEngineHomogeneity PreparationVacuumCanonicalMoyal PreparationVacuumEngineSmooth
open PreparationVacuumMoyalSymmetry PreparationVacuumClockSymbol PreparationVacuumEngineSource
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev Symbol := PreparationVacuumCanonicalMoyal.Symbol
abbrev ArrayBound := ℕ → ℝ

def unitPhase (x : Phase) : Phase := radial (‖x.2‖⁻¹) x

theorem unitPhase_admitted (x : Phase) (hx : x∈poleDomain) (nonzero : x.2≠0) :
    unitPhase x∈poleDomain :=
  radial_admitted _ (inv_ne_zero (norm_ne_zero_iff.mpr nonzero)) x hx

theorem unitPhase_norm (x : Phase) (nonzero : x.2≠0) : ‖(unitPhase x).2‖=1 := by
  have positive : 0<‖x.2‖:=norm_pos_iff.mpr nonzero
  change ‖‖x.2‖⁻¹ • x.2‖=1
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr positive),inv_mul_cancel₀ positive.ne']

theorem energy_jet_unitrestriction (k m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈poleDomain) (nonzero : x.2≠0) :
    jet m (sourceEngineEnergy k) w x=
      ‖x.2‖^((2 : ℤ)-k-(momentumCount (List.ofFn w) : ℤ))*
        jet m (sourceEngineEnergy k) w (unitPhase x) := by
  have normal:=unitPhase_admitted x hx nonzero
  have np : ‖x.2‖≠0:=norm_ne_zero_iff.mpr nonzero
  have law:=jet_radial (2-(k : ℤ)) m w (sourceEngineEnergy k)
    (fun y hy=>(sourceEngineEnergy_smooth k y hy).contDiffAt (poleDomain_open.mem_nhds hy))
    (sourceEngineEnergy_radial k) ‖x.2‖ np (unitPhase x) normal
  have back : radial ‖x.2‖ (unitPhase x)=x := by
    simp [unitPhase,radial,smul_smul,mul_inv_cancel₀ np]
  rw [back] at law
  exact law

theorem energy_jet_radial_bound (k m : ℕ) (w : Word m) (x : Phase)
    (hx : x∈poleDomain) (outside : 1≤‖x.2‖) (B : ArrayBound)
    (bound : |jet m (sourceEngineEnergy k) w (unitPhase x)|≤B m) :
    |jet m (sourceEngineEnergy k) w x|≤B m*‖x.2‖^((2 : ℤ)-k) := by
  have positive : 0<‖x.2‖:=lt_of_lt_of_le (by norm_num) outside
  have nonzero : x.2≠0:=norm_ne_zero_iff.mp positive.ne'
  rw [energy_jet_unitrestriction k m w x hx nonzero,abs_mul,
    abs_of_pos (zpow_pos positive _)]
  have decay : ‖x.2‖^((2 : ℤ)-k-(momentumCount (List.ofFn w) : ℤ))≤‖x.2‖^((2 : ℤ)-k) := by
    apply zpow_le_zpow_right₀ outside
    omega
  have bpositive : 0≤B m:=(abs_nonneg _).trans bound
  calc
    _≤‖x.2‖^((2 : ℤ)-k-(momentumCount (List.ofFn w) : ℤ))*B m :=
      mul_le_mul_of_nonneg_left bound (zpow_nonneg positive.le _)
    _≤‖x.2‖^((2 : ℤ)-k)*B m := mul_le_mul_of_nonneg_right decay bpositive
    _=_:=mul_comm _ _

end LowEnergy.PreparationVacuumLocalizedTail
