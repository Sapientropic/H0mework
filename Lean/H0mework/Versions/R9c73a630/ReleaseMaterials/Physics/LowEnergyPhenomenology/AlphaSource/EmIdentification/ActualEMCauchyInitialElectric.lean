import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyElectricIR
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchySourceIR

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback PreparationPhysicalNativePhotonFluxReturn
open PreparationVacuumSoftPoleSelection CanonicalGradedSpatialSource Filter
open scoped Matrix Topology

private theorem electric_smul (p : Fin 4→ℂ) (f : Fin 289→ℂ) (a : ℂ) (i : Fin 3) :
    voltageYElectric p (a • f) i=a*voltageYElectric p f i := by
  simp only [voltageYElectric,Pi.smul_apply,smul_eq_mul]
  ring

/-- Both ends of the actual Cauchy initial-data pole are now evaluated, on both generated sheets and with the full residual controlled. -/
theorem voltage_initial_electric_ir (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (i : Fin 3) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      voltageYElectric (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (voltageInitialPole e.val (sourceSheet branch n unit e.val) n) i/(e.val:ℂ)^6)
      scaleApproach (𝓝 (if branch=0 then
        (-3000/49379:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)*(sourceSpeed branch:ℂ)*
          (n i:ℂ)*(softCoefficient branch:ℂ) else 0)) := by
  have result:=(voltage_initial_emitter_ir branch n unit).mul (voltage_y_electric_ir branch n unit i)
  have equal : (if branch=0 then (50/67:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ) else 0)*
      (if branch=0 then (-60/737:ℂ)*(sourceSpeed branch:ℂ)*(n i:ℂ)*(softCoefficient branch:ℂ) else 0)=
      if branch=0 then (-3000/49379:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)*(sourceSpeed branch:ℂ)*
        (n i:ℂ)*(softCoefficient branch:ℂ) else 0 := by
    split_ifs <;> ring
  rw [equal] at result
  apply result.congr'
  filter_upwards [voltage_initial_pole_factor branch n unit] with e factor
  rw [factor,electric_smul]
  have ne : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [ne]

/-- For every actual unit direction, the initial co-source contribution has a nonzero ordinary Y electric residue on the first generated sheet. -/
theorem voltage_initial_electric_visible (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∃i : Fin 3,
      voltageYElectric (frequencyRay e.val (sourceSheet 0 n unit e.val) n)
        (voltageInitialPole e.val (sourceSheet 0 n unit e.val) n) i≠0 := by
  have direction : ∃i : Fin 3,n i≠0 := by
    by_contra none
    have zero : ∀i : Fin 3,n i=0 := by simpa only [not_exists,not_not] using none
    have empty : spatialSquare n=0 := by simp [spatialSquare,zero]
    linarith
  obtain ⟨i,ni⟩:=direction
  have nonzero : (-3000/49379:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)*(sourceSpeed 0:ℂ)*
      (n i:ℂ)*(softCoefficient 0:ℂ)≠0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Stage9C.Material.SpinPair.lapse_pos.ne')
        · exact Complex.ofReal_ne_zero.mpr (sourceSpeed_positive 0).ne'
      · exact Complex.ofReal_ne_zero.mpr ni
    · exact Complex.ofReal_ne_zero.mpr (softCoefficient_nonzero 0)
  have limit:=voltage_initial_electric_ir 0 n unit i
  simp only [ite_true] at limit
  filter_upwards [limit.eventually_ne nonzero] with e visible
  refine ⟨i,?_⟩
  intro zero
  apply visible
  rw [zero,mul_zero,zero_div]

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
