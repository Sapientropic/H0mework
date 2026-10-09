import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCauchyInitialElectric

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCauchyDynamic
open SaturationMonoid.PhysicsCore
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalFeedback PreparationVacuumMixedFieldReturn
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalCurvatureSheetLimit PreparationVacuumSoftPoleSelection CanonicalGradedSpatialSource Filter
open scoped Matrix BigOperators Topology

/-- Antisymmetric spatial electric read; its vanishing is the longitudinal condition and involves no angular average. -/
def voltageTransverseRead (n : PhysicalMomentum) (E : Fin 3→ℂ) (i j : Fin 3) : ℂ :=
  (n i:ℂ)*E j-(n j:ℂ)*E i

/-- The actual source pole's computed second electric jet is longitudinal; its full transverse remainder remains. -/
theorem voltage_transverse_exact (branch : Fin 2) (e s : ℝ) (n : PhysicalMomentum)
    (nonzero : e≠0) (i j : Fin 3) :
    voltageTransverseRead n (voltageYElectric (frequencyRay e s n)
      (sourceNativeFrequencyPolarization branch e s n)) i j=
      (e:ℂ)^2*voltageTransverseRead n (voltageYElectric (physicalFrequencyMomentum s n)
        (sourcePoleFrameResidual branch e s n)) i j := by
  simp only [voltageTransverseRead,voltage_y_frequency_electric branch e s n nonzero]
  ring

/-- The two-sided initial electric residue retains its complete field while its transverse leading coefficient is generated zero. -/
theorem voltage_initial_transverse_ir (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (i j : Fin 3) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      voltageTransverseRead n (voltageYElectric (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (voltageInitialPole e.val (sourceSheet branch n unit e.val) n)) i j/(e.val:ℂ)^6)
      scaleApproach (𝓝 0) := by
  have first:=(tendsto_const_nhds (x:=(n i:ℂ))).mul (voltage_initial_electric_ir branch n unit j)
  have second:=(tendsto_const_nhds (x:=(n j:ℂ))).mul (voltage_initial_electric_ir branch n unit i)
  have result:=first.sub second
  have zero : (n i:ℂ)*(if branch=0 then (-3000/49379:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)*
      (sourceSpeed branch:ℂ)*(n j:ℂ)*(softCoefficient branch:ℂ) else 0)-
      (n j:ℂ)*(if branch=0 then (-3000/49379:ℂ)*(Stage9C.Material.SpinPair.lapse:ℂ)*
      (sourceSpeed branch:ℂ)*(n i:ℂ)*(softCoefficient branch:ℂ) else 0)=0 := by
    split_ifs <;> ring
  rw [zero] at result
  apply result.congr'
  filter_upwards [] with e
  unfold voltageTransverseRead
  ring

/-- The magnetic read is the original antisymmetric Y spatial curvature. -/
def voltageYMagneticPair (p : Fin 4→ℂ) (f : Fin 289→ℂ) (i j : Fin 3) : ℂ :=
  p i.succ*f (gaugeSlot j.succ 11)-p j.succ*f (gaugeSlot i.succ 11)

theorem voltage_magnetic_ir (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (i j : Fin 3) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      voltageYMagneticPair (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (sourceNativeFrequencyPolarization branch e.val (sourceSheet branch n unit e.val) n) i j/(e.val:ℂ)^4)
      scaleApproach (𝓝 0) := by
  have ni:=tendsto_pi_nhds.mp (sourceCurvatureDirection_tendsto branch n unit) i.succ
  have nj:=tendsto_pi_nhds.mp (sourceCurvatureDirection_tendsto branch n unit) j.succ
  have result:=(ni.mul (voltage_pole_residual_divided branch n unit (gaugeSlot j.succ 11))).sub
    (nj.mul (voltage_pole_residual_divided branch n unit (gaugeSlot i.succ 11)))
  simp only [mul_zero,sub_zero] at result
  apply result.congr'
  filter_upwards [] with e
  rw [voltageYMagneticPair,voltage_y_frequency_magnetic branch e.val _ n e.property.1.ne']
  have ne : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [ne]

/-- The actual initial co-source keeps both pole factors when its magnetic leading coefficient is evaluated. -/
theorem voltage_initial_magnetic_ir (branch : Fin 2) (n : PhysicalMomentum)
    (unit : spatialSquare n=1) (i j : Fin 3) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet branch n unit e.val:ℂ))*
      voltageYMagneticPair (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (voltageInitialPole e.val (sourceSheet branch n unit e.val) n) i j/(e.val:ℂ)^6)
      scaleApproach (𝓝 0) := by
  have result:=(voltage_initial_emitter_ir branch n unit).mul (voltage_magnetic_ir branch n unit i j)
  simp only [mul_zero] at result
  apply result.congr'
  filter_upwards [voltage_initial_pole_factor branch n unit] with e factor
  rw [factor]
  simp only [voltageYMagneticPair,Pi.smul_apply,smul_eq_mul]
  have ne : (e.val:ℂ)≠0:=Complex.ofReal_ne_zero.mpr e.property.1.ne'
  field_simp [ne]

end LowEnergy.GaussComposite.ActualEMCauchyDynamic
