import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMGaugeCurvature
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherResponse

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMDressedGaugePole
open SaturationMonoid.PhysicsCore
open ActualEMGaugeCurvature ActualEMCauchyDynamic ActualDressedNoether ActualDressedFullCoulomb
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumFieldConstraintResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumCurrentNativeLaplaceBridge PreparationVacuumCausalPoleResponse
open PreparationVacuumGaugeSourceInjection PreparationVacuumNativePoleTensor
open PreparationPhysicalNativePhotonFluxReturn CanonicalGradedSpatialSource
open SourcePropagationNoetherTime ActualEMAction Filter MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] sourceWholePhotonGreen sourceWholePhotonFrequencyResidue
  originalJacobi sourceTemporalFirst sourceTemporalSecond dressedNoetherJet

private theorem weight_continuous : Continuous (fun x : ℂ×ℝ=>laplaceWeight x.1 x.2) := by
  unfold laplaceWeight
  fun_prop

/-- The actual unit-minus-background Noether observer generates spectral continuity on the true finite source window. -/
theorem dressed_voltage_spectral_continuous (event : DressedEvent) (k : PhysicalMomentum) (T : ℝ) :
    Continuous (fun z : ℂ=>dressedVoltageForcing event k z T) := by
  have quadrature (imaginary : Bool) : Continuous (fun z : ℂ=>
      dressedNoetherForcing event k (voltageNativeTimeJet (physicalSpatial k) imaginary) z T) := by
    apply continuous_pi
    intro i
    have current:= (dressed_noether_jet_continuous event k
      (voltageNativeTimeJet (physicalSpatial k) imaginary)
      (voltage_timejet_continuous (physicalSpatial k) imaginary) i).1
    have joint:=weight_continuous.mul (current.comp continuous_snd)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' joint 0 T
  exact (quadrature false).add ((quadrature true).const_smul Complex.I)

private theorem window_continuous (spatial : Fin 3→ℂ) (T : ℝ) :
    Continuous (fun z : ℂ=>voltageWindowForcing spatial z T) := by
  have mass : Continuous (fun z : ℂ=>voltageWindowMass z T) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' weight_continuous 0 T
  have moment : Continuous (fun z : ℂ=>voltageWindowMoment z T) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (weight_continuous.mul (Complex.continuous_ofReal.comp continuous_snd)) 0 T
  have weight (t : ℝ) : Continuous (fun z : ℂ=>laplaceWeight z t) :=
    weight_continuous.comp (continuous_id.prodMk continuous_const)
  unfold voltageWindowForcing voltageWindowBulk voltageBoundaryTrace voltageTimeValue
  fun_prop

/-- The same momentum transfer enters the original quantum vertex and the full native Green. -/
def dressedGaugeMomentum (e omega : ℝ) (n : PhysicalMomentum) : Fin 4→ℂ :=
  fullMomentum (physicalSpatial ((e^2:ℝ) • n)) (-Complex.I*(omega:ℂ))

def dressedGaugeCurrent (event : DressedEvent) (e omega : ℝ) (n : PhysicalMomentum) (T : ℝ) : Fin 289→ℂ :=
  dressedVoltageForcing event ((e^2:ℝ) • n) (-Complex.I*(omega:ℂ)) T

/-- The original maintained finite Cauchy event retains both boundary traces and its actual creation-connected quantum response. -/
def dressedGaugeForcing (event : DressedEvent) (e omega : ℝ) (n : PhysicalMomentum) (T : ℝ) : Fin 289→ℂ :=
  voltageWindowForcing (physicalSpatial ((e^2:ℝ) • n)) (-Complex.I*(omega:ℂ)) T+
    dressedGaugeCurrent event e omega n T

def dressedGaugeField (event : DressedEvent) (e omega : ℝ) (n : PhysicalMomentum) (T : ℝ) : Fin 289→ℂ :=
  sourceWholePhotonGreen e (omega/e^2) n *ᵥ dressedGaugeForcing event e omega n T

def dressedGaugePole (event : DressedEvent) (e s : ℝ) (n : PhysicalMomentum) (T : ℝ) : Fin 289→ℂ :=
  sourceWholePhotonFrequencyResidue e s n *ᵥ dressedGaugeCurrent event e (sourceFrequency e s) n T

theorem dressed_gauge_clock (e s : ℝ) (n : PhysicalMomentum) :
    dressedGaugeMomentum e (sourceFrequency e s) n=frequencyRay e s n := by
  exact voltage_frequency_ray e s n

/-- The whole mixed Green and the original sourceField are the same operator on this actual created-state forcing. -/
theorem dressed_gauge_field_original (event : DressedEvent) (e : scaleDomain) (s : slopeDomain)
    (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (regular : IsUnit (normalizedEffective e s n (unit_direction_bound n unit)).det) (T : ℝ) :
    dressedGaugeField event e.val (sourceFrequency e.val s.val) n T=
      PreparationVacuumOriginalGreenFeedback.sourceField
        (dynamicPoint e s n (unit_direction_bound n unit) regular)
        (dressedGaugeForcing event e.val (sourceFrequency e.val s.val) n T) := by
  have ratio : sourceFrequency e.val s.val/e.val^2=s.val := by
    unfold sourceFrequency
    field_simp [e.property.1.ne']
  have original : sourceWholePhotonGreen e.val s.val n=
      sourceGreen (dynamicPoint e s n (unit_direction_bound n unit) regular) := by
    ext i j
    rw [sourceWholePhotonGreen,nativeResponse_original e s n (unit_direction_bound n unit) regular]
    simp only [PreparationVacuumOriginalGreenFeedback.sourceField,Matrix.mulVec_single_one,Matrix.col_apply]
  rw [dressedGaugeField,ratio,original]
  rfl

private theorem forcing_continuous (event : DressedEvent) (e : ℝ) (n : PhysicalMomentum) (T : ℝ) :
    Continuous (fun w : ℝ=>dressedGaugeForcing event e w n T) := by
  have clock : Continuous (fun w : ℝ=>-Complex.I*(w:ℂ)) := by fun_prop
  exact ((window_continuous _ T).comp clock).add
    ((dressed_voltage_spectral_continuous event _ T).comp clock)

/-- At a source-generated pole, the complete classical window has zero pole contraction because it is the original Jacobi action on the finite field. No boundary datum is dropped. -/
theorem dressed_gauge_classical_pole (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n *ᵥ
        voltageWindowForcing (physicalSpatial ((e.val^2:ℝ) • n))
          (-Complex.I*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) T=0 := by
  filter_upwards [sourceWholePhotonResidue_homogeneous branch n unit] with e homogeneous
  have action:=voltage_window_action (physicalSpatial ((e.val^2:ℝ) • n))
    (-Complex.I*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ)) T
  rw [em_jacobi_source] at action
  change originalJacobi (dressedGaugeMomentum e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n)*ᵥ
    voltageWindowField _ _ T=voltageWindowForcing _ _ T at action
  rw [←action,dressed_gauge_clock,Matrix.mulVec_mulVec,
    sourceWholePhotonFrequencyResidue,Matrix.smul_mul,homogeneous.1,smul_zero,Matrix.zero_mulVec]

/-- The genuine physical-frequency pole of the same actual created-state event is generated from its complete Noether current. -/
theorem dressed_gauge_frequency_pole (event : DressedEvent) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (T : ℝ) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun w : ℝ=>((w-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
        dressedGaugeField event e.val w n T)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T)) := by
  filter_upwards [sourceWholePhotonGreen_frequencyResidue branch n unit,
    dressed_gauge_classical_pole branch n unit T] with e pole classical
  have current : Tendsto (fun w : ℝ=>dressedGaugeForcing event e.val w n T)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (dressedGaugeForcing event e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n T)) :=
    ((forcing_continuous event e.val n T).tendsto _).mono_left nhdsWithin_le_nhds
  have continuous : Continuous (fun x : Matrix (Fin 289) (Fin 289) ℂ×(Fin 289→ℂ)=>x.1*ᵥx.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have result:=(continuous.tendsto _).comp (pole.prodMk_nhds current)
  change Tendsto (fun w=>(((w-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ) •
    sourceWholePhotonGreen e.val (w/e.val^2) n)*ᵥdressedGaugeForcing event e.val w n T) _
    (𝓝 (sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
      dressedGaugeForcing event e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n T)) at result
  simpa only [dressedGaugeForcing,Matrix.mulVec_add,classical,zero_add,Matrix.smul_mulVec,
    dressedGaugeField,dressedGaugePole,smul_add] using result

/-- All72 original gauge curvature channels consume the same moving-frequency residue and the actual unit-minus-background source. -/
theorem dressed_gauge_curvature_pole (event : DressedEvent) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (T : ℝ) (pair : Fin 6) (a : Fin 12) :
    ∀ᶠ e in scaleApproach,Tendsto
      (fun w : ℝ=>((w-sourceFrequency e.val (sourceSheet branch n unit e.val):ℝ):ℂ)*
        fullGaugeCurvature (dressedGaugeMomentum e.val w n) (dressedGaugeField event e.val w n T) pair a)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (fullGaugeCurvature (frequencyRay e.val (sourceSheet branch n unit e.val) n)
        (dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T) pair a)) := by
  filter_upwards [dressed_gauge_frequency_pole event branch n unit T] with e pole
  have momentum : Continuous (fun w : ℝ=>dressedGaugeMomentum e.val w n) := by
    apply continuous_pi
    intro mu
    refine Fin.cases ?_ (fun _=>continuous_const) mu
    change Continuous (fun w : ℝ=>-Complex.I*(w:ℂ))
    fun_prop
  have mp : Tendsto (fun w : ℝ=>dressedGaugeMomentum e.val w n)
      (𝓝[≠] (sourceFrequency e.val (sourceSheet branch n unit e.val)))
      (𝓝 (dressedGaugeMomentum e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n)) :=
    (momentum.tendsto _).mono_left nhdsWithin_le_nhds
  have result:=((full_gauge_curvature_continuous pair a).tendsto _).comp (mp.prodMk_nhds pole)
  simpa only [Function.comp_def,fullGaugeCurvature,map_smul,RingHom.id_apply,smul_eq_mul,
    dressed_gauge_clock] using result

/-- The same full source action fixes the propagated current's physical-frequency flux. -/
theorem dressed_gauge_frequency_flux (event : DressedEvent) (branch : Fin 2)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (T : ℝ) :
    ∀ᶠ e in scaleApproach,
      sourceWholePhotonFrequencyResidue e.val (sourceSheet branch n unit e.val) n*ᵥ
        (emActionFrequencyJet e.val (sourceFrequency e.val (sourceSheet branch n unit e.val)) n*ᵥ
          dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T)=
        dressedGaugePole event e.val (sourceSheet branch n unit e.val) n T := by
  filter_upwards [sourceWholePhotonResidue_frequencyFlux branch n unit] with e flux
  rw [dressedGaugePole,em_action_frequency_jet]
  simp only [Matrix.mulVec_mulVec,←Matrix.mul_assoc]
  rw [flux]

end LowEnergy.GaussComposite.ActualEMDressedGaugePole
