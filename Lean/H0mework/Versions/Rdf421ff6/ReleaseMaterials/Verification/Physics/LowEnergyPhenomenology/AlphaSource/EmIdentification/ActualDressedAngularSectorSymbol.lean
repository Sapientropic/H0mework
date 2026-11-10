import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularCoulombCoefficient
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMNewtonIntegrability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource ActualDressedFullCoulomb
open ActualDressedAngularSpherePrice ActualDressedOrderedStatic ActualDressedCorrectedElectronRead ActualDressedEMTensorClock ActualCompositeFieldCurrent
open ActualEMCarrierOwn MeasureTheory Filter Set
open scoped Topology Matrix SchwartzMap
attribute [local irreducible] sourceDirectionRadius directionLeadingRead

def sectorDirection (k : PhysicalMomentum) : PhysicalMomentum := (Real.sqrt (spatialSquare k))⁻¹ • k

def sectorIR (scale : ℝ) (k : PhysicalMomentum) : ℝ := Real.sqrt (scale*Real.sqrt (spatialSquare k))

def sectorActive (event : DressedEvent) (eta scale : ℝ) (k : PhysicalMomentum) : Prop :=
  0<scale ∧ 0<spatialSquare k ∧ eta≤‖directionLeadingRead event (sectorDirection k)‖ ∧
    sectorIR scale k<sourceDirectionRadius event eta

/-- The same full source polynomial read is retained on its own angular/radial chart, before Fourier integration. -/
def sectorSymbol (event : DressedEvent) (N : DirectionParameters[X]) (eta scale : ℝ) (k : PhysicalMomentum) : ℂ := by
  classical
  exact if sectorActive event eta scale k then
    (spatialSquare k : ℂ)⁻¹ *
      (-(directionScaledNumerator event N).eval₂ (MvPolynomial.eval (directionValues (sectorDirection k))) (sectorIR scale k : ℂ)/
        (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues (sectorDirection k))) (sectorIR scale k : ℂ))
  else 0

def sectorProbeSymbol (event : DressedEvent) (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (eta scale : ℝ) : PhysicalMomentum→ℂ := sectorSymbol event (directionZeroClockProbe event pd ps dL dR sL sR) eta scale

def sectorEMSymbol (event : DressedEvent) (eta scale : ℝ) (k : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  fun mu nu => sectorSymbol event (directionZeroClockEM event mu nu) eta scale k

theorem sector_direction_unit (k : PhysicalMomentum) (positive : 0<spatialSquare k) : spatialSquare (sectorDirection k)=1 := by
  have rp := (Real.sqrt_pos.mpr positive).ne'
  have square := Real.sq_sqrt positive.le
  calc
    _=(Real.sqrt (spatialSquare k))⁻¹^2*spatialSquare k := by
      simp only [sectorDirection,spatialSquare,Pi.smul_apply,smul_eq_mul]
      ring
    _=1 := by field_simp [rp];exact square.symm

private theorem sector_spatial_nonneg (k : PhysicalMomentum) : 0≤ spatialSquare k := by unfold spatialSquare; positivity

private theorem quotient_price (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ) (positive : 0<eta)
    (n : PhysicalMomentum) (chart : n∈sourceDirectionChart event eta) (eps : ℝ)
    (small : |eps|<sourceDirectionRadius event eta) :
    ‖-(directionScaledNumerator event N).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)/
      (directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)‖≤ sourceAngularReadPrice event N eta := by
  rw [norm_div,norm_neg]
  have lower := actual_direction_reduced_denominator_price event eta positive n chart eps small
  have radiusBound : sourceDirectionRadius event eta≤1 := by unfold sourceDirectionRadius;exact min_le_left _ _
  have bound := actual_direction_polynomial_price (directionScaledNumerator event N) n chart.1 (eps : ℂ)
    (by rw [Complex.norm_real,Real.norm_eq_abs];exact (small.trans_le radiusBound).le)
  have denominatorPositive : 0<‖(directionReducedDenominator event).eval₂ (MvPolynomial.eval (directionValues n)) (eps : ℂ)‖ := by linarith
  rw [div_le_iff₀ denominatorPositive]
  unfold sourceAngularReadPrice
  have mass := direction_polynomial_price_nonneg (directionScaledNumerator event N)
  have weighted := mul_le_mul_of_nonneg_left lower (div_nonneg (by positivity : 0≤2*directionPolynomialPrice (directionScaledNumerator event N)) positive.le)
  have cancel : (2*directionPolynomialPrice (directionScaledNumerator event N)/eta)*(eta/2)=
      directionPolynomialPrice (directionScaledNumerator event N) := by field_simp
  rw [cancel] at weighted
  exact bound.trans weighted

theorem actual_sector_symbol_price (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ) (positive : 0<eta)
    (scale : ℝ) (k : PhysicalMomentum) :
    ‖sectorSymbol event N eta scale k‖≤ sourceAngularReadPrice event N eta/spatialSquare k := by
  classical
  by_cases active : sectorActive event eta scale k
  · have chart : sectorDirection k∈sourceDirectionChart event eta := ⟨sector_direction_unit k active.2.1,active.2.2.1⟩
    have small : |sectorIR scale k|<sourceDirectionRadius event eta := by
      rw [abs_of_nonneg (show 0≤ sectorIR scale k from Real.sqrt_nonneg _)]
      exact active.2.2.2
    have paid := quotient_price event N eta positive _ chart _ small
    rw [sectorSymbol,if_pos active,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos active.2.1]
    exact (mul_le_mul_of_nonneg_left paid (inv_nonneg.mpr active.2.1.le)).trans_eq (by rw [div_eq_mul_inv,mul_comm])
  · rw [sectorSymbol,if_neg active,norm_zero]
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) (direction_polynomial_price_nonneg _)) positive.le) (sector_spatial_nonneg k)

private theorem direction_measurable : Measurable sectorDirection := by
  unfold sectorDirection spatialSquare
  fun_prop

private theorem sector_ir_measurable (scale : ℝ) : Measurable (sectorIR scale) := by
  unfold sectorIR spatialSquare
  fun_prop

private theorem source_polynomial_read_measurable (P : DirectionParameters[X]) (scale : ℝ) :
    Measurable (fun k : PhysicalMomentum => P.eval₂ (MvPolynomial.eval (directionValues (sectorDirection k))) (sectorIR scale k : ℂ)) := by
  simp only [Polynomial.eval₂_eq_sum,Polynomial.sum,MvPolynomial.eval_eq']
  unfold directionValues sectorDirection sectorIR spatialSquare
  fun_prop

theorem actual_sector_symbol_measurable (event : DressedEvent) (N : DirectionParameters[X]) (eta scale : ℝ) :
    Measurable (sectorSymbol event N eta scale) := by
  have squared : Measurable spatialSquare := by unfold spatialSquare;fun_prop
  have leading := (direction_leading_continuous event).measurable.comp direction_measurable
  have active : MeasurableSet {k : PhysicalMomentum | sectorActive event eta scale k} := by
    have fixed : MeasurableSet {k : PhysicalMomentum | 0<scale} := by
      by_cases positive : 0<scale <;> simp [positive]
    change MeasurableSet ({k : PhysicalMomentum | 0<scale} ∩
      ({k : PhysicalMomentum | 0<spatialSquare k} ∩
        ({k : PhysicalMomentum | eta≤‖directionLeadingRead event (sectorDirection k)‖} ∩
          {k : PhysicalMomentum | sectorIR scale k<sourceDirectionRadius event eta})))
    have spatial : MeasurableSet {k : PhysicalMomentum | 0<spatialSquare k} :=
      measurableSet_lt (measurable_const : Measurable (fun _ : PhysicalMomentum => (0:ℝ))) squared
    have bound : MeasurableSet {k : PhysicalMomentum | eta≤‖directionLeadingRead event (sectorDirection k)‖} :=
      measurableSet_le (measurable_const : Measurable (fun _ : PhysicalMomentum => eta)) leading.norm
    have cutoff : MeasurableSet {k : PhysicalMomentum | sectorIR scale k<sourceDirectionRadius event eta} :=
      measurableSet_lt (sector_ir_measurable scale) (measurable_const : Measurable (fun _ : PhysicalMomentum => sourceDirectionRadius event eta))
    exact fixed.inter (spatial.inter (bound.inter cutoff))
  unfold sectorSymbol
  exact Measurable.ite active
    ((Complex.measurable_ofReal.comp squared).inv.mul
      ((source_polynomial_read_measurable _ scale).neg.div (source_polynomial_read_measurable _ scale))) measurable_const

def sectorFourierPacket (event : DressedEvent) (N : DirectionParameters[X]) (eta scale : ℝ)
    (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceSpatialPhase frequency x*test frequency*sectorSymbol event N eta scale (sourceSpatialMomentum frequency)

theorem actual_sector_fourier_integrable (event : DressedEvent) (N : DirectionParameters[X]) (eta : ℝ) (positive : 0<eta)
    (scale : ℝ) (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    Integrable (fun frequency=>sourceSpatialPhase frequency x*test frequency*sectorSymbol event N eta scale (sourceSpatialMomentum frequency)) := by
  have phase : Measurable (fun frequency : PhysicalMomentum => sourceSpatialPhase frequency x) := by
    unfold sourceSpatialPhase sourceSpatialMomentum
    fun_prop
  have momentum : Measurable sourceSpatialMomentum := by unfold sourceSpatialMomentum;fun_prop
  apply (em_physical_coulomb_budget_integrable (sourceAngularReadPrice event N eta) test).mono'
    ((phase.mul test.continuous.measurable).mul ((actual_sector_symbol_measurable event N eta scale).comp momentum)).aestronglyMeasurable
  apply Eventually.of_forall
  intro frequency
  have normPhase : ‖sourceSpatialPhase frequency x‖=1 := by simp [sourceSpatialPhase,Complex.norm_exp]
  change ‖sourceSpatialPhase frequency x*test frequency*sectorSymbol event N eta scale (sourceSpatialMomentum frequency)‖≤_
  rw [norm_mul,norm_mul,normPhase,one_mul]
  exact (mul_le_mul_of_nonneg_left (actual_sector_symbol_price event N eta positive scale _) (norm_nonneg _)).trans_eq (by ring)

end LowEnergy.GaussComposite.ActualDressedAngularSectorFourier
