import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMStaticCoefficient
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussActionTimeReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTensorClock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open GaussCoreHilbert GaussUnitaryHistory PreparationVacuumFieldConstraintResponse
open PreparationPhysicalActionUnits PreparationVacuumRawJointFeedback PreparationVacuumPhysicalModeContact
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedNoether ActualDressedCorrectedElectronRead
open PreparationVacuumPhysicalHalfAxis PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph ActualCompositeFieldCurrent
open LowEnergy.ActualDressedVisiblePole
open scoped Matrix BigOperators Topology InnerProductSpace
attribute [local irreducible] sourceDressedUnit sourceProfile dressedEulerObserver physicalTime actualC actualA

/-- The full principal packet is re-expressed in its original affine clock, preserving every negative power. -/
def clockPrincipalCoefficient (R : RatFunc ℂ) (a b : ℂ) (k : ℕ) : ℂ :=
  b^(poleOrder R a-k)*principalCoefficient R a k

def clockResidue (R : RatFunc ℂ) (a b : ℂ) : ℂ :=
  b*poleResidue R a

private theorem affine_principal_term (b c a z v : ℂ) (k m : ℕ) (nonzero : b≠0)
    (away : z ≠ c+b*a) (bounded : k ≤ m) :
    v*((z-c)/b-a)^k/((z-c)/b-a)^m=
      (b^(m-k)*v)*(z-(c+b*a))^k/(z-(c+b*a))^m := by
  have shifted : (z-c)/b-a=(z-(c+b*a))/b := by field_simp;ring
  rw [shifted, div_pow, div_pow]
  have different : z-(c+b*a)≠0 := sub_ne_zero.mpr away
  field_simp [nonzero, different]
  rw [← pow_sub_mul_pow b bounded]
  ring

/-- This is the exact complete meromorphic read, not an assumption that a pole is simple. -/
theorem source_affine_principal_return (R : RatFunc ℂ) (a b c z : ℂ) (nonzero : b≠0)
    (root : a ∈ visibleRoots R) (away : z≠c+b*a)
    (regular : (rootRemainder R a).eval ((z-c)/b)≠0) :
    R.num.eval ((z-c)/b)/R.denom.eval ((z-c)/b)=
      (∑k ∈ Finset.range (poleOrder R a), clockPrincipalCoefficient R a b k*
        (z-(c+b*a))^k/(z-(c+b*a))^poleOrder R a)+
        (analyticNumerator R a).eval ((z-c)/b)/(rootRemainder R a).eval ((z-c)/b) := by
  have inverseAway : (z-c)/b≠a := by
    intro same
    apply away
    have cross := (div_eq_iff nonzero).mp same
    linear_combination cross
  rw [complete_principal_part R a ((z-c)/b) inverseAway regular,
    principal_negative_powers R a ((z-c)/b) root]
  congr 1
  apply Finset.sum_congr rfl
  intro k inside
  exact affine_principal_term b c a z _ k _ nonzero away (Nat.le_of_lt (Finset.mem_range.mp inside))

theorem clock_residue_generated (R : RatFunc ℂ) (a b : ℂ) (root : a ∈ visibleRoots R) :
    clockPrincipalCoefficient R a b (poleOrder R a-1)=clockResidue R a b := by
  have positive := visible_pole_order_positive R a root
  have power : poleOrder R a-(poleOrder R a-1)=1 := by omega
  simp only [clockPrincipalCoefficient, clockResidue, poleResidue, power, pow_one]

/-- Original action-time sheet frequency and damping are different coordinates. -/
def physicalFrequencyPole (eps : ℝ) (a : ℂ) : ℂ := (eps^2 : ℂ)*a

def physicalLaplacePole (eps sigma : ℝ) (a : ℂ) : ℂ := (sigma : ℂ)-Complex.I*physicalFrequencyPole eps a

def frequencyTensorCoefficient (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (a : ℂ) (k : ℕ) : ℂ :=
  clockPrincipalCoefficient (emSheetFraction event eps sigma n mu nu) a (eps^2 : ℂ) k

def laplaceTensorCoefficient (event : DressedEvent) (eps sigma : ℝ) (n : PhysicalMomentum)
    (mu nu : Fin 4) (a : ℂ) (k : ℕ) : ℂ :=
  clockPrincipalCoefficient (emSheetFraction event eps sigma n mu nu) a (-Complex.I*(eps^2 : ℂ)) k

theorem actual_frequency_tensor_principal (event : DressedEvent) (eps sigma omega : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0) (positive : 0<sigma)
    (chart : ActualDressedCorrectedGreen.correctedDet event eps (omega/eps^2) sigma n≠0)
    (root : a ∈ visibleRoots (emSheetFraction event eps sigma n mu nu))
    (away : (omega : ℂ)≠physicalFrequencyPole eps a)
    (regular : (rootRemainder (emSheetFraction event eps sigma n mu nu) a).eval ((omega/eps^2 : ℝ) : ℂ)≠0) :
    correctedEMTensor event eps (omega/eps^2) sigma n mu nu=
      (∑k ∈ Finset.range (poleOrder (emSheetFraction event eps sigma n mu nu) a),
        frequencyTensorCoefficient event eps sigma n mu nu a k*
          ((omega : ℂ)-physicalFrequencyPole eps a)^k/
            ((omega : ℂ)-physicalFrequencyPole eps a)^poleOrder (emSheetFraction event eps sigma n mu nu) a)+
      (analyticNumerator (emSheetFraction event eps sigma n mu nu) a).eval ((omega/eps^2 : ℝ) : ℂ)/
        (rootRemainder (emSheetFraction event eps sigma n mu nu) a).eval ((omega/eps^2 : ℝ) : ℂ) := by
  rw [actual_corrected_em_tensor_canonical event eps sigma (omega/eps^2) n positive chart mu nu]
  simpa only [sub_zero, zero_add, Complex.ofReal_div, Complex.ofReal_pow, physicalFrequencyPole,
    frequencyTensorCoefficient] using source_affine_principal_return
    (emSheetFraction event eps sigma n mu nu) a (eps^2 : ℂ) 0 (omega : ℂ)
    (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr nonzero)) root
    (by simpa only [physicalFrequencyPole, zero_add, Complex.ofReal_pow] using away)
    (by simpa only [sub_zero, Complex.ofReal_div, Complex.ofReal_pow] using regular)

private theorem energy_projection_split {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E→L[ℂ]E) (x y : E) :
    inner ℂ x (T x)=inner ℂ y (T y)+
      (inner ℂ y (T (x-y))+inner ℂ (x-y) (T y)+inner ℂ (x-y) (T (x-y))) := by
  have same : y+(x-y)=x := by abel
  calc
    _=inner ℂ (y+(x-y)) (T (y+(x-y))) := by rw [same]
    _=_ := by rw [map_add,inner_add_left,inner_add_right,inner_add_right];ring

private theorem signed_energy_calibration {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E→L[ℂ]E) (x y px py : E) (h dx dy ux uy : ℂ)
    (created : h*dx=inner ℂ px (T px)+ux)
    (background : h*dy=inner ℂ py (T py)+uy) :
    h*(-dx+dy)= -inner ℂ x (T x)+inner ℂ y (T y)+
      (-ux+uy+(inner ℂ px (T (x-px))+inner ℂ (x-px) (T px)+inner ℂ (x-px) (T (x-px)))-
        (inner ℂ py (T (y-py))+inner ℂ (y-py) (T py)+inner ℂ (y-py) (T (y-py)))) := by
  have splitx := energy_projection_split T x px
  have splity := energy_projection_split T y py
  linear_combination -created+background+splitx-splity

def projectionEnergyRemainder (event : DressedEvent) (p : PhysicalMomentum) (x : H) : ℂ :=
  let y := sourceApprox event.frame x
  let T := actualC p event.frame+actualA p event.frame
  inner ℂ y (T (x-y))+inner ℂ (x-y) (T y)+inner ℂ (x-y) (T (x-y))

def dressedActionRead (event : DressedEvent) (p : PhysicalMomentum) : ℂ :=
  -sourceDensityEnergyRead p (sourceTestApprox event.frame (sourceDressedUnit event.epsilon event.precision))
    (sourceTestApprox event.frame (sourceDressedUnit event.epsilon event.precision))+
  sourceDensityEnergyRead p (sourceTestApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))
    (sourceTestApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))

def dressedActionCalibration (event : DressedEvent) (p : PhysicalMomentum) : ℂ :=
  -sourceActualUnitDefect p event.frame (sourceTestApprox event.frame (sourceDressedUnit event.epsilon event.precision))
    (sourceTestApprox event.frame (sourceDressedUnit event.epsilon event.precision))+
  sourceActualUnitDefect p event.frame (sourceTestApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))
    (sourceTestApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))+
  projectionEnergyRemainder event p (sourceDressedUnit event.epsilon event.precision)-
    projectionEnergyRemainder event p (SourceGraph.prepared (sourceProfile event.epsilon event.precision))

/-- Source h, the complete uncut time generator and the original created-minus-background observer are aligned with all generated unit and frame defects. -/
theorem actual_dressed_action_time_unit (event : DressedEvent) (p : PhysicalMomentum) :
    (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹*dressedActionRead event p=
      dressedEulerObserver event (actualC p event.frame+actualA p event.frame)+dressedActionCalibration event p := by
  have created := sourceDensityEnergyRead_actual_time p event.frame
    (sourceTestApprox event.frame (sourceDressedUnit event.epsilon event.precision))
    (sourceTestApprox event.frame (sourceDressedUnit event.epsilon event.precision))
  have background := sourceDensityEnergyRead_actual_time p event.frame
    (sourceTestApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))
    (sourceTestApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))
  rw [sourceTestApprox_embed] at created background
  have calibrated := signed_energy_calibration
    (actualC p event.frame+actualA p event.frame)
    (sourceDressedUnit event.epsilon event.precision)
    (SourceGraph.prepared (sourceProfile event.epsilon event.precision))
    (sourceApprox event.frame (sourceDressedUnit event.epsilon event.precision))
    (sourceApprox event.frame (SourceGraph.prepared (sourceProfile event.epsilon event.precision)))
    _ _ _ _ _ created background
  have hunit : (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹=
      (Stage10.ActionNormalization.actionScale : ℂ) := by
    rw [Stage10.ActionNormalization.actionScale, Complex.ofReal_inv]
  have paid : (Stage10.ActionNormalization.actionScale : ℂ)*dressedActionRead event p=
      dressedEulerObserver event (actualC p event.frame+actualA p event.frame)+dressedActionCalibration event p :=
    calibrated.trans (congrArg (fun z : ℂ => z+dressedActionCalibration event p)
      (dressed_euler_observer_original event (actualC p event.frame+actualA p event.frame)).symm)
  exact (congrArg (fun h : ℂ => h*dressedActionRead event p) hunit).trans paid

/-- Both actual external endpoints retain the original density-weight, compression and uncut-retainer calibration. -/
theorem actual_probe_action_time_unit (event : DressedEvent) (p : PhysicalMomentum) (left right : CompositeLeg) :
    (Stage10.ActionNormalization.phaseMomentum : ℂ)⁻¹*
      sourceDensityEnergyRead p (preparedProbeEndpoint left) (preparedProbeEndpoint right)=
      inner ℂ (embed (preparedProbeEndpoint left))
        ((actualC p event.frame+actualA p event.frame) (embed (preparedProbeEndpoint right)))+
      sourceActualUnitDefect p event.frame (preparedProbeEndpoint left) (preparedProbeEndpoint right) := by
  rw [← Complex.ofReal_inv, ← Stage10.ActionNormalization.actionScale]
  exact sourceDensityEnergyRead_actual_time _ _ _ _

end LowEnergy.GaussComposite.ActualDressedEMTensorClock
