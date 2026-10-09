import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Symmetries
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Variation

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

namespace CPS1Deformation
noncomputable section
open CPS1ElectronicSource ContinuousLinearMap
open scoped BigOperators Matrix Matrix.Norms.Elementwise
variable {frame : CPS1Recycling.Frame}

def occupiedPhysicalLinear (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source) :
    OccupiedConfiguration source →ₗ[ℝ] ℝ where
  toFun := fun direction => 2 *
    (Matrix.trace (occupied.conjTranspose * physicalFockAt source positions occupied * direction)).re
  map_add' := by
    intro first second
    simp only [Matrix.mul_add,Matrix.trace_add,Complex.add_re,mul_add]
  map_smul' := by
    intro scalar direction
    simp only [Matrix.mul_smul,Matrix.trace_smul,Complex.real_smul,smul_eq_mul,RingHom.id_apply,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring

def occupiedPhysicalDifferential (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source) :
    OccupiedConfiguration source →L[ℝ] ℝ :=
  (occupiedPhysicalLinear source positions occupied).toContinuousLinearMap

theorem occupied_physical_differential_apply (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied direction : OccupiedConfiguration source) :
    occupiedPhysicalDifferential source positions occupied direction = 2 *
      (Matrix.trace (occupied.conjTranspose * physicalFockAt source positions occupied * direction)).re := rfl

theorem occupied_physical_variation (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied direction : OccupiedConfiguration source) :
    HasDerivAt (fun time : ℝ => energyAt source positions (occupied + time • direction))
      (occupiedPhysicalDifferential source positions occupied direction) 0 := by
  have generated := FiniteVariation.occupied_energy_line (coreAt source positions) (twoBodyAt source positions)
    (two_body_swap source positions) occupied direction (physical_fock_hermitian source positions occupied)
  have paid := generated.const_add (nuclearEnergyAt source positions (energySourceMomenta source))
  simpa only [energyAt,electronicEnergyAt,densityAt,FiniteVariation.densityEnergy,
    FiniteVariation.fock,FiniteVariation.interaction,physicalFockAt,occupied_physical_differential_apply] using! paid

theorem electronic_occupation_differentiable (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source) :
    DifferentiableAt ℝ (fun next : OccupiedConfiguration source => electronicEnergyAt source positions next) occupied := by
  simp only [electronicEnergyAt,densityAt,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
  fun_prop

theorem occupied_physical_hasFDerivAt (source : CPS1ElectronicSource.State frame)
    (positions : NuclearConfiguration source) (occupied : OccupiedConfiguration source) :
    HasFDerivAt (fun next : OccupiedConfiguration source => energyAt source positions next)
      (occupiedPhysicalDifferential source positions occupied) occupied := by
  have smooth := (electronic_occupation_differentiable source positions occupied).const_add
    (nuclearEnergyAt source positions (energySourceMomenta source))
  have same : fderiv ℝ (fun next : OccupiedConfiguration source => energyAt source positions next) occupied =
      occupiedPhysicalDifferential source positions occupied := by
    ext direction
    have line : HasDerivAt (fun time : ℝ => occupied + time • direction) direction 0 := by
      simpa only [one_smul,zero_add] using!
        (hasDerivAt_const (0 : ℝ) occupied).add ((hasDerivAt_id (0 : ℝ)).smul_const direction)
    have actual : HasDerivAt (fun time : ℝ => energyAt source positions (occupied + time • direction))
        (fderiv ℝ (fun next : OccupiedConfiguration source => energyAt source positions next) occupied direction) 0 := by
      have atSource : HasFDerivAt (fun next : OccupiedConfiguration source => energyAt source positions next)
          (fderiv ℝ (fun next : OccupiedConfiguration source => energyAt source positions next) occupied) occupied :=
        smooth.hasFDerivAt
      have atCurve : HasFDerivAt (fun next : OccupiedConfiguration source => energyAt source positions next)
          (fderiv ℝ (fun next : OccupiedConfiguration source => energyAt source positions next) occupied)
          (occupied + (0 : ℝ) • direction) := by
        simpa only [zero_smul,add_zero] using atSource
      have generated := atCurve.comp_hasDerivAt (0 : ℝ) line
      simpa only [Function.comp_def,zero_smul,add_zero] using! generated
    exact actual.unique (occupied_physical_variation source positions occupied direction)
  rw [← same]
  exact smooth.hasFDerivAt

end
end CPS1Deformation
