import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedOrderedSpatialReturn
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMClockAction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroClockFrequency
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedZeroDamping ActualDressedOrderedStatic
open ActualCompositeFieldCurrent
open scoped Matrix
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

/-- The same complete source occurrence: frequency is kept, damping is the outer variable. -/
def frequencyClockSlice (eps : ℝ) : Parameters →+* (ℂ[X])[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun i : Fin 3 => if i=0 then Polynomial.C (Polynomial.C (eps : ℂ))
      else if i=1 then Polynomial.X else Polynomial.C Polynomial.X)

def frequencyDampingSlice (eps s : ℝ) : Parameters →+* ℂ[X] :=
  MvPolynomial.eval₂Hom Polynomial.C
    (fun i : Fin 3 => if i=0 then Polynomial.C (eps : ℂ)
      else if i=1 then Polynomial.X else Polynomial.C (s : ℂ))

theorem frequency_clock_specialize (eps s : ℝ) (P : Parameters) :
    clockSpecialize s (frequencyClockSlice eps P)=frequencyDampingSlice eps s P := by
  have hom : (clockSpecialize s).comp (frequencyClockSlice eps)=frequencyDampingSlice eps s := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [clockSpecialize,frequencyClockSlice,frequencyDampingSlice]
    · intro i
      simp [clockSpecialize,frequencyClockSlice,frequencyDampingSlice]
      split_ifs <;> simp_all
  exact congrArg (fun f : Parameters →+* ℂ[X] => f P) hom

theorem frequency_damping_eval (eps s sigma : ℝ) (P : Parameters) :
    (frequencyDampingSlice eps s P).eval (sigma : ℂ)=MvPolynomial.eval (irValues eps sigma s) P := by
  have hom : (Polynomial.evalRingHom (sigma : ℂ)).comp (frequencyDampingSlice eps s)=
      MvPolynomial.eval (irValues eps sigma s) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [frequencyDampingSlice]
    · intro i
      simp [frequencyDampingSlice,irValues]
      split_ifs <;> simp_all
  exact congrArg (fun f : Parameters →+* ℂ => f P) hom

def frequencyClockDeterminant (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  frequencyClockSlice eps (commonDeterminant event n)

def frequencyClockEMNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) (ℂ[X])[X] := (commonEMTensorNumerator event n).map (frequencyClockSlice eps)

def frequencyClockProbeNumerator (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : (ℂ[X])[X] :=
  frequencyClockSlice eps (commonCurrentNumerator event n pd ps dL dR sL sR)

def frequencyClockOrder (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℕ :=
  (frequencyClockDeterminant event eps n).natTrailingDegree

def zeroClockFrequencyDenominator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) : ℂ[X] :=
  (frequencyClockDeterminant event eps n).coeff (frequencyClockOrder event eps n)

def zeroClockFrequencyEMNumerator (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) ℂ[X] :=
  fun mu nu => (frequencyClockEMNumerator event eps n mu nu).coeff (frequencyClockOrder event eps n)

def zeroClockFrequencyProbeNumerator (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ[X] :=
  (frequencyClockProbeNumerator event eps n pd ps dL dR sL sR).coeff (frequencyClockOrder event eps n)

def zeroClockFrequencyEMFraction (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) (RatFunc ℂ) :=
  fun mu nu => readFraction (zeroClockFrequencyEMNumerator event eps n mu nu)
    (zeroClockFrequencyDenominator event eps n)

def zeroClockFrequencyProbeFraction (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : RatFunc ℂ :=
  readFraction (zeroClockFrequencyProbeNumerator event eps n pd ps dL dR sL sR)
    (zeroClockFrequencyDenominator event eps n)

def FrequencyClockFinite (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : Prop :=
  (∀mu nu, X^frequencyClockOrder event eps n∣frequencyClockEMNumerator event eps n mu nu) ∧
    X^frequencyClockOrder event eps n∣frequencyClockProbeNumerator event eps n pd ps dL dR sL sR

theorem source_frequency_clock_factor (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    X^frequencyClockOrder event eps n∣frequencyClockDeterminant event eps n :=
  X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)

theorem source_frequency_denominator_nonzero (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum)
    (nonzero : frequencyClockDeterminant event eps n≠0) : zeroClockFrequencyDenominator event eps n≠0 :=
  coeff_natTrailingDegree_ne_zero.mpr nonzero

end LowEnergy.GaussComposite.ActualDressedZeroClockFrequency
