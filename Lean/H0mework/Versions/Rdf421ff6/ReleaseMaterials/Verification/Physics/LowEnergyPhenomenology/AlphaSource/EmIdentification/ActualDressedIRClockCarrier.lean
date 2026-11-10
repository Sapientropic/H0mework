import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedDampingPrincipal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedOrderedStatic
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedZeroDamping ActualCompositeFieldCurrent
open scoped Matrix
attribute [local irreducible] commonEMTensorNumerator commonDeterminant correctedEMTensor

/-- One original static occurrence: inner variable is spatial IR epsilon, outer variable is damping. -/
def staticIRClockSlice : Parameters →+* (ℂ[X])[X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun i : Fin 3 => if i=0 then Polynomial.C Polynomial.X else if i=1 then Polynomial.X else 0)

def clockSpecialize (eps : ℝ) : (ℂ[X])[X] →+* ℂ[X] :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (eps : ℂ))

theorem ir_clock_specialize (eps : ℝ) (P : Parameters) :
    clockSpecialize eps (staticIRClockSlice P)=dampingSlice eps P := by
  have hom : (clockSpecialize eps).comp staticIRClockSlice=dampingSlice eps := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [clockSpecialize,staticIRClockSlice,dampingSlice]
    · intro i
      simp [clockSpecialize,staticIRClockSlice,dampingSlice]
      split_ifs <;> simp_all
  exact congrArg (fun f : Parameters →+* ℂ[X] => f P) hom

def irClockDeterminant (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  staticIRClockSlice (commonDeterminant event n)

def irClockEMNumerator (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin 4) (Fin 4) (ℂ[X])[X] := (commonEMTensorNumerator event n).map staticIRClockSlice

def irClockProbeNumerator (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : (ℂ[X])[X] :=
  staticIRClockSlice (commonCurrentNumerator event n pd ps dL dR sL sR)

theorem actual_ir_clock_determinant (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    clockSpecialize eps (irClockDeterminant event n)=dampingDeterminant event eps n :=
  ir_clock_specialize eps _

theorem actual_ir_clock_em_numerator (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) :
    clockSpecialize eps (irClockEMNumerator event n mu nu)=dampingEMNumerator event eps n mu nu :=
  ir_clock_specialize eps _

theorem actual_ir_clock_probe_numerator (event : DressedEvent) (eps : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    clockSpecialize eps (irClockProbeNumerator event n pd ps dL dR sL sR)=
      dampingProbeNumerator event eps n pd ps dL dR sL sR :=
  ir_clock_specialize eps _

def sourceClockOrder (event : DressedEvent) (n : PhysicalMomentum) : ℕ :=
  (irClockDeterminant event n).natTrailingDegree

def sourceClockDenominator (event : DressedEvent) (n : PhysicalMomentum) : ℂ[X] :=
  (irClockDeterminant event n).coeff (sourceClockOrder event n)

def zeroClockEMNumerator (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ[X] :=
  fun mu nu => (irClockEMNumerator event n mu nu).coeff (sourceClockOrder event n)

def zeroClockProbeNumerator (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ[X] :=
  (irClockProbeNumerator event n pd ps dL dR sL sR).coeff (sourceClockOrder event n)

def zeroClockEMFraction (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) (RatFunc ℂ) :=
  fun mu nu => readFraction (zeroClockEMNumerator event n mu nu) (sourceClockDenominator event n)

def zeroClockProbeFraction (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : RatFunc ℂ :=
  readFraction (zeroClockProbeNumerator event n pd ps dL dR sL sR) (sourceClockDenominator event n)

end LowEnergy.GaussComposite.ActualDressedOrderedStatic
