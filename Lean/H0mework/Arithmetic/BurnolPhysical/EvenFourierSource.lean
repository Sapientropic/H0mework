import H0mework.Arithmetic.SonineGap.BalancedSonineGapFace
import H0mework.Arithmetic.BurnolPhysical.PhysicalityProjection
import H0mework.Arithmetic.BurnolPhysical.ConcreteAnnulusCoPoisson

/-!
# Even Fourier source and exact Burnol physicality residual

The concrete annulus source is first reflected and then added to its actual
Schwartz Fourier transform.  The resulting source is fixed by Fourier, so
the existing co-Poisson Tate/reflection law makes its log-energy realization
an actual member of the even `L²` face.

For the original nonzero annulus realization, the canonical admission port
is nonzero at every radius.  For the self-Fourier realization, the remaining
orthogonal residual is exactly the simultaneous local-constant position and
Fourier obligation.  No projection image is asserted nonzero and no log
orbit is renamed as Burnol's additive co-sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open Complex FourierTransform MeasureTheory
open scoped SchwartzMap ENNReal

noncomputable section

def burnolAnnulusSchwartzReflection : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) burnolAnnulusSchwartz

@[simp] theorem burnolAnnulusSchwartzReflection_apply (x : ℝ) :
    burnolAnnulusSchwartzReflection x = burnolAnnulusSchwartz (-x) := by
  rfl

/-- Evenization preserves the concrete two-sided annulus and introduces no
spectral parameter. -/
def burnolEvenAnnulusSchwartz : SchwartzMap ℝ ℂ :=
  burnolAnnulusSchwartz + burnolAnnulusSchwartzReflection

theorem burnolEvenAnnulusSchwartz_even (x : ℝ) :
    burnolEvenAnnulusSchwartz (-x) = burnolEvenAnnulusSchwartz x := by
  simp [burnolEvenAnnulusSchwartz, add_comm]

/-- The even annulus source plus its actual Fourier transform. -/
def burnolSelfFourierAnnulusSchwartz : SchwartzMap ℝ ℂ :=
  burnolEvenAnnulusSchwartz +
    FourierTransform.fourier burnolEvenAnnulusSchwartz

theorem fourier_burnolSelfFourierAnnulusSchwartz :
    FourierTransform.fourier burnolSelfFourierAnnulusSchwartz =
      burnolSelfFourierAnnulusSchwartz := by
  apply SchwartzMap.ext
  intro x
  change FourierTransform.fourier
      (burnolEvenAnnulusSchwartz +
        FourierTransform.fourier burnolEvenAnnulusSchwartz) x =
    (burnolEvenAnnulusSchwartz +
      FourierTransform.fourier burnolEvenAnnulusSchwartz) x
  rw [FourierTransform.fourier_add]
  change FourierTransform.fourier burnolEvenAnnulusSchwartz x +
      FourierTransform.fourier
        (FourierTransform.fourier burnolEvenAnnulusSchwartz) x =
    burnolEvenAnnulusSchwartz x +
      FourierTransform.fourier burnolEvenAnnulusSchwartz x
  rw [sonine_fourier_fourier_apply]
  rw [burnolEvenAnnulusSchwartz_even]
  ac_rfl

theorem coPoissonLogOrbitMap_selfFourierAnnulus_even (x : ℝ) :
    coPoissonLogOrbitMap burnolSelfFourierAnnulusSchwartz (-x) =
      coPoissonLogOrbitMap burnolSelfFourierAnnulusSchwartz x := by
  have source := coPoissonLogOrbitMap_fourier_reflection
    burnolSelfFourierAnnulusSchwartz x
  rwa [fourier_burnolSelfFourierAnnulusSchwartz] at source

theorem reflectL2_coPoissonLogOrbitEnergyMap_selfFourierAnnulus :
    reflectL2
        (coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz) =
      coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz := by
  apply Lp.ext
  have reflectedOrbit :=
    negMeasurePreserving.quasiMeasurePreserving.ae
      (coPoissonLogOrbitEnergyMap_coeFn
        burnolSelfFourierAnnulusSchwartz)
  filter_upwards [
    Lp.coeFn_compMeasurePreserving
      (coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz)
      negMeasurePreserving,
    reflectedOrbit,
    coPoissonLogOrbitEnergyMap_coeFn
      burnolSelfFourierAnnulusSchwartz] with x href hneg hpos
  calc
    reflectL2
        (coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz) x =
      (coPoissonLogOrbitEnergyMap
        burnolSelfFourierAnnulusSchwartz) (-x) := href
    _ = coPoissonLogOrbitMap burnolSelfFourierAnnulusSchwartz (-x) := hneg
    _ = coPoissonLogOrbitMap burnolSelfFourierAnnulusSchwartz x :=
      coPoissonLogOrbitMap_selfFourierAnnulus_even x
    _ = (coPoissonLogOrbitEnergyMap
        burnolSelfFourierAnnulusSchwartz) x := hpos.symm

/-- The actual self-Fourier source closes the even/cosine constraint before
any constant-gap admission is considered. -/
theorem coPoissonLogOrbitEnergyMap_selfFourierAnnulus_mem_even :
    coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz ∈
      evenL2ClosedFace := by
  exact mem_evenL2ClosedFace_iff.mpr
    reflectL2_coPoissonLogOrbitEnergyMap_selfFourierAnnulus

def burnolAnnulusAdmissionState (radius : ℝ) :=
  evenBurnolAdmissionPort radius
    (coPoissonLogOrbitEnergyMap burnolAnnulusSchwartz)

/-- The full admission state cannot erase the concrete source: its physical
and orthogonal coordinates are jointly nonzero at every radius. -/
theorem burnolAnnulusAdmissionState_ne_zero (radius : ℝ) :
    burnolAnnulusAdmissionState radius ≠ 0 := by
  exact (evenBurnolAdmissionPort_ne_zero_iff radius
    (coPoissonLogOrbitEnergyMap burnolAnnulusSchwartz)).mpr
      coPoissonLogOrbitEnergyMap_burnolAnnulus_ne_zero

/-- Exact residual left after testing the self-Fourier annulus source against
the full even Burnol face. -/
def selfFourierAnnulusConstantGapResidual (radius : ℝ) :=
  evenBurnolOrthogonalResidual radius
    (coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz)

/-- Evenness is already paid, so vanishing of the remaining residual is
precisely the two local-constant conditions. -/
theorem selfFourierAnnulusConstantGapResidual_eq_zero_iff
    (radius : ℝ) :
    selfFourierAnnulusConstantGapResidual radius = 0 ↔
      coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz ∈
        burnolClosedFace radius := by
  rw [selfFourierAnnulusConstantGapResidual,
    evenBurnolOrthogonalResidual_eq_zero_iff]
  change (coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz ∈
      burnolClosedFace radius ∧
    coPoissonLogOrbitEnergyMap burnolSelfFourierAnnulusSchwartz ∈
      evenL2ClosedFace) ↔ _
  exact and_iff_left
    coPoissonLogOrbitEnergyMap_selfFourierAnnulus_mem_even

end

end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
