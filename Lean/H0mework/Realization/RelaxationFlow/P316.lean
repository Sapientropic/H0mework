import H0mework.Realization.Fibres.P315
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Proposition 316: sigma time coordinates give the heat-kernel input

The Mellin-transform bridge should not be smuggled in as rhetoric.  The first
machine-checkable step is the carrier-side coordinate change

`σ(t) = 1 - exp(-t)`.

In this coordinate, the sigma residual / headroom is exactly the heat kernel:

`1 - iteratedRate (σ(t)) n = exp (-(n : ℝ) * t)`.

This is the concrete input needed by the usual Mellin formula for zeta-shaped
objects.  The later analytic step must still provide a real Mellin /
functional-equation certificate.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

/-! ## The sigma-time coordinate -/

/-- Sigma as a time parameter: `σ(t) = 1 - exp(-t)`. -/
def sigmaOfTime (t : ℝ) : ℝ :=
  1 - Real.exp (-t)

/-- The heat-kernel headroom for depth `n` at time `t`. -/
def heatHeadroom (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (-(n : ℝ) * t)

/-- The corresponding rate coordinate, `1 - exp(-nt)`. -/
def heatRate (n : ℕ) (t : ℝ) : ℝ :=
  1 - heatHeadroom n t

/-- THEOREM 1: the complement of `σ(t)` is `exp(-t)`. -/
@[simp] theorem complement_sigmaOfTime (t : ℝ) :
    complement (sigmaOfTime t) = Real.exp (-t) := by
  simp [complement, sigmaOfTime]

/-- THEOREM 2: serial time addition is noisy-OR composition in the sigma
coordinate. -/
theorem sigmaOfTime_add (t u : ℝ) :
    sigmaOfTime (t + u) =
      satOrField (sigmaOfTime t) (sigmaOfTime u) := by
  unfold sigmaOfTime satOrField
  rw [show -(t + u) = -t + -u by ring, Real.exp_add]
  ring

/-- THEOREM 3: the `n`-fold sigma residual in time coordinates is the heat
kernel `exp(-nt)`. -/
theorem complement_iteratedRate_sigmaOfTime (n : ℕ) (t : ℝ) :
    complement (iteratedRate (sigmaOfTime t) n) =
      heatHeadroom n t := by
  unfold complement heatHeadroom
  rw [keep_iteratedRate]
  simp [sigmaOfTime]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- THEOREM 4: the `n`-fold iterated rate at `σ(t)` is exactly the heat rate
`1 - exp(-nt)`. -/
theorem iteratedRate_sigmaOfTime_eq_heatRate (n : ℕ) (t : ℝ) :
    iteratedRate (sigmaOfTime t) n = heatRate n t := by
  unfold iteratedRate sigmaOfTime heatRate heatHeadroom
  simp
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- THEOREM 5: equivalently, `n` repetitions at time `t` equal one sigma step at
time `n*t`. -/
theorem iteratedRate_sigmaOfTime_eq_sigmaOfTime_nat_mul (n : ℕ) (t : ℝ) :
    iteratedRate (sigmaOfTime t) n =
      sigmaOfTime ((n : ℝ) * t) := by
  rw [iteratedRate_sigmaOfTime_eq_heatRate]
  unfold heatRate heatHeadroom sigmaOfTime
  rw [show -(n : ℝ) * t = -((n : ℝ) * t) by ring]

/-- THEOREM 6: heat headrooms multiply under serializing depths. -/
theorem heatHeadroom_add_depth (n m : ℕ) (t : ℝ) :
    heatHeadroom (n + m) t = heatHeadroom n t * heatHeadroom m t := by
  unfold heatHeadroom
  rw [show -((n + m : ℕ) : ℝ) * t =
      (-(n : ℝ) * t) + (-(m : ℝ) * t) by
    norm_num
    ring, Real.exp_add]

/-- THEOREM 7: heat headrooms multiply under serializing times. -/
theorem heatHeadroom_add_time (n : ℕ) (t u : ℝ) :
    heatHeadroom n (t + u) = heatHeadroom n t * heatHeadroom n u := by
  unfold heatHeadroom
  rw [show -(n : ℝ) * (t + u) =
      (-(n : ℝ) * t) + (-(n : ℝ) * u) by ring, Real.exp_add]

/-! ## Abstract Mellin bridge interface -/

/-- A minimal interface for the later Mellin step: the carrier kernel consumed
by the transform must be the heat headroom proven above, and the spectral-side
reflection must be the analytic complement `s ↦ 1-s`.

This structure deliberately does not define Riemann zeta or analytic
continuation.  It is the certificate shape a later, real Mellin theorem must
fill. -/
structure MellinHeatKernelBridge
    (Spectral Value : Type*) [One Spectral] [Sub Spectral] where
  mellin : (ℕ -> ℝ -> ℝ) -> Spectral -> Value
  carrierKernel : ℕ -> ℝ -> ℝ
  carrierKernel_eq_heat : carrierKernel = heatHeadroom
  spectralComplement : Spectral -> Spectral
  spectralComplement_eq :
    ∀ s : Spectral, spectralComplement s = analyticComplement s

namespace MellinHeatKernelBridge

/-- THEOREM 8: any bridge whose spectral complement is `s ↦ 1-s` has an
involutive spectral reflection. -/
theorem spectralComplement_involutive
    {Spectral Value : Type*} [Ring Spectral]
    (B : MellinHeatKernelBridge Spectral Value)
    (s : Spectral) :
    B.spectralComplement (B.spectralComplement s) = s := by
  rw [B.spectralComplement_eq, B.spectralComplement_eq]
  exact analyticComplement_involutive s

/-- THEOREM 9: the bridge's carrier kernel is pointwise the sigma-derived heat
headroom. -/
theorem carrierKernel_apply
    {Spectral Value : Type*} [One Spectral] [Sub Spectral]
    (B : MellinHeatKernelBridge Spectral Value)
    (n : ℕ) (t : ℝ) :
    B.carrierKernel n t = heatHeadroom n t := by
  rw [B.carrierKernel_eq_heat]

end MellinHeatKernelBridge

/-- A compact certificate for the carrier-to-heat-kernel part of the Mellin
route. -/
structure SigmaTimeHeatKernelCertificate where
  sigma_headroom :
    ∀ t : ℝ, complement (sigmaOfTime t) = Real.exp (-t)
  serial_time :
    ∀ t u : ℝ,
      sigmaOfTime (t + u) =
        satOrField (sigmaOfTime t) (sigmaOfTime u)
  iterated_headroom :
    ∀ (n : ℕ) (t : ℝ),
      complement (iteratedRate (sigmaOfTime t) n) = heatHeadroom n t
  iterated_rate :
    ∀ (n : ℕ) (t : ℝ),
      iteratedRate (sigmaOfTime t) n = heatRate n t
  iterated_time :
    ∀ (n : ℕ) (t : ℝ),
      iteratedRate (sigmaOfTime t) n =
        sigmaOfTime ((n : ℝ) * t)

/-- THEOREM 10: the canonical sigma-time heat-kernel certificate. -/
theorem sigmaTimeHeatKernelCertificate :
    SigmaTimeHeatKernelCertificate where
  sigma_headroom := complement_sigmaOfTime
  serial_time := sigmaOfTime_add
  iterated_headroom := complement_iteratedRate_sigmaOfTime
  iterated_rate := iteratedRate_sigmaOfTime_eq_heatRate
  iterated_time := iteratedRate_sigmaOfTime_eq_sigmaOfTime_nat_mul

end AffineRelaxation
end SaturationMonoid
