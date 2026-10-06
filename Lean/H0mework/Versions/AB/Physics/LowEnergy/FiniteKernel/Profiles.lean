import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Source
import H0mework.Physics.SpinPair.Phase
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual smooth test fields and their holonomic first jets. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FiniteKernel
open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource StageNineHolonomicField
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

structure Modes (ι : Type*) where
  value : ι → BasePoint → ℂ
  smooth : ∀ i, ContDiff ℝ ∞ (value i)

def profile (modes : Modes ι) (v : ι → DiracExteriorMatterCarrier) (point : BasePoint) :
    DiracExteriorMatterCarrier := ∑ i, modes.value i point • v i

def dualProfile (modes : Modes ι) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  ∑ i, star (modes.value i point) • chi i

theorem dualProfile_smooth (modes : Modes ι) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier)
    (v : DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point => dualProfile modes chi point v) := by
  simp only [dualProfile, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro i _
  exact (Complex.conjCLE.contDiff.comp (modes.smooth i)).mul contDiff_const

def configuration (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (v : ι → DiracExteriorMatterCarrier) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier) :
    StageNineHolonomicConfiguration :=
  { C with matter := profile modes v, conjugateMatter := dualProfile modes chi }

theorem profile_coordinates (modes : Modes ι) (v : ι → DiracExteriorMatterCarrier)
    (point : BasePoint) :
    matterCoordinateEquiv (profile modes v point) =
      ∑ i, modes.value i point • matterCoordinateEquiv (v i) := by
  simp [profile]

theorem profile_smooth (modes : Modes ι) (v : ι → DiracExteriorMatterCarrier) :
    ContDiff ℝ ∞ (fun point => matterCoordinateEquiv (profile modes v point)) := by
  simp only [profile_coordinates]
  apply ContDiff.sum
  intro i _
  exact (modes.smooth i).smul contDiff_const

theorem profile_derivative (modes : Modes ι) (v : ι → DiracExteriorMatterCarrier)
    (point : BasePoint) :
    HasFDerivAt (fun p => matterCoordinateEquiv (profile modes v p))
      (∑ i, (fderiv ℝ (modes.value i) point).smulRight (matterCoordinateEquiv (v i))) point := by
  have summands (i : ι) :
      HasFDerivAt (fun p => modes.value i p • matterCoordinateEquiv (v i))
        ((fderiv ℝ (modes.value i) point).smulRight (matterCoordinateEquiv (v i))) point :=
    ((modes.smooth i).differentiable (by simp) point).hasFDerivAt.smul_const _
  simpa only [profile_coordinates] using HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => summands i)

theorem profile_directional (modes : Modes ι) (v : ι → DiracExteriorMatterCarrier)
    (point : BasePoint) (mu : LorentzianIndex) :
    matterCoordinateEquiv.symm (fieldDirectionalDerivative
      (fun p => matterCoordinateEquiv (profile modes v p)) point mu) =
      ∑ i, fieldDirectionalDerivative (modes.value i) point mu • v i := by
  unfold fieldDirectionalDerivative
  rw [(profile_derivative modes v point).fderiv]
  simp [map_sum, map_smul]

theorem profile_covariant (C : StageNineHolonomicConfiguration) (modes : Modes ι)
    (v : ι → DiracExteriorMatterCarrier) (chi : ι → Module.Dual ℂ DiracExteriorMatterCarrier)
    (point : BasePoint) (mu : LorentzianIndex) :
    holonomicMatterCovariantDerivative (configuration C modes v chi) point mu =
      ∑ i, (fieldDirectionalDerivative (modes.value i) point mu • v i +
        modes.value i point • FullQuantum.connection C point mu (v i)) := by
  unfold holonomicMatterCovariantDerivative
  simp only [configuration]
  rw [profile_directional]
  simp only [profile, map_sum, map_smul, FullQuantum.connection, LinearMap.add_apply,
    smul_add, Finset.sum_add_distrib]
  abel

def coordinateModes : Modes (Fin 5) where
  value i := Fin.cases (fun _ => 1) (fun j p => (p j : ℂ)) i
  smooth i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact contDiff_const
    · exact Complex.ofRealCLM.contDiff.comp
        (EuclideanSpace.proj j : BasePoint →L[ℝ] ℝ).contDiff

theorem coordinateModes_directional (j : Fin 4) (point : BasePoint) (mu : LorentzianIndex) :
    fieldDirectionalDerivative (coordinateModes.value j.succ) point mu =
      if mu=j then 1 else 0 := by
  unfold fieldDirectionalDerivative
  have derivative := Complex.ofRealCLM.hasFDerivAt.comp point
    (EuclideanSpace.proj j : BasePoint →L[ℝ] ℝ).hasFDerivAt
  change HasFDerivAt (fun p : BasePoint => (p j : ℂ)) _ point at derivative
  rw [show coordinateModes.value j.succ = (fun p : BasePoint => (p j : ℂ)) from rfl,
    derivative.fderiv]
  by_cases same : mu=j
  · subst mu
    simp [coordinateDirection]
  · simp [coordinateDirection, same, Ne.symm same]

def phaseModes : Modes (Fin 2) where
  value := ![Stage9C.Material.SpinPair.upperPhase, Stage9C.Material.SpinPair.lowerPhase]
  smooth i := by
    fin_cases i
    · exact Stage9C.Material.SpinPair.phase_smooth _
    · exact Stage9C.Material.SpinPair.phase_smooth _

def originalModes : Modes (Fin 5 ⊕ Fin 2) where
  value := Sum.elim coordinateModes.value phaseModes.value
  smooth i := by cases i with
    | inl i => exact coordinateModes.smooth i
    | inr i => exact phaseModes.smooth i

end
end SaturationMonoid.PhysicsCore.LowEnergy.FiniteKernel
