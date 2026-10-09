import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Dynamics.BodyTransferSpectatorKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Producer.SourceGeneratedReservoirCurrent

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel

open Collision Load.Source Propagation.Producer
open scoped Matrix ComplexOrder
noncomputable section

section Tensor
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem local_product (U V : Matrix.unitaryGroup ι ℂ) (E : Matrix.unitaryGroup κ ℂ) :
    Load.Quantum.localUnitary (U * V) E =
      Load.Quantum.localUnitary U E * Load.Quantum.localUnitary V 1 := by
  apply Subtype.ext
  change Matrix.kronecker ((U * V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) (E : Matrix κ κ ℂ) =
    Matrix.kronecker (U : Matrix ι ι ℂ) (E : Matrix κ κ ℂ) *
      Matrix.kronecker (V : Matrix ι ι ℂ) (1 : Matrix κ κ ℂ)
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul, Matrix.mul_one, MulMemClass.coe_mul]

theorem regroup_local (U V : Matrix.unitaryGroup ι ℂ) (E : Matrix.unitaryGroup κ ℂ) :
    Load.Quantum.localUnitary (Quantum.localUnitary U V) E =
      Incidence.localLift (Load.Quantum.localUnitary U E) V := by
  apply Subtype.ext
  ext i j
  change ((U : Matrix ι ι ℂ) i.1.1 j.1.1 * (V : Matrix ι ι ℂ) i.1.2 j.1.2) * (E : Matrix κ κ ℂ) i.2 j.2 =
    ((U : Matrix ι ι ℂ) i.1.1 j.1.1 * (E : Matrix κ κ ℂ) i.2 j.2) * (V : Matrix ι ι ℂ) i.1.2 j.1.2
  ring
end Tensor

def sourceBodyChannel (rho : LoadedJoint) : LoadedJoint :=
  Incidence.bodyRead (Quantum.conjugation (Current.pulse (nativeClockStep : ℝ))
    (Incidence.receivedJoint rho Source.donor))

def bodyFree : Matrix.unitaryGroup (PairController × Fin 2) ℂ :=
  Load.Quantum.localUnitary (Native.freePCUnitary (nativeClockStep : ℝ))
    (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))

theorem source_pulse_factor :
    Current.pulse (nativeClockStep : ℝ) =
      Incidence.localLift bodyFree (Native.freePCUnitary (nativeClockStep : ℝ)) *
        Load.Quantum.localUnitary (Exchange.nearTransfer (nativeClockStep : ℝ)) (1 : Matrix.unitaryGroup (Fin 2) ℂ) := by
  rw [Current.pulse, Native.pairFlow_factor, Native.sourceCoupling_clock, local_product, regroup_local]
  rfl

theorem sourceBodyChannel_factor (rho : LoadedJoint) :
    sourceBodyChannel rho = Quantum.conjugation bodyFree
      (bodyExchange rho Source.donor (Real.pi / 2 - (nativeClockStep : ℝ))) := by
  unfold sourceBodyChannel
  rw [source_pulse_factor]
  change Incidence.bodyRead (Unitary.conjStarAlgAut ℂ Current.FullJoint (_ * _) _) = _
  rw [Unitary.conjStarAlgAut_mul_apply]
  change Incidence.bodyRead (Quantum.conjugation
    (Incidence.localLift bodyFree (Native.freePCUnitary (nativeClockStep : ℝ)))
    (Load.Quantum.localConjugation (Exchange.nearTransfer (nativeClockStep : ℝ))
      (1 : Matrix.unitaryGroup (Fin 2) ℂ) (Incidence.receivedJoint rho Source.donor))) = _
  rw [Incidence.localLift_read]
  rfl

theorem source_cos_nonzero : Real.cos (Real.pi / 2 - (nativeClockStep : ℝ)) ≠ 0 := by
  rw [Real.cos_pi_div_two_sub]
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi Load.Producer.StrictThermal.nativeClock_small.1
  have small : (nativeClockStep : ℝ) < 1 := by rw [nativeClockStep_exact]; norm_num
  linarith [Real.pi_gt_three]

theorem sourceBodyChannel_injective : Function.Injective sourceBodyChannel := by
  intro left right same
  rw [sourceBodyChannel_factor, sourceBodyChannel_factor] at same
  have erased := (Unitary.conjStarAlgAut ℂ LoadedJoint bodyFree).injective same
  exact bodyExchange_injective Source.donor Source.donor_positive.isHermitian Source.donor_trace
    (Real.pi / 2 - (nativeClockStep : ℝ)) source_cos_nonzero erased

theorem sourceBodyChannel_actual :
    sourceBodyChannel Source.received.joint = Incidence.bodyRead (Current.supplyNext Current.initial).joint := by
  rw [Current.supplyNext_joint, Current.initial_receives_actual]
  rfl

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.BodyKernel
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
