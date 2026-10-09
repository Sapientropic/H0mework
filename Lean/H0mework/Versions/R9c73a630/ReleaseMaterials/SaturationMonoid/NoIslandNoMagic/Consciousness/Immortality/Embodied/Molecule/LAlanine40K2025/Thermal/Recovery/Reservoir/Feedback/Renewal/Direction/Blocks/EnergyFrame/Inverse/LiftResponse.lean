import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Commutator

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
open Collision Load.Source
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem local_lift_star (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ) :
    star (Incidence.localLift U V)=Incidence.localLift (star U) (star V) := by
  apply Subtype.ext
  simp only [Incidence.localLift,Incidence.regroupUnitary,Load.Quantum.localUnitary,
    Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_submatrix,Matrix.kronecker,
    Matrix.conjTranspose_kronecker]

theorem body_observable_local (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    Quantum.conjugation (Incidence.localLift U V) (Incidence.bodyObservable O)=
      Incidence.bodyObservable (Quantum.conjugation U O) := by
  rw [Incidence.localLift,Incidence.bodyObservable,Incidence.regroup_conjugation]
  have tensor := Load.Quantum.localConjugation_tensor U V O (1 : Matrix ι ι ℂ)
  have fixed : Quantum.conjugation V (1 : Matrix ι ι ℂ)=1 :=
    map_one (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) V)
  rw [fixed] at tensor
  exact congrArg (fun A => A.submatrix Incidence.bodyReservoir Incidence.bodyReservoir) tensor

theorem body_observable_response (U : Matrix.unitaryGroup (ι × κ) ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (O : Matrix (ι × κ) (ι × κ) ℂ) :
    ‖Quantum.conjugation (star (Incidence.localLift U V)) (Incidence.bodyObservable O)-Incidence.bodyObservable O‖ ≤
      ‖Quantum.conjugation (star U) O-O‖ := by
  rw [local_lift_star,body_observable_local,← bodyObservable_sub]
  exact body_observable_norm _

theorem original_PC_body_observable : Sectors.pcObservable=Incidence.bodyObservable
    (Matrix.kronecker Powered.Producer.poweredTotalHamiltonian (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  ext i j
  simp only [Sectors.pcObservable,Incidence.bodyObservable,Incidence.bodyReservoir,Matrix.submatrix_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply,Equiv.coe_fn_mk]
  ring

theorem original_body_load_response (time : ℝ) :
    ‖Quantum.conjugation (star (Current.loadPulse time)) Sectors.pcObservable-Sectors.pcObservable‖ ≤
    |time| * (‖loadInteraction*numericLoadPC-numericLoadPC*loadInteraction‖+(252/10^12 : ℝ)) := by
  rw [original_PC_body_observable]
  exact (body_observable_response (loadUnitary time) (Native.freePCUnitary time) _).trans
    (original_load_response_numeric time)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
