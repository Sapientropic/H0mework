import H0mework.Chemistry.LAlanineThermalDynamics.UnequalPartialTrace
import H0mework.Chemistry.LAlanineWork.UnitaryWorkCapacity
import H0mework.Quantum.Generator.P257

/-! # A finite controller and a non-diagonal system generate one full-joint flow -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Dynamics

open _root_.SaturationMonoid.AffineRelaxation
open scoped Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

abbrev ControllerJoint (ι : Type*) := Matrix (ι × Fin 2) (ι × Fin 2) ℂ
abbrev ControllerSpace (ι : Type*) := EuclideanSpace ℂ (ι × Fin 2)

def controllerHamiltonian (gap : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![0, (gap : ℂ)]

theorem controllerHamiltonian_hermitian (gap : ℝ) : (controllerHamiltonian gap).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [isSelfAdjoint_iff]

def bareHamiltonian (systemH : Matrix ι ι ℂ) (gap : ℝ) : ControllerJoint ι :=
  Matrix.kronecker systemH 1 + Matrix.kronecker 1 (controllerHamiltonian gap)

omit [Fintype ι] in
theorem bareHamiltonian_hermitian (systemH : Matrix ι ι ℂ) (gap : ℝ)
    (hH : systemH.IsHermitian) : (bareHamiltonian systemH gap).IsHermitian := by
  change _ᴴ = _
  unfold bareHamiltonian
  dsimp only [Matrix.kronecker]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    hH.eq, (controllerHamiltonian_hermitian gap).eq]
  simp only [Matrix.conjTranspose_one]

def totalHamiltonian (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι) :
    ControllerJoint ι := bareHamiltonian systemH gap + interaction

omit [Fintype ι] in
theorem totalHamiltonian_hermitian (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) :
    (totalHamiltonian systemH gap interaction).IsHermitian :=
  (bareHamiltonian_hermitian systemH gap hH).add hV

def controllerOperator (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι) :
    ControllerSpace ι →L[ℂ] ControllerSpace ι :=
  Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ) (totalHamiltonian systemH gap interaction)

/-- Only the source Hamiltonian enters the existing flow producer. -/
theorem sourceFlow (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) :
    BoundedSelfAdjointHamiltonianSchrodingerFlowCertificate (ControllerSpace ι)
      (controllerOperator systemH gap interaction) :=
  boundedSelfAdjointHamiltonianSchrodingerFlowCertificate _
    ((totalHamiltonian_hermitian systemH gap interaction hH hV).isSelfAdjoint.map
      (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)))

def flowUnitary (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ) :
    Matrix.unitaryGroup (ι × Fin 2) ℂ :=
  ⟨(Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).symm
      (NormedSpace.exp ((time : ℂ) • (-Complex.I • controllerOperator systemH gap interaction))),
    Unitary.map_mem (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).symm
      ((sourceFlow systemH gap interaction hH hV).exponential_group.unitarySlice time)⟩

def coupledNext (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ)
    (current : ControllerJoint ι) : ControllerJoint ι :=
  Unitary.conjStarAlgAut ℂ _ (flowUnitary systemH gap interaction hH hV time) current

theorem coupledNext_positive (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ)
    (current : ControllerJoint ι) (positive : current.PosSemidef) :
    (coupledNext systemH gap interaction hH hV time current).PosSemidef :=
  positive.mul_mul_conjTranspose_same (flowUnitary systemH gap interaction hH hV time : ControllerJoint ι)

theorem coupledNext_trace (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ) (current : ControllerJoint ι) :
    (coupledNext systemH gap interaction hH hV time current).trace = current.trace :=
  Quantum.unitary_conjugate_trace current (flowUnitary systemH gap interaction hH hV time)

theorem coupledNext_spectralEntropy (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ)
    (current : ControllerJoint ι) (positive : current.PosSemidef) (normalized : current.trace = 1) :
    Quantum.spectralEntropy (coupledNext systemH gap interaction hH hV time current)
      (coupledNext_positive systemH gap interaction hH hV time current positive)
      ((coupledNext_trace systemH gap interaction hH hV time current).trans normalized) =
      Quantum.spectralEntropy current positive normalized :=
  Quantum.spectralEntropy_unitary_conjugation current positive normalized
    (flowUnitary systemH gap interaction hH hV time)

theorem flowUnitary_zero (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) :
    flowUnitary systemH gap interaction hH hV 0 = 1 := by
  apply Subtype.ext
  exact (congrArg (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).symm
    (sourceFlow systemH gap interaction hH hV).exponential_group.zero_slice).trans
      (map_one (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).symm)

theorem flowUnitary_add (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time next : ℝ) :
    flowUnitary systemH gap interaction hH hV (time + next) =
      flowUnitary systemH gap interaction hH hV time * flowUnitary systemH gap interaction hH hV next := by
  apply Subtype.ext
  change (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).symm _ = _
  rw [(sourceFlow systemH gap interaction hH hV).exponential_group.addSlice time next, map_mul]
  rfl

theorem coupledNext_zero (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (current : ControllerJoint ι) :
    coupledNext systemH gap interaction hH hV 0 current = current := by
  simp [coupledNext, flowUnitary_zero]

/-- The second action consumes the first complete target, including controller backreaction. -/
theorem coupledNext_add (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time next : ℝ)
    (current : ControllerJoint ι) :
    coupledNext systemH gap interaction hH hV (time + next) current =
      coupledNext systemH gap interaction hH hV time
        (coupledNext systemH gap interaction hH hV next current) := by
  simp only [coupledNext, flowUnitary_add, Unitary.conjStarAlgAut_mul_apply]

theorem observable_commutes_with_flow (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ)
    (observable : ControllerJoint ι) (commutes : Commute observable (totalHamiltonian systemH gap interaction)) :
    Commute observable (flowUnitary systemH gap interaction hH hV time : ControllerJoint ι) := by
  apply Commute.of_map (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).injective
  change Commute (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ) observable)
    (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)
      ((Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ)).symm _))
  rw [StarAlgEquiv.apply_symm_apply]
  exact (((commutes.map (Matrix.toEuclideanCLM (n := ι × Fin 2) (𝕜 := ℂ))).smul_right
    (-Complex.I)).smul_right (time : ℂ)).exp_right

theorem energy_of_commuting_observable (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ)
    (observable current : ControllerJoint ι)
    (commutes : Commute observable (totalHamiltonian systemH gap interaction)) :
    Collision.energy observable (coupledNext systemH gap interaction hH hV time current) =
      Collision.energy observable current := by
  have commute := observable_commutes_with_flow systemH gap interaction hH hV time observable commutes
  have stationary : Unitary.conjStarAlgAut ℂ _ (flowUnitary systemH gap interaction hH hV time) observable =
      observable := by
    rw [Unitary.conjStarAlgAut_apply, ← commute.eq, Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem (flowUnitary systemH gap interaction hH hV time).property, Matrix.mul_one]
  have same := Work.Capacity.energy_unitary_conjugation observable current
    (flowUnitary systemH gap interaction hH hV time)
  rw [stationary] at same
  exact same

theorem totalEnergy_conserved (systemH : Matrix ι ι ℂ) (gap : ℝ) (interaction : ControllerJoint ι)
    (hH : systemH.IsHermitian) (hV : interaction.IsHermitian) (time : ℝ) (current : ControllerJoint ι) :
    Collision.energy (totalHamiltonian systemH gap interaction)
      (coupledNext systemH gap interaction hH hV time current) =
      Collision.energy (totalHamiltonian systemH gap interaction) current :=
  energy_of_commuting_observable systemH gap interaction hH hV time _ current (Commute.refl _)

end

end LAlanine40K2025.Thermal.Powered.Dynamics
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
