import H0mework.Physics.LowEnergyMatterSpace.PerturbedFlow

/-! The genuine interaction propagator returns to the spatial Schrödinger equation and its initial clock. -/
set_option autoImplicit false
open Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section
namespace PerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : PerturbedDevelopment perturbation)

def physicalCurve (epsilon start : ℝ) (initial : MatterL2) (time : ℝ) : MatterL2 :=
  spatialUnitary time (development.curve epsilon start (spatialUnitary (-start) initial) time)

theorem physicalCurve_starts (epsilon start : ℝ) (initial : MatterL2)
    (coupling : |epsilon|≤1) (located : start ∈ Ioo (-development.radius) development.radius) :
    development.physicalCurve epsilon start initial start=initial := by
  rw [physicalCurve,development.starts epsilon start _ coupling located,
    ← spatialUnitary_add,add_neg_cancel,spatialUnitary_zero]

theorem physicalCurve_weak (epsilon start : ℝ) (initial : MatterL2)
    (coupling : |epsilon|≤1) (located : start ∈ Ioo (-development.radius) development.radius)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius)
    (test : Quantum.Generator.domain spatialAction) :
    HasDerivAt (fun t => inner ℂ (test : MatterL2) (development.physicalCurve epsilon start initial t))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian spatialAction test)
          (development.physicalCurve epsilon start initial time)+
        inner ℂ (test : MatterL2) ((-Complex.I*(epsilon : ℂ)) •
          perturbation time (development.physicalCurve epsilon start initial time))) time :=
  perturbed_physical_weak perturbation epsilon time _
    (development.evolves epsilon start _ coupling located time inside) test

theorem physicalCurve_continuousOn (epsilon start : ℝ) (initial : MatterL2)
    (coupling : |epsilon|≤1) (located : start ∈ Ioo (-development.radius) development.radius) :
    ContinuousOn (development.physicalCurve epsilon start initial) (Ioo (-development.radius) development.radius) := by
  have continuousCurve : ContinuousOn (development.curve epsilon start (spatialUnitary (-start) initial))
      (Ioo (-development.radius) development.radius) :=
    fun time inside => (development.evolves epsilon start _ coupling located time inside).continuousAt.continuousWithinAt
  convert! spatialUnitary_joint.comp_continuousOn (continuousOn_id.prodMk continuousCurve) using 1

def physicalUnitary (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (epsilon : ℝ) (coupling : |epsilon|≤1) (start time : ℝ)
    (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius) : MatterL2 ≃ₗᵢ[ℂ] MatterL2 :=
  ((spatialUnitary (-start)).trans
    (development.unitary symmetric epsilon coupling start time atStart atTime)).trans (spatialUnitary time)

@[simp] theorem physicalUnitary_apply (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (epsilon : ℝ) (coupling : |epsilon|≤1) (start time : ℝ)
    (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius) (initial : MatterL2) :
    development.physicalUnitary symmetric epsilon coupling start time atStart atTime initial=
      development.physicalCurve epsilon start initial time := rfl

theorem physicalCurve_compose (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (epsilon : ℝ) (coupling : |epsilon|≤1) (start time middle : ℝ)
    (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius)
    (atMiddle : middle ∈ Ioo (-development.radius) development.radius) (initial : MatterL2) :
    development.physicalCurve epsilon middle (development.physicalCurve epsilon start initial middle) time=
      development.physicalCurve epsilon start initial time := by
  simp only [physicalCurve,← spatialUnitary_add,neg_add_cancel,spatialUnitary_zero]
  rw [development.compose symmetric epsilon coupling start time atStart atTime middle atMiddle]

theorem zeroCoupling (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (start time : ℝ) (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius) (initial : MatterL2) :
    development.curve 0 start initial time=initial := by
  apply perturbed_curve_unique perturbation symmetric 0 development.radius start atStart
    (development.curve 0 start initial) (fun _ => initial)
    (development.evolves 0 start initial (by norm_num) atStart) _
    (development.starts 0 start initial (by norm_num) atStart) atTime
  intro t _
  simpa [interactionGenerator] using hasDerivAt_const t initial

theorem physicalCurve_zeroCoupling (symmetric : ∀ t, IsSelfAdjoint (perturbation t))
    (start time : ℝ) (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius) (initial : MatterL2) :
    development.physicalCurve 0 start initial time=spatialUnitary (time-start) initial := by
  rw [physicalCurve,development.zeroCoupling symmetric start time atStart atTime,
    ← spatialUnitary_add,← sub_eq_add_neg]

theorem zeroPast (past : ∀ t≤0, perturbation t=0) (epsilon : ℝ) (coupling : |epsilon|≤1)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) (before : time≤0)
    (initial : MatterL2) : development.curve epsilon 0 initial time=initial := by
  have atZero : (0 : ℝ) ∈ Ioo (-development.radius) development.radius :=
    ⟨neg_lt_zero.mpr development.positive,development.positive⟩
  have derivative (t : ℝ) (segment : t ∈ Icc time 0) :
      HasDerivAt (development.curve epsilon 0 initial) 0 t := by
    have located : t ∈ Ioo (-development.radius) development.radius :=
      ⟨lt_of_lt_of_le inside.1 segment.1,lt_of_le_of_lt segment.2 development.positive⟩
    simpa [interactionGenerator,heisenberg,past t segment.2] using
      development.evolves epsilon 0 initial coupling atZero t located
  have same := (convex_Icc time 0).norm_image_sub_le_of_norm_deriv_le (C := 0)
    (fun t segment => (derivative t segment).differentiableAt)
    (fun t segment => by simp only [(derivative t segment).deriv,norm_zero,le_refl])
    (left_mem_Icc.mpr before) (right_mem_Icc.mpr before)
  rw [development.starts epsilon 0 initial coupling atZero,zero_mul] at same
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp same)).symm

theorem physicalCurve_zeroPast (past : ∀ t≤0, perturbation t=0) (epsilon : ℝ) (coupling : |epsilon|≤1)
    (time : ℝ) (inside : time ∈ Ioo (-development.radius) development.radius) (before : time≤0)
    (initial : MatterL2) : development.physicalCurve epsilon 0 initial time=spatialUnitary time initial := by
  rw [physicalCurve,neg_zero,spatialUnitary_zero,development.zeroPast past epsilon coupling time inside before]

end PerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
