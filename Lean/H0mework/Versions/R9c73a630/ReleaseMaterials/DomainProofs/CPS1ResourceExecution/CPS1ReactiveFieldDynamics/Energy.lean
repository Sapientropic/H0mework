import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Fock

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix Matrix.Norms.Elementwise
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)

private theorem sum_three_rotate {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (f : a → b → c → ℂ) :
    (∑ x, ∑ y, ∑ z, f x y z) = ∑ z, ∑ x, ∑ y, f x y z := by
  calc
    _ = ∑ x, ∑ z, ∑ y, f x y z := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

private theorem list_sum_finite {a b : Type*} [Fintype b]
    (values : List a) (f : a → b → ℂ) :
    (values.map (fun x => ∑ y, f x y)).sum = ∑ y, (values.map (fun x => f x y)).sum := by
  induction values with
  | nil => simp only [List.map_nil,List.sum_nil,Finset.sum_const_zero]
  | cons head tail ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

private theorem list_mul_sum {a : Type*} (values : List a) (f : a → ℂ) (factor : ℂ) :
    (values.map (fun x => factor * f x)).sum = factor * (values.map f).sum := by
  induction values with
  | nil => simp only [List.map_nil,List.sum_nil,mul_zero]
  | cons head tail ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

/-- The stored first jets supply the kinetic kernel, including raw null relations. -/
theorem kinetic_contraction (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ)
    (i j : state.ElectronIndex) :
    (withOccupation state coefficients).kinetic i j =
      ∑ p, ∑ q, star (coefficients p i) * coefficients q j * rawKinetic state p q := by
  change ((1/(2*state.electronInertia) : ℝ) : ℂ) *
    (∑ axis : Fin 3, inner ℂ
      (∑ p, coefficients p i • (state.primitive p).jet (raise 0 axis))
      (∑ q, coefficients q j • (state.primitive q).jet (raise 0 axis))) = _
  simp only [sum_inner,inner_sum,inner_smul_left,inner_smul_right,
    starRingEnd_apply,Finset.mul_sum,rawKinetic]
  calc
    _ = ∑ p, ∑ axis : Fin 3, ∑ q,
        ((1/(2*state.electronInertia) : ℝ) : ℂ) *
          (star (coefficients p i) * (coefficients q j *
            inner ℂ ((state.primitive p).jet (raise 0 axis))
              ((state.primitive q).jet (raise 0 axis)))) := by
      rw [sum_three_rotate]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro axis _
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro axis _
      ring

theorem attraction_contraction (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ)
    (i j : state.ElectronIndex) :
    (withOccupation state coefficients).attraction i j =
      ∑ p, ∑ q, star (coefficients p i) * coefficients q j * rawAttraction state p q := by
  have nucleus (nuclear : CPS1AtomicDynamics.Body.Node) :
      -(nuclear.particle.charge : ℂ) *
        (∑ spin : Bool, ∑ p, ∑ q, star (coefficients p i) * coefficients q j *
          state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear)) =
        ∑ p, ∑ q, star (coefficients p i) * coefficients q j *
          (-(nuclear.particle.charge : ℂ) *
            ∑ spin : Bool, state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro spin _
    ring
  change (state.nuclei.map (fun nuclear => -(nuclear.particle.charge : ℂ) *
    (∑ spin : Bool, ∑ p, ∑ q, star (coefficients p i) * coefficients q j *
      state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear)))).sum = _
  simp_rw [nucleus,list_sum_finite,list_mul_sum]
  rfl

theorem core_contraction (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ)
    (i j : state.ElectronIndex) :
    (withOccupation state coefficients).kinetic i j +
      (withOccupation state coefficients).attraction i j =
      ∑ p, ∑ q, star (coefficients p i) * coefficients q j * rawCore state p q := by
  rw [kinetic_contraction,attraction_contraction]
  simp only [rawCore,mul_add,Finset.sum_add_distrib]

/-- Both spin sums are the same primitive pair occurrence used by rawTensor. -/
theorem two_body_contraction (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ)
    (i j k l : state.ElectronIndex) :
    (withOccupation state coefficients).twoBody i j k l =
      Polynomial.occupiedTwoBody (rawTensor state) coefficients i j k l := by
  rw [Polynomial.occupiedTwoBody]
  change (∑ spin : Bool, ∑ secondSpin : Bool, ∑ p, ∑ q, ∑ r, ∑ s,
    (star (coefficients p i) * coefficients q k *
      star (coefficients r j) * coefficients s l) *
      state.pairIntegral p q r s spin secondSpin) = _
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro p _
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro q _
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro r _
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro s _
  simp only [rawTensor,Finset.mul_sum]

/-- The actual Snapshot energy equals its full finite occupied contraction. -/
theorem energy_occupied (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    (withOccupation state coefficients).energy =
      CPS1AtomicDynamics.Body.energy state.nuclei +
        Polynomial.occupiedEnergy (rawCore state) (rawTensor state) coefficients := by
  have one : (∑ i, ((withOccupation state coefficients).kinetic i i +
      (withOccupation state coefficients).attraction i i)) =
      ∑ i, ∑ p, ∑ q, star (coefficients p i) * coefficients q i * rawCore state p q := by
    apply Finset.sum_congr rfl
    intro i _
    exact core_contraction state coefficients i i
  have pair : (∑ i, ∑ j, ((withOccupation state coefficients).twoBody i j i j -
      (withOccupation state coefficients).twoBody i j j i)) =
      ∑ i, ∑ j, ∑ p, ∑ q, ∑ r, ∑ s,
        (star (coefficients p i) * coefficients q i *
          star (coefficients r j) * coefficients s j) *
          (rawTensor state p r q s - rawTensor state p r s q) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (congrArg₂ (fun first second : ℂ => first - second)
      (two_body_contraction state coefficients i j i j)
      (two_body_contraction state coefficients i j j i)).trans
        (Polynomial.occupied_direct_exchange (rawTensor state) coefficients i j)
  rw [CPS1ReactiveField.Carried.Snapshot.energy,one,pair,Polynomial.occupiedEnergy]
  change CPS1AtomicDynamics.Body.energy state.nuclei + _ + _ = _
  ring

/-- No symmetry or caller-supplied energy equality is needed for this same-source seam. -/
theorem energy_density (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    (withOccupation state coefficients).energy =
      CPS1AtomicDynamics.Body.energy state.nuclei +
        CPS1Deformation.FiniteVariation.densityEnergy (rawCore state) (rawTensor state)
          (coefficients * coefficients.conjTranspose) := by
  rw [energy_occupied,Polynomial.occupied_energy_eq_density_energy]

theorem actual_energy_continuous (state : Snapshot) :
    Continuous (fun coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ =>
      (withOccupation state coefficients).energy) := by
  simpa only [energy_density] using! continuous_const.add
    (Polynomial.continuous_density_energy (m := state.ElectronIndex) (rawCore state) (rawTensor state))

theorem actual_energy_hasFDerivAt (state : Snapshot)
    (coefficients : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    HasFDerivAt (fun next : Matrix state.PrimitiveIndex state.ElectronIndex ℂ =>
      (withOccupation state next).energy)
      (Polynomial.occupiedDifferential (rawCore state) (rawTensor state) coefficients) coefficients := by
  simpa only [energy_density] using!
    (Polynomial.occupied_hasFDerivAt (rawCore state) (rawTensor state) coefficients).const_add
      (CPS1AtomicDynamics.Body.energy state.nuclei)

/-- The actual stored energy generates the Fock variation from source kernel symmetries. -/
theorem actual_energy_line (state : Snapshot)
    (direction : Matrix state.PrimitiveIndex state.ElectronIndex ℂ) :
    HasDerivAt (fun time : ℝ => (withOccupation state (state.occupied + time • direction)).energy)
      (2 * (Matrix.trace (state.occupied.conjTranspose * rawFock state * direction)).re) 0 := by
  have generated := CPS1Deformation.FiniteVariation.occupied_energy_line
    (rawCore state) (rawTensor state) (tensor_swap state) state.occupied direction
    (raw_fock_hermitian state)
  simpa only [energy_density,rawFock,rawDensity] using
    generated.const_add (CPS1AtomicDynamics.Body.energy state.nuclei)

end
end CPS1ReactiveFieldDynamics
