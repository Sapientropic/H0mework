import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Basis
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveFieldDynamics.Polynomial
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Symmetries

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics
noncomputable section
open CPS1ElectronicSource InnerProductSpace
open scoped BigOperators InnerProductSpace Matrix

-- All kernels retain the actual stored primitive expansion and nuclear rows.
def rawKinetic (state : Snapshot) (p q : state.PrimitiveIndex) : ℂ :=
  ((1/(2*state.electronInertia) : ℝ) : ℂ) *
    ∑ axis : Fin 3, inner ℂ ((state.primitive p).jet
      (SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel.raise 0 axis))
      ((state.primitive q).jet
      (SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel.raise 0 axis))
def rawAttraction (state : Snapshot) (p q : state.PrimitiveIndex) : ℂ :=
  (state.nuclei.map (fun nuclear => -(nuclear.particle.charge : ℂ) *
    (∑ spin : Bool, state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear)))).sum

def rawCore (state : Snapshot) : Matrix state.PrimitiveIndex state.PrimitiveIndex ℂ :=
  fun p q => rawKinetic state p q + rawAttraction state p q

def rawTensor (state : Snapshot) (p q r s : state.PrimitiveIndex) : ℂ :=
  ∑ spin : Bool, ∑ secondSpin : Bool, state.pairIntegral p r q s spin secondSpin

def rawDensity (state : Snapshot) : Matrix state.PrimitiveIndex state.PrimitiveIndex ℂ :=
  state.occupied * state.occupied.conjTranspose

def rawFock (state : Snapshot) : Matrix state.PrimitiveIndex state.PrimitiveIndex ℂ :=
  CPS1Deformation.FiniteVariation.fock (rawCore state) (rawTensor state) (rawDensity state)

def fullFock (state : Snapshot) : Matrix (BasisIndex state) (BasisIndex state) ℂ :=
  (sourceCoefficient state).conjTranspose * rawFock state * sourceCoefficient state

theorem nuclear_star (state : Snapshot) (p q : state.PrimitiveIndex) (spin : Bool) (nuclear : Point) :
    star (state.nuclearIntegral p q spin nuclear) = state.nuclearIntegral q p spin nuclear := by
  unfold CPS1ReactiveField.Carried.Snapshot.nuclearIntegral
  by_cases present : (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin
  · rw [if_pos present,if_pos ⟨present.2,present.1⟩]
    exact CPS1Deformation.primitive_nuclear_star _ _ _ _ _
  · have absent : ¬ ((state.primitive q).spin = spin ∧ (state.primitive p).spin = spin) :=
      fun same => present ⟨same.2,same.1⟩
    rw [if_neg present,if_neg absent,star_zero]

theorem pair_star (state : Snapshot) (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) :
    star (state.pairIntegral p q r s spin secondSpin) = state.pairIntegral q p s r spin secondSpin := by
  unfold CPS1ReactiveField.Carried.Snapshot.pairIntegral
  by_cases present : (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin ∧
      (state.primitive r).spin = secondSpin ∧ (state.primitive s).spin = secondSpin
  · rw [if_pos present,if_pos ⟨present.2.1,present.1,present.2.2.2,present.2.2.1⟩]
    exact CPS1Deformation.primitive_pair_star _ _ _ _ _ _ _ _
  · have absent : ¬ ((state.primitive q).spin = spin ∧ (state.primitive p).spin = spin ∧
        (state.primitive s).spin = secondSpin ∧ (state.primitive r).spin = secondSpin) :=
      fun same => present ⟨same.2.1,same.1,same.2.2.2,same.2.2.1⟩
    rw [if_neg present,if_neg absent,star_zero]

theorem pair_swap (state : Snapshot) (p q r s : state.PrimitiveIndex) (spin secondSpin : Bool) :
    state.pairIntegral p q r s spin secondSpin = state.pairIntegral r s p q secondSpin spin := by
  unfold CPS1ReactiveField.Carried.Snapshot.pairIntegral
  by_cases present : (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin ∧
      (state.primitive r).spin = secondSpin ∧ (state.primitive s).spin = secondSpin
  · rw [if_pos present,if_pos ⟨present.2.2.1,present.2.2.2,present.1,present.2.1⟩]
    exact CPS1Deformation.primitive_pair_swap _ _ _ _ _ _ _ _
  · have absent : ¬ ((state.primitive r).spin = secondSpin ∧ (state.primitive s).spin = secondSpin ∧
        (state.primitive p).spin = spin ∧ (state.primitive q).spin = spin) :=
      fun same => present ⟨same.2.2.1,same.2.2.2,same.1,same.2.1⟩
    rw [if_neg present,if_neg absent]

theorem tensor_star (state : Snapshot) (p q r s : state.PrimitiveIndex) :
    star (rawTensor state p q r s) = rawTensor state r s p q := by
  simp only [rawTensor,star_sum,pair_star]

theorem tensor_swap (state : Snapshot) (p q r s : state.PrimitiveIndex) :
    rawTensor state p q r s = rawTensor state q p s r := by
  simp only [rawTensor,pair_swap]
  rw [Finset.sum_comm]

theorem kinetic_star (state : Snapshot) (p q : state.PrimitiveIndex) :
    star (rawKinetic state p q) = rawKinetic state q p := by
  unfold rawKinetic
  simp only [Complex.star_def,map_mul,map_sum,Complex.conj_ofReal]
  apply congrArg (fun z : ℂ => ((1/(2*state.electronInertia) : ℝ) : ℂ)*z)
  apply Finset.sum_congr rfl
  intro axis _
  exact inner_conj_symm _ _

theorem core_hermitian (state : Snapshot) : (rawCore state).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro p q
  have attraction : star (rawAttraction state q p) = rawAttraction state p q := by
    unfold rawAttraction
    have nodes (list : List CPS1AtomicDynamics.Body.Node) :
        star (list.map (fun nuclear => -(nuclear.particle.charge : ℂ) *
          (∑ spin : Bool, state.nuclearIntegral q p spin (Geometry.nucleusPosition nuclear)))).sum =
        (list.map (fun nuclear => -(nuclear.particle.charge : ℂ) *
          (∑ spin : Bool, state.nuclearIntegral p q spin (Geometry.nucleusPosition nuclear)))).sum := by
      induction list with
      | nil => simp only [List.map_nil,List.sum_nil,star_zero]
      | cons node rest previous =>
        simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_neg,
          star_intCast,star_sum,nuclear_star,previous]
        ring
    exact nodes state.nuclei
  simp only [rawCore,star_add,kinetic_star,attraction]

theorem raw_fock_hermitian (state : Snapshot) : (rawFock state).IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i k
  have coreStar : star (rawCore state k i) = rawCore state i k := (core_hermitian state).apply i k
  have densityStar (j l : state.PrimitiveIndex) : star (rawDensity state l j) = rawDensity state j l :=
    (Matrix.isHermitian_mul_conjTranspose_self state.occupied).apply j l
  simp only [rawFock,CPS1Deformation.FiniteVariation.fock,CPS1Deformation.FiniteVariation.interaction,
    star_add,star_sum,star_mul,star_sub,coreStar,densityStar,tensor_star]
  rw [Finset.sum_comm]
  apply congrArg (fun z : ℂ => rawCore state i k+z)
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [tensor_swap state j i k l]
  ring

theorem full_fock_hermitian (state : Snapshot) : (fullFock state).IsHermitian := by
  unfold fullFock
  exact Matrix.isHermitian_conjTranspose_mul_mul _ (raw_fock_hermitian state)

end
end CPS1ReactiveFieldDynamics
