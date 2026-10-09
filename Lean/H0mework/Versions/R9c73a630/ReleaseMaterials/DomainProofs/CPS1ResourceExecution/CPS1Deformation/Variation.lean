import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Integrals
import Mathlib.Analysis.Calculus.FDeriv.Star

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000

namespace CPS1Deformation.FiniteVariation
noncomputable section
open scoped BigOperators Matrix
variable {n m : Type*} [Fintype n] [Fintype m]

def interaction (tensor : n → n → n → n → ℂ) (i j k l : n) : ℂ :=
  tensor i j k l - tensor i j l k

def fock (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ) (density : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i k => core i k + ∑ j, ∑ l, density l j * interaction tensor i j k l

def densityEnergy (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ) (density : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (core * density)).re + (1/2) *
    (∑ i, ∑ j, ∑ k, ∑ l, density k i * density l j * interaction tensor i j k l).re

def densityRate (occupied direction : Matrix n m ℂ) : Matrix n n ℂ :=
  direction * occupied.conjTranspose + occupied * direction.conjTranspose

omit [Fintype n] [Fintype m] in
theorem occupied_entry_line (occupied direction : Matrix n m ℂ) (i : n) (slot : m) :
    HasDerivAt (fun time : ℝ => (occupied + time • direction) i slot) (direction i slot) 0 := by
  have generated := (hasDerivAt_const (0 : ℝ) (occupied i slot)).add
    ((hasDerivAt_id (0 : ℝ)).smul_const (direction i slot))
  simpa only [Matrix.add_apply,Matrix.smul_apply,one_smul,zero_add] using! generated

omit [Fintype n] in
theorem density_entry_line (occupied direction : Matrix n m ℂ) (i j : n) :
    HasDerivAt (fun time : ℝ =>
      ((occupied + time • direction) * (occupied + time • direction).conjTranspose) i j)
      (densityRate occupied direction i j) 0 := by
  have generated := HasDerivAt.fun_sum (u := Finset.univ) (fun slot _ =>
    (occupied_entry_line occupied direction i slot).mul (occupied_entry_line occupied direction j slot).star)
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,zero_smul,add_zero,densityRate,
    Matrix.add_apply,Finset.sum_add_distrib,Pi.mul_apply,Matrix.zero_apply] using! generated

def densityEnergyRate (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ)
    (density direction : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (core * direction)).re + (1/2) *
    (∑ i, ∑ j, ∑ k, ∑ l,
      (direction k i * density l j + density k i * direction l j) * interaction tensor i j k l).re

theorem density_energy_line (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ)
    (occupied direction : Matrix n m ℂ) :
    HasDerivAt (fun time : ℝ => densityEnergy core tensor
      ((occupied + time • direction) * (occupied + time • direction).conjTranspose))
      (densityEnergyRate core tensor (occupied * occupied.conjTranspose) (densityRate occupied direction)) 0 := by
  have oneBody := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
      (density_entry_line occupied direction k i).const_mul (core i k)))
  have pair := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      HasDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
        HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
          ((density_entry_line occupied direction k i).mul (density_entry_line occupied direction l j)).mul_const
            (interaction tensor i j k l)))))
  have realOne := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) oneBody
  have realPair := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) pair
  simpa only [densityEnergy,densityEnergyRate,Matrix.trace,Matrix.diag,Matrix.mul_apply,
    zero_smul,add_zero,Complex.reCLM_apply,Function.comp_def] using!
      realOne.add (realPair.const_mul (1/2 : ℝ))

omit [Fintype n] in
theorem interaction_pair_swap (tensor : n → n → n → n → ℂ)
    (symmetry : ∀ i j k l, tensor i j k l = tensor j i l k) (i j k l : n) :
    interaction tensor i j k l = interaction tensor j i l k := by
  rw [interaction,interaction,symmetry i j k l,symmetry i j l k]

theorem swapped_density_sum (tensor : n → n → n → n → ℂ)
    (symmetry : ∀ i j k l, tensor i j k l = tensor j i l k)
    (density direction : Matrix n n ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, density k i * direction l j * interaction tensor i j k l) =
      ∑ i, ∑ j, ∑ k, ∑ l, direction k i * density l j * interaction tensor i j k l := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  rw [← interaction_pair_swap tensor symmetry]
  ring

theorem density_energy_rate_fock (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ)
    (symmetry : ∀ i j k l, tensor i j k l = tensor j i l k)
    (density direction : Matrix n n ℂ) :
    densityEnergyRate core tensor density direction = (Matrix.trace (fock core tensor density * direction)).re := by
  have split : (∑ i, ∑ j, ∑ k, ∑ l,
      (direction k i * density l j + density k i * direction l j) * interaction tensor i j k l) =
      (∑ i, ∑ j, ∑ k, ∑ l, direction k i * density l j * interaction tensor i j k l) +
        (∑ i, ∑ j, ∑ k, ∑ l, direction k i * density l j * interaction tensor i j k l) := by
    simp only [add_mul,Finset.sum_add_distrib,swapped_density_sum tensor symmetry]
  rw [densityEnergyRate,split,Complex.add_re]
  have trace : Matrix.trace (fock core tensor density * direction) = Matrix.trace (core * direction) +
      ∑ i, ∑ j, ∑ k, ∑ l, direction k i * density l j * interaction tensor i j k l := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,fock,add_mul,Finset.sum_add_distrib,
      Finset.sum_mul]
    apply congrArg (fun z : ℂ => (∑ i, ∑ k, core i k * direction k i) + z)
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [trace,Complex.add_re]
  ring

theorem density_rate_trace (hamiltonian : Matrix n n ℂ) (occupied direction : Matrix n m ℂ)
    (hermitian : hamiltonian.IsHermitian) :
    (Matrix.trace (hamiltonian * densityRate occupied direction)).re =
      2 * (Matrix.trace (occupied.conjTranspose * hamiltonian * direction)).re := by
  have first : Matrix.trace (hamiltonian * (direction * occupied.conjTranspose)) =
      Matrix.trace (occupied.conjTranspose * hamiltonian * direction) := by
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
  have second : Matrix.trace (hamiltonian * (occupied * direction.conjTranspose)) =
      star (Matrix.trace (occupied.conjTranspose * hamiltonian * direction)) := by
    calc
      _ = Matrix.trace (direction.conjTranspose * hamiltonian * occupied) := by
        rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
      _ = _ := by
        rw [← Matrix.trace_conjTranspose]
        simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hermitian.eq,Matrix.mul_assoc]
  rw [densityRate,Matrix.mul_add,Matrix.trace_add,Complex.add_re,first,second,
    Complex.star_def,Complex.conj_re]
  ring

theorem occupied_energy_line (core : Matrix n n ℂ) (tensor : n → n → n → n → ℂ)
    (symmetry : ∀ i j k l, tensor i j k l = tensor j i l k)
    (occupied direction : Matrix n m ℂ)
    (hermitian : (fock core tensor (occupied * occupied.conjTranspose)).IsHermitian) :
    HasDerivAt (fun time : ℝ => densityEnergy core tensor
      ((occupied + time • direction) * (occupied + time • direction).conjTranspose))
      (2 * (Matrix.trace (occupied.conjTranspose *
        fock core tensor (occupied * occupied.conjTranspose) * direction)).re) 0 := by
  have generated := density_energy_line core tensor occupied direction
  rw [density_energy_rate_fock core tensor symmetry,density_rate_trace _ _ _ hermitian] at generated
  exact generated

end
end CPS1Deformation.FiniteVariation
