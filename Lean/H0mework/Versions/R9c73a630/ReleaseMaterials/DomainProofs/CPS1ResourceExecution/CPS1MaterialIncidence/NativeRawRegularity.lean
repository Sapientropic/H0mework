import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualAmmoniaDynamics
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Coulomb

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

namespace CPS1MaterialIncidence.NativeBodyFunctionProbe
noncomputable section
open CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange NativeAmmoniaDynamics
open MeasureTheory CPS1ElectronicSource
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement
open scoped BigOperators Matrix Topology

private theorem primitive_nuclear_differentiable (left right : Point) (i j : Nat) (nuclear : Point) :
    DifferentiableAt ℝ (fun next => CPS1MolecularFrame.primitiveNuclearIntegral left right i j next 0 0) nuclear := by
  let selected : Point → Fin 3 → Point := fun next => ![left,right,next]
  have selection : DifferentiableAt ℝ selected nuclear := by
    apply differentiableAt_pi.mpr
    intro slot
    fin_cases slot
    · exact differentiableAt_const _
    · exact differentiableAt_const _
    · exact differentiableAt_id
  exact (CPS1Deformation.multicentre_nuclear_hasFDerivAt i j 0 0 (selected nuclear)).differentiableAt.comp
    nuclear selection

private theorem stored_local_integral (n : Nat) (index : Fin n) (centre nuclear : Point) :
    (∫ point : Point, (SourceCoulomb.kernel (point-nuclear) : ℂ)*
      star (spatialValue 0 n index 0 point)*orbitalValue centre 0 0 point) =
      ∑ mode : Fin n, star (coefficients 0 n mode index)*
        CPS1MolecularFrame.primitiveNuclearIntegral 0 centre mode.val 0 nuclear 0 0 := by
  let integrand (mode : Fin n) (point : Point) : ℂ :=
    star (coefficients 0 n mode index)*((SourceCoulomb.kernel (point-nuclear) : ℂ)*
      star (orbitalValue 0 mode.val 0 point)*orbitalValue centre 0 0 point)
  have each (mode : Fin n) : Integrable (integrand mode) := by
    exact (CPS1MolecularFrame.multicentre_nuclear_integrable 0 centre mode.val 0 nuclear 0 0).const_mul _
  have expansion : (fun point : Point => (SourceCoulomb.kernel (point-nuclear) : ℂ)*
      star (spatialValue 0 n index 0 point)*orbitalValue centre 0 0 point) =
      fun point => ∑ mode : Fin n, integrand mode point := by
    funext point
    simp only [spatialValue,star_sum,star_mul,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro mode _
    dsimp only [integrand]
    ring
  rw [expansion,integral_finsetSum _ (fun mode _ => each mode)]
  apply Finset.sum_congr rfl
  intro mode _
  simpa only [integrand,CPS1MolecularFrame.primitiveNuclearIntegral] using integral_const_mul _ _

private theorem local_stored_integral (n : Nat) (index : Fin n) (centre nuclear : Point) :
    (∫ point : Point, (SourceCoulomb.kernel (point-nuclear) : ℂ)*
      star (orbitalValue centre 0 0 point)*spatialValue 0 n index 0 point) =
      ∑ mode : Fin n, coefficients 0 n mode index*
        CPS1MolecularFrame.primitiveNuclearIntegral centre 0 0 mode.val nuclear 0 0 := by
  let integrand (mode : Fin n) (point : Point) : ℂ :=
    coefficients 0 n mode index*((SourceCoulomb.kernel (point-nuclear) : ℂ)*
      star (orbitalValue centre 0 0 point)*orbitalValue 0 mode.val 0 point)
  have each (mode : Fin n) : Integrable (integrand mode) := by
    exact (CPS1MolecularFrame.multicentre_nuclear_integrable centre 0 0 mode.val nuclear 0 0).const_mul _
  have expansion : (fun point : Point => (SourceCoulomb.kernel (point-nuclear) : ℂ)*
      star (orbitalValue centre 0 0 point)*spatialValue 0 n index 0 point) =
      fun point => ∑ mode : Fin n, integrand mode point := by
    funext point
    simp only [spatialValue,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro mode _
    dsimp only [integrand]
    ring
  rw [expansion,integral_finsetSum _ (fun mode _ => each mode)]
  apply Finset.sum_congr rfl
  intro mode _
  simpa only [integrand,CPS1MolecularFrame.primitiveNuclearIntegral] using integral_const_mul _ _

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw}

theorem full_raw_nuclear_differentiable (current : NativeCurrent source) (i j : RawIndex current)
    (spin : Bool) (nuclear : Point) :
    DifferentiableAt ℝ (rawNuclearIntegral current i j spin) nuclear := by
  change DifferentiableAt ℝ (fun next => rawNuclearIntegral current i j spin next) nuclear
  cases i with
  | inl first =>
    cases j with
    | inl second =>
      by_cases a : first.2 = spin <;> by_cases b : second.2 = spin
      · change DifferentiableAt ℝ (fun next => ∫ point : Point, (SourceCoulomb.kernel (point-next) : ℂ)*
          star (if first.2 = spin then spatialValue 0 (electronCount source.nodes+1) first.1 0 point else 0)*
          (if second.2 = spin then spatialValue 0 (electronCount source.nodes+1) second.1 0 point else 0)) nuclear
        simp only [if_pos a,if_pos b]
        exact CPS1PhosphorylExchange.nuclear_integral_differentiable _ _ _ _
      all_goals
        simpa only [rawNuclearIntegral,rawValue,a,b,if_true,if_false,star_zero,mul_zero,zero_mul,integral_zero]
          using (show DifferentiableAt ℝ (fun _ : Point => (0 : ℂ)) nuclear from differentiableAt_const _)
    | inr second =>
      by_cases a : first.2 = spin <;> by_cases b : second.2 = spin
      · have expansion : rawNuclearIntegral current (.inl first) (.inr second) spin =
            fun next => ∑ mode : Fin (electronCount source.nodes+1), star (coefficients 0 _ mode first.1)*
              CPS1MolecularFrame.primitiveNuclearIntegral 0 (Geometry.nucleusPosition (localNode current second))
                mode.val 0 next 0 0 := by
          funext next
          simp only [rawNuclearIntegral,rawValue,if_pos a,if_pos b]
          exact stored_local_integral _ _ _ _
        rw [expansion]
        apply DifferentiableAt.fun_sum
        intro mode _
        exact (primitive_nuclear_differentiable _ _ _ _ _).const_mul _
      all_goals
        simpa only [rawNuclearIntegral,rawValue,a,b,if_true,if_false,star_zero,mul_zero,zero_mul,integral_zero]
          using (show DifferentiableAt ℝ (fun _ : Point => (0 : ℂ)) nuclear from differentiableAt_const _)
  | inr first =>
    cases j with
    | inl second =>
      by_cases a : first.2 = spin <;> by_cases b : second.2 = spin
      · have expansion : rawNuclearIntegral current (.inr first) (.inl second) spin =
            fun next => ∑ mode : Fin (electronCount source.nodes+1), coefficients 0 _ mode second.1*
              CPS1MolecularFrame.primitiveNuclearIntegral (Geometry.nucleusPosition (localNode current first)) 0
                0 mode.val next 0 0 := by
          funext next
          simp only [rawNuclearIntegral,rawValue,if_pos a,if_pos b]
          exact local_stored_integral _ _ _ _
        rw [expansion]
        apply DifferentiableAt.fun_sum
        intro mode _
        exact (primitive_nuclear_differentiable _ _ _ _ _).const_mul _
      all_goals
        simpa only [rawNuclearIntegral,rawValue,a,b,if_true,if_false,star_zero,mul_zero,zero_mul,integral_zero]
          using (show DifferentiableAt ℝ (fun _ : Point => (0 : ℂ)) nuclear from differentiableAt_const _)
    | inr second =>
      by_cases a : first.2 = spin <;> by_cases b : second.2 = spin
      · change DifferentiableAt ℝ (fun next => ∫ point : Point, (SourceCoulomb.kernel (point-next) : ℂ)*
          star (if first.2 = spin then orbitalValue (Geometry.nucleusPosition (localNode current first)) 0 0 point else 0)*
          (if second.2 = spin then orbitalValue (Geometry.nucleusPosition (localNode current second)) 0 0 point else 0)) nuclear
        simp only [if_pos a,if_pos b]
        exact primitive_nuclear_differentiable _ _ _ _ _
      all_goals
        simpa only [rawNuclearIntegral,rawValue,a,b,if_true,if_false,star_zero,mul_zero,zero_mul,integral_zero]
          using (show DifferentiableAt ℝ (fun _ : Point => (0 : ℂ)) nuclear from differentiableAt_const _)


end
end CPS1MaterialIncidence.NativeBodyFunctionProbe
