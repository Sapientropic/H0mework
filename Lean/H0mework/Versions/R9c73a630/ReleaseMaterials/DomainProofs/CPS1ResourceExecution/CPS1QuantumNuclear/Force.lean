import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1QuantumNuclear.Derivatives

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators Matrix InnerProductSpace
variable {frame : CPS1Recycling.Frame}

def nucleusMatrix (state : CPS1ElectronicSource.State frame) (position : Point) :
    Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  fun i j => if i.2 = j.2 then
    nuclearIntegral 0 (spatialModes frame state.geometry.originJoint) i.1 j.1 position else 0

def nucleusMatrixRate (state : CPS1ElectronicSource.State frame) (position direction : Point) :
    Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  fun i j => if i.2 = j.2 then
    nuclearRate 0 (spatialModes frame state.geometry.originJoint) i.1 j.1 position direction else 0

def nucleusMatrixGradient (state : CPS1ElectronicSource.State frame) (position : Point) (axis : Fin 3) :
    Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  fun i j => if i.2 = j.2 then
    nuclearGradient 0 (spatialModes frame state.geometry.originJoint) i.1 j.1 position axis else 0

def nucleusEnergyAt (state : CPS1ElectronicSource.State frame) (nucleus : CPS1AtomicDynamics.Body.Node)
    (position : Point) : ℝ :=
  (-(nucleus.particle.charge : ℝ)) * (Matrix.trace (nucleusMatrix state position * state.density)).re

def electronForce (state : CPS1ElectronicSource.State frame) (nucleus : CPS1AtomicDynamics.Body.Node) :
    CPS1AtomicDynamics.Body.Point :=
  WithLp.toLp 2 (fun axis => (nucleus.particle.charge : ℝ) *
    (Matrix.trace (nucleusMatrixGradient state (Geometry.nucleusPosition nucleus) axis * state.density)).re)

def kineticMatrix (state : CPS1ElectronicSource.State frame) :
    Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  fun i j => if i.2=j.2 then kinetic state.geometry i.1 j.1 else 0

def attractionMatrixAt (state : CPS1ElectronicSource.State frame)
    (positions : CPS1AtomicDynamics.Body.Node → Point) :
    Matrix (SpinIndex state.geometry) (SpinIndex state.geometry) ℂ :=
  (state.geometry.nuclei.map (fun nucleus => -(nucleus.particle.charge : ℂ) •
    nucleusMatrix state (positions nucleus))).sum

def exchangeEnergy (state : CPS1ElectronicSource.State frame) : ℝ :=
  (1/2) * (∑ i, ∑ j, ∑ k, ∑ l, state.density k i * state.density l j *
    (twoBody state.geometry i j k l-twoBody state.geometry i j l k)).re

def electronicEnergyAt (state : CPS1ElectronicSource.State frame)
    (positions : CPS1AtomicDynamics.Body.Node → Point) : ℝ :=
  (Matrix.trace (kineticMatrix state * state.density)).re +
    (state.geometry.nuclei.map (fun nucleus => nucleusEnergyAt state nucleus (positions nucleus))).sum +
    exchangeEnergy state

theorem matrix_list_sum_apply {n m : Type*} (matrices : List (Matrix n m ℂ)) (i : n) (j : m) :
    matrices.sum i j = (matrices.map (fun matrix => matrix i j)).sum := by
  induction matrices with
  | nil => rfl
  | cons matrix rest ih =>
    simp only [List.sum_cons,List.map_cons,Matrix.add_apply,ih]

theorem actual_core_split (state : CPS1ElectronicSource.State frame) :
    core state.geometry = kineticMatrix state + attractionMatrixAt state Geometry.nucleusPosition := by
  ext i j
  have entry (nucleus : CPS1AtomicDynamics.Body.Node) :
      (-(nucleus.particle.charge : ℂ) • nucleusMatrix state (Geometry.nucleusPosition nucleus)) i j =
        -(nucleus.particle.charge : ℂ) * (if i.2=j.2 then
          nuclearIntegral 0 (spatialModes frame state.geometry.originJoint) i.1 j.1
            (Geometry.nucleusPosition nucleus) else 0) := rfl
  simp only [core,kineticMatrix,Matrix.add_apply,attractionMatrixAt,matrix_list_sum_apply,List.map_map,
    Function.comp_def,entry]
  by_cases spin : i.2=j.2
  · simp only [if_pos spin,attraction]
  · simp only [if_neg spin,mul_zero,zero_add]
    simp

theorem trace_nuclei (state : CPS1ElectronicSource.State frame) (nuclei : List CPS1AtomicDynamics.Body.Node)
    (positions : CPS1AtomicDynamics.Body.Node → Point) :
    (Matrix.trace ((nuclei.map (fun nucleus => -(nucleus.particle.charge : ℂ) •
      nucleusMatrix state (positions nucleus))).sum * state.density)).re =
      (nuclei.map (fun nucleus => nucleusEnergyAt state nucleus (positions nucleus))).sum := by
  induction nuclei with
  | nil => simp only [List.map_nil,List.sum_nil,Matrix.zero_mul,Matrix.trace_zero,Complex.zero_re]
  | cons nucleus rest ih =>
    simp only [List.map_cons,List.sum_cons,Matrix.add_mul,Matrix.trace_add,Complex.add_re,ih,
      Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul,nucleusEnergyAt,Complex.mul_re,Complex.neg_re,
      Complex.intCast_re,Complex.intCast_im,zero_mul,sub_zero,neg_mul]

theorem original_electronic_energy (state : CPS1ElectronicSource.State frame) :
    electronicEnergyAt state Geometry.nucleusPosition = electronicEnergy state.geometry state.density := by
  unfold electronicEnergyAt electronicEnergy exchangeEnergy
  rw [actual_core_split,Matrix.add_mul,Matrix.trace_add,Complex.add_re]
  rw [attractionMatrixAt,trace_nuclei]

theorem matrix_nuclear_line (state : CPS1ElectronicSource.State frame) (position direction : Point)
    (i j : SpinIndex state.geometry) :
    HasDerivAt (fun time : ℝ => nucleusMatrix state (position+time • direction) i j)
      (nucleusMatrixRate state position direction i j) 0 := by
  by_cases spin : i.2 = j.2
  · simp only [nucleusMatrix,nucleusMatrixRate,if_pos spin]
    exact normalized_nuclear_line 0 _ i.1 j.1 position direction
  · simp only [nucleusMatrix,nucleusMatrixRate,if_neg spin]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem nucleus_trace_line (state : CPS1ElectronicSource.State frame) (position direction : Point) :
    HasDerivAt (fun time : ℝ => Matrix.trace (nucleusMatrix state (position+time • direction) * state.density))
      (Matrix.trace (nucleusMatrixRate state position direction * state.density)) 0 := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun j _ =>
    (matrix_nuclear_line state position direction i j).mul_const (state.density j i)))

theorem rate_matrix_components (state : CPS1ElectronicSource.State frame) (position direction : Point) :
    nucleusMatrixRate state position direction =
      ∑ axis : Fin 3, (direction axis : ℂ) • nucleusMatrixGradient state position axis := by
  apply Matrix.ext
  intro i j
  change nucleusMatrixRate state position direction i j =
    ∑ axis : Fin 3, (direction axis : ℂ) * nucleusMatrixGradient state position axis i j
  by_cases spin : i.2 = j.2
  · simp only [nucleusMatrixRate,nucleusMatrixGradient,if_pos spin]
    exact nuclear_rate_linear 0 _ i.1 j.1 position direction
  · simp only [nucleusMatrixRate,nucleusMatrixGradient,if_neg spin,mul_zero,Finset.sum_const_zero]

theorem trace_rate_components (state : CPS1ElectronicSource.State frame) (position direction : Point) :
    Matrix.trace (nucleusMatrixRate state position direction * state.density) =
      ∑ axis : Fin 3, (direction axis : ℂ) *
        Matrix.trace (nucleusMatrixGradient state position axis * state.density) := by
  rw [rate_matrix_components,Matrix.sum_mul,Matrix.trace_sum]
  simp only [Matrix.smul_mul,Matrix.trace_smul,smul_eq_mul]

theorem electron_force_work (state : CPS1ElectronicSource.State frame) (nucleus : CPS1AtomicDynamics.Body.Node)
    (direction : CPS1AtomicDynamics.Body.Point) :
    inner ℝ (electronForce state nucleus) direction =
      (nucleus.particle.charge : ℝ) *
        (Matrix.trace (nucleusMatrixRate state (Geometry.nucleusPosition nucleus)
          (fun axis => direction axis) * state.density)).re := by
  rw [trace_rate_components]
  simp only [electronForce,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,Complex.re_sum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,star_trivial]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro axis _
  ring

theorem nucleus_energy_line (state : CPS1ElectronicSource.State frame) (nucleus : CPS1AtomicDynamics.Body.Node)
    (direction : CPS1AtomicDynamics.Body.Point) :
    HasDerivAt (fun time : ℝ => nucleusEnergyAt state nucleus
        (Geometry.nucleusPosition nucleus+time • (fun axis => direction axis)))
      (-inner ℝ (electronForce state nucleus) direction) 0 := by
  have complex := nucleus_trace_line state (Geometry.nucleusPosition nucleus) (fun axis => direction axis)
  have real := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) complex
  have paid := real.const_mul (-(nucleus.particle.charge : ℝ))
  rw [electron_force_work]
  simpa only [nucleusEnergyAt,Complex.reCLM_apply,Function.comp_def,neg_mul] using! paid

theorem electronic_energy_line (state : CPS1ElectronicSource.State frame)
    (direction : CPS1AtomicDynamics.Charged.Address → CPS1AtomicDynamics.Body.Point) :
    HasDerivAt (fun time : ℝ => electronicEnergyAt state (fun nucleus =>
      Geometry.nucleusPosition nucleus+time • (fun axis => direction nucleus.particle.address axis)))
      (-(state.geometry.nuclei.map (fun nucleus =>
        inner ℝ (electronForce state nucleus) (direction nucleus.particle.address))).sum) 0 := by
  have each := CPS1AtomicDynamics.Field.list_sum_derivative state.geometry.nuclei
    (fun nucleus time => nucleusEnergyAt state nucleus
      (Geometry.nucleusPosition nucleus+time • (fun axis => direction nucleus.particle.address axis)))
    (fun nucleus => -inner ℝ (electronForce state nucleus) (direction nucleus.particle.address))
    (fun nucleus _ => nucleus_energy_line state nucleus (direction nucleus.particle.address))
  have paid := (each.const_add (Matrix.trace (kineticMatrix state * state.density)).re).add_const (exchangeEnergy state)
  simpa only [electronicEnergyAt,CPS1AtomicDynamics.Field.list_sum_neg] using! paid

def nuclearForce (state : CPS1ElectronicSource.State frame) (nucleus : CPS1AtomicDynamics.Body.Node) :
    CPS1AtomicDynamics.Body.Point :=
  CPS1AtomicDynamics.Body.force nucleus state.geometry.nuclei + electronForce state nucleus

def nuclearPotentialAt (state : CPS1ElectronicSource.State frame)
    (positions : CPS1AtomicDynamics.Body.Node → Point) : ℝ :=
  CPS1AtomicDynamics.Body.potential (state.geometry.nuclei.map (fun nucleus =>
    {nucleus with row := {nucleus.row with position := euclideanPoint (positions nucleus)}}))

def spatialEnergyAt (state : CPS1ElectronicSource.State frame)
    (positions : CPS1AtomicDynamics.Body.Node → Point) : ℝ :=
  (state.geometry.nuclei.map (fun nucleus =>
    CPS1AtomicDynamics.Coulomb.kinetic nucleus.row.inertia nucleus.row.momentum)).sum +
      nuclearPotentialAt state positions + electronicEnergyAt state positions

theorem original_total_energy (state : CPS1ElectronicSource.State frame) :
    spatialEnergyAt state Geometry.nucleusPosition = state.energy := by
  have same (nucleus : CPS1AtomicDynamics.Body.Node) :
      {nucleus with row := {nucleus.row with position := euclideanPoint (Geometry.nucleusPosition nucleus)}} = nucleus := rfl
  have mapped : state.geometry.nuclei.map (fun nucleus => nucleus) = state.geometry.nuclei := List.map_id _
  simp only [spatialEnergyAt,nuclearPotentialAt,same,mapped,original_electronic_energy,
    CPS1ElectronicSource.State.energy,totalEnergy,Geometry.nuclearEnergy,CPS1AtomicDynamics.Body.energy,
    CPS1AtomicDynamics.Body.kinetic]

theorem source_nuclear_energy_line (state : CPS1ElectronicSource.State frame)
    (unique : (state.geometry.nuclei.map (fun node => node.particle.address)).Nodup)
    (separated : CPS1AtomicDynamics.Body.ready state.geometry.nuclei)
    (direction : CPS1AtomicDynamics.Charged.Address → CPS1AtomicDynamics.Body.Point) :
    HasDerivAt (fun time : ℝ => spatialEnergyAt state (fun nucleus =>
      Geometry.nucleusPosition nucleus+time • (fun axis => direction nucleus.particle.address axis)))
      (-(state.geometry.nuclei.map (fun nucleus =>
        inner ℝ (nuclearForce state nucleus) (direction nucleus.particle.address))).sum) 0 := by
  have nuclear := CPS1AtomicDynamics.Field.potential_line_derivative state.geometry.nuclei unique separated direction
  have electronic := electronic_energy_line state direction
  have paid := ((nuclear.const_add (state.geometry.nuclei.map (fun nucleus =>
    CPS1AtomicDynamics.Coulomb.kinetic nucleus.row.inertia nucleus.row.momentum)).sum).add electronic)
  have same : (fun time : ℝ => spatialEnergyAt state (fun nucleus =>
      Geometry.nucleusPosition nucleus+time • (fun axis => direction nucleus.particle.address axis))) =
      fun time => (state.geometry.nuclei.map (fun nucleus =>
        CPS1AtomicDynamics.Coulomb.kinetic nucleus.row.inertia nucleus.row.momentum)).sum +
        CPS1AtomicDynamics.Body.potential (state.geometry.nuclei.map (CPS1AtomicDynamics.Field.perturb direction time)) +
        electronicEnergyAt state (fun nucleus => Geometry.nucleusPosition nucleus+
          time • (fun axis => direction nucleus.particle.address axis)) := rfl
  rw [same]
  have combined : (state.geometry.nuclei.map (fun nucleus =>
      inner ℝ (nuclearForce state nucleus) (direction nucleus.particle.address))).sum =
      (state.geometry.nuclei.map (fun nucleus => inner ℝ
        (CPS1AtomicDynamics.Body.force nucleus state.geometry.nuclei) (direction nucleus.particle.address))).sum +
      (state.geometry.nuclei.map (fun nucleus => inner ℝ
        (electronForce state nucleus) (direction nucleus.particle.address))).sum := by
    simp only [nuclearForce,inner_add_left,List.sum_map_add]
  rw [combined,neg_add]
  exact paid

end
end CPS1QuantumNuclear
