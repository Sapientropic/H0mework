import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ReactiveField.Carried
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deformation.Fields

/-!
Actual Gaussian L² relations preserve every spatial jet. A common translation
preserves a source relation, and differentiation of that zero curve generates
the raised relation. The generated normed source coefficients therefore recover
the same primitive jets, including the kinetic first derivatives.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace CPS1ReactiveFieldDynamics.JetRecovery
noncomputable section
open CPS1ElectronicSource
open scoped BigOperators Matrix
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGaussianModel (raise)
abbrev Primitive := CPS1ReactiveField.Carried.Primitive
variable {ι : Type*} [Fintype ι]

def shiftedJet (source : Primitive) (jet : Fin 3 → Nat) (displacement : Point) : SpinSpace :=
  PiLp.single 2 source.spin (orbitalField (displacement + source.centre) source.mode jet)

def weightedJet (source : ι → Primitive) (weights : ι → ℂ) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ index, weights index • (source index).jet jet

omit [Fintype ι] in
theorem translate_primitive_jet (source : Primitive) (jet : Fin 3 → Nat) (displacement : Point) :
    CPS1Following.translate displacement (source.jet jet) = shiftedJet source jet displacement := by
  change CPS1Following.translate displacement (PiLp.single 2 source.spin _) = _
  rw [CPS1Following.translate, LinearIsometryEquiv.piLpCongrRight_single]
  change (PiLp.single 2 source.spin
    (CPS1Following.spatialTranslate displacement (orbitalField source.centre source.mode jet)) : SpinSpace) = _
  rw [CPS1Following.spatial_translate_primitive]
  rfl

theorem translate_weighted_jet (source : ι → Primitive) (weights : ι → ℂ)
    (jet : Fin 3 → Nat) (displacement : Point) :
    CPS1Following.translate displacement (weightedJet source weights jet) =
      ∑ index, weights index • shiftedJet (source index) jet displacement := by
  simp only [weightedJet, map_sum, map_smul, translate_primitive_jet]

omit [Fintype ι] in
theorem shifted_jet_axis_derivative (source : Primitive) (jet : Fin 3 → Nat) (axis : Fin 3) :
    HasDerivAt (fun time : ℝ => shiftedJet source jet (time • Pi.single axis (1 : ℝ)))
      (-source.jet (raise jet axis)) 0 := by
  have motion : HasDerivAt
      (fun time : ℝ => time • Pi.single axis (1 : ℝ) + source.centre)
      (Pi.single axis (1 : ℝ)) 0 := by
    simpa only [one_smul] using!
      ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single axis (1 : ℝ))).add_const source.centre
  have orbital := CPS1Following.primitive_curve_derivative source.mode jet
    (fun time : ℝ => time • Pi.single axis (1 : ℝ) + source.centre)
    (Pi.single axis (1 : ℝ)) 0 motion
  have spin := (CPS1Following.spinInjection source.spin).hasFDerivAt.comp_hasDerivAt 0 orbital
  simpa [Function.comp_def, shiftedJet, CPS1ReactiveField.Carried.Primitive.jet,
    zero_smul, zero_add, Pi.single_apply, CPS1Following.spin_injection_apply,
    PiLp.single_neg] using spin

/-- A common physical translation differentiates a null relation to its next spatial jet. -/
theorem weighted_jet_raise_zero (source : ι → Primitive) (weights : ι → ℂ)
    (jet : Fin 3 → Nat) (zero : weightedJet source weights jet = 0) (axis : Fin 3) :
    weightedJet source weights (raise jet axis) = 0 := by
  have translated (time : ℝ) :
      (∑ index, weights index • shiftedJet (source index) jet
        (time • Pi.single axis (1 : ℝ))) = 0 := by
    rw [← translate_weighted_jet, zero, map_zero]
  have derivative := HasDerivAt.fun_sum (u := Finset.univ) (fun index _ =>
    (shifted_jet_axis_derivative (source index) jet axis).const_smul (weights index))
  simp only [Pi.smul_apply] at derivative
  have zeroCurve : (fun time : ℝ => ∑ index, weights index • shiftedJet (source index) jet
      (time • Pi.single axis (1 : ℝ))) = (fun _ : ℝ => (0 : SpinSpace)) :=
    funext translated
  rw [zeroCurve] at derivative
  have equal := derivative.unique (hasDerivAt_const (0 : ℝ) (0 : SpinSpace))
  simpa only [smul_neg, Finset.sum_neg_distrib, neg_eq_zero, weightedJet] using equal

theorem weighted_jet_update_zero (source : ι → Primitive) (weights : ι → ℂ)
    (jet : Fin 3 → Nat) (zero : weightedJet source weights jet = 0)
    (axis : Fin 3) (count : Nat) :
    weightedJet source weights (Function.update jet axis (jet axis + count)) = 0 := by
  induction count with
  | zero => simpa only [Nat.add_zero, Function.update_eq_self] using zero
  | succ count previous =>
    have generated := weighted_jet_raise_zero source weights
      (Function.update jet axis (jet axis + count)) previous axis
    simpa only [raise, Function.update_self, Function.update_idem, Nat.add_assoc] using generated

/-- Every finite Gaussian jet factors through the actual zeroth L² source field. -/
theorem weighted_jet_all_zero (source : ι → Primitive) (weights : ι → ℂ)
    (zero : weightedJet source weights 0 = 0) (jet : Fin 3 → Nat) :
    weightedJet source weights jet = 0 := by
  have first := weighted_jet_update_zero source weights 0 zero 0 (jet 0)
  have second := weighted_jet_update_zero source weights
    (Function.update 0 0 (jet 0)) (by simpa only [Pi.zero_apply, zero_add] using first) 1 (jet 1)
  have secondPaid : weightedJet source weights
      (Function.update (Function.update 0 0 (jet 0)) 1 (jet 1)) = 0 := by
    simpa only [Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0), Pi.zero_apply, zero_add] using second
  have third := weighted_jet_update_zero source weights
    (Function.update (Function.update 0 0 (jet 0)) 1 (jet 1)) secondPaid 2 (jet 2)
  have exactJet :
      Function.update (Function.update
        (Function.update (0 : Fin 3 → Nat) 0 (jet 0)) 1 (jet 1)) 2 (jet 2) = jet := by
    funext axis
    fin_cases axis <;> simp
  simpa only [Function.update_of_ne (by decide : (2 : Fin 3) ≠ 1),
    Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0), Pi.zero_apply, zero_add, exactJet] using third

theorem weighted_jet_eq (source : ι → Primitive) (first second : ι → ℂ)
    (same : weightedJet source first 0 = weightedJet source second 0) (jet : Fin 3 → Nat) :
    weightedJet source first jet = weightedJet source second jet := by
  have zero : weightedJet source (fun index => first index - second index) 0 = 0 := by
    simp only [weightedJet, sub_smul, Finset.sum_sub_distrib]
    change weightedJet source first 0 - weightedJet source second 0 = 0
    rw [same, sub_self]
  have generated := weighted_jet_all_zero source _ zero jet
  simpa only [weightedJet, sub_smul, Finset.sum_sub_distrib, sub_eq_zero] using generated

def rawField (source : ι → Primitive) : ι → SpinSpace := fun index => (source index).jet 0

abbrev NormedIndex (source : ι → Primitive) :=
  CPS1MolecularFrame.FiniteNormed.Index (𝕜 := ℂ) (rawField source)

def normedJet (source : ι → Primitive) (index : NormedIndex source) (jet : Fin 3 → Nat) : SpinSpace :=
  ∑ primitive, CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField source)
    primitive index • (source primitive).jet jet

theorem normed_jet_zero (source : ι → Primitive) (index : NormedIndex source) :
    normedJet source index 0 = CPS1MolecularFrame.FiniteNormed.field (𝕜 := ℂ) (rawField source) index :=
  (CPS1MolecularFrame.FiniteNormed.field_synthesis (rawField source) index).symm

theorem normed_jet_expansion (source : ι → Primitive) (primitive : ι) (jet : Fin 3 → Nat) :
    (∑ index, CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source)
      index primitive • normedJet source index jet) =
      weightedJet source (fun p =>
        (CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField source) *
          CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source)) p primitive) jet := by
  simp only [normedJet, weightedJet, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul,
    smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro index _
  rw [mul_comm]

/-- Actual Gaussian differentiation pays raw readback for every generated normed source jet. -/
theorem normed_raw_jet_synthesis (source : ι → Primitive) (primitive : ι) (jet : Fin 3 → Nat) :
    (∑ index, CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source)
      index primitive • normedJet source index jet) = (source primitive).jet jet := by
  classical
  let weights : ι → ℂ := fun p =>
    (CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField source) *
      CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source)) p primitive
  have same : weightedJet source weights 0 = weightedJet source (Pi.single primitive (1 : ℂ)) 0 := by
    change weightedJet source (fun p =>
      (CPS1MolecularFrame.FiniteNormed.coefficients (𝕜 := ℂ) (rawField source) *
        CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source)) p primitive) 0 = _
    rw [← normed_jet_expansion]
    simp only [normed_jet_zero]
    rw [← CPS1MolecularFrame.FiniteNormed.raw_synthesis]
    simp only [rawField, weightedJet, Pi.single_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have generated := weighted_jet_eq source weights (Pi.single primitive (1 : ℂ)) same jet
  rw [normed_jet_expansion]
  simpa only [weights, weightedJet, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using generated

theorem normed_occupied_jet {m : Type*} (source : ι → Primitive) (occupied : Matrix ι m ℂ)
    (slot : m) (jet : Fin 3 → Nat) :
    (∑ index, (CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source) *
      occupied) index slot • normedJet source index jet) =
      ∑ primitive, occupied primitive slot • (source primitive).jet jet := by
  simp only [Matrix.mul_apply, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro primitive _
  calc
    _ = occupied primitive slot •
        (∑ index, CPS1MolecularFrame.FiniteNormed.rawCoordinates (𝕜 := ℂ) (rawField source)
          index primitive • normedJet source index jet) := by
      simp only [Finset.smul_sum, smul_smul]
      apply Finset.sum_congr rfl
      intro index _
      rw [mul_comm]
    _ = _ := by rw [normed_raw_jet_synthesis]

end
end CPS1ReactiveFieldDynamics.JetRecovery
