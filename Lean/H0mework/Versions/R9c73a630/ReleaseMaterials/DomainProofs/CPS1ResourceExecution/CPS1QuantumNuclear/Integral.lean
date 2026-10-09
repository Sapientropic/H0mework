import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Contract
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearCoulomb.AttractionFTC

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1QuantumNuclear
noncomputable section
open CPS1ElectronicSource
open MeasureTheory
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open BasinRefinement SourceGaussianModel ReceiverBody.NuclearCoulomb

abbrev Point := CPS1ElectronicSource.Point

theorem orbital_centred (centre : Point) (mode : Nat) (jet : MultiIndex) (x : Point) :
    orbitalValue centre mode jet x = (ReceiverBody.NuclearBasis.centredValue (primitive mode) jet centre x : ℂ) := by
  simp only [orbitalValue,SourceGaussianModel.orbital,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,ReceiverBody.NuclearBasis.centredValue]
  apply congrArg (fun value : ℝ => (value : ℂ))
  apply congrArg (SourceGaussianModel.value (primitive mode) jet)
  funext axis
  simp only [Pi.sub_apply,primitive,Pi.zero_apply,Rat.cast_zero,add_zero]

theorem centred_translate (term : Term) (jet : MultiIndex) (centre shift x : Point) :
    ReceiverBody.NuclearBasis.centredValue term jet centre (x+shift) =
      ReceiverBody.NuclearBasis.centredValue term jet (centre-shift) x := by
  have coordinate (axis : Fin 3) : x axis+shift axis-centre axis = x axis-(centre axis-shift axis) := by ring
  simp only [ReceiverBody.NuclearBasis.centred_value_formula,Pi.add_apply,Pi.sub_apply,coordinate]

theorem primitive_integral_relative (centre : Point) (left right : Nat) (nucleus : Point) :
    (∫ x : Point, (SourceCoulomb.kernel (x-nucleus) : ℂ) *
      star (orbitalValue centre left 0 x) * orbitalValue centre right 0 x) =
      (primitiveAttraction (primitive left) (primitive right) 0 0 (centre-nucleus) (centre-nucleus) : ℂ) := by
  let field : Point → ℝ := fun x =>
    ReceiverBody.NuclearBasis.centredValue (primitive left) 0 centre x *
      ReceiverBody.NuclearBasis.centredValue (primitive right) 0 centre x * SourceCoulomb.kernel (x-nucleus)
  have actual : (fun x : Point => (SourceCoulomb.kernel (x-nucleus) : ℂ) *
      star (orbitalValue centre left 0 x) * orbitalValue centre right 0 x) = fun x => (field x : ℂ) := by
    funext x
    rw [orbital_centred,orbital_centred]
    simp only [field,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_mul]
    ring
  have rebased : (fun x => field (x+nucleus)) =
      attractionIntegrand (primitive left) (primitive right) 0 0 (centre-nucleus) (centre-nucleus) := by
    funext x
    simp only [field,attractionIntegrand,centred_translate,add_sub_cancel_right]
  have translated : (∫ x : Point, field (x+nucleus)) = ∫ x : Point, field x := by
    simpa only [sub_neg_eq_add] using integral_sub_right_eq_self (μ := (volume : Measure Point)) field (-nucleus)
  rw [actual]
  calc
    (∫ x : Point, (field x : ℂ)) = (((∫ x : Point, field x) : ℝ) : ℂ) :=
      integral_complex_ofReal (μ := (volume : Measure Point)) (f := field)
    _ = _ := congrArg (fun value : ℝ => (value : ℂ))
      (translated.symm.trans (congrArg (fun f : Point → ℝ => ∫ x : Point, f x) rebased))

theorem normalized_integral_expansion (centre : Point) (n : Nat) (i j : Fin n) (nucleus : Point) :
    nuclearIntegral centre n i j nucleus =
      ∑ b : Fin n, ∑ a : Fin n, (star (coefficients centre n a i) * coefficients centre n b j) *
        (primitiveAttraction (primitive a.val) (primitive b.val) 0 0 (centre-nucleus) (centre-nucleus) : ℂ) := by
  let field (a b : Fin n) (x : Point) : ℂ :=
    (star (coefficients centre n a i) * coefficients centre n b j) *
      ((SourceCoulomb.kernel (x-nucleus) : ℂ) * star (orbitalValue centre a.val 0 x) * orbitalValue centre b.val 0 x)
  have each (a b : Fin n) : Integrable (field a b) := by
    have generated := (primitive_nuclear_integrable centre a.val b.val nucleus 0 0).const_mul
      (star (coefficients centre n a i) * coefficients centre n b j)
    convert! generated using 1
    funext x
    simp only [field,Complex.real_smul]
    ring
  have actual : (fun x : Point => (SourceCoulomb.kernel (x-nucleus) : ℂ) *
      star (spatialValue centre n i 0 x) * spatialValue centre n j 0 x) =
      fun x => ∑ b : Fin n, ∑ a : Fin n, field a b x := by
    funext x
    simp only [spatialValue,star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    dsimp only [field]
    ring
  unfold nuclearIntegral
  rw [actual,integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun a _ => each a b))]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun a _ => each a b)]
  apply Finset.sum_congr rfl
  intro a _
  dsimp only [field]
  rw [integral_const_mul,primitive_integral_relative]

theorem primitive_nuclear_line (left right : Nat) (centre nucleus direction : Point) :
    HasDerivAt (fun time : ℝ => primitiveAttraction (primitive left) (primitive right) 0 0
      (centre-(nucleus+time • direction)) (centre-(nucleus+time • direction)))
      (primitiveAttractionRate (primitive left) (primitive right) 0 0
        (centre-nucleus) (centre-nucleus) (-direction) (-direction)) 0 := by
  have positive (mode : Nat) : 0 < (primitive mode).exponent := by norm_num [primitive]
  have derivative : ∀ time axis, HasDerivAt
      (fun s : ℝ => (centre-(nucleus+s • direction)) axis) ((-direction) axis) time := by
    intro time axis
    simpa only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Pi.neg_apply,id_eq,one_mul] using
      ((((hasDerivAt_id time).mul_const (direction axis)).const_add (nucleus axis)).const_sub (centre axis))
  simpa only [zero_smul,add_zero] using
    primitive_attraction_equation (primitive left) (primitive right) (positive left) (positive right)
      0 0 (fun time => centre-(nucleus+time • direction))
      (fun time => centre-(nucleus+time • direction)) (fun _ => -direction) (fun _ => -direction)
      continuous_const continuous_const derivative derivative 0

end
end CPS1QuantumNuclear
