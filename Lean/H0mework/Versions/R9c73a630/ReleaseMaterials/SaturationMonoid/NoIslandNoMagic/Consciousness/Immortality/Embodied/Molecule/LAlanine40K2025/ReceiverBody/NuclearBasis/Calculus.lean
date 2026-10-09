import H0mework.Chemistry.LAlanineRefinementDensity.GaussianModel

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
open BasinRefinement.SourceGaussianModel
noncomputable section

/-- Read the original primitive at a real centre, keeping its weight, exponent and powers. -/
def centredValue (term : Term) (jet : MultiIndex) (centre x : Point) : ℝ :=
  value term jet (fun k => x k-centre k+(term.centre k : ℝ))

theorem centred_value_formula (term : Term) (jet : MultiIndex) (centre x : Point) :
    centredValue term jet centre x=(term.weight : ℝ)*
      factor term.exponent (term.powers 0) (jet 0) (x 0-centre 0)*
      factor term.exponent (term.powers 1) (jet 1) (x 1-centre 1)*
      factor term.exponent (term.powers 2) (jet 2) (x 2-centre 2) := by
  simp only [centredValue,value,add_sub_cancel_right]

theorem centred_value_original (term : Term) (jet : MultiIndex) (x : Point) :
    centredValue term jet (fun k => (term.centre k : ℝ)) x=value term jet x := by
  simp only [centredValue,sub_add_cancel]

theorem centred_value_derivative (term : Term) (jet : MultiIndex) (centre : ℝ → Point)
    (speed : Point) (t : ℝ) (x : Point)
    (motion : ∀ k, HasDerivAt (fun time => centre time k) (speed k) t) :
    HasDerivAt (fun time => centredValue term jet (centre time) x)
      (-(∑ k : Fin 3, speed k*centredValue term (raise jet k) (centre t) x)) t := by
  have each (k : Fin 3) : HasDerivAt
      (fun time => factor term.exponent (term.powers k) (jet k) (x k-centre time k))
      (factor term.exponent (term.powers k) (jet k+1) (x k-centre t k)*(-speed k)) t := by
    simpa only [Function.comp_def,zero_sub,Pi.sub_apply] using!
      (factor_hasDerivAt term.exponent (term.powers k) (jet k) (x k-centre t k)).comp t
        ((hasDerivAt_const t (x k)).sub (motion k))
  have composed := (((each 0).const_mul (term.weight : ℝ)).mul (each 1)).mul (each 2)
  simp only [centred_value_formula]
  convert! composed using 1
  simp [Fin.sum_univ_three,raise,Function.update]

  ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.NuclearBasis
