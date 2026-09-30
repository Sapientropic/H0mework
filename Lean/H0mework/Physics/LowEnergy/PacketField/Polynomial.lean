import H0mework.Physics.LowEnergy.LightInteraction.Normalization

/-! The actual pole numerator has no constant monomial. Dividing its source
radial factor is polynomial and preserves the Fourier reality of every field. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
noncomputable section

structure PoleTerm where
  coefficient : ℝ
  timeDegree : ℕ
  spaceDegree : ℕ
  nonconstant : 0 < timeDegree+spaceDegree

def rawTerm (term : PoleTerm) (time space : ℂ) : ℂ :=
  (term.coefficient : ℂ)*time^term.timeDegree*(Complex.I*space)^term.spaceDegree

def reducedTerm (term : PoleTerm) (timeFactor spaceFactor : ℂ) (radius : ℂ) : ℂ :=
  (term.coefficient : ℂ)*timeFactor^term.timeDegree*(Complex.I*spaceFactor)^term.spaceDegree*
    radius^(term.timeDegree+term.spaceDegree-1)

theorem term_radial_factor (term : PoleTerm) (timeFactor spaceFactor radius : ℂ) :
    rawTerm term (timeFactor*radius) (spaceFactor*radius)=radius*reducedTerm term timeFactor spaceFactor radius := by
  have degree : term.timeDegree+term.spaceDegree=1+(term.timeDegree+term.spaceDegree-1) := by
    have positive := term.nonconstant
    omega
  have power : radius^term.timeDegree*radius^term.spaceDegree=
      radius*radius^(term.timeDegree+term.spaceDegree-1) := by
    rw [← pow_add]
    calc
      _ = radius^(1+(term.timeDegree+term.spaceDegree-1)) := congrArg (fun power : ℕ => radius^power) degree
      _ = _ := by rw [pow_add,pow_one]
  unfold rawTerm reducedTerm
  rw [mul_pow,← mul_assoc Complex.I spaceFactor radius,mul_pow]
  calc
    _ = ((term.coefficient : ℂ)*timeFactor^term.timeDegree*(Complex.I*spaceFactor)^term.spaceDegree)*
        (radius^term.timeDegree*radius^term.spaceDegree) := by ring
    _ = _ := by rw [power]; ring

def rawPolynomial (terms : List PoleTerm) (time space : ℂ) : ℂ :=
  (terms.map (fun term => rawTerm term time space)).sum

def reducedPolynomial (terms : List PoleTerm) (timeFactor spaceFactor radius : ℂ) : ℂ :=
  (terms.map (fun term => reducedTerm term timeFactor spaceFactor radius)).sum

theorem polynomial_radial_factor (terms : List PoleTerm) (timeFactor spaceFactor radius : ℂ) :
    rawPolynomial terms (timeFactor*radius) (spaceFactor*radius)=
      radius*reducedPolynomial terms timeFactor spaceFactor radius := by
  induction terms with
  | nil => simp [rawPolynomial,reducedPolynomial]
  | cons term rest induction =>
      simp only [rawPolynomial,reducedPolynomial,List.map_cons,List.sum_cons] at induction ⊢
      rw [term_radial_factor,induction,mul_add]

theorem rawTerm_reality (term : PoleTerm) (time space : ℝ) :
    (starRingEnd ℂ) (rawTerm term time space)=rawTerm term time (-space) := by
  simp only [rawTerm,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I,neg_mul,mul_neg]

theorem reducedTerm_continuous (term : PoleTerm) :
    Continuous (fun point : ℂ × ℂ × ℂ => reducedTerm term point.1 point.2.1 point.2.2) := by
  unfold reducedTerm
  fun_prop

theorem reducedPolynomial_continuous (terms : List PoleTerm) :
    Continuous (fun point : ℂ × ℂ × ℂ => reducedPolynomial terms point.1 point.2.1 point.2.2) := by
  induction terms with
  | nil => simpa only [reducedPolynomial,List.map_nil,List.sum_nil] using continuous_const (y := (0 : ℂ))
  | cons term rest induction =>
      have generated := (reducedTerm_continuous term).add induction
      change Continuous (fun point : ℂ × ℂ × ℂ => reducedTerm term point.1 point.2.1 point.2.2+
        reducedPolynomial rest point.1 point.2.1 point.2.2) at generated
      simpa only [reducedPolynomial,List.map_cons,List.sum_cons] using generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
