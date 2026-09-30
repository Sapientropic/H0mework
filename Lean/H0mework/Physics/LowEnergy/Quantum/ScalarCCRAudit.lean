import H0mework.Physics.LowEnergy.Quantum.ScalarCCR

/-! Independent consumers on the actual polynomial domain, including the
nonempty 61-coordinate carrier used by the peripheral scalar phase. -/
set_option autoImplicit false
open SourceScalarCCR

example : position (0 : Fin 61) (1 : BosonSpace (Fin 61)) = MvPolynomial.X 0 := by
  simp [position_apply]

example : momentum (0 : Fin 61) (MvPolynomial.X 0) =
    (-Complex.I) • (1 : BosonSpace (Fin 61)) := by
  simp [momentum_apply]

example : (position (0 : Fin 61) * momentum 0 - momentum 0 * position 0 : BosonEnd (Fin 61))
    (1 : BosonSpace (Fin 61)) = Complex.I • (1 : BosonSpace (Fin 61)) := by
  have identity := LinearMap.congr_fun (position_momentum (0 : Fin 61) 0)
    (1 : BosonSpace (Fin 61))
  simpa using identity

example : position (0 : Fin 61) * momentum 1 - momentum 1 * position 0 = 0 := by
  simpa using position_momentum (0 : Fin 61) 1

#print axioms SourceScalarCCR.position_apply
#print axioms SourceScalarCCR.momentum_apply
#print axioms SourceScalarCCR.position_position
#print axioms SourceScalarCCR.position_momentum
#print axioms SourceScalarCCR.pderiv_commute
#print axioms SourceScalarCCR.momentum_momentum
#check SourceScalarCCR.position_momentum
#check SourceScalarCCR.momentum_momentum
