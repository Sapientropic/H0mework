import H0mework.Physics.LowEnergy.LightCausal.Rate

/-! The original theta pole residue is real because both its source numerator and derivative are evaluated on the generated real branch. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
open LightSpace LightModes Stage9C.Material.SpinPair
noncomputable section

def axialWaveReal (q : ℝ) : ℝ := q*Real.sqrt ((sourceRoot .axialPhase).root (q^2))

theorem axialWaveReal_cast (q : ℝ) : (axialWaveReal q : ℂ)=sourceWave .axialPhase q := by
  simp [axialWaveReal,sourceWave,sourcePower]

def axialDerivativeReal (q : ℝ) : ℝ :=
  (squaredPolynomial .axialPhase (q^2)).derivative.eval ((axialWaveReal q)^2)*(2*axialWaveReal q)

theorem axialDerivativeReal_cast (q : ℝ) : (axialDerivativeReal q : ℂ)=axialTimeDerivative q := by
  rw [axialTimeDerivative,← axialWaveReal_cast,complexSquaredPolynomial,Polynomial.derivative_map,
    ← Complex.ofReal_pow]
  change Complex.ofRealHom (axialDerivativeReal q)=
    ((squaredPolynomial .axialPhase (q^2)).derivative.map Complex.ofRealHom).eval
      (Complex.ofRealHom ((axialWaveReal q)^2))*(2*Complex.ofRealHom (axialWaveReal q))
  rw [Polynomial.eval_map_apply]
  simp only [axialDerivativeReal,map_mul,map_ofNat]

def metricResidueReal (momentum : Fin 3 → ℝ) : ℝ :=
  let q := radialMomentum momentum
  lapse*spinScale*((Real.sqrt 30/3125)*metricRaw ((axialWaveReal q)^2) (q^2)/axialDerivativeReal q)

theorem metricResidueReal_cast (momentum : Fin 3 → ℝ) : (metricResidueReal momentum : ℂ)=metricResidue momentum := by
  simp only [metricResidue,metricNumerator,← axialWaveReal_cast,← Complex.ofReal_pow,metric_raw_cast,
    ← axialDerivativeReal_cast,metricResidueReal,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]

theorem metricResidue_real (momentum : Fin 3 → ℝ) : star (metricResidue momentum)=metricResidue momentum := by
  rw [← metricResidueReal_cast]
  exact Complex.conj_ofReal _

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightCausal
