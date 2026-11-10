import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFreeClockOffAxis
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformClockNonzero
open Polynomial GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalPoleSheet
open SourcePropagationAlgebraicResponse PreparationVacuumPhysicalCharacteristic
open ActualDressedNoether ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedPhysicalRayNumerator ActualDressedUniformRayCoefficients
open ActualDressedUniformMaterialCoefficients
attribute [local irreducible] uniformClockPolynomial dressedKinematicPoint commonClockPolynomial materialDenominator
/-- Nonzero source denominator for the independent external IR scale, damping and sheet-frequency parameters. -/
theorem actual_common_ir_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma s : ℝ) (positive : 0<sigma) :
    MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n)≠0 := by
  let v:=irValues eps sigma s
  let q:=dressedKinematicPoint event ((eps^2:ℝ) • n)
  have clock (lambda : Parameters) :
      MvPolynomial.eval v ((commonClockPolynomial event n).eval lambda)=
        (uniformClockPolynomial q).eval (MvPolynomial.eval v lambda) := by
    exact (eval_map_apply (p:=commonClockPolynomial event n) (MvPolynomial.eval v) lambda).symm.trans
      (congrArg (fun P : ℂ[X]=>P.eval (MvPolynomial.eval v lambda)) (common_clock_polynomial_eval event n eps sigma s))
  have frequency : MvPolynomial.eval v irClock=dampedFourierClock (sourceFrequency eps s) sigma := by
    simp [v,irClock,irValues,dampedFourierClock,sourceFrequency,Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc]
  have damping : MvPolynomial.eval v (MvPolynomial.X 1 : Parameters)=(sigma:ℂ) := by simp [v,irValues]
  have future : (dampedFourierClock (sourceFrequency eps s) sigma).re≠0 := by
    simpa [dampedFourierClock] using positive.ne'
  have first : MvPolynomial.eval v ((commonClockPolynomial event n).eval irClock)≠0 := by
    rw [clock,frequency];exact actual_uniform_clock_off_axis q _ future
  have second : MvPolynomial.eval v ((commonClockPolynomial event n).eval (MvPolynomial.X 1))≠0 := by
    rw [clock,damping];exact actual_uniform_clock_off_axis q (sigma:ℂ) (by simpa using positive.ne')
  simpa only [commonDenominator,map_mul] using
    mul_ne_zero (mul_ne_zero first second) (material_denominator_nonzero event n eps sigma s)
end LowEnergy.GaussComposite.ActualDressedUniformClockNonzero
