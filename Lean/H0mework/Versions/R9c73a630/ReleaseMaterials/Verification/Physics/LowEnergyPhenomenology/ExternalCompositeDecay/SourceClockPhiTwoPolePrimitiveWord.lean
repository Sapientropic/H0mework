import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiOriginalNormalizerRadialDebit
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiDilationPrimitive
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.OriginalRPrimitiveDifference
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory SourceQuantumConfigurationHilbert
open SourceClockPhiNormalizedScalarBudget SourceResolventBandLimit
open ClockPhiHeatCorrectedCovarianceSource SourceScalarDoubleCurrent
open FirstCurrentAdmissibleElectric FirstCurrentWholeCarrier FirstCurrentWholeVariance
open FirstCurrentClockPrimitive FirstCurrentClockPrimitiveSquare FirstCurrentDilationPrimitive
open FirstCurrentJointBudget OriginalRCommutatorSource SourceLocalizedInverseFormPayment
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev K(s:ℝ)(hs:0<s)(x:ℝ×ℝ):End:=correctedCompleteCore s hs x.1 x.2
attribute [local irreducible] sourcePair embed diagonalAction positivePrimitive correctedCompleteCore normalizedState normalizedForcing
private theorem pair_add_l(f g h:QuantumTest):sourcePair (f+g) h=sourcePair f h+sourcePair g h:=by
  simp only [sourcePair,map_add,inner_add_left]

def actualPrimitiveCommutator(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(w:QuantumTest):QuantumTest:=
  diagonalAction (K s hs x w)-K s hs x (diagonalAction w)

/-- Both genuine poles share exactly one full H0 clock commutator. -/
theorem actual_two_pole_clock_source(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(z:ℂ)(w f:QuantumTest):
    let b:=clockSourcePair s hs x (w,f)
    b.2=K s hs x f+actualPrimitiveCommutator s hs x w ∧
    oppositeForcing z b.1 b.2=K s hs x (oppositeForcing z w f)+actualPrimitiveCommutator s hs x w:=by
  dsimp only
  have hb:(clockSourcePair s hs x (w,f)).2=K s hs x f+actualPrimitiveCommutator s hs x w:=by
    simp only [clockSourcePair,bracket,Module.End.mul_apply,LinearMap.sub_apply,actualPrimitiveCommutator]
  refine ⟨hb,?_⟩
  rw [oppositeForcing,hb]
  change K s hs x f+actualPrimitiveCommutator s hs x w+(2*(z.im:ℂ)*Complex.I) • K s hs x w=
    K s hs x (f+(2*(z.im:ℂ)*Complex.I) • w)+actualPrimitiveCommutator s hs x w
  simp only [map_add,map_smul]
  module

/-- The complete Pplus-weighted commutator square cancels before any estimate. Its surviving work is a single ordered first-H0 pairing with the original Pplus current. -/
theorem actual_two_pole_primitive_clock_difference(s:ℝ)(hs:0<s)(x:ℝ×ℝ)(z:ℂ)(w f:QuantumTest):
    let b:=clockSourcePair s hs x (w,f)
    primitiveEnergy b.2-primitiveEnergy (oppositeForcing z b.1 b.2)=
      primitiveEnergy (K s hs x f)-primitiveEnergy (K s hs x (oppositeForcing z w f))+
        4*z.im*(sourcePair (actualPrimitiveCommutator s hs x w) (positivePrimitive (K s hs x w))).im:=by
  dsimp only
  have hb:=actual_two_pole_clock_source s hs x z w f
  dsimp only at hb
  have hp:=actual_primitive_forcing_square z (K s hs x w) ((clockSourcePair s hs x (w,f)).2)
  have hq:=actual_primitive_forcing_square z (K s hs x w) (K s hs x f)
  have ho:oppositeForcing z (K s hs x w) (K s hs x f)=K s hs x (oppositeForcing z w f):=by
    simp only [oppositeForcing,map_add,map_smul]
  rw [ho] at hq
  rw [hb.1,pair_add_l,Complex.add_im] at hp
  change 12*z.im*((sourcePair (K s hs x f) (positivePrimitive (K s hs x w))).im+
      (sourcePair (actualPrimitiveCommutator s hs x w) (positivePrimitive (K s hs x w))).im)-
      12*z.im^2*primitiveEnergy (K s hs x w)=
    3*primitiveEnergy (K s hs x f+actualPrimitiveCommutator s hs x w)-
      3*primitiveEnergy (oppositeForcing z (K s hs x w) (K s hs x f+actualPrimitiveCommutator s hs x w)) at hp
  rw [hb.1]
  change primitiveEnergy (K s hs x f+actualPrimitiveCommutator s hs x w)-
    primitiveEnergy (oppositeForcing z (K s hs x w) (K s hs x f+actualPrimitiveCommutator s hs x w))=_
  linarith only [hp,hq]

/-- Direct restriction to the original full-forcing electric update; no shifted forcing is substituted for its own source. -/
theorem actual_whole_source_two_pole_primitive_difference(s:ℝ)(hs:0<s)(half advanced:Bool)(m ell:ℕ)
    (F:Index)(g:diagonal.domain)(q:ℝ)(x:ℝ×ℝ):
    let z:=actualFrequency advanced (sourceNoetherFrequency half) q
    let a:=wholeSourceNext s hs half advanced m ell F g q
    let b:=clockSourcePair s hs x a
    primitiveEnergy b.2-primitiveEnergy (oppositeForcing z b.1 b.2)=
      primitiveEnergy (K s hs x a.2)-primitiveEnergy (K s hs x (oppositeForcing z a.1 a.2))+
        4*z.im*(sourcePair (actualPrimitiveCommutator s hs x a.1) (positivePrimitive (K s hs x a.1))).im:=by
  dsimp only
  exact actual_two_pole_primitive_clock_difference s hs x _ _ _
end LowEnergy.OriginalRPrimitiveDifference
