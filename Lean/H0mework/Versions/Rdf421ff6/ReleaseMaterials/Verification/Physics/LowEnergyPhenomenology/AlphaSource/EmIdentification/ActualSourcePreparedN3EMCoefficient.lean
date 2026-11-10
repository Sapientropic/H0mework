import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedN3EMAnalyticPrice

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedN3EMCoefficient
open Polynomial CanonicalGradedSpatialSource ActualDressedFullCoulomb ActualCompositeFieldCurrent
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator
open ActualEMCarrierOwn ActualEMCurrentSplit ActualDressedEMTensorClock ActualDressedNoetherCoulombUnit
open ActualSourcePreparedN3EMIRSplit ActualSourcePreparedN3ChargeEndpoint
open PhysicalN3SourceEnergy ActualDressedZeroDamping
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonEMTensorNumerator commonDenominator

private theorem constant_em_force (event : DressedEvent) (leg : CompositeLeg)
    (poles : N3SourceEnergyPoleSection event.momentum leg) :
    (fun i => MvPolynomial.C (emCurrentForce (physicalN3PoleCurrent event leg poles) i) : Fin 289 → Parameters) =
      (MvPolynomial.C noetherPairScale : Parameters) • ((emInsertion.map (MvPolynomial.C : ℂ →+* Parameters)) *ᵥ
        (fun mu => MvPolynomial.C (physicalN3PoleNoetherCurrent event leg poles mu))) := by
  have actual := em_current_force_insertion (physicalN3PoleCurrent event leg poles)
  rw [physical_n3_pole_coordinate_noether_unit, Matrix.mulVec_smul] at actual
  funext i
  have read := congrArg (fun z : ℂ => (MvPolynomial.C z : Parameters)) (congrFun actual i)
  simpa only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    map_mul, map_sum, Matrix.map_apply, Finset.mul_sum] using read

private theorem insertion_pullback {α ι κ : Type*} [CommRing α] [Fintype ι] [Fintype κ]
    (E : Matrix ι κ α) (H : Matrix ι ι α) (d s : κ → α) :
    dotProduct (E*ᵥd) (H*ᵥ(E*ᵥs)) = dotProduct d ((E.transpose*H*E)*ᵥs) := by
  calc
    _ = dotProduct (H*ᵥ(E*ᵥs)) (E*ᵥd) := dotProduct_comm _ _
    _ = dotProduct d (E.transpose*ᵥ(H*ᵥ(E*ᵥs))) :=
      (Matrix.dotProduct_transpose_mulVec E d _).symm
    _ = _ := by rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

private theorem em_tensor_cofactor (event : DressedEvent) (n : PhysicalMomentum) :
    commonEMTensorNumerator event n = commonDenominator event n •
      ((emInsertion.map (MvPolynomial.C : ℂ →+* Parameters)).transpose*(commonClearedPencil event n).adjugate*
        (emInsertion.map (MvPolynomial.C : ℂ →+* Parameters))) := by
  ext mu nu
  unfold commonEMTensorNumerator
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.mul_assoc]
  rfl

/-- Before reduction or chart selection, the actual N3 EM cofactor contracts
only the original sixteen tensor numerators with its physical Noether currents. -/
theorem source_n3_em_numerator_noether (fieldEvent detector source : DressedEvent)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles true true =
      MvPolynomial.C (noetherPairScale^2) *
        dotProduct (fun mu => MvPolynomial.C (physicalN3PoleNoetherCurrent detector dLeg dPoles mu))
          ((commonEMTensorNumerator fieldEvent n)*ᵥ
            (fun nu => MvPolynomial.C (physicalN3PoleNoetherCurrent source sLeg sPoles nu))) := by
  unfold sourceN3ArmNumerator
  simp only [sourceN3ArmCurrent, ↓reduceIte]
  rw [constant_em_force detector dLeg dPoles, constant_em_force source sLeg sPoles,
    Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, insertion_pullback, em_tensor_cofactor]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, map_pow]
  ring

def sourceN3OtherEMNumerator (fieldEvent detector source : DressedEvent)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) : Parameters :=
  MvPolynomial.C (noetherPairScale^2) *
    ∑ mu : Fin 4, ∑ nu : Fin 4, if mu=0 ∧ nu=0 then 0 else
      MvPolynomial.C (physicalN3PoleNoetherCurrent detector dLeg dPoles mu)*
        commonEMTensorNumerator fieldEvent n mu nu*
          MvPolynomial.C (physicalN3PoleNoetherCurrent source sLeg sPoles nu)

private theorem temporal_tensor_split {α : Type*} [CommRing α]
    (T : Matrix (Fin 4) (Fin 4) α) (d s : Fin 4 → α) :
    dotProduct d (T*ᵥs)=d 0*T 0 0*s 0+
      ∑ mu : Fin 4, ∑ nu : Fin 4, if mu=0 ∧ nu=0 then 0 else d mu*T mu nu*s nu := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_four]
  ring

/-- The same-state charge endpoint is paid in the original polynomial itself,
so extracting clock coefficients does not need a regular evaluation chart. -/
theorem source_n3_em_numerator_charge_endpoint (fieldEvent detector source : DressedEvent)
    (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) :
    sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles true true =
      MvPolynomial.C (noetherPairScale^2 *
        (sourceN3AmputatedPoleCharge detector dLeg dPoles+sourceN3ChargeReadDefect detector dLeg dPoles)*
        (sourceN3AmputatedPoleCharge source sLeg sPoles+sourceN3ChargeReadDefect source sLeg sPoles)) *
          commonEMTensorNumerator fieldEvent n 0 0+
      sourceN3OtherEMNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles := by
  rw [source_n3_em_numerator_noether, temporal_tensor_split]
  simp only [source_n3_noether_charge_endpoint, map_mul]
  unfold sourceN3OtherEMNumerator
  ring

theorem source_n3_em_clock_charge_coefficient (fieldEvent detector source : DressedEvent)
    (epsilon : ℝ) (n : PhysicalMomentum) (dLeg sLeg : CompositeLeg)
    (dPoles : N3SourceEnergyPoleSection detector.momentum dLeg)
    (sPoles : N3SourceEnergyPoleSection source.momentum sLeg) (k : ℕ) :
    (dampingSlice epsilon
      (sourceN3ArmNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles true true)).coeff k =
      (noetherPairScale^2 *
        (sourceN3AmputatedPoleCharge detector dLeg dPoles+sourceN3ChargeReadDefect detector dLeg dPoles)*
        (sourceN3AmputatedPoleCharge source sLeg sPoles+sourceN3ChargeReadDefect source sLeg sPoles)) *
          (dampingSlice epsilon (commonEMTensorNumerator fieldEvent n 0 0)).coeff k+
      (dampingSlice epsilon
        (sourceN3OtherEMNumerator fieldEvent detector source n dLeg sLeg dPoles sPoles)).coeff k := by
  rw [source_n3_em_numerator_charge_endpoint, map_add, map_mul, coeff_add]
  simp only [dampingSlice, MvPolynomial.eval₂Hom_C, coeff_C_mul]

end LowEnergy.GaussComposite.ActualSourcePreparedN3EMCoefficient
