import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceJointRotationMatrix

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalJointRotationCharge
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair Stage10
open FullQuantum FullSpace YangMills.FullPairing FullQuantum.Triangular
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField
open StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumElectromagneticIdentity ChargedPreparation.Dynamics
open scoped InnerProductSpace Topology BigOperators Matrix Matrix.Norms.L2Operator

def sourceRotatedMomentum (theta : ℝ) (p : Fin 3→ℝ) : Fin 3→ℝ :=
  ![Real.cos theta*p 0-Real.sin theta*p 1,Real.sin theta*p 0+Real.cos theta*p 1,p 2]

/-- This finite internal action is the exponential of the source current's actual charge weights. -/
def sourceInternalRotation (theta : ℝ) : Matrix Source.Index Source.Index ℂ :=
  Matrix.diagonal (fun index=>Complex.exp ((theta*(sourceLockedSourceWeight index).re:ℝ)*Complex.I))

theorem sourceRotatedMomentum_zero (p : Fin 3→ℝ) : sourceRotatedMomentum 0 p=p := by
  ext j
  fin_cases j <;> simp [sourceRotatedMomentum,Matrix.cons_val_two]

theorem sourceRotatedMomentum_add (a b : ℝ) (p : Fin 3→ℝ) :
    sourceRotatedMomentum a (sourceRotatedMomentum b p)=sourceRotatedMomentum (a+b) p := by
  ext j
  fin_cases j <;> simp [sourceRotatedMomentum,Real.cos_add,Real.sin_add,Matrix.cons_val_two] <;> ring

theorem sourceRotatedMomentum_square (theta : ℝ) (p : Fin 3→ℝ) :
    ∑j : Fin 3,(sourceRotatedMomentum theta p j)^2=∑j : Fin 3,(p j)^2 := by
  simp only [Fin.sum_univ_three]
  change (Real.cos theta*p 0-Real.sin theta*p 1)^2+
    (Real.sin theta*p 0+Real.cos theta*p 1)^2+(p 2)^2=(p 0)^2+(p 1)^2+(p 2)^2
  calc
    _=((Real.sin theta)^2+(Real.cos theta)^2)*((p 0)^2+(p 1)^2)+(p 2)^2 := by ring
    _=_ := by rw [Real.sin_sq_add_cos_sq];ring

theorem sourceInternalRotation_add (a b : ℝ) :
    sourceInternalRotation (a+b)=sourceInternalRotation a*sourceInternalRotation b := by
  rw [sourceInternalRotation,sourceInternalRotation,sourceInternalRotation,Matrix.diagonal_mul_diagonal]
  apply congrArg Matrix.diagonal
  funext index
  simp only [add_mul,Complex.ofReal_add,Complex.exp_add ]

theorem sourceInternalRotation_zero : sourceInternalRotation 0=1 := by
  simp [sourceInternalRotation]

theorem sourceInternalRotation_unitary (theta : ℝ) :
    (sourceInternalRotation theta).conjTranspose*sourceInternalRotation theta=1 := by
  simp only [sourceInternalRotation,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
  rw [←Matrix.diagonal_one]
  apply congrArg Matrix.diagonal
  funext index
  change star (Complex.exp ((theta*(sourceLockedSourceWeight index).re:ℝ)*Complex.I))*
    Complex.exp ((theta*(sourceLockedSourceWeight index).re:ℝ)*Complex.I)=1
  rw [Complex.star_def,←Complex.exp_conj]
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,←Complex.exp_add,neg_add_cancel,Complex.exp_zero]

private theorem moving_entry (p : Fin 3→ℝ) (row column : Source.Index) :
    sourceMovingFullHamiltonian p row column=
      if row.1.val/2=column.1.val/2 then
        (if row.1.val<2 then (-1:ℂ) else 1)*
          ChargedPreparation.SpatialSpectrum.sourceMatrix p
            ⟨2*(row.1.val%2)+row.2.val,by omega⟩
            ⟨2*(column.1.val%2)+column.2.val,by omega⟩ else 0 := rfl

/-- The source background and all physical momentum terms transform together; no angular averaging enters. -/
theorem sourceJointRotation_covariance (theta : ℝ) (p : Fin 3→ℝ) :
    sourceMovingFullHamiltonian (sourceRotatedMomentum theta p)*sourceInternalRotation theta=
      sourceInternalRotation theta*sourceMovingFullHamiltonian p := by
  have trig : Complex.sin (theta:ℂ)^2=1-Complex.cos (theta:ℂ)^2 := by
    linear_combination Complex.sin_sq_add_cos_sq (theta:ℂ)
  have phaseNeg : Complex.exp (-(Complex.I*(theta:ℂ)))=
      Complex.cos (theta:ℂ)-Complex.sin (theta:ℂ)*Complex.I := by
    rw [show -(Complex.I*(theta:ℂ))=(-(theta:ℂ))*Complex.I by ring,Complex.exp_mul_I,
      Complex.cos_neg,Complex.sin_neg]
    ring
  simp only [sourceInternalRotation]
  ext row column
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
  rcases row with ⟨spin,color⟩
  rcases column with ⟨other,colour⟩
  fin_cases spin <;> fin_cases color <;> fin_cases other <;> fin_cases colour <;>
    norm_num [sourceLockedSourceWeight,sourceRotatedMomentum,moving_entry,
      ChargedPreparation.SpatialSpectrum.sourceMatrix,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,
      Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  all_goals try ring_nf
  all_goals try rw [phaseNeg]
  all_goals try ring_nf
  all_goals try simp only [Complex.I_sq]
  all_goals try ring_nf
  all_goals try rw [trig]
  all_goals ring

/-- The source temporal principal keeps its original factor and its spin-color indices. -/
def sourceTimeMatrix : Matrix Source.Index Source.Index ℂ := fun row column=>
  (Complex.I*(lapse:ℂ)⁻¹)*diracGammaZero row.1 column.1*(if row.2=column.2 then 1 else 0)

theorem sourceTimeMatrix_original (values : Source.Index→ℂ) :
    currentCoframeMatterTemporalPrincipal (actual.coframe 0) (embed values)=embed (sourceTimeMatrix*ᵥvalues) := by
  rw [actual_temporal_principal,spin_embed,←map_smul]
  apply congrArg embed
  funext index
  rcases index with ⟨spin,color⟩
  fin_cases spin <;> fin_cases color <;>
    simp [sourceTimeMatrix,Matrix.mulVec,dotProduct,Fintype.sum_prod_type,
      Fin.sum_univ_four,diracGammaZero]

def sourceDiracMatrix (p : Fin 3→ℝ) (z : ℂ) : Matrix Source.Index Source.Index ℂ :=
  (-Complex.I) • (sourceTimeMatrix*(z • (1:Matrix Source.Index Source.Index ℂ)-sourceMovingFullHamiltonian p))

/-- This finite matrix is the restriction of the full original Dirac source, before any inverse. -/
theorem sourceDiracMatrix_original (p : Fin 3→ℝ) (z : ℂ) (values : Source.Index→ℂ) :
    diracKernel actual 0 p z (embed values)=embed (sourceDiracMatrix p z*ᵥvalues) := by
  rw [diracKernel_factor actual 0 p z (actual_noncharacteristic 0)]
  simp only [LinearMap.smul_apply,Module.End.mul_apply,fullKernel,LinearMap.sub_apply,
    LinearMap.smul_apply,Module.End.one_apply,sourceMovingHamiltonian_original]
  have input : z • embed values-embed (sourceMovingFullHamiltonian p*ᵥvalues)=
      embed (z • values-sourceMovingFullHamiltonian p*ᵥvalues) := by rw [map_sub,map_smul]
  rw [input,sourceTimeMatrix_original,←map_smul]
  apply congrArg embed
  simp only [sourceDiracMatrix,Matrix.smul_mulVec]
  rw [←Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]

theorem sourceInternalRotation_principal (theta : ℝ) :
    sourceTimeMatrix*sourceInternalRotation theta=sourceInternalRotation theta*sourceTimeMatrix := by
  simp only [sourceInternalRotation]
  ext row column
  simp only [Matrix.mul_diagonal,Matrix.diagonal_mul]
  rcases row with ⟨spin,color⟩
  rcases column with ⟨other,colour⟩
  fin_cases spin <;> fin_cases color <;> fin_cases other <;> fin_cases colour <;>
    simp [sourceTimeMatrix,diracGammaZero,sourceLockedSourceWeight]
  all_goals ring

/-- Full Dirac covariance keeps the original C0 ordering and the full mother-space source restriction. -/
theorem sourceJointDirac_covariance (theta : ℝ) (p : Fin 3→ℝ) (z : ℂ) :
    sourceDiracMatrix (sourceRotatedMomentum theta p) z*sourceInternalRotation theta=
      sourceInternalRotation theta*sourceDiracMatrix p z := by
  rw [sourceDiracMatrix,sourceDiracMatrix,smul_mul_assoc,mul_smul_comm]
  congr 1
  rw [mul_assoc,sub_mul,smul_mul_assoc,one_mul,sourceJointRotation_covariance,
    ]
  have scalar : z • sourceInternalRotation theta=sourceInternalRotation theta*(z • 1) := by
    rw [mul_smul_comm,mul_one]
  rw [scalar,←mul_sub,←mul_assoc,sourceInternalRotation_principal,mul_assoc]

end LowEnergy.PreparationPhysicalJointRotationCharge
