import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeNoetherCoulomb
import H0mework.Physics.LowEnergy.Electromagnetic.Units

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeCoulomb
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic
open ActualDressedEMNativeMomentum ActualDressedNoetherCoulombUnit ActualDressedOrderedStatic ActualDressedFullCoulomb
open ActualCompositeFieldCurrent ActualEMCarrierOwn
open scoped Matrix BigOperators

/-- Primitive propagation is read from the generated transverse time and space coefficients. -/
def nativePrimitiveSpeed : ℝ := lapse⁻¹

/-- The complete source symbol restricts to transverse fields; the Gauss component is still included in this identity. -/
theorem actual_native_transverse_principal (omega : ℝ) (k : PhysicalMomentum) (v : Fin 4 → ℂ)
    (temporal : v 0=0) (transverse : nativeSpatialContraction k v=0) :
    nativeEMMomentumMatrix (physicalFrequencyMomentum omega k)*ᵥv=
      (2*(lapse : ℂ)*((omega : ℂ)^2-(nativePrimitiveSpeed : ℂ)^2*(spatialSquare k : ℂ))) • v := by
  rw [actual_native_physical_em_principal]
  have contraction : (k 0 : ℂ)*v 1+(k 1 : ℂ)*v 2+(k 2 : ℂ)*v 3=0 := transverse
  have ln : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  have vZero (h : 0<4) : v (⟨0,h⟩ : Fin 4)=v 0 := rfl
  have vOne (h : 1<4) : v (⟨1,h⟩ : Fin 4)=v 1 := rfl
  have vTwo (h : 2<4) : v (⟨2,h⟩ : Fin 4)=v 2 := rfl
  have vThree (h : 3<4) : v (⟨3,h⟩ : Fin 4)=v 3 := rfl
  funext mu
  fin_cases mu <;> simp only [nativePhysicalEMPrincipal,Pi.smul_apply,smul_eq_mul,temporal,contraction,
    mul_zero,add_zero,sub_zero,nativePrimitiveSpeed,Complex.ofReal_inv,spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  all_goals dsimp only [Matrix.vecCons,Matrix.vecHead,Matrix.vecTail,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals simp only [eq_mpr_eq_cast,cast_eq,vZero,vOne,vTwo,vThree,temporal]
  all_goals generalize hl : (lapse : ℂ)=L at ln ⊢
  all_goals field_simp [ln]
  all_goals ring1

/-- This is the native propagation-normalized coefficient. Corrected propagation keeps its original full spectral/residue responsibility. -/
def nativePrincipalCoupling : ℂ :=
  nativeNoetherCoulomb/((Stage10.ActionNormalization.phaseMomentum : ℂ)*(nativePrimitiveSpeed : ℂ))

theorem actual_native_principal_coupling :
    nativePrincipalCoupling=(Stage10.ActionNormalization.phaseMomentum : ℂ)/(6*(Real.pi : ℂ)) := by
  have hn : (Stage10.ActionNormalization.phaseMomentum : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  have ln : (lapse : ℂ)≠0 := Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  unfold nativePrincipalCoupling nativeNoetherCoulomb
  rw [actual_native_noether_response_weight]
  simp only [nativePrimitiveSpeed,Complex.ofReal_inv]
  generalize hh : (Stage10.ActionNormalization.phaseMomentum : ℂ)=H at hn ⊢
  generalize hl : (lapse : ℂ)=L at ln ⊢
  field_simp [hn,ln,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  all_goals ring1

theorem actual_native_source_coupling :
    nativePrincipalCoupling=(2/3 : ℂ)*(spinScale : ℂ)/(Real.pi : ℂ) := by
  rw [actual_native_principal_coupling,Stage10.ActionNormalization.phaseMomentum_source]
  push_cast
  all_goals ring1

/-- This minus belongs to the unchanged original ordered action read. -/
def nativeDirectionalOrderedCoulomb (n : PhysicalMomentum) : ℂ :=
  -nativeNoetherCoulomb/(spatialSquare n : ℂ)

/-- A retained actual coefficient balance, not a premise asserting that the full infrared coefficient equals its principal part. -/
def actualNativeCoulombCorrection (event : DressedEvent) (n : PhysicalMomentum) : ℂ :=
  directionalNoetherCoulombCoefficient event n-nativeDirectionalOrderedCoulomb n

/-- The unchanged complete source coefficient consumes the native baseline and preserves every actual correction, charge calibration, other EM component and non-pure channel. -/
theorem actual_noether_native_coulomb_balance (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    sourceOrderedProbeCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ))=
      sourceInputCharge dR*sourceInputCharge sR*
        (nativeDirectionalOrderedCoulomb n+actualNativeCoulombCorrection event n)+
      (noetherChargeCalibration pd dL dR*sourceInputCharge sR+
        sourceInputCharge dR*noetherChargeCalibration ps sL sR+
        noetherChargeCalibration pd dL dR*noetherChargeCalibration ps sL sR)*
          (nativeDirectionalOrderedCoulomb n+actualNativeCoulombCorrection event n)+
      otherEMCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ))+
      noetherNonPureCoefficient event n pd ps dL dR sL sR/(4*(Real.pi : ℂ)) := by
  rw [actual_noether_coulomb_coefficient]
  have same : nativeDirectionalOrderedCoulomb n+actualNativeCoulombCorrection event n=
      directionalNoetherCoulombCoefficient event n := by
    unfold actualNativeCoulombCorrection
    ring
  rw [same]

private theorem source_square_smul (scale : ℝ) (k : PhysicalMomentum) :
    spatialSquare (scale • k)=scale^2*spatialSquare k := by
  simp only [spatialSquare,Pi.smul_apply,smul_eq_mul]
  all_goals ring1

/-- The original ordered minus consumes the actual principal Green on the same radial physical momenta. -/
theorem actual_native_ordered_noether_ray (kappa : ℝ) (kappa_ne : kappa≠0)
    (n pd ps : PhysicalMomentum) (nonzero : spatialSquare n≠0) (dL dR sL sR : CompositeLeg) :
    -(kappa : ℂ)^2*nativeTemporalNoetherRead (kappa • n) pd ps dL dR sL sR/(4*(Real.pi : ℂ))=
      noetherEMCurrent pd dL dR 0*nativeDirectionalOrderedCoulomb n*noetherEMCurrent ps sL sR 0 := by
  rw [actual_native_noether_temporal_read,source_square_smul]
  unfold nativeDirectionalOrderedCoulomb nativeNoetherCoulomb
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr kappa_ne,Complex.ofReal_ne_zero.mpr nonzero,
    Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Original source units pull the complete principal through its action measure, field coordinate, time and spatial jets together. -/
def nativeUnitPrincipal (energy length time field : ℝ) (omega : ℝ) (k : PhysicalMomentum)
    (v : Fin 4 → ℂ) : Fin 4 → ℂ :=
  ((length^3/energy*field^2 : ℝ) : ℂ) •
    (nativeEMMomentumMatrix (physicalFrequencyMomentum (omega/time) (length⁻¹ • k))*ᵥv)

theorem actual_native_unit_action_measure (energy length time : ℝ) (time_ne : time≠0) :
    length^3/energy=(length^3*time)/(energy*time) := by
  rw [mul_div_mul_right _ _ time_ne]

/-- The static electric Hessian is rescaled along with the original measure and field, before a Coulomb coefficient is read. -/
theorem actual_native_unit_gauss_hessian (energy length time field : ℝ) (length_ne : length≠0)
    (k : PhysicalMomentum) (v : Fin 4 → ℂ) :
    nativeUnitPrincipal energy length time field 0 k v 0=
      ((length/energy*field^2 : ℝ) : ℂ)*
        (2*(lapse : ℂ)*(spatialSquare k : ℂ)*v 0) := by
  rw [nativeUnitPrincipal,actual_native_physical_em_principal]
  simp only [Pi.smul_apply,smul_eq_mul,zero_div,nativePhysicalEMPrincipal,Matrix.cons_val_zero,
    Complex.ofReal_zero,zero_mul,add_zero]
  have square : ((length⁻¹ • k) 0 : ℂ)^2+((length⁻¹ • k) 1 : ℂ)^2+((length⁻¹ • k) 2 : ℂ)^2=
      (spatialSquare (length⁻¹ • k) : ℂ) := by
    simp only [spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  simp only [Pi.smul_apply,smul_eq_mul] at square
  rw [square,source_square_smul]
  push_cast
  have lc : (length : ℂ)≠0 := Complex.ofReal_ne_zero.mpr length_ne
  field_simp [lc]

/-- The propagation unit is read from the same pulled-back source principal as its static Hessian. -/
theorem actual_native_unit_transverse_principal (energy length time field omega : ℝ)
    (energy_ne : energy≠0) (length_ne : length≠0) (time_ne : time≠0)
    (k : PhysicalMomentum) (v : Fin 4 → ℂ) (temporal : v 0=0) (transverse : nativeSpatialContraction k v=0) :
    nativeUnitPrincipal energy length time field omega k v=
      (((length^3/(energy*time^2)*field^2 : ℝ) : ℂ)*2*(lapse : ℂ)*
        ((omega : ℂ)^2-((nativePrimitiveSpeed*time/length : ℝ) : ℂ)^2*(spatialSquare k : ℂ))) • v := by
  have scaled : nativeSpatialContraction (length⁻¹ • k) v=0 := by
    have same : nativeSpatialContraction (length⁻¹ • k) v=((length⁻¹ : ℝ) : ℂ)*nativeSpatialContraction k v := by
      simp only [nativeSpatialContraction,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]
      all_goals ring1
    rw [same,transverse,mul_zero]
  rw [nativeUnitPrincipal,actual_native_transverse_principal _ _ _ temporal scaled,smul_smul,source_square_smul]
  congr 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr energy_ne,Complex.ofReal_ne_zero.mpr length_ne,
    Complex.ofReal_ne_zero.mpr time_ne]

/-- The electron field vertex is pulled through the same action measure and conserved charge density unit. -/
def nativeUnitVertex (energy field : ℝ) : ℂ :=
  ((field/energy : ℝ) : ℂ)*(Stage10.ActionNormalization.phaseMomentum : ℂ)

theorem actual_native_unit_action_vertex (energy field : ℝ) (p : PhysicalMomentum) (left right : CompositeLeg) :
    ((Stage10.ActionNormalization.phaseMomentum/energy : ℝ) : ℂ)*
      rescaledFieldNoetherCurrent field p left right 0=
      nativeUnitVertex energy field*noetherEMCurrent p left right 0 := by
  rw [actual_generator_current_rescale]
  simp only [nativeUnitVertex,Pi.smul_apply,smul_eq_mul,Complex.ofReal_div]
  all_goals ring1

def nativeUnitCoulomb (energy length field : ℝ) : ℂ :=
  (nativeUnitVertex energy field)^2/
    ((((length/energy*field^2 : ℝ) : ℂ)*(3/2 : ℂ)*(lapse : ℂ))*(4*(Real.pi : ℂ)))

/-- Field scale cancels only after its actual Hessian and both vertices have been transformed. -/
theorem actual_native_unit_coulomb (energy length field : ℝ)
    (energy_ne : energy≠0) (length_ne : length≠0) (field_ne : field≠0) :
    nativeUnitCoulomb energy length field=nativeNoetherCoulomb/((energy*length : ℝ) : ℂ) := by
  unfold nativeUnitCoulomb nativeUnitVertex nativeNoetherCoulomb
  rw [actual_native_noether_response_weight]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr energy_ne,Complex.ofReal_ne_zero.mpr length_ne,
    Complex.ofReal_ne_zero.mpr field_ne,Complex.ofReal_ne_zero.mpr lapse_pos.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Original action and propagation units are transformed together with the source Hessian; this is not a change of h alone. -/
theorem actual_native_unit_coupling (energy length time field : ℝ)
    (energy_ne : energy≠0) (length_ne : length≠0) (time_ne : time≠0) (field_ne : field≠0) :
    nativeUnitCoulomb energy length field/
      (((Stage10.ActionNormalization.phaseMomentum/(energy*time) : ℝ) : ℂ)*
        ((nativePrimitiveSpeed*time/length : ℝ) : ℂ))=nativePrincipalCoupling := by
  rw [actual_native_unit_coulomb _ _ _ energy_ne length_ne field_ne]
  unfold nativePrincipalCoupling
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr energy_ne,Complex.ofReal_ne_zero.mpr length_ne,
    Complex.ofReal_ne_zero.mpr time_ne]

end LowEnergy.GaussComposite.ActualDressedEMNativeCoulomb
