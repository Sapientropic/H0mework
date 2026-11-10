import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNormalizedPoleSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMPhysicalResidueFlux
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedFullCoulomb ActualDressedZeroClockFrequency ActualDressedZeroClockVector
open ActualDressedEMZeroClockColumns ActualDressedEMQuantumThreshold ActualDressedEMClockDispersion
open ActualDressedEMFullPoleFlux ActualDressedEMTaylorPoleFlux LowEnergy.ActualDressedVisiblePole
open ActualEMCarrierOwn Filter Set
open scoped Matrix BigOperators Topology

private theorem normalized_principal_series (W T A B : ℂ[X]) (a : ℂ) (q : ℕ)
    (regular : T.eval a≠0) (equation : W=T*A+(X-C a)^q*B) :
    (taylor a W : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹=
      (taylor a A : PowerSeries ℂ)+(PowerSeries.X : PowerSeries ℂ)^q*
        ((taylor a B : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹) := by
  have unit : PowerSeries.constantCoeff (taylor a T : PowerSeries ℂ)≠0 := by
    simpa only [Polynomial.constantCoeff_coe,taylor_coeff_zero] using regular
  have mapped := congrArg (fun P : ℂ[X] => (taylor a P : PowerSeries ℂ)) equation
  simp only [map_add,taylor_mul,taylor_pow,map_sub,taylor_X,taylor_C,add_sub_cancel_right,
    Polynomial.coe_add,Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_X] at mapped
  rw [mapped,add_mul]
  have cancel : (taylor a T : PowerSeries ℂ)*(taylor a A : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹=
      (taylor a A : PowerSeries ℂ) := by
    calc
      _=(taylor a A : PowerSeries ℂ)*((taylor a T : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹) := by ring
      _=_ := by rw [PowerSeries.mul_inv_cancel _ unit,mul_one]
  rw [cancel,mul_assoc]

/-- The normalized full series contains every canonical principal coefficient and the same analytic column. -/
theorem source_em_normalized_principal_series (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (i : Fin 289) :
    emNormalizedPoleColumnSeries event eps n nu a i=
      (taylor a (emFullPrincipalPolynomial event eps n nu a i) : PowerSeries ℂ)+
        (PowerSeries.X : PowerSeries ℂ)^emFullColumnPoleOrder event eps n nu a*
          ((taylor a (emFullAnalyticColumnNumerator event eps n nu a i) : PowerSeries ℂ)*
            (taylor a (emColumnDenominatorTail event eps n a) : PowerSeries ℂ)⁻¹) := by
  have equation := congrFun (source_em_full_principal_decomposition event eps n mu nu a root) i
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at equation
  exact normalized_principal_series _ _ _ _ a _
    (source_em_denominator_tail_nonzero event eps n mu nu a root) equation

theorem source_em_normalized_principal_coefficient (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (r : ℕ)
    (lower : r<emFullColumnPoleOrder event eps n nu a) :
    emNormalizedPoleColumnCoefficient event eps n nu a r=emFullPrincipalCoefficient event eps n nu a r := by
  funext i
  have value := congrArg (PowerSeries.coeff r) (source_em_normalized_principal_series event eps n mu nu a root i)
  simp only [map_add,PowerSeries.coeff_X_pow_mul',if_neg (Nat.not_le_of_lt lower),add_zero,Polynomial.coeff_coe] at value
  exact value

private theorem normalized_analytic_coefficient (A B T : ℂ[X]) (a : ℂ) (q : ℕ)
    (degree : A.degree<(q : WithBot ℕ)) :
    PowerSeries.coeff q ((taylor a A : PowerSeries ℂ)+(PowerSeries.X : PowerSeries ℂ)^q*
      ((taylor a B : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹))=B.eval a/T.eval a := by
  have zero : (taylor a A).coeff q=0 := coeff_eq_zero_of_degree_lt (by simpa only [degree_taylor] using degree)
  rw [map_add]
  have shifted := PowerSeries.coeff_X_pow_mul
    ((taylor a B : PowerSeries ℂ)*(taylor a T : PowerSeries ℂ)⁻¹) q 0
  simp only [zero_add] at shifted
  rw [Polynomial.coeff_coe,zero,shifted,zero_add,PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp only [map_mul,Polynomial.constantCoeff_coe,PowerSeries.constantCoeff_inv,taylor_coeff_zero,div_eq_mul_inv]

theorem source_em_normalized_analytic_coefficient (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emNormalizedPoleColumnCoefficient event eps n nu a (emFullColumnPoleOrder event eps n nu a)=
      (fun i => (emFullAnalyticColumnNumerator event eps n nu a i).eval a/
        (emColumnDenominatorTail event eps n a).eval a) := by
  funext i
  have value := congrArg (PowerSeries.coeff (emFullColumnPoleOrder event eps n nu a))
    (source_em_normalized_principal_series event eps n mu nu a root i)
  exact value.trans (normalized_analytic_coefficient _ _ _ a _ (source_em_full_principal_degree event eps n nu a i))

private theorem physical_coefficient (A beta : ℂ) (q r : ℕ) (regular : beta≠0) (lower : r≤q) :
    beta^q*A/beta^r=beta^(q-r)*A := by
  have power : beta^q=beta^r*beta^(q-r) := by rw [← pow_add,Nat.add_sub_of_le lower]
  rw [power]
  calc
    _=(beta^r*(beta^(q-r)*A))/beta^r := by rw [mul_assoc]
    _=_ := by rw [mul_div_cancel_left₀ _ (pow_ne_zero r regular)]

theorem source_em_physical_canonical_principal_coefficient (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) (r : ℕ)
    (lower : r<emFullColumnPoleOrder event eps n nu a) :
    emPhysicalNormalizedPoleColumnCoefficient event eps n nu a r=emPhysicalPrincipalCoefficient event eps n nu a r := by
  have same := source_em_normalized_principal_coefficient event eps n mu nu a root r lower
  funext i
  change ((eps^2 : ℝ) : ℂ)^emFullColumnPoleOrder event eps n nu a*
    emNormalizedPoleColumnCoefficient event eps n nu a r i/((eps^2 : ℝ) : ℂ)^r=
      ((eps^2 : ℝ) : ℂ)^(emFullColumnPoleOrder event eps n nu a-r)*emFullPrincipalCoefficient event eps n nu a r i
  rw [congrFun same i]
  exact physical_coefficient _ _ _ r (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 nonzero)) lower.le

theorem source_em_physical_canonical_residue (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emPhysicalNormalizedPoleColumnCoefficient event eps n nu a (emFullColumnPoleOrder event eps n nu a-1)=
      emFullPhysicalResidue event eps n nu a := by
  have positive := source_em_full_pole_order_positive event eps n mu nu a root
  have lower : emFullColumnPoleOrder event eps n nu a-1<emFullColumnPoleOrder event eps n nu a := by omega
  have order : emFullColumnPoleOrder event eps n nu a-(emFullColumnPoleOrder event eps n nu a-1)=1 := by omega
  have same := source_em_physical_canonical_principal_coefficient event eps n mu nu a nonzero root _ lower
  simpa only [emPhysicalPrincipalCoefficient,emFullPhysicalResidue,order,pow_one] using same

theorem source_em_physical_canonical_analytic_coefficient (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) (a : ℂ) (nonzero : eps≠0)
    (root : a∈visibleRoots (zeroClockFrequencyEMFraction event eps n mu nu)) :
    emPhysicalNormalizedPoleColumnCoefficient event eps n nu a (emFullColumnPoleOrder event eps n nu a)=
      (fun i => (emFullAnalyticColumnNumerator event eps n nu a i).eval a/
        (emColumnDenominatorTail event eps n a).eval a) := by
  have same := source_em_normalized_analytic_coefficient event eps n mu nu a root
  funext i
  change ((eps^2 : ℝ) : ℂ)^emFullColumnPoleOrder event eps n nu a*
    emNormalizedPoleColumnCoefficient event eps n nu a (emFullColumnPoleOrder event eps n nu a) i/
      ((eps^2 : ℝ) : ℂ)^emFullColumnPoleOrder event eps n nu a=_
  rw [mul_div_cancel_left₀ _ (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 nonzero)))]
  exact congrFun same i

end LowEnergy.GaussComposite.ActualDressedEMPhysicalResidueFlux
