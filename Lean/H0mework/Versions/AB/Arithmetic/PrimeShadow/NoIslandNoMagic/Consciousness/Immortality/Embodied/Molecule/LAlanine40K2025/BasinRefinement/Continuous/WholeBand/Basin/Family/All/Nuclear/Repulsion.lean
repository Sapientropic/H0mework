import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.Basin.Family.All.Nuclear.SourceData
import H0mework.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.Continuous.WholeBand.IQA.Coulomb.Kernel

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
open SourceGaussianModel SourceFiniteData GlobalSource WholeBandBasin Set MeasureTheory
open scoped BigOperators
noncomputable section

/-- Integer picobohr squared distance between two recorded nuclei. -/
def pairDistSqZ (a b : Fin 13) : ℤ :=
  (positionTable a 0 - positionTable b 0)^2 +
    (positionTable a 1 - positionTable b 1)^2 +
    (positionTable a 2 - positionTable b 2)^2

/-- Coulomb repulsion of the recorded pair, in hartree. -/
def nuclearRepulsion (a b : Fin 13) : ℝ :=
  nuclearCharge a * nuclearCharge b *
    SourceCoulomb.kernel (nuclearPosition a - nuclearPosition b)

/-- The recorded pairwise repulsion summed over `a < b`. -/
def totalRepulsion : ℝ :=
  ∑ p ∈ (Finset.univ : Finset (Fin 13 × Fin 13)).filter (fun p => p.1 < p.2),
    nuclearRepulsion p.1 p.2

/-- Rational squeeze certificate: `Ln/10^15 ≤ dist ≤ Un/10^15` from the integer
    checks `Ln² ≤ 10^6·pairDistSqZ ≤ Un²`, and the nanohartree rounding window
    `(r-1)·Un ≤ Zn·10^24 ≤ (r+1)·Ln`; together they pin the ledger row within
    one nanohartree of the kernel repulsion. Every hypothesis is a `ℤ`/`ℕ`
    check the kernel can reject. -/
private theorem repulsion_close (a b : Fin 13) (r : ℤ) (Ln Un : ℤ) (Zn : ℕ)
    (hZ : nuclearChargeNat a * nuclearChargeNat b = Zn)
    (hL : (0 : ℤ) < Ln) (hU : (0 : ℤ) < Un)
    (hlow : Ln * Ln ≤ pairDistSqZ a b * 10^6)
    (hup : pairDistSqZ a b * 10^6 ≤ Un * Un)
    (hub : (r - 1) * Un ≤ (Zn : ℤ) * 10^24)
    (hlb : (Zn : ℤ) * 10^24 ≤ (r + 1) * Ln) :
    |nuclearRepulsion a b - (r : ℝ) / 10^9| ≤ (1 : ℝ) / 10^9 := by
  have sumSq : (∑ k : Fin 3, (nuclearPosition a - nuclearPosition b) k ^ 2) =
      ((pairDistSqZ a b : ℤ) : ℝ) / 10^24 := by
    have per (k : Fin 3) : ((nuclearPosition a - nuclearPosition b) k)^2 =
        (((positionTable a k - positionTable b k : ℤ) : ℝ)/10^12)^2 := by
      simp only [Pi.sub_apply,nuclearPosition,nuclearPositionQ_eq_table]
      push_cast
      ring
    have per2 (k : Fin 3) :
        (((positionTable a k - positionTable b k : ℤ) : ℝ)/10^12)^2 =
          (((positionTable a k - positionTable b k : ℤ) : ℝ)^2)/10^24 := by
      rw [div_pow]
      norm_num
    rw [Finset.sum_congr rfl (fun k _ => per k),Finset.sum_congr rfl (fun k _ => per2 k)]
    rw [← Finset.sum_div]
    rw [Fin.sum_univ_three]
    unfold pairDistSqZ
    push_cast
    ring_nf
  have distEq : SourceCoulomb.distance (nuclearPosition a - nuclearPosition b) =
      Real.sqrt (((pairDistSqZ a b : ℤ) : ℝ) / 10^24) :=
    congrArg Real.sqrt sumSq
  have hLR : (0 : ℝ) < (Ln : ℝ) := by exact_mod_cast hL
  have hUR : (0 : ℝ) < (Un : ℝ) := by exact_mod_cast hU
  have Lb : (0 : ℝ) < (Ln : ℝ)/10^15 := by positivity
  have Ub : (0 : ℝ) < (Un : ℝ)/10^15 := by positivity
  have hlowR : ((Ln : ℝ))^2 ≤ ((pairDistSqZ a b : ℤ) : ℝ) * 10^6 := by
    calc ((Ln : ℝ))^2 = (((Ln * Ln : ℤ)) : ℝ) := by push_cast; ring
      _ ≤ (((pairDistSqZ a b * 10^6 : ℤ)) : ℝ) := by exact_mod_cast hlow
      _ = ((pairDistSqZ a b : ℤ) : ℝ) * 10^6 := by push_cast; ring
  have hupR : ((pairDistSqZ a b : ℤ) : ℝ) * 10^6 ≤ ((Un : ℝ))^2 := by
    calc ((pairDistSqZ a b : ℤ) : ℝ) * 10^6 = (((pairDistSqZ a b * 10^6 : ℤ)) : ℝ) := by
          push_cast; ring
      _ ≤ (((Un * Un : ℤ)) : ℝ) := by exact_mod_cast hup
      _ = ((Un : ℝ))^2 := by push_cast; ring
  have dge : (Ln : ℝ)/10^15 ≤
      SourceCoulomb.distance (nuclearPosition a - nuclearPosition b) := by
    rw [distEq]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (10^15:ℝ)^2) (by norm_num : (0:ℝ) < 10^24)]
    nlinarith [hlowR]
  have dle : SourceCoulomb.distance (nuclearPosition a - nuclearPosition b) ≤
      (Un : ℝ)/10^15 := by
    rw [distEq]
    rw [Real.sqrt_le_left (le_of_lt Ub)]
    rw [div_pow]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^24)]
    nlinarith [hupR]
  have dpos : (0 : ℝ) <
      SourceCoulomb.distance (nuclearPosition a - nuclearPosition b) :=
    lt_of_lt_of_le Lb dge
  have repEq : nuclearRepulsion a b = (Zn : ℝ) *
      (SourceCoulomb.distance (nuclearPosition a - nuclearPosition b))⁻¹ := by
    simp only [nuclearRepulsion,nuclearCharge,SourceCoulomb.kernel]
    rw [← Nat.cast_mul,hZ]
  have repLo : (Zn : ℝ) * ((Un : ℝ)/10^15)⁻¹ ≤ nuclearRepulsion a b := by
    rw [repEq]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact inv_anti₀ dpos dle
  have repHi : nuclearRepulsion a b ≤ (Zn : ℝ) * ((Ln : ℝ)/10^15)⁻¹ := by
    rw [repEq]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact inv_anti₀ Lb dge
  have hubR : ((r : ℝ) - 1) * (Un : ℝ) ≤ (Zn : ℝ) * 10^24 := by
    exact_mod_cast hub
  have hlbR : (Zn : ℝ) * 10^24 ≤ ((r : ℝ) + 1) * (Ln : ℝ) := by
    exact_mod_cast hlb
  have lower : ((r : ℝ) - 1)/10^9 ≤ nuclearRepulsion a b := by
    have step : ((r : ℝ) - 1)/10^9 ≤ (Zn : ℝ) * ((Un : ℝ)/10^15)⁻¹ := by
      rw [inv_div,← mul_div_assoc]
      rw [le_div_iff₀ hUR]
      nlinarith [hubR]
    exact step.trans repLo
  have upper : nuclearRepulsion a b ≤ ((r : ℝ) + 1)/10^9 := by
    calc nuclearRepulsion a b ≤ (Zn : ℝ) * ((Ln : ℝ)/10^15)⁻¹ := repHi
      _ ≤ ((r : ℝ) + 1)/10^9 := by
        rw [inv_div,← mul_div_assoc]
        rw [div_le_iff₀ hLR]
        nlinarith [hlbR]
  rw [abs_le]
  constructor <;> linarith [lower,upper]

/-- The literal squeeze table for all 78 source rows. -/
private def pairCert : Array (Fin 13 × Fin 13 × ℤ × ℤ) := #[
  ⟨0,1,4238682284441660,4238682284441661⟩,
  ⟨0,2,6826571728902471,6826571728902472⟩,
  ⟨0,3,7284731197068161,7284731197068162⟩,
  ⟨0,4,7070414002146168,7070414002146169⟩,
  ⟨0,5,8123022969657846,8123022969657847⟩,
  ⟨0,6,2394327246106967,2394327246106968⟩,
  ⟨0,7,4498010286415602,4498010286415603⟩,
  ⟨0,8,4780174830139994,4780174830139995⟩,
  ⟨0,9,5826647585851061,5826647585851062⟩,
  ⟨0,10,7404578672347882,7404578672347883⟩,
  ⟨0,11,5357311669846359,5357311669846360⟩,
  ⟨0,12,6496057572388191,6496057572388192⟩,
  ⟨1,2,5072488262144122,5072488262144123⟩,
  ⟨1,3,4685965843089857,4685965843089858⟩,
  ⟨1,4,5134865899337696,5134865899337697⟩,
  ⟨1,5,6731756395465016,6731756395465017⟩,
  ⟨1,6,2364464023940392,2364464023940393⟩,
  ⟨1,7,4529230262923186,4529230262923187⟩,
  ⟨1,8,5838503478229004,5838503478229005⟩,
  ⟨1,9,6311298536801110,6311298536801111⟩,
  ⟨1,10,7846139714720938,7846139714720939⟩,
  ⟨1,11,6941012969210866,6941012969210867⟩,
  ⟨1,12,6097968303517721,6097968303517722⟩,
  ⟨2,3,1688468858625539,1688468858625540⟩,
  ⟨2,4,1688126228504857,1688126228504858⟩,
  ⟨2,5,1687749961999136,1687749961999137⟩,
  ⟨2,6,4685128256565057,4685128256565058⟩,
  ⟨2,7,2813423892475644,2813423892475645⟩,
  ⟨2,8,3832347706118062,3832347706118063⟩,
  ⟨2,9,4663461407549742,4663461407549743⟩,
  ⟨2,10,5031492977287495,5031492977287496⟩,
  ⟨2,11,6229471001227932,6229471001227933⟩,
  ⟨2,12,5009303060765153,5009303060765154⟩,
  ⟨3,4,2754306033114167,2754306033114168⟩,
  ⟨3,5,2754744238865437,2754744238865438⟩,
  ⟨3,6,4951316194479603,4951316194479604⟩,
  ⟨3,7,3733973537517593,3733973537517594⟩,
  ⟨3,8,5193853902306178,5193853902306179⟩,
  ⟨3,9,5016887148725813,5016887148725814⟩,
  ⟨3,10,5585897095145044,5585897095145045⟩,
  ⟨3,11,6650407168619464,6650407168619465⟩,
  ⟨3,12,4732150814280096,4732150814280097⟩,
  ⟨4,5,2754552923720309,2754552923720310⟩,
  ⟨4,6,5002354534891723,5002354534891724⟩,
  ⟨4,7,3735669482968738,3735669482968739⟩,
  ⟨4,8,4282270455056760,4282270455056761⟩,
  ⟨4,9,6123706000211302,6123706000211303⟩,
  ⟨4,10,6539282661523990,6539282661523991⟩,
  ⟨4,11,7523093991734222,7523093991734223⟩,
  ⟨4,12,6577839718208844,6577839718208845⟩,
  ⟨5,6,6147132288758380,6147132288758381⟩,
  ⟨5,7,3735662091924687,3735662091924688⟩,
  ⟨5,8,4343935857786365,4343935857786366⟩,
  ⟨5,9,4899912030594609,4899912030594610⟩,
  ⟨5,10,4632157029570799,4632157029570800⟩,
  ⟨5,11,6573268037871856,6573268037871857⟩,
  ⟨5,12,5380173794269977,5380173794269978⟩,
  ⟨6,7,2903855974779630,2903855974779631⟩,
  ⟨6,8,3914300408327623,3914300408327624⟩,
  ⟨6,9,4773435594800275,4773435594800276⟩,
  ⟨6,10,6337664093215963,6337664093215964⟩,
  ⟨6,11,5084637066776294,5084637066776295⟩,
  ⟨6,12,5159692711378569,5159692711378570⟩,
  ⟨7,8,1857164901104073,1857164901104074⟩,
  ⟨7,9,2884385954691389,2884385954691390⟩,
  ⟨7,10,3892455646846731,3892455646846732⟩,
  ⟨7,11,3891382719496023,3891382719496024⟩,
  ⟨7,12,3890687065652957,3890687065652958⟩,
  ⟨8,9,3897372410557997,3897372410557998⟩,
  ⟨8,10,4419853525982634,4419853525982635⟩,
  ⟨8,11,4463168274829526,4463168274829527⟩,
  ⟨8,12,5362699684265047,5362699684265048⟩,
  ⟨9,10,1818815463124570,1818815463124571⟩,
  ⟨9,11,1819173071587549,1819173071587550⟩,
  ⟨9,12,1818997720289387,1818997720289388⟩,
  ⟨10,11,2968524561969234,2968524561969235⟩,
  ⟨10,12,2968608019191434,2968608019191435⟩,
  ⟨11,12,2968460030732104,2968460030732105⟩]

/-- Every row of the source `nuclearPairs` ledger is a distinct `a < b` pair of
    recorded nuclei whose charge product matches the ledger and whose recorded
    nanohartree lies within `1/10^9` hartree of the kernel repulsion. -/
theorem nuclearPairs_same_account :
    ∀ row ∈ Reentry.Source.nuclearReadout.targetLedger.nuclearPairs.toList,
      ∃ a b : Fin 13, a < b ∧
        row[0]! = (a.val : ℤ) ∧ row[1]! = (b.val : ℤ) ∧
        row[2]! = (((nuclearChargeNat a * nuclearChargeNat b : ℕ)) : ℤ) ∧
        |nuclearRepulsion a b - (row[4]! : ℝ) / 10^9| ≤ (1 : ℝ) / 10^9 := by
  intro row hrow
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hrow
  have hlen : Reentry.Source.nuclearReadout.targetLedger.nuclearPairs.toList.length = 78 := by
    decide
  rw [hlen] at hi
  interval_cases i
  · refine ⟨(pairCert[0]!).1, (pairCert[0]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[0]!).2.2.1 (pairCert[0]!).2.2.2
      (nuclearChargeNat (pairCert[0]!).1 * nuclearChargeNat (pairCert[0]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[1]!).1, (pairCert[1]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[1]!).2.2.1 (pairCert[1]!).2.2.2
      (nuclearChargeNat (pairCert[1]!).1 * nuclearChargeNat (pairCert[1]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[2]!).1, (pairCert[2]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[2]!).2.2.1 (pairCert[2]!).2.2.2
      (nuclearChargeNat (pairCert[2]!).1 * nuclearChargeNat (pairCert[2]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[3]!).1, (pairCert[3]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[3]!).2.2.1 (pairCert[3]!).2.2.2
      (nuclearChargeNat (pairCert[3]!).1 * nuclearChargeNat (pairCert[3]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[4]!).1, (pairCert[4]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[4]!).2.2.1 (pairCert[4]!).2.2.2
      (nuclearChargeNat (pairCert[4]!).1 * nuclearChargeNat (pairCert[4]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[5]!).1, (pairCert[5]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[5]!).2.2.1 (pairCert[5]!).2.2.2
      (nuclearChargeNat (pairCert[5]!).1 * nuclearChargeNat (pairCert[5]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[6]!).1, (pairCert[6]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[6]!).2.2.1 (pairCert[6]!).2.2.2
      (nuclearChargeNat (pairCert[6]!).1 * nuclearChargeNat (pairCert[6]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[7]!).1, (pairCert[7]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[7]!).2.2.1 (pairCert[7]!).2.2.2
      (nuclearChargeNat (pairCert[7]!).1 * nuclearChargeNat (pairCert[7]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[8]!).1, (pairCert[8]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[8]!).2.2.1 (pairCert[8]!).2.2.2
      (nuclearChargeNat (pairCert[8]!).1 * nuclearChargeNat (pairCert[8]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[9]!).1, (pairCert[9]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[9]!).2.2.1 (pairCert[9]!).2.2.2
      (nuclearChargeNat (pairCert[9]!).1 * nuclearChargeNat (pairCert[9]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[10]!).1, (pairCert[10]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[10]!).2.2.1 (pairCert[10]!).2.2.2
      (nuclearChargeNat (pairCert[10]!).1 * nuclearChargeNat (pairCert[10]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[11]!).1, (pairCert[11]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[11]!).2.2.1 (pairCert[11]!).2.2.2
      (nuclearChargeNat (pairCert[11]!).1 * nuclearChargeNat (pairCert[11]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[12]!).1, (pairCert[12]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[12]!).2.2.1 (pairCert[12]!).2.2.2
      (nuclearChargeNat (pairCert[12]!).1 * nuclearChargeNat (pairCert[12]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[13]!).1, (pairCert[13]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[13]!).2.2.1 (pairCert[13]!).2.2.2
      (nuclearChargeNat (pairCert[13]!).1 * nuclearChargeNat (pairCert[13]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[14]!).1, (pairCert[14]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[14]!).2.2.1 (pairCert[14]!).2.2.2
      (nuclearChargeNat (pairCert[14]!).1 * nuclearChargeNat (pairCert[14]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[15]!).1, (pairCert[15]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[15]!).2.2.1 (pairCert[15]!).2.2.2
      (nuclearChargeNat (pairCert[15]!).1 * nuclearChargeNat (pairCert[15]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[16]!).1, (pairCert[16]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[16]!).2.2.1 (pairCert[16]!).2.2.2
      (nuclearChargeNat (pairCert[16]!).1 * nuclearChargeNat (pairCert[16]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[17]!).1, (pairCert[17]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[17]!).2.2.1 (pairCert[17]!).2.2.2
      (nuclearChargeNat (pairCert[17]!).1 * nuclearChargeNat (pairCert[17]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[18]!).1, (pairCert[18]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[18]!).2.2.1 (pairCert[18]!).2.2.2
      (nuclearChargeNat (pairCert[18]!).1 * nuclearChargeNat (pairCert[18]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[19]!).1, (pairCert[19]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[19]!).2.2.1 (pairCert[19]!).2.2.2
      (nuclearChargeNat (pairCert[19]!).1 * nuclearChargeNat (pairCert[19]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[20]!).1, (pairCert[20]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[20]!).2.2.1 (pairCert[20]!).2.2.2
      (nuclearChargeNat (pairCert[20]!).1 * nuclearChargeNat (pairCert[20]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[21]!).1, (pairCert[21]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[21]!).2.2.1 (pairCert[21]!).2.2.2
      (nuclearChargeNat (pairCert[21]!).1 * nuclearChargeNat (pairCert[21]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[22]!).1, (pairCert[22]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[22]!).2.2.1 (pairCert[22]!).2.2.2
      (nuclearChargeNat (pairCert[22]!).1 * nuclearChargeNat (pairCert[22]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[23]!).1, (pairCert[23]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[23]!).2.2.1 (pairCert[23]!).2.2.2
      (nuclearChargeNat (pairCert[23]!).1 * nuclearChargeNat (pairCert[23]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[24]!).1, (pairCert[24]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[24]!).2.2.1 (pairCert[24]!).2.2.2
      (nuclearChargeNat (pairCert[24]!).1 * nuclearChargeNat (pairCert[24]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[25]!).1, (pairCert[25]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[25]!).2.2.1 (pairCert[25]!).2.2.2
      (nuclearChargeNat (pairCert[25]!).1 * nuclearChargeNat (pairCert[25]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[26]!).1, (pairCert[26]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[26]!).2.2.1 (pairCert[26]!).2.2.2
      (nuclearChargeNat (pairCert[26]!).1 * nuclearChargeNat (pairCert[26]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[27]!).1, (pairCert[27]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[27]!).2.2.1 (pairCert[27]!).2.2.2
      (nuclearChargeNat (pairCert[27]!).1 * nuclearChargeNat (pairCert[27]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[28]!).1, (pairCert[28]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[28]!).2.2.1 (pairCert[28]!).2.2.2
      (nuclearChargeNat (pairCert[28]!).1 * nuclearChargeNat (pairCert[28]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[29]!).1, (pairCert[29]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[29]!).2.2.1 (pairCert[29]!).2.2.2
      (nuclearChargeNat (pairCert[29]!).1 * nuclearChargeNat (pairCert[29]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[30]!).1, (pairCert[30]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[30]!).2.2.1 (pairCert[30]!).2.2.2
      (nuclearChargeNat (pairCert[30]!).1 * nuclearChargeNat (pairCert[30]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[31]!).1, (pairCert[31]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[31]!).2.2.1 (pairCert[31]!).2.2.2
      (nuclearChargeNat (pairCert[31]!).1 * nuclearChargeNat (pairCert[31]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[32]!).1, (pairCert[32]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[32]!).2.2.1 (pairCert[32]!).2.2.2
      (nuclearChargeNat (pairCert[32]!).1 * nuclearChargeNat (pairCert[32]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[33]!).1, (pairCert[33]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[33]!).2.2.1 (pairCert[33]!).2.2.2
      (nuclearChargeNat (pairCert[33]!).1 * nuclearChargeNat (pairCert[33]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[34]!).1, (pairCert[34]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[34]!).2.2.1 (pairCert[34]!).2.2.2
      (nuclearChargeNat (pairCert[34]!).1 * nuclearChargeNat (pairCert[34]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[35]!).1, (pairCert[35]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[35]!).2.2.1 (pairCert[35]!).2.2.2
      (nuclearChargeNat (pairCert[35]!).1 * nuclearChargeNat (pairCert[35]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[36]!).1, (pairCert[36]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[36]!).2.2.1 (pairCert[36]!).2.2.2
      (nuclearChargeNat (pairCert[36]!).1 * nuclearChargeNat (pairCert[36]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[37]!).1, (pairCert[37]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[37]!).2.2.1 (pairCert[37]!).2.2.2
      (nuclearChargeNat (pairCert[37]!).1 * nuclearChargeNat (pairCert[37]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[38]!).1, (pairCert[38]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[38]!).2.2.1 (pairCert[38]!).2.2.2
      (nuclearChargeNat (pairCert[38]!).1 * nuclearChargeNat (pairCert[38]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[39]!).1, (pairCert[39]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[39]!).2.2.1 (pairCert[39]!).2.2.2
      (nuclearChargeNat (pairCert[39]!).1 * nuclearChargeNat (pairCert[39]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[40]!).1, (pairCert[40]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[40]!).2.2.1 (pairCert[40]!).2.2.2
      (nuclearChargeNat (pairCert[40]!).1 * nuclearChargeNat (pairCert[40]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[41]!).1, (pairCert[41]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[41]!).2.2.1 (pairCert[41]!).2.2.2
      (nuclearChargeNat (pairCert[41]!).1 * nuclearChargeNat (pairCert[41]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[42]!).1, (pairCert[42]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[42]!).2.2.1 (pairCert[42]!).2.2.2
      (nuclearChargeNat (pairCert[42]!).1 * nuclearChargeNat (pairCert[42]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[43]!).1, (pairCert[43]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[43]!).2.2.1 (pairCert[43]!).2.2.2
      (nuclearChargeNat (pairCert[43]!).1 * nuclearChargeNat (pairCert[43]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[44]!).1, (pairCert[44]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[44]!).2.2.1 (pairCert[44]!).2.2.2
      (nuclearChargeNat (pairCert[44]!).1 * nuclearChargeNat (pairCert[44]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[45]!).1, (pairCert[45]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[45]!).2.2.1 (pairCert[45]!).2.2.2
      (nuclearChargeNat (pairCert[45]!).1 * nuclearChargeNat (pairCert[45]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[46]!).1, (pairCert[46]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[46]!).2.2.1 (pairCert[46]!).2.2.2
      (nuclearChargeNat (pairCert[46]!).1 * nuclearChargeNat (pairCert[46]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[47]!).1, (pairCert[47]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[47]!).2.2.1 (pairCert[47]!).2.2.2
      (nuclearChargeNat (pairCert[47]!).1 * nuclearChargeNat (pairCert[47]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[48]!).1, (pairCert[48]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[48]!).2.2.1 (pairCert[48]!).2.2.2
      (nuclearChargeNat (pairCert[48]!).1 * nuclearChargeNat (pairCert[48]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[49]!).1, (pairCert[49]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[49]!).2.2.1 (pairCert[49]!).2.2.2
      (nuclearChargeNat (pairCert[49]!).1 * nuclearChargeNat (pairCert[49]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[50]!).1, (pairCert[50]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[50]!).2.2.1 (pairCert[50]!).2.2.2
      (nuclearChargeNat (pairCert[50]!).1 * nuclearChargeNat (pairCert[50]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[51]!).1, (pairCert[51]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[51]!).2.2.1 (pairCert[51]!).2.2.2
      (nuclearChargeNat (pairCert[51]!).1 * nuclearChargeNat (pairCert[51]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[52]!).1, (pairCert[52]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[52]!).2.2.1 (pairCert[52]!).2.2.2
      (nuclearChargeNat (pairCert[52]!).1 * nuclearChargeNat (pairCert[52]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[53]!).1, (pairCert[53]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[53]!).2.2.1 (pairCert[53]!).2.2.2
      (nuclearChargeNat (pairCert[53]!).1 * nuclearChargeNat (pairCert[53]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[54]!).1, (pairCert[54]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[54]!).2.2.1 (pairCert[54]!).2.2.2
      (nuclearChargeNat (pairCert[54]!).1 * nuclearChargeNat (pairCert[54]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[55]!).1, (pairCert[55]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[55]!).2.2.1 (pairCert[55]!).2.2.2
      (nuclearChargeNat (pairCert[55]!).1 * nuclearChargeNat (pairCert[55]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[56]!).1, (pairCert[56]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[56]!).2.2.1 (pairCert[56]!).2.2.2
      (nuclearChargeNat (pairCert[56]!).1 * nuclearChargeNat (pairCert[56]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[57]!).1, (pairCert[57]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[57]!).2.2.1 (pairCert[57]!).2.2.2
      (nuclearChargeNat (pairCert[57]!).1 * nuclearChargeNat (pairCert[57]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[58]!).1, (pairCert[58]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[58]!).2.2.1 (pairCert[58]!).2.2.2
      (nuclearChargeNat (pairCert[58]!).1 * nuclearChargeNat (pairCert[58]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[59]!).1, (pairCert[59]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[59]!).2.2.1 (pairCert[59]!).2.2.2
      (nuclearChargeNat (pairCert[59]!).1 * nuclearChargeNat (pairCert[59]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[60]!).1, (pairCert[60]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[60]!).2.2.1 (pairCert[60]!).2.2.2
      (nuclearChargeNat (pairCert[60]!).1 * nuclearChargeNat (pairCert[60]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[61]!).1, (pairCert[61]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[61]!).2.2.1 (pairCert[61]!).2.2.2
      (nuclearChargeNat (pairCert[61]!).1 * nuclearChargeNat (pairCert[61]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[62]!).1, (pairCert[62]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[62]!).2.2.1 (pairCert[62]!).2.2.2
      (nuclearChargeNat (pairCert[62]!).1 * nuclearChargeNat (pairCert[62]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[63]!).1, (pairCert[63]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[63]!).2.2.1 (pairCert[63]!).2.2.2
      (nuclearChargeNat (pairCert[63]!).1 * nuclearChargeNat (pairCert[63]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[64]!).1, (pairCert[64]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[64]!).2.2.1 (pairCert[64]!).2.2.2
      (nuclearChargeNat (pairCert[64]!).1 * nuclearChargeNat (pairCert[64]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[65]!).1, (pairCert[65]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[65]!).2.2.1 (pairCert[65]!).2.2.2
      (nuclearChargeNat (pairCert[65]!).1 * nuclearChargeNat (pairCert[65]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[66]!).1, (pairCert[66]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[66]!).2.2.1 (pairCert[66]!).2.2.2
      (nuclearChargeNat (pairCert[66]!).1 * nuclearChargeNat (pairCert[66]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[67]!).1, (pairCert[67]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[67]!).2.2.1 (pairCert[67]!).2.2.2
      (nuclearChargeNat (pairCert[67]!).1 * nuclearChargeNat (pairCert[67]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[68]!).1, (pairCert[68]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[68]!).2.2.1 (pairCert[68]!).2.2.2
      (nuclearChargeNat (pairCert[68]!).1 * nuclearChargeNat (pairCert[68]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[69]!).1, (pairCert[69]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[69]!).2.2.1 (pairCert[69]!).2.2.2
      (nuclearChargeNat (pairCert[69]!).1 * nuclearChargeNat (pairCert[69]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[70]!).1, (pairCert[70]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[70]!).2.2.1 (pairCert[70]!).2.2.2
      (nuclearChargeNat (pairCert[70]!).1 * nuclearChargeNat (pairCert[70]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[71]!).1, (pairCert[71]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[71]!).2.2.1 (pairCert[71]!).2.2.2
      (nuclearChargeNat (pairCert[71]!).1 * nuclearChargeNat (pairCert[71]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[72]!).1, (pairCert[72]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[72]!).2.2.1 (pairCert[72]!).2.2.2
      (nuclearChargeNat (pairCert[72]!).1 * nuclearChargeNat (pairCert[72]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[73]!).1, (pairCert[73]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[73]!).2.2.1 (pairCert[73]!).2.2.2
      (nuclearChargeNat (pairCert[73]!).1 * nuclearChargeNat (pairCert[73]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[74]!).1, (pairCert[74]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[74]!).2.2.1 (pairCert[74]!).2.2.2
      (nuclearChargeNat (pairCert[74]!).1 * nuclearChargeNat (pairCert[74]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[75]!).1, (pairCert[75]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[75]!).2.2.1 (pairCert[75]!).2.2.2
      (nuclearChargeNat (pairCert[75]!).1 * nuclearChargeNat (pairCert[75]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[76]!).1, (pairCert[76]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[76]!).2.2.1 (pairCert[76]!).2.2.2
      (nuclearChargeNat (pairCert[76]!).1 * nuclearChargeNat (pairCert[76]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
  · refine ⟨(pairCert[77]!).1, (pairCert[77]!).2.1,
      by decide +revert, by decide +revert, by decide +revert, by decide +revert, ?_⟩
    exact repulsion_close _ _ _ (pairCert[77]!).2.2.1 (pairCert[77]!).2.2.2
      (nuclearChargeNat (pairCert[77]!).1 * nuclearChargeNat (pairCert[77]!).2.1) rfl
      (by decide +revert) (by decide +revert) (by decide +revert) (by decide +revert)
        (by decide +revert) (by decide +revert)
end
end LAlanine40K2025.BasinRefinement.WholeBandBasin.Family.All.Nuclear
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
