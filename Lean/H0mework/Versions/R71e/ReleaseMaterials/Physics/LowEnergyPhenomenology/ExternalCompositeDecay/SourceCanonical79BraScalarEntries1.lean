import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCanonical79BraScalarKernel
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.ActualCanonical79Imaginary
open MixedSpectatorCanonical79Data
open SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
open scoped BigOperators Matrix

theorem actual_scalar_entry_18_31 : axialInverse Complex.I 0 18 31 =
    (((74437728291/541470906188) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 38 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator38_point,actual_denominator_point]
  have hn : numeratorPoint 38 = (((310947426562899120376716337/130143530410444800000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_35 : axialInverse Complex.I 0 18 35 =
    (((1278864375/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 40 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator40_point,actual_denominator_point]
  have hn : numeratorPoint 40 = (((1051340608940273592585263/1249377891940270080000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_55 : axialInverse Complex.I 0 18 55 =
    (((-353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 45 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator45_point,actual_denominator_point]
  have hn : numeratorPoint 45 = ((-3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_56 : axialInverse Complex.I 0 18 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 46 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator46_point,actual_denominator_point]
  have hn : numeratorPoint 46 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_61 : axialInverse Complex.I 0 18 61 =
    (((136349674707/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 47 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator47_point,actual_denominator_point]
  have hn : numeratorPoint 47 = ((1708713367652148228219566147/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_63 : axialInverse Complex.I 0 18 63 =
    (((180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 48 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator48_point,actual_denominator_point]
  have hn : numeratorPoint 48 = ((2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_67 : axialInverse Complex.I 0 18 67 =
    (((-6343882959/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 49 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator49_point,actual_denominator_point]
  have hn : numeratorPoint 49 = ((-3259523597430378755370051799/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_71 : axialInverse Complex.I 0 18 71 =
    (((-124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 50 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator50_point,actual_denominator_point]
  have hn : numeratorPoint 50 = (((-310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_73 : axialInverse Complex.I 0 18 73 =
    (((227249457845/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 51 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator51_point,actual_denominator_point]
  have hn : numeratorPoint 51 = (((1708713367652148228219566147/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_18_77 : axialInverse Complex.I 0 18 77 =
    (((2900539445/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 52 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator52_point,actual_denominator_point]
  have hn : numeratorPoint 52 = (((894188322264895135298870587/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_18 : axialInverse Complex.I 0 19 18 =
    (((1254786105956609/57071033512215200) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 34 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator34_point,actual_denominator_point]
  have hn : numeratorPoint 34 = ((89514924879639556283603337821/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_19 : axialInverse Complex.I 0 19 19 =
    (((5961120834805891/57071033512215200) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 53 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator53_point,actual_denominator_point]
  have hn : numeratorPoint 53 = ((425259158666964068099586774679/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_22 : axialInverse Complex.I 0 19 22 =
    (((641453125/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 54 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator54_point,actual_denominator_point]
  have hn : numeratorPoint 54 = ((63279803446942504843999/149925347032832409600) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_23 : axialInverse Complex.I 0 19 23 =
    (((160152875/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 55 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator55_point,actual_denominator_point]
  have hn : numeratorPoint 55 = ((1974899267086498352952109/18740668379104051200000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_30 : axialInverse Complex.I 0 19 30 =
    (((74437728291/541470906188) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 38 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator38_point,actual_denominator_point]
  have hn : numeratorPoint 38 = (((310947426562899120376716337/130143530410444800000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_34 : axialInverse Complex.I 0 19 34 =
    (((-290390625/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 57 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator57_point,actual_denominator_point]
  have hn : numeratorPoint 57 = (((-636605335142066462879/3331674378507386880) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_35 : axialInverse Complex.I 0 19 35 =
    (((-1278864375/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 58 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator58_point,actual_denominator_point]
  have hn : numeratorPoint 58 = (((-1051340608940273592585263/1249377891940270080000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_55 : axialInverse Complex.I 0 19 55 =
    (((353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 63 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator63_point,actual_denominator_point]
  have hn : numeratorPoint 63 = ((3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_56 : axialInverse Complex.I 0 19 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 64 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator64_point,actual_denominator_point]
  have hn : numeratorPoint 64 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_61 : axialInverse Complex.I 0 19 61 =
    (((-161401238457/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 65 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator65_point,actual_denominator_point]
  have hn : numeratorPoint 65 = ((-2022655751102641216301029897/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_63 : axialInverse Complex.I 0 19 63 =
    (((-180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 66 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator66_point,actual_denominator_point]
  have hn : numeratorPoint 66 = ((-2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_67 : axialInverse Complex.I 0 19 67 =
    (((5121855459/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 67 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator67_point,actual_denominator_point]
  have hn : numeratorPoint 67 = ((877212943509797593069041433/260287060820889600000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_71 : axialInverse Complex.I 0 19 71 =
    (((124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 68 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator68_point,actual_denominator_point]
  have hn : numeratorPoint 68 = (((310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_73 : axialInverse Complex.I 0 19 73 =
    (((-269002064095/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 69 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator69_point,actual_denominator_point]
  have hn : numeratorPoint 69 = (((-2022655751102641216301029897/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_19_77 : axialInverse Complex.I 0 19 77 =
    (((-1882183195/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 70 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator70_point,actual_denominator_point]
  have hn : numeratorPoint 70 = (((-580245938814402147217406837/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_19 : axialInverse Complex.I 0 22 19 =
    (((641453125/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 54 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator54_point,actual_denominator_point]
  have hn : numeratorPoint 54 = ((63279803446942504843999/149925347032832409600) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_23 : axialInverse Complex.I 0 22 23 =
    (((-40015625/13206607468) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 72 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator72_point,actual_denominator_point]
  have hn : numeratorPoint 72 = ((-3947569644791361286763/74962673516416204800) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_31 : axialInverse Complex.I 0 22 31 =
    (((-290390625/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 57 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator57_point,actual_denominator_point]
  have hn : numeratorPoint 57 = (((-636605335142066462879/3331674378507386880) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_35 : axialInverse Complex.I 0 22 35 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 74 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator74_point,actual_denominator_point]
  have hn : numeratorPoint 74 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_55 : axialInverse Complex.I 0 22 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_56 : axialInverse Complex.I 0 22 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_61 : axialInverse Complex.I 0 22 61 =
    (((-290390625/13206607468) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 77 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator77_point,actual_denominator_point]
  have hn : numeratorPoint 77 = ((-636605335142066462879/832918594626846720) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_63 : axialInverse Complex.I 0 22 63 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 78 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator78_point,actual_denominator_point]
  have hn : numeratorPoint 78 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_67 : axialInverse Complex.I 0 22 67 =
    (((-290390625/13206607468) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 79 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator79_point,actual_denominator_point]
  have hn : numeratorPoint 79 = ((-636605335142066462879/832918594626846720) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_71 : axialInverse Complex.I 0 22 71 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 80 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator80_point,actual_denominator_point]
  have hn : numeratorPoint 80 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_73 : axialInverse Complex.I 0 22 73 =
    (((-483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 81 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator81_point,actual_denominator_point]
  have hn : numeratorPoint 81 = (((-636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_22_77 : axialInverse Complex.I 0 22 77 =
    (((483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 82 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator82_point,actual_denominator_point]
  have hn : numeratorPoint 82 = (((636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_18 : axialInverse Complex.I 0 23 18 =
    (((-2909121625/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 36 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator36_point,actual_denominator_point]
  have hn : numeratorPoint 36 = ((-35873362654763350980117359/18740668379104051200000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_19 : axialInverse Complex.I 0 23 19 =
    (((160152875/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 55 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator55_point,actual_denominator_point]
  have hn : numeratorPoint 55 = ((1974899267086498352952109/18740668379104051200000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_22 : axialInverse Complex.I 0 23 22 =
    (((-40015625/13206607468) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 72 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator72_point,actual_denominator_point]
  have hn : numeratorPoint 72 = ((-3947569644791361286763/74962673516416204800) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_23 : axialInverse Complex.I 0 23 23 =
    (((1156159125/13206607468) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 83 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator83_point,actual_denominator_point]
  have hn : numeratorPoint 83 = ((1584109910676746435112251/1041148243283558400000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_30 : axialInverse Complex.I 0 23 30 =
    (((1278864375/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 40 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator40_point,actual_denominator_point]
  have hn : numeratorPoint 40 = (((1051340608940273592585263/1249377891940270080000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_31 : axialInverse Complex.I 0 23 31 =
    (((-1278864375/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 58 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator58_point,actual_denominator_point]
  have hn : numeratorPoint 58 = (((-1051340608940273592585263/1249377891940270080000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_34 : axialInverse Complex.I 0 23 34 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 74 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator74_point,actual_denominator_point]
  have hn : numeratorPoint 74 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_55 : axialInverse Complex.I 0 23 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_56 : axialInverse Complex.I 0 23 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_71 : axialInverse Complex.I 0 23 71 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 90 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator90_point,actual_denominator_point]
  have hn : numeratorPoint 90 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_73 : axialInverse Complex.I 0 23 73 =
    (((-2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 91 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator91_point,actual_denominator_point]
  have hn : numeratorPoint 91 = (((-1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_23_77 : axialInverse Complex.I 0 23 77 =
    (((2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 92 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator92_point,actual_denominator_point]
  have hn : numeratorPoint 92 = (((1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_24_13 : axialInverse Complex.I 0 24 13 =
    (((-15625/83147952) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 331 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator331_point,actual_denominator_point]
  have hn : numeratorPoint 331 = ((4699442915771470375/6940988288557056) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_24_24 : axialInverse Complex.I 0 24 24 =
    (((152125/10393494) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 330 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator330_point,actual_denominator_point]
  have hn : numeratorPoint 330 = ((-45753776227951035571/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_24_50 : axialInverse Complex.I 0 24 50 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 338 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator338_point,actual_denominator_point]
  have hn : numeratorPoint 338 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_24_53 : axialInverse Complex.I 0 24 53 =
    (((-125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 336 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator336_point,actual_denominator_point]
  have hn : numeratorPoint 336 = ((123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_25_12 : axialInverse Complex.I 0 25 12 =
    (((611673062212006469/2206970437113545440) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 311 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator311_point,actual_denominator_point]
  have hn : numeratorPoint 311 = ((-2887948914216331858691317/2892078453565440000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_25_25 : axialInverse Complex.I 0 25 25 =
    (((-500434632922009219/2206970437113545440) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 355 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator355_point,actual_denominator_point]
  have hn : numeratorPoint 355 = ((2362748572835543872522067/2892078453565440000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_25_52 : axialInverse Complex.I 0 25 52 =
    (((-8/155) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 362 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator362_point,actual_denominator_point]
  have hn : numeratorPoint 362 = ((2100801365523151944677/5648590729620000) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_28_17 : axialInverse Complex.I 0 28 17 =
    (((2626956333/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 207 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator207_point,actual_denominator_point]
  have hn : numeratorPoint 207 = ((7712066754541874426433689/1096847532018892800000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_28_28 : axialInverse Complex.I 0 28 28 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 196 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator196_point,actual_denominator_point]
  have hn : numeratorPoint 196 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_29_16 : axialInverse Complex.I 0 29 16 =
    (((-2626956333/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 199 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator199_point,actual_denominator_point]
  have hn : numeratorPoint 199 = ((-7712066754541874426433689/1096847532018892800000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_29_29 : axialInverse Complex.I 0 29 29 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 196 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator196_point,actual_denominator_point]
  have hn : numeratorPoint 196 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_19 : axialInverse Complex.I 0 30 19 =
    (((-74437728291/541470906188) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 94 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator94_point,actual_denominator_point]
  have hn : numeratorPoint 94 = (((-310947426562899120376716337/130143530410444800000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_23 : axialInverse Complex.I 0 30 23 =
    (((-1278864375/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 96 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator96_point,actual_denominator_point]
  have hn : numeratorPoint 96 = (((-1051340608940273592585263/1249377891940270080000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_31 : axialInverse Complex.I 0 30 31 =
    (((1254786105956609/57071033512215200) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 34 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator34_point,actual_denominator_point]
  have hn : numeratorPoint 34 = ((89514924879639556283603337821/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_35 : axialInverse Complex.I 0 30 35 =
    (((-2909121625/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 36 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator36_point,actual_denominator_point]
  have hn : numeratorPoint 36 = ((-35873362654763350980117359/18740668379104051200000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_55 : axialInverse Complex.I 0 30 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 64 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator64_point,actual_denominator_point]
  have hn : numeratorPoint 64 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_56 : axialInverse Complex.I 0 30 56 =
    (((-353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 45 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator45_point,actual_denominator_point]
  have hn : numeratorPoint 45 = ((-3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_61 : axialInverse Complex.I 0 30 61 =
    (((124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 98 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator98_point,actual_denominator_point]
  have hn : numeratorPoint 98 = (((310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_63 : axialInverse Complex.I 0 30 63 =
    (((227249457845/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 51 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator51_point,actual_denominator_point]
  have hn : numeratorPoint 51 = (((1708713367652148228219566147/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_67 : axialInverse Complex.I 0 30 67 =
    (((-2900539445/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 99 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator99_point,actual_denominator_point]
  have hn : numeratorPoint 99 = (((-894188322264895135298870587/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_71 : axialInverse Complex.I 0 30 71 =
    (((136349674707/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 47 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator47_point,actual_denominator_point]
  have hn : numeratorPoint 47 = ((1708713367652148228219566147/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_73 : axialInverse Complex.I 0 30 73 =
    (((-180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 100 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator100_point,actual_denominator_point]
  have hn : numeratorPoint 100 = ((-2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_30_77 : axialInverse Complex.I 0 30 77 =
    (((-6343882959/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 49 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator49_point,actual_denominator_point]
  have hn : numeratorPoint 49 = ((-3259523597430378755370051799/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_18 : axialInverse Complex.I 0 31 18 =
    (((-74437728291/541470906188) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 94 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator94_point,actual_denominator_point]
  have hn : numeratorPoint 94 = (((-310947426562899120376716337/130143530410444800000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_22 : axialInverse Complex.I 0 31 22 =
    (((290390625/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 102 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator102_point,actual_denominator_point]
  have hn : numeratorPoint 102 = (((636605335142066462879/3331674378507386880) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_23 : axialInverse Complex.I 0 31 23 =
    (((1278864375/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 103 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator103_point,actual_denominator_point]
  have hn : numeratorPoint 103 = (((1051340608940273592585263/1249377891940270080000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_30 : axialInverse Complex.I 0 31 30 =
    (((1254786105956609/57071033512215200) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 34 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator34_point,actual_denominator_point]
  have hn : numeratorPoint 34 = ((89514924879639556283603337821/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_31 : axialInverse Complex.I 0 31 31 =
    (((5961120834805891/57071033512215200) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 53 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator53_point,actual_denominator_point]
  have hn : numeratorPoint 53 = ((425259158666964068099586774679/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_34 : axialInverse Complex.I 0 31 34 =
    (((641453125/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 54 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator54_point,actual_denominator_point]
  have hn : numeratorPoint 54 = ((63279803446942504843999/149925347032832409600) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_35 : axialInverse Complex.I 0 31 35 =
    (((160152875/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 55 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator55_point,actual_denominator_point]
  have hn : numeratorPoint 55 = ((1974899267086498352952109/18740668379104051200000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_55 : axialInverse Complex.I 0 31 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 46 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator46_point,actual_denominator_point]
  have hn : numeratorPoint 46 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_56 : axialInverse Complex.I 0 31 56 =
    (((353/5270) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 63 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator63_point,actual_denominator_point]
  have hn : numeratorPoint 63 = ((3408910435696732153461713479/1464114717117504000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_61 : axialInverse Complex.I 0 31 61 =
    (((-124062880485/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 105 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator105_point,actual_denominator_point]
  have hn : numeratorPoint 105 = (((-310947426562899120376716337/78086118246266880000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_63 : axialInverse Complex.I 0 31 63 =
    (((-269002064095/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 69 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator69_point,actual_denominator_point]
  have hn : numeratorPoint 69 = (((-2022655751102641216301029897/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_67 : axialInverse Complex.I 0 31 67 =
    (((1882183195/52826429872) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 106 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator106_point,actual_denominator_point]
  have hn : numeratorPoint 106 = (((580245938814402147217406837/468516709477601280000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_71 : axialInverse Complex.I 0 31 71 =
    (((-161401238457/1082941812376) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 65 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator65_point,actual_denominator_point]
  have hn : numeratorPoint 65 = ((-2022655751102641216301029897/390430591231334400000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_73 : axialInverse Complex.I 0 31 73 =
    (((180358252539/2165883624752) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 107 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator107_point,actual_denominator_point]
  have hn : numeratorPoint 107 = ((2260222165854200959748285419/780861182462668800000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_31_77 : axialInverse Complex.I 0 31 77 =
    (((5121855459/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 67 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator67_point,actual_denominator_point]
  have hn : numeratorPoint 67 = ((877212943509797593069041433/260287060820889600000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_19 : axialInverse Complex.I 0 34 19 =
    (((290390625/26413214936) : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 102 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator102_point,actual_denominator_point]
  have hn : numeratorPoint 102 = (((636605335142066462879/3331674378507386880) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
