import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceCanonical79BraScalarKernel
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

theorem actual_scalar_entry_34_23 : axialInverse Complex.I 0 34 23 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 109 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator109_point,actual_denominator_point]
  have hn : numeratorPoint 109 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_31 : axialInverse Complex.I 0 34 31 =
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

theorem actual_scalar_entry_34_35 : axialInverse Complex.I 0 34 35 =
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

theorem actual_scalar_entry_34_55 : axialInverse Complex.I 0 34 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_56 : axialInverse Complex.I 0 34 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_61 : axialInverse Complex.I 0 34 61 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 111 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator111_point,actual_denominator_point]
  have hn : numeratorPoint 111 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_63 : axialInverse Complex.I 0 34 63 =
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

theorem actual_scalar_entry_34_67 : axialInverse Complex.I 0 34 67 =
    (((-483984375/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 112 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator112_point,actual_denominator_point]
  have hn : numeratorPoint 112 = (((-636605335142066462879/999502313552216064) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_71 : axialInverse Complex.I 0 34 71 =
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

theorem actual_scalar_entry_34_73 : axialInverse Complex.I 0 34 73 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 113 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator113_point,actual_denominator_point]
  have hn : numeratorPoint 113 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_34_77 : axialInverse Complex.I 0 34 77 =
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

theorem actual_scalar_entry_35_18 : axialInverse Complex.I 0 35 18 =
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

theorem actual_scalar_entry_35_19 : axialInverse Complex.I 0 35 19 =
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

theorem actual_scalar_entry_35_22 : axialInverse Complex.I 0 35 22 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 109 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator109_point,actual_denominator_point]
  have hn : numeratorPoint 109 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_35_30 : axialInverse Complex.I 0 35 30 =
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

theorem actual_scalar_entry_35_31 : axialInverse Complex.I 0 35 31 =
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

theorem actual_scalar_entry_35_34 : axialInverse Complex.I 0 35 34 =
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

theorem actual_scalar_entry_35_35 : axialInverse Complex.I 0 35 35 =
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

theorem actual_scalar_entry_35_55 : axialInverse Complex.I 0 35 55 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_35_56 : axialInverse Complex.I 0 35 56 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_35_61 : axialInverse Complex.I 0 35 61 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 116 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator116_point,actual_denominator_point]
  have hn : numeratorPoint 116 = (0 : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_35_63 : axialInverse Complex.I 0 35 63 =
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

theorem actual_scalar_entry_35_67 : axialInverse Complex.I 0 35 67 =
    (((-2131440625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 117 / denominator Complex.I 0 0) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator117_point,actual_denominator_point]
  have hn : numeratorPoint 117 = (((-1051340608940273592585263/374813367582081024000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_36_1 : axialInverse Complex.I 0 36 1 =
    (((-28603494981963/4196399522957000) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 11 / denominator Complex.I 0 0) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator11_point,actual_denominator_point]
  have hn : numeratorPoint 11 = (((-3854351021054933968234856311/3904305912313344000000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_36_36 : axialInverse Complex.I 0 36 36 =
    (((354007878702773/3357119618365600) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 119 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator119_point,actual_denominator_point]
  have hn : numeratorPoint 119 = ((429326404566976143648794270929/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_36_49 : axialInverse Complex.I 0 36 49 =
    (((71/1640) : ℂ)*(Real.sqrt 15 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 121 / denominator Complex.I 0 0) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator121_point,actual_denominator_point]
  have hn : numeratorPoint 121 = (((8813045102775141780285837991/1405550128432803840000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_37_0 : axialInverse Complex.I 0 37 0 =
    (((28603494981963/4196399522957000) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 27 / denominator Complex.I 0 0) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator27_point,actual_denominator_point]
  have hn : numeratorPoint 27 = (((3854351021054933968234856311/3904305912313344000000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_37_37 : axialInverse Complex.I 0 37 37 =
    (((354007878702773/3357119618365600) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 119 / denominator Complex.I 0 0) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator119_point,actual_denominator_point]
  have hn : numeratorPoint 119 = ((429326404566976143648794270929/234258354738800640000000000) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_37_51 : axialInverse Complex.I 0 37 51 =
    (((-71/1640) : ℂ)*(Real.sqrt 15 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 132 / denominator Complex.I 0 0) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator132_point,actual_denominator_point]
  have hn : numeratorPoint 132 = (((-8813045102775141780285837991/1405550128432803840000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 0 = ((5089223228363110042136892361/146411471711750400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_38_3 : axialInverse Complex.I 0 38 3 =
    (((-534798/20798405) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 186 / denominator Complex.I 0 1) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator186_point,actual_denominator_point]
  have hn : numeratorPoint 186 = (((-6290321572306551200243471/493581389408501760000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_38_38 : axialInverse Complex.I 0 38 38 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 215 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator215_point,actual_denominator_point]
  have hn : numeratorPoint 215 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_39_2 : axialInverse Complex.I 0 39 2 =
    (((534798/20798405) : ℂ)*(Real.sqrt 30 : ℂ)*Complex.I)/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 193 / denominator Complex.I 0 1) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator193_point,actual_denominator_point]
  have hn : numeratorPoint 193 = (((6290321572306551200243471/493581389408501760000000) * Complex.I) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_39_39 : axialInverse Complex.I 0 39 39 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 215 / denominator Complex.I 0 1) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator215_point,actual_denominator_point]
  have hn : numeratorPoint 215 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 1 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_40_4 : axialInverse Complex.I 0 40 4 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 185 / denominator Complex.I 0 2) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator185_point,actual_denominator_point]
  have hn : numeratorPoint 185 = (0 : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_40_40 : axialInverse Complex.I 0 40 40 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 215 / denominator Complex.I 0 2) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator215_point,actual_denominator_point]
  have hn : numeratorPoint 215 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_41_5 : axialInverse Complex.I 0 41 5 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 185 / denominator Complex.I 0 2) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator185_point,actual_denominator_point]
  have hn : numeratorPoint 185 = (0 : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_41_41 : axialInverse Complex.I 0 41 41 =
    (((492804417/22221015902) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 215 / denominator Complex.I 0 2) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator215_point,actual_denominator_point]
  have hn : numeratorPoint 215 = ((13020720831119279499364549/9871627788170035200000000) : ℂ) := rfl
  have hd : denominatorPoint 2 = ((880674872209406859519368641/7403720841127526400000000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_7 : axialInverse Complex.I 0 42 7 =
    (((294407560425/173640474989264) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 265 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator265_point,actual_denominator_point]
  have hn : numeratorPoint 265 = ((-117780502224385409585/2313662762852352) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_10 : axialInverse Complex.I 0 42 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 286 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator286_point,actual_denominator_point]
  have hn : numeratorPoint 286 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_11 : axialInverse Complex.I 0 42 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 298 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator298_point,actual_denominator_point]
  have hn : numeratorPoint 298 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_42 : axialInverse Complex.I 0 42 42 =
    (((19468076179961375/274525590958026384) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 375 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator375_point,actual_denominator_point]
  have hn : numeratorPoint 375 = ((-1773446580038113611299/6940988288557056) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_43 : axialInverse Complex.I 0 42 43 =
    (((11431855535683375/274525590958026384) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 376 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator376_point,actual_denominator_point]
  have hn : numeratorPoint 376 = ((-1041386160390897042163/6940988288557056) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_46 : axialInverse Complex.I 0 42 46 =
    (((292984375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 377 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator377_point,actual_denominator_point]
  have hn : numeratorPoint 377 = ((-46232763467512763875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_47 : axialInverse Complex.I 0 42 47 =
    (((-1374484375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 378 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator378_point,actual_denominator_point]
  have hn : numeratorPoint 378 = ((216892832592752135875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_48 : axialInverse Complex.I 0 42 48 =
    (((25/3287) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 379 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator379_point,actual_denominator_point]
  have hn : numeratorPoint 379 = ((-99064256664462595505/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_50 : axialInverse Complex.I 0 42 50 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 380 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator380_point,actual_denominator_point]
  have hn : numeratorPoint 380 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_53 : axialInverse Complex.I 0 42 53 =
    (((125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 382 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator382_point,actual_denominator_point]
  have hn : numeratorPoint 382 = ((-123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_54 : axialInverse Complex.I 0 42 54 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 383 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator383_point,actual_denominator_point]
  have hn : numeratorPoint 383 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_57 : axialInverse Complex.I 0 42 57 =
    (((-125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 384 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator384_point,actual_denominator_point]
  have hn : numeratorPoint 384 = ((123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_58 : axialInverse Complex.I 0 42 58 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 385 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator385_point,actual_denominator_point]
  have hn : numeratorPoint 385 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_60 : axialInverse Complex.I 0 42 60 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 386 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator386_point,actual_denominator_point]
  have hn : numeratorPoint 386 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_64 : axialInverse Complex.I 0 42 64 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 387 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator387_point,actual_denominator_point]
  have hn : numeratorPoint 387 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_42_66 : axialInverse Complex.I 0 42 66 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 388 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator388_point,actual_denominator_point]
  have hn : numeratorPoint 388 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_6 : axialInverse Complex.I 0 43 6 =
    (((696087999675/173640474989264) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 242 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator242_point,actual_denominator_point]
  have hn : numeratorPoint 242 = ((-30941836048162774715/257073640316928) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_7 : axialInverse Complex.I 0 43 7 =
    (((-696087999675/173640474989264) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 266 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator266_point,actual_denominator_point]
  have hn : numeratorPoint 266 = ((30941836048162774715/257073640316928) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_10 : axialInverse Complex.I 0 43 10 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 287 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator287_point,actual_denominator_point]
  have hn : numeratorPoint 287 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_11 : axialInverse Complex.I 0 43 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 299 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator299_point,actual_denominator_point]
  have hn : numeratorPoint 299 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_42 : axialInverse Complex.I 0 43 42 =
    (((11431855535683375/274525590958026384) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 376 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator376_point,actual_denominator_point]
  have hn : numeratorPoint 376 = ((-1041386160390897042163/6940988288557056) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_43 : axialInverse Complex.I 0 43 43 =
    (((19468076179961375/274525590958026384) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 394 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator394_point,actual_denominator_point]
  have hn : numeratorPoint 394 = ((-1773446580038113611299/6940988288557056) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_46 : axialInverse Complex.I 0 43 46 =
    (((292984375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 395 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator395_point,actual_denominator_point]
  have hn : numeratorPoint 395 = ((-46232763467512763875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_47 : axialInverse Complex.I 0 43 47 =
    (((-1374484375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 396 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator396_point,actual_denominator_point]
  have hn : numeratorPoint 396 = ((216892832592752135875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_48 : axialInverse Complex.I 0 43 48 =
    (((-25/3287) : ℂ)*(Real.sqrt 15 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 397 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator397_point,actual_denominator_point]
  have hn : numeratorPoint 397 = ((99064256664462595505/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_50 : axialInverse Complex.I 0 43 50 =
    (((-125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 398 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator398_point,actual_denominator_point]
  have hn : numeratorPoint 398 = ((123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_52 : axialInverse Complex.I 0 43 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 399 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator399_point,actual_denominator_point]
  have hn : numeratorPoint 399 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_53 : axialInverse Complex.I 0 43 53 =
    (((-125/6324) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 400 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator400_point,actual_denominator_point]
  have hn : numeratorPoint 400 = ((123576550913126584981/867623536069632) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_54 : axialInverse Complex.I 0 43 54 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 401 / denominator Complex.I 0 3) * (((3/25) * (Real.sqrt 30 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator401_point,actual_denominator_point]
  have hn : numeratorPoint 401 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_57 : axialInverse Complex.I 0 43 57 =
    (((125/3162) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 402 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator402_point,actual_denominator_point]
  have hn : numeratorPoint 402 = ((-123576550913126584981/433811768034816) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_58 : axialInverse Complex.I 0 43 58 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 403 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator403_point,actual_denominator_point]
  have hn : numeratorPoint 403 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_43_66 : axialInverse Complex.I 0 43 66 =
    (((-305506875/52826429872) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 406 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator406_point,actual_denominator_point]
  have hn : numeratorPoint 406 = ((16069602220907956285/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_6 : axialInverse Complex.I 0 46 6 =
    (((58078125/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 243 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator243_point,actual_denominator_point]
  have hn : numeratorPoint 243 = ((-25457484016962790625/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_7 : axialInverse Complex.I 0 46 7 =
    (((-58078125/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 267 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator267_point,actual_denominator_point]
  have hn : numeratorPoint 267 = ((25457484016962790625/385610460475392) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_11 : axialInverse Complex.I 0 46 11 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 289 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator289_point,actual_denominator_point]
  have hn : numeratorPoint 289 = (0 : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_42 : axialInverse Complex.I 0 46 42 =
    (((292984375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 377 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator377_point,actual_denominator_point]
  have hn : numeratorPoint 377 = ((-46232763467512763875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_43 : axialInverse Complex.I 0 46 43 =
    (((292984375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 395 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator395_point,actual_denominator_point]
  have hn : numeratorPoint 395 = ((-46232763467512763875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_48 : axialInverse Complex.I 0 46 48 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(((3/25) * (Real.sqrt 30 : ℂ)) : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_50 : axialInverse Complex.I 0 46 50 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_53 : axialInverse Complex.I 0 46 53 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_57 : axialInverse Complex.I 0 46 57 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_58 : axialInverse Complex.I 0 46 58 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 412 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator412_point,actual_denominator_point]
  have hn : numeratorPoint 412 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_60 : axialInverse Complex.I 0 46 60 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 413 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator413_point,actual_denominator_point]
  have hn : numeratorPoint 413 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_64 : axialInverse Complex.I 0 46 64 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 413 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator413_point,actual_denominator_point]
  have hn : numeratorPoint 413 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_46_66 : axialInverse Complex.I 0 46 66 =
    (((-290390625/26413214936) : ℂ)*(Real.sqrt 2 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 412 / denominator Complex.I 0 3) * (1 : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator412_point,actual_denominator_point]
  have hn : numeratorPoint 412 = ((5091496803392558125/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_6 : axialInverse Complex.I 0 47 6 =
    (((255772875/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 244 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator244_point,actual_denominator_point]
  have hn : numeratorPoint 244 = ((-336340087285107175525/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_7 : axialInverse Complex.I 0 47 7 =
    (((-255772875/26413214936) : ℂ)*(Real.sqrt 30 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 268 / denominator Complex.I 0 3) * (((6/25) * (Real.sqrt 15 : ℂ)) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator268_point,actual_denominator_point]
  have hn : numeratorPoint 268 = ((336340087285107175525/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_42 : axialInverse Complex.I 0 47 42 =
    (((-1374484375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 378 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator378_point,actual_denominator_point]
  have hn : numeratorPoint 378 = ((216892832592752135875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_43 : axialInverse Complex.I 0 47 43 =
    (((-1374484375/26413214936) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 396 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator396_point,actual_denominator_point]
  have hn : numeratorPoint 396 = ((216892832592752135875/1156831381426176) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_47 : axialInverse Complex.I 0 47 47 =
    (((1156159125/13206607468) : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ) * (numeratorPolynomial Complex.I 0 417 / denominator Complex.I 0 3) * ((Real.sqrt 2 : ℂ) : ℂ) / (lapse : ℂ) = _
  rw [actual_numerator417_point,actual_denominator_point]
  have hn : numeratorPoint 417 = ((-20271248388788849617/64268410079232) : ℂ) := rfl
  have hd : denominatorPoint 3 = ((-65124842331217710284987/9037745167392000) : ℂ) := rfl
  rw [hn,hd]
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring

theorem actual_scalar_entry_47_52 : axialInverse Complex.I 0 47 52 =
    ((0 : ℂ))/(lapse : ℂ) := by
  change ((Real.sqrt 2 : ℂ) : ℂ)*0*(1 : ℂ)/(lapse : ℂ) = _
  norm_num
  all_goals try simp only [ActualCandidateBra.sqrt30_factor]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq,ActualCandidateBra.sqrt2_square,ActualCandidateBra.sqrt15_square]
  all_goals ring


end LowEnergy.ActualCanonical79Imaginary
