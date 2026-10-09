import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block0000
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block0486
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block0972
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block1458
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block1944
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block2430
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block2916
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block3402
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block3888
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Blocks.Block4374
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight.Address

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 400000000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
open LAlanine40K2025.UnifiedOrbitals
open BasinRefinement SourceFiniteData
open scoped BigOperators
noncomputable section

def sumBound : ℚ := 73862793974669879121443 / 18446744073709551616
def amaxBound : ℚ := 270751228816450671815 / 18446744073709551616
def sourceBound : ℚ := 9327823154664009778946798518702957336296729 / 43556142965880123323311949751266331066368
def reportBound : ℚ := 3950486769081059945858255341180697 / 18446744073709551616000000000000
def hartreeBound : ℚ := 859 / 1000000000
def hartreeNanoBound : ℕ := 859

theorem block0_sum :
    ((List.range' 0 486).map addressMajorant).sum = 1867592230775287123325 / 9223372036854775808 := by
  have h := congrArg Prod.fst (block_0)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block0_max :
    ((List.range' 0 486).map addressMajorant).foldl max 0 = 83700160913998769151 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_0)
  rw [weightBlock_max_eq] at h
  exact h

theorem block0_source :
    ((List.range' 0 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 348062751769964940066999030175909797984255 / 10889035741470030830827987437816582766592 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_0)
  rw [weightBlock_source_eq] at h
  exact h

theorem block0_report :
    ((List.range' 0 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 589641236921761198735190513089293 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_0)
  rw [weightBlock_report_eq] at h
  exact h

theorem block486_sum :
    ((List.range' 486 486).map addressMajorant).sum = 5870463110520067934711 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_486)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block486_max :
    ((List.range' 486 486).map addressMajorant).foldl max 0 = 162370802263716330663 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_486)
  rw [weightBlock_max_eq] at h
  exact h

theorem block486_source :
    ((List.range' 486 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 83360881476597325475530217407240065120955 / 5444517870735015415413993718908291383296 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_486)
  rw [weightBlock_source_eq] at h
  exact h

theorem block486_report :
    ((List.range' 486 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 141218826245874302928783858979611 / 9223372036854775808000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_486)
  rw [weightBlock_report_eq] at h
  exact h

theorem block972_sum :
    ((List.range' 972 486).map addressMajorant).sum = 6872656240108618345393 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_972)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block972_max :
    ((List.range' 972 486).map addressMajorant).foldl max 0 = 270751228816450671815 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_972)
  rw [weightBlock_max_eq] at h
  exact h

theorem block972_source :
    ((List.range' 972 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 265950960563985906840735268822127295380893 / 21778071482940061661655974875633165533184 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_972)
  rw [weightBlock_source_eq] at h
  exact h

theorem block972_report :
    ((List.range' 972 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 225269225951444766651857790404241 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_972)
  rw [weightBlock_report_eq] at h
  exact h

theorem block1458_sum :
    ((List.range' 1458 486).map addressMajorant).sum = 5178669774370278667265 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_1458)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block1458_max :
    ((List.range' 1458 486).map addressMajorant).foldl max 0 = 52505516973933298085 / 9223372036854775808 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_1458)
  rw [weightBlock_max_eq] at h
  exact h

theorem block1458_source :
    ((List.range' 1458 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 40908655382640153760871317112078360892967 / 1361129467683753853853498429727072845824 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_1458)
  rw [weightBlock_source_eq] at h
  exact h

theorem block1458_report :
    ((List.range' 1458 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 277207831495688772897046780568207 / 9223372036854775808000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_1458)
  rw [weightBlock_report_eq] at h
  exact h

theorem block1944_sum :
    ((List.range' 1944 486).map addressMajorant).sum = 7466580969719492769167 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_1944)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block1944_max :
    ((List.range' 1944 486).map addressMajorant).foldl max 0 = 270751228816450671815 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_1944)
  rw [weightBlock_max_eq] at h
  exact h

theorem block1944_source :
    ((List.range' 1944 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 363585766288012559287612167408790097181689 / 43556142965880123323311949751266331066368 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_1944)
  rw [weightBlock_source_eq] at h
  exact h

theorem block1944_report :
    ((List.range' 1944 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 153984561599124411058998500794173 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_1944)
  rw [weightBlock_report_eq] at h
  exact h

theorem block2430_sum :
    ((List.range' 2430 486).map addressMajorant).sum = 3553033808238265463209 / 9223372036854775808 := by
  have h := congrArg Prod.fst (block_2430)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block2430_max :
    ((List.range' 2430 486).map addressMajorant).foldl max 0 = 53340443096899328121 / 9223372036854775808 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_2430)
  rw [weightBlock_max_eq] at h
  exact h

theorem block2430_source :
    ((List.range' 2430 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 11208571200671518627884534085164796953237 / 340282366920938463463374607431768211456 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_2430)
  rw [weightBlock_source_eq] at h
  exact h

theorem block2430_report :
    ((List.range' 2430 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 60761786231148192447237329202303 / 1844674407370955161600000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_2430)
  rw [weightBlock_report_eq] at h
  exact h

theorem block2916_sum :
    ((List.range' 2916 486).map addressMajorant).sum = 7396801802114586911431 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_2916)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block2916_max :
    ((List.range' 2916 486).map addressMajorant).foldl max 0 = 270751228816450671815 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_2916)
  rw [weightBlock_max_eq] at h
  exact h

theorem block2916_source :
    ((List.range' 2916 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 37842281875465813328393615656590550280913 / 10889035741470030830827987437816582766592 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_2916)
  rw [weightBlock_source_eq] at h
  exact h

theorem block2916_report :
    ((List.range' 2916 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 64107319096108961834703015336317 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_2916)
  rw [weightBlock_report_eq] at h
  exact h

theorem block3402_sum :
    ((List.range' 3402 486).map addressMajorant).sum = 2668959920466970492059 / 9223372036854775808 := by
  have h := congrArg Prod.fst (block_3402)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block3402_max :
    ((List.range' 3402 486).map addressMajorant).foldl max 0 = 28254975559824199107 / 4611686018427387904 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_3402)
  rw [weightBlock_max_eq] at h
  exact h

theorem block3402_source :
    ((List.range' 3402 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 54367384428325966522389297330119481783869 / 2722258935367507707706996859454145691648 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_3402)
  rw [weightBlock_source_eq] at h
  exact h

theorem block3402_report :
    ((List.range' 3402 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 368407726934708477611011680963947 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_3402)
  rw [weightBlock_report_eq] at h
  exact h

theorem block3888_sum :
    ((List.range' 3888 486).map addressMajorant).sum = 9859187051142502426881 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_3888)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block3888_max :
    ((List.range' 3888 486).map addressMajorant).foldl max 0 = 270751228816450671815 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_3888)
  rw [weightBlock_max_eq] at h
  exact h

theorem block3888_source :
    ((List.range' 3888 486).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 585876408391378550804278585439428084031085 / 21778071482940061661655974875633165533184 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_3888)
  rw [weightBlock_source_eq] at h
  exact h

theorem block3888_report :
    ((List.range' 3888 486).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 496256620926302887458847042417669 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_3888)
  rw [weightBlock_report_eq] at h
  exact h

theorem block4374_sum :
    ((List.range' 4374 477).map addressMajorant).sum = 15039263107733285909409 / 18446744073709551616 := by
  have h := congrArg Prod.fst (block_4374)
  rw [weightBlock_sum_eq] at h
  exact h

theorem block4374_max :
    ((List.range' 4374 477).map addressMajorant).foldl max 0 = 270751228816450671815 / 18446744073709551616 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_4374)
  rw [weightBlock_max_eq] at h
  exact h

theorem block4374_source :
    ((List.range' 4374 477).map fun a =>
      sourceCoefficientAbs a * addressMajorant a).sum = 359105806821777979477003763103405324782897 / 10889035741470030830827987437816582766592 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.1) (block_4374)
  rw [weightBlock_source_eq] at h
  exact h

theorem block4374_report :
    ((List.range' 4374 477).map fun a =>
      reportCoefficientAbs a * addressMajorant a).sum = 608348899857001166383612227056391 / 18446744073709551616000000000000 := by
  have h := congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.2.2) (block_4374)
  rw [weightBlock_report_eq] at h
  exact h

private theorem rangeSplit4851 : List.range' 0 4851 =
    List.range' 0 486 ++ List.range' 486 486 ++ List.range' 972 486 ++ List.range' 1458 486 ++ List.range' 1944 486 ++ List.range' 2430 486 ++ List.range' 2916 486 ++ List.range' 3402 486 ++ List.range' 3888 486 ++ List.range' 4374 477 := by
  decide +kernel

theorem addressMajorant_total_sum :
    ((List.range' 0 4851).map addressMajorant).sum = sumBound := by
  rw [rangeSplit4851]
  simp only [List.map_append, List.sum_append]
  rw [block0_sum, block486_sum, block972_sum, block1458_sum, block1944_sum, block2430_sum, block2916_sum, block3402_sum, block3888_sum, block4374_sum]
  unfold sumBound
  decide +kernel

theorem addressMajorant_source_total :
    ((List.range' 0 4851).map fun a => sourceCoefficientAbs a * addressMajorant a).sum = sourceBound := by
  rw [rangeSplit4851]
  simp only [List.map_append, List.sum_append]
  rw [block0_source, block486_source, block972_source, block1458_source, block1944_source, block2430_source, block2916_source, block3402_source, block3888_source, block4374_source]
  unfold sourceBound
  decide +kernel

theorem addressMajorant_report_total :
    ((List.range' 0 4851).map fun a => reportCoefficientAbs a * addressMajorant a).sum = reportBound := by
  rw [rangeSplit4851]
  simp only [List.map_append, List.sum_append]
  rw [block0_report, block486_report, block972_report, block1458_report, block1944_report, block2430_report, block2916_report, block3402_report, block3888_report, block4374_report]
  unfold reportBound
  decide +kernel

theorem addressMajorant_le_amax (a : Nat) (h : a < 4851) :
    addressMajorant a ≤ amaxBound := by
  by_cases h486 : a < 486
  · have mem : a ∈ List.range' 0 486 := by
      rw [List.mem_range']
      exact ⟨a - 0, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 0 486 mem
    have hub : (weightBlock 0 486).2.1 = 83700160913998769151 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_0)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h972 : a < 972
  · have mem : a ∈ List.range' 486 486 := by
      rw [List.mem_range']
      exact ⟨a - 486, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 486 486 mem
    have hub : (weightBlock 486 486).2.1 = 162370802263716330663 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_486)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h1458 : a < 1458
  · have mem : a ∈ List.range' 972 486 := by
      rw [List.mem_range']
      exact ⟨a - 972, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 972 486 mem
    have hub : (weightBlock 972 486).2.1 = 270751228816450671815 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_972)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h1944 : a < 1944
  · have mem : a ∈ List.range' 1458 486 := by
      rw [List.mem_range']
      exact ⟨a - 1458, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 1458 486 mem
    have hub : (weightBlock 1458 486).2.1 = 52505516973933298085 / 9223372036854775808 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_1458)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h2430 : a < 2430
  · have mem : a ∈ List.range' 1944 486 := by
      rw [List.mem_range']
      exact ⟨a - 1944, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 1944 486 mem
    have hub : (weightBlock 1944 486).2.1 = 270751228816450671815 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_1944)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h2916 : a < 2916
  · have mem : a ∈ List.range' 2430 486 := by
      rw [List.mem_range']
      exact ⟨a - 2430, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 2430 486 mem
    have hub : (weightBlock 2430 486).2.1 = 53340443096899328121 / 9223372036854775808 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_2430)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h3402 : a < 3402
  · have mem : a ∈ List.range' 2916 486 := by
      rw [List.mem_range']
      exact ⟨a - 2916, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 2916 486 mem
    have hub : (weightBlock 2916 486).2.1 = 270751228816450671815 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_2916)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h3888 : a < 3888
  · have mem : a ∈ List.range' 3402 486 := by
      rw [List.mem_range']
      exact ⟨a - 3402, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 3402 486 mem
    have hub : (weightBlock 3402 486).2.1 = 28254975559824199107 / 4611686018427387904 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_3402)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h4374 : a < 4374
  · have mem : a ∈ List.range' 3888 486 := by
      rw [List.mem_range']
      exact ⟨a - 3888, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 3888 486 mem
    have hub : (weightBlock 3888 486).2.1 = 270751228816450671815 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_3888)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  by_cases h4851 : a < 4851
  · have mem : a ∈ List.range' 4374 477 := by
      rw [List.mem_range']
      exact ⟨a - 4374, by omega, by omega⟩
    have hb := addressMajorant_le_block_max a 4374 477 mem
    have hub : (weightBlock 4374 477).2.1 = 270751228816450671815 / 18446744073709551616 := by
      exact congrArg (fun x : ℚ × ℚ × ℚ × ℚ => x.2.1) (block_4374)
    rw [hub] at hb
    refine hb.trans ?_
    unfold amaxBound
    decide +kernel
  omega

private theorem list_cast_sum (l : List ℚ) :
    ((l.map (Rat.cast : ℚ → ℝ)).sum) = (l.sum : ℝ) := by
  have h := (map_list_sum (Rat.castHom ℝ) l).symm
  simpa only [Rat.coe_castHom] using h

private theorem finset_range_sum_eq_list {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range n, f i = ((List.range n).map f).sum := by
  show Multiset.sum (Multiset.map f (Finset.range n).val) = _
  rw [Finset.range_val]
  show Multiset.sum ((Multiset.range n).map f) = _
  rw [show Multiset.range n = (List.range n : Multiset ℕ) from rfl]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem fin4851_sum_addressMajorant :
    (∑ a : Fin 4851, (addressMajorant a.val : ℝ)) = (sumBound : ℝ) := by
  have key : (∑ a : Fin 4851, (addressMajorant a.val : ℝ)) =
      ∑ i ∈ Finset.range 4851, (addressMajorant i : ℝ) := by
    rw [Finset.sum_range (fun i : ℕ => (addressMajorant i : ℝ))]
  rw [key]
  rw [finset_range_sum_eq_list, List.range_eq_range']
  rw [show ((List.range' 0 4851).map fun i => (addressMajorant i : ℝ)) =
      (List.map (Rat.cast : ℚ → ℝ))
        ((List.range' 0 4851).map addressMajorant) from by
    rw [List.map_map]; rfl]
  rw [list_cast_sum, addressMajorant_total_sum]

private theorem finOfNat_cast (a : Nat) (h : a < 4851) :
    (Fin.ofNat 4851 a) = ⟨a, h⟩ :=
  Fin.ext (Nat.mod_eq_of_lt h)

theorem sourceCoefficientAbs_eq_ofLt (a : Nat) (h : a < 4851) :
    sourceCoefficientAbs a = |sourceCoefficientAt ⟨a, h⟩| := by
  unfold sourceCoefficientAbs
  rw [finOfNat_cast a h]

theorem reportCoefficientAbs_eq_ofLt (a : Nat) (h : a < 4851) :
    reportCoefficientAbs a = |reportCoefficientAt ⟨a, h⟩| := by
  unfold reportCoefficientAbs
  rw [finOfNat_cast a h]

private theorem ofNat4851_self (a : Fin 4851) :
    Fin.ofNat 4851 a.val = a :=
  Fin.ext (Nat.mod_eq_of_lt a.isLt)

theorem fin4851_sum_sourceCoeffMajorant :
    (∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ)) =
      (sourceBound : ℝ) := by
  have step1 :
      (∑ a : Fin 4851, |(sourceCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ)) =
        ∑ a : Fin 4851, (fun i : ℕ =>
          |(sourceCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ)) a.val := by
    apply Finset.sum_congr rfl
    intro a _
    show |(sourceCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ) =
      |(sourceCoefficientAt (Fin.ofNat 4851 a.val) : ℝ)| * (addressMajorant a.val : ℝ)
    rw [ofNat4851_self a]
  rw [step1]
  have key : (∑ a : Fin 4851, (fun i : ℕ =>
        |(sourceCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ)) a.val) =
      ∑ i ∈ Finset.range 4851,
        |(sourceCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ) := by
    rw [Finset.sum_range (fun i : ℕ =>
      |(sourceCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ))]
  rw [key]
  rw [finset_range_sum_eq_list, List.range_eq_range']
  rw [show ((List.range' 0 4851).map fun i =>
        |(sourceCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ)) =
      (List.map (Rat.cast : ℚ → ℝ))
        ((List.range' 0 4851).map fun i =>
          sourceCoefficientAbs i * addressMajorant i) from by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply]
    unfold sourceCoefficientAbs
    rw [Rat.cast_mul, Rat.cast_abs]]
  rw [list_cast_sum, addressMajorant_source_total]

theorem fin4851_sum_reportCoeffMajorant :
    (∑ a : Fin 4851, |(reportCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ)) =
      (reportBound : ℝ) := by
  have step1 :
      (∑ a : Fin 4851, |(reportCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ)) =
        ∑ a : Fin 4851, (fun i : ℕ =>
          |(reportCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ)) a.val := by
    apply Finset.sum_congr rfl
    intro a _
    show |(reportCoefficientAt a : ℝ)| * (addressMajorant a.val : ℝ) =
      |(reportCoefficientAt (Fin.ofNat 4851 a.val) : ℝ)| * (addressMajorant a.val : ℝ)
    rw [ofNat4851_self a]
  rw [step1]
  have key : (∑ a : Fin 4851, (fun i : ℕ =>
        |(reportCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ)) a.val) =
      ∑ i ∈ Finset.range 4851,
        |(reportCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ) := by
    rw [Finset.sum_range (fun i : ℕ =>
      |(reportCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ))]
  rw [key]
  rw [finset_range_sum_eq_list, List.range_eq_range']
  rw [show ((List.range' 0 4851).map fun i =>
        |(reportCoefficientAt (Fin.ofNat 4851 i) : ℝ)| * (addressMajorant i : ℝ)) =
      (List.map (Rat.cast : ℚ → ℝ))
        ((List.range' 0 4851).map fun i =>
          reportCoefficientAbs i * addressMajorant i) from by
    rw [List.map_map]
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply]
    unfold reportCoefficientAbs
    rw [Rat.cast_mul, Rat.cast_abs]]
  rw [list_cast_sum, addressMajorant_report_total]

end
end LAlanine40K2025.UnifiedOrbitals.Frame.Occupation.Factor.ManyBody.Pair.Coulomb.Hartree.Charge.Residual.Interaction.AO.UpperTriangle.SourceJoin.Weight
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
