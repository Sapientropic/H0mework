import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_015_028
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_028_039
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_039_049
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_049_062
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_062_073
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_073_082
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_082_096
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V015_096_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_15 (j : Basis) (ordered : (15 : Basis) ≤ j) :
    |aoIntegral (15 : Basis) j - (recordedAttraction (15 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (15 : Basis) = ⟨15,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(15 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (9 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (10 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (11 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (12 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (13 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(15 : Basis) ≤ (14 : Basis) by decide) ordered)
  · convert vcell15_15_error using 1; norm_num
  · convert vcell15_16_error using 1; norm_num
  · convert vcell15_17_error using 1; norm_num
  · convert vcell15_18_error using 1; norm_num
  · convert vcell15_19_error using 1; norm_num
  · convert vcell15_20_error using 1; norm_num
  · convert vcell15_21_error using 1; norm_num
  · convert vcell15_22_error using 1; norm_num
  · convert vcell15_23_error using 1; norm_num
  · convert vcell15_24_error using 1; norm_num
  · convert vcell15_25_error using 1; norm_num
  · convert vcell15_26_error using 1; norm_num
  · convert vcell15_27_error using 1; norm_num
  · convert vcell15_28_error using 1; norm_num
  · convert vcell15_29_error using 1; norm_num
  · convert vcell15_30_error using 1; norm_num
  · convert vcell15_31_error using 1; norm_num
  · convert vcell15_32_error using 1; norm_num
  · convert vcell15_33_error using 1; norm_num
  · convert vcell15_34_error using 1; norm_num
  · convert vcell15_35_error using 1; norm_num
  · convert vcell15_36_error using 1; norm_num
  · convert vcell15_37_error using 1; norm_num
  · convert vcell15_38_error using 1; norm_num
  · convert vcell15_39_error using 1; norm_num
  · convert vcell15_40_error using 1; norm_num
  · convert vcell15_41_error using 1; norm_num
  · convert vcell15_42_error using 1; norm_num
  · convert vcell15_43_error using 1; norm_num
  · convert vcell15_44_error using 1; norm_num
  · convert vcell15_45_error using 1; norm_num
  · convert vcell15_46_error using 1; norm_num
  · convert vcell15_47_error using 1; norm_num
  · convert vcell15_48_error using 1; norm_num
  · convert vcell15_49_error using 1; norm_num
  · convert vcell15_50_error using 1; norm_num
  · convert vcell15_51_error using 1; norm_num
  · convert vcell15_52_error using 1; norm_num
  · convert vcell15_53_error using 1; norm_num
  · convert vcell15_54_error using 1; norm_num
  · convert vcell15_55_error using 1; norm_num
  · convert vcell15_56_error using 1; norm_num
  · convert vcell15_57_error using 1; norm_num
  · convert vcell15_58_error using 1; norm_num
  · convert vcell15_59_error using 1; norm_num
  · convert vcell15_60_error using 1; norm_num
  · convert vcell15_61_error using 1; norm_num
  · convert vcell15_62_error using 1; norm_num
  · convert vcell15_63_error using 1; norm_num
  · convert vcell15_64_error using 1; norm_num
  · convert vcell15_65_error using 1; norm_num
  · convert vcell15_66_error using 1; norm_num
  · convert vcell15_67_error using 1; norm_num
  · convert vcell15_68_error using 1; norm_num
  · convert vcell15_69_error using 1; norm_num
  · convert vcell15_70_error using 1; norm_num
  · convert vcell15_71_error using 1; norm_num
  · convert vcell15_72_error using 1; norm_num
  · convert vcell15_73_error using 1; norm_num
  · convert vcell15_74_error using 1; norm_num
  · convert vcell15_75_error using 1; norm_num
  · convert vcell15_76_error using 1; norm_num
  · convert vcell15_77_error using 1; norm_num
  · convert vcell15_78_error using 1; norm_num
  · convert vcell15_79_error using 1; norm_num
  · convert vcell15_80_error using 1; norm_num
  · convert vcell15_81_error using 1; norm_num
  · convert vcell15_82_error using 1; norm_num
  · convert vcell15_83_error using 1; norm_num
  · convert vcell15_84_error using 1; norm_num
  · convert vcell15_85_error using 1; norm_num
  · convert vcell15_86_error using 1; norm_num
  · convert vcell15_87_error using 1; norm_num
  · convert vcell15_88_error using 1; norm_num
  · convert vcell15_89_error using 1; norm_num
  · convert vcell15_90_error using 1; norm_num
  · convert vcell15_91_error using 1; norm_num
  · convert vcell15_92_error using 1; norm_num
  · convert vcell15_93_error using 1; norm_num
  · convert vcell15_94_error using 1; norm_num
  · convert vcell15_95_error using 1; norm_num
  · convert vcell15_96_error using 1; norm_num
  · convert vcell15_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
