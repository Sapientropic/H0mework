import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V010_010_046
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V010_046_079
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Attraction.Precise.Rows.V010_079_098

set_option autoImplicit false
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
open LAlanine40K2025.BasinRefinement.SourceFiniteData

theorem upper_row_10 (j : Basis) (ordered : (10 : Basis) ≤ j) :
    |aoIntegral (10 : Basis) j - (recordedAttraction (10 : Basis) j : ℝ)| ≤
      (1/10^12 : ℝ) := by
  have rowSame : (10 : Basis) = ⟨10,by decide⟩ := by decide
  rw [rowSame]
  fin_cases j
  · exact False.elim ((show ¬(10 : Basis) ≤ (0 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (1 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (2 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (3 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (4 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (5 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (6 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (7 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (8 : Basis) by decide) ordered)
  · exact False.elim ((show ¬(10 : Basis) ≤ (9 : Basis) by decide) ordered)
  · convert vcell10_10_error using 1; norm_num
  · convert vcell10_11_error using 1; norm_num
  · convert vcell10_12_error using 1; norm_num
  · convert vcell10_13_error using 1; norm_num
  · convert vcell10_14_error using 1; norm_num
  · convert vcell10_15_error using 1; norm_num
  · convert vcell10_16_error using 1; norm_num
  · convert vcell10_17_error using 1; norm_num
  · convert vcell10_18_error using 1; norm_num
  · convert vcell10_19_error using 1; norm_num
  · convert vcell10_20_error using 1; norm_num
  · convert vcell10_21_error using 1; norm_num
  · convert vcell10_22_error using 1; norm_num
  · convert vcell10_23_error using 1; norm_num
  · convert vcell10_24_error using 1; norm_num
  · convert vcell10_25_error using 1; norm_num
  · convert vcell10_26_error using 1; norm_num
  · convert vcell10_27_error using 1; norm_num
  · convert vcell10_28_error using 1; norm_num
  · convert vcell10_29_error using 1; norm_num
  · convert vcell10_30_error using 1; norm_num
  · convert vcell10_31_error using 1; norm_num
  · convert vcell10_32_error using 1; norm_num
  · convert vcell10_33_error using 1; norm_num
  · convert vcell10_34_error using 1; norm_num
  · convert vcell10_35_error using 1; norm_num
  · convert vcell10_36_error using 1; norm_num
  · convert vcell10_37_error using 1; norm_num
  · convert vcell10_38_error using 1; norm_num
  · convert vcell10_39_error using 1; norm_num
  · convert vcell10_40_error using 1; norm_num
  · convert vcell10_41_error using 1; norm_num
  · convert vcell10_42_error using 1; norm_num
  · convert vcell10_43_error using 1; norm_num
  · convert vcell10_44_error using 1; norm_num
  · convert vcell10_45_error using 1; norm_num
  · convert vcell10_46_error using 1; norm_num
  · convert vcell10_47_error using 1; norm_num
  · convert vcell10_48_error using 1; norm_num
  · convert vcell10_49_error using 1; norm_num
  · convert vcell10_50_error using 1; norm_num
  · convert vcell10_51_error using 1; norm_num
  · convert vcell10_52_error using 1; norm_num
  · convert vcell10_53_error using 1; norm_num
  · convert vcell10_54_error using 1; norm_num
  · convert vcell10_55_error using 1; norm_num
  · convert vcell10_56_error using 1; norm_num
  · convert vcell10_57_error using 1; norm_num
  · convert vcell10_58_error using 1; norm_num
  · convert vcell10_59_error using 1; norm_num
  · convert vcell10_60_error using 1; norm_num
  · convert vcell10_61_error using 1; norm_num
  · convert vcell10_62_error using 1; norm_num
  · convert vcell10_63_error using 1; norm_num
  · convert vcell10_64_error using 1; norm_num
  · convert vcell10_65_error using 1; norm_num
  · convert vcell10_66_error using 1; norm_num
  · convert vcell10_67_error using 1; norm_num
  · convert vcell10_68_error using 1; norm_num
  · convert vcell10_69_error using 1; norm_num
  · convert vcell10_70_error using 1; norm_num
  · convert vcell10_71_error using 1; norm_num
  · convert vcell10_72_error using 1; norm_num
  · convert vcell10_73_error using 1; norm_num
  · convert vcell10_74_error using 1; norm_num
  · convert vcell10_75_error using 1; norm_num
  · convert vcell10_76_error using 1; norm_num
  · convert vcell10_77_error using 1; norm_num
  · convert vcell10_78_error using 1; norm_num
  · convert vcell10_79_error using 1; norm_num
  · convert vcell10_80_error using 1; norm_num
  · convert vcell10_81_error using 1; norm_num
  · convert vcell10_82_error using 1; norm_num
  · convert vcell10_83_error using 1; norm_num
  · convert vcell10_84_error using 1; norm_num
  · convert vcell10_85_error using 1; norm_num
  · convert vcell10_86_error using 1; norm_num
  · convert vcell10_87_error using 1; norm_num
  · convert vcell10_88_error using 1; norm_num
  · convert vcell10_89_error using 1; norm_num
  · convert vcell10_90_error using 1; norm_num
  · convert vcell10_91_error using 1; norm_num
  · convert vcell10_92_error using 1; norm_num
  · convert vcell10_93_error using 1; norm_num
  · convert vcell10_94_error using 1; norm_num
  · convert vcell10_95_error using 1; norm_num
  · convert vcell10_96_error using 1; norm_num
  · convert vcell10_97_error using 1; norm_num

end LAlanine40K2025.UnifiedOrbitals.Attraction.Precise.Rows
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
