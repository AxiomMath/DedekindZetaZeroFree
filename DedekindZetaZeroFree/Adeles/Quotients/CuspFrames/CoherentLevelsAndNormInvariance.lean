module

public import DedekindZetaZeroFree.Adeles.Quotients.CompactOpenFiniteLevels

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.KPShift81CoherentLevel
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def compactBaseLevel : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  Classical.choose (KPCompactFiniteLevel.exists_level F ζ hζ)

theorem compactBaseLevel_le :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ (compactBaseLevel F ζ hζ) ≤
      (KPContFlatSourceRecipe.D F ζ hζ).K :=
  Classical.choose_spec (KPCompactFiniteLevel.exists_level F ζ hζ)

def level (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
  ⟨U.toOpenSubgroup ⊓ (compactBaseLevel F ζ hζ).toOpenSubgroup,
    U.isCompact.inter_right (compactBaseLevel F ζ hζ).toOpenSubgroup.isClosed⟩

theorem level_le (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    (level F ζ hζ U).toOpenSubgroup.toSubgroup ≤ U.toOpenSubgroup.toSubgroup := inf_le_left

theorem level_le_compact (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ (level F ζ hζ U) ≤
      (KPContFlatSourceRecipe.D F ζ hζ).K :=
  (Subgroup.map_mono (show (level F ζ hζ U).toOpenSubgroup.toSubgroup ≤
    (compactBaseLevel F ζ hζ).toOpenSubgroup.toSubgroup from inf_le_right)).trans
      (compactBaseLevel_le F ζ hζ)

theorem globalLevel_le (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ (level F ζ hζ U) ≤
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U := Subgroup.map_mono (level_le F ζ hζ U)

theorem norm_right_level
    (U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ (level F ζ hζ U)) :
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) (g * u.val) =
    KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) g :=
  KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact F ζ hζ
    (KPContFlatSourceRecipe.D F ζ hζ) g ⟨u.val, level_le_compact F ζ hζ U u.property⟩

end DedekindZetaZeroFree.KPShift81CoherentLevel

end
