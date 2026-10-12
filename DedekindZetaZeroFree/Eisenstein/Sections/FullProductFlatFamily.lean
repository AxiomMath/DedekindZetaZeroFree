module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.CanonicalIwasawaCompact
public import DedekindZetaZeroFree.Eisenstein.Induction.IwasawaCompactOverlap

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField

namespace DedekindZetaZeroFree.KPContFlatFullProductIwasawa

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def rawIwasawa (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ) :
    KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ where
  K := D.K
  compact := D.compact
  decomposition := D.decomposition
  overlap := D.overlap

def iwasawaData : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ where
  K := PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ
  compact := PrincipalOfKP.iwasawaCompactSubgroupMax_compact F ζ hζ
  decomposition := PrincipalOfKP.iwasawaCompactSubgroupMax_decomposition F ζ hζ
  overlap := KPLiteralChamber.compact_overlap F ζ hζ
    (PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ)
    (PrincipalOfKP.iwasawaCompactSubgroupMax_compact F ζ hζ)

theorem complexCompactLift_mem
    (w : InfinitePlace F) (k : KPCplxCharacterHaar.ComplexSU2) :
    KPGlobalResidualConstruction.complexCompactLift F ζ hζ w k ∈
      (iwasawaData F ζ hζ).K :=
  PrincipalOfKP.complexCompactLift_mem_iwasawaCompactSubgroupMax F ζ hζ w k

def alpha (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℝ :=
  Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
    (iwasawaData F ζ hζ) g : ℝ≥0) : ℝ))

theorem alpha_borel_mul
    (h : KPGlobalTorusFunctionData.E F ζ hζ)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    alpha F ζ hζ ((h.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ h : ℝ≥0) : ℝ)) +
        alpha F ζ hζ g := by
  have hnorm :
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (iwasawaData F ζ hζ)
          ((h.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
        KPGlobalTorusFunctionData.delta F ζ hζ h *
          KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
            (iwasawaData F ζ hζ) g :=
    KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_borel_mul F ζ hζ
      (rawIwasawa F ζ hζ (iwasawaData F ζ hζ)) h x g
  have hd : (((KPGlobalTorusFunctionData.delta F ζ hζ h : ℝ≥0) : ℝ)) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero _)
  have hn : (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
      (iwasawaData F ζ hζ) g : ℝ≥0) : ℝ)) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero _)
  simp only [alpha]
  rw [hnorm, Units.val_mul, NNReal.coe_mul, Real.log_mul hd hn]

theorem alpha_mul_compact
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (k : (iwasawaData F ζ hζ).K) :
    alpha F ζ hζ (g * k.val) = alpha F ζ hζ g := by
  have hnorm :
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (iwasawaData F ζ hζ)
          (g * k.val) =
        KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
          (iwasawaData F ζ hζ) g :=
    KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_right_compact F ζ hζ
      (rawIwasawa F ζ hζ (iwasawaData F ζ hζ)) g k
  simp only [alpha, hnorm]

end DedekindZetaZeroFree.KPContFlatFullProductIwasawa

end

section

noncomputable section
open scoped NumberField Classical NNReal
open NumberField

namespace DedekindZetaZeroFree.KPContFlatFullProductIwasawa

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

@[simp] theorem iwasawaData_K :
    (iwasawaData F ζ hζ).K =
      PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ := rfl

@[simp] theorem alpha_one : alpha F ζ hζ 1 = 0 := by
  have hnorm :
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ (iwasawaData F ζ hζ) 1 = 1 :=
    KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_compact F ζ hζ
      (rawIwasawa F ζ hζ (iwasawaData F ζ hζ)) (1 : (iwasawaData F ζ hζ).K)
  simp only [alpha, hnorm]
  norm_num

end DedekindZetaZeroFree.KPContFlatFullProductIwasawa

end
end
