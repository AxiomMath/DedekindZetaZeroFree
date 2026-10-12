module

public import DedekindZetaZeroFree.Adeles.Characters.SIntegerTraceAnnihilation
public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacterNondegeneracy

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

def adelicRationalFrequencyCharacter (t : F) :
    AddChar (AdeleRing (𝓞 F) F) Circle :=
  (adelicTraceCharacter F).compAddMonoidHom
    (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) t))

theorem continuous_adelicRationalFrequencyCharacter (t : F) :
    Continuous (adelicRationalFrequencyCharacter F t :
      AdeleRing (𝓞 F) F → Circle) := by
  exact (continuous_adelicTraceCharacter F).comp (continuous_const.mul continuous_id)

theorem adelicRationalFrequencyCharacter_diagonal (t a : F) :
    adelicRationalFrequencyCharacter F t
      (algebraMap F (AdeleRing (𝓞 F) F) a) = 1 := by
  change adelicTraceCharacter F (algebraMap F (AdeleRing (𝓞 F) F) t *
    algebraMap F (AdeleRing (𝓞 F) F) a) = 1
  rw [← map_mul]
  exact adelicTraceCharacter_diagonal F (t * a)

def adelicRationalFrequencyQuotientCharacter (t : F) :
    AddChar (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) Circle := by
  exact AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (AdeleRing.principalSubgroup (𝓞 F) F)
      (adelicRationalFrequencyCharacter F t).toAddMonoidHom (by
        rintro x ⟨a, rfl⟩
        exact adelicRationalFrequencyCharacter_diagonal F t a))

theorem adelicRationalFrequencyQuotientCharacter_mk (t : F)
    (x : AdeleRing (𝓞 F) F) :
    adelicRationalFrequencyQuotientCharacter F t
      (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x) =
        adelicTraceCharacter F (algebraMap F (AdeleRing (𝓞 F) F) t * x) := by
  rfl

theorem continuous_adelicRationalFrequencyQuotientCharacter (t : F) :
    Continuous (adelicRationalFrequencyQuotientCharacter F t :
      (AdeleRing (𝓞 F) F ⧸ AdeleRing.principalSubgroup (𝓞 F) F) → Circle) := by
  apply (QuotientAddGroup.isQuotientMap_mk
    (AdeleRing.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
  exact continuous_adelicRationalFrequencyCharacter F t

theorem adelicRationalFrequencyQuotientCharacter_eq_one_iff (t : F) :
    adelicRationalFrequencyQuotientCharacter F t = 1 ↔ t = 0 := by
  constructor
  · intro h
    have ht : algebraMap F (AdeleRing (𝓞 F) F) t = 0 := by
      apply (adelicTraceCharacter_nondegenerate F _).mp
      intro x
      have he := congrArg (fun χ => χ
        (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x)) h
      simpa only [adelicRationalFrequencyQuotientCharacter_mk, AddChar.one_apply] using he
    exact (map_eq_zero (algebraMap F (AdeleRing (𝓞 F) F))).mp ht
  · rintro rfl
    apply AddChar.ext
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H x =>
      change adelicRationalFrequencyQuotientCharacter F 0
        (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x) = 1
      rw [adelicRationalFrequencyQuotientCharacter_mk]
      simp

theorem adelicRationalFrequencyQuotientCharacter_ne_one_iff (t : F) :
    adelicRationalFrequencyQuotientCharacter F t ≠ 1 ↔ t ≠ 0 := by
  exact not_congr (adelicRationalFrequencyQuotientCharacter_eq_one_iff F t)

theorem adelicRationalFrequencyQuotientCharacter_one :
    adelicRationalFrequencyQuotientCharacter F 1 =
      adelicTraceQuotientCharacter F := by
  apply AddChar.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    change adelicRationalFrequencyQuotientCharacter F 1
      (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x) =
        adelicTraceQuotientCharacter F
          (QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) x)
    rw [adelicRationalFrequencyQuotientCharacter_mk, adelicTraceQuotientCharacter_mk]
    simp

theorem adelicTraceQuotientCharacter_ne_one :
    adelicTraceQuotientCharacter F ≠ 1 := by
  rw [← adelicRationalFrequencyQuotientCharacter_one,
    adelicRationalFrequencyQuotientCharacter_ne_one_iff]
  exact one_ne_zero

end DedekindZetaZeroFree

end

section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

theorem adelicTraceCharacter_ne_one :
    adelicTraceCharacter F ≠ 1 := by
  intro h
  have hz : (1 : AdeleRing (𝓞 F) F) = 0 := by
    apply (adelicTraceCharacter_nondegenerate F 1).mp
    intro y
    simp [h]
  exact one_ne_zero hz

end DedekindZetaZeroFree

end
end
