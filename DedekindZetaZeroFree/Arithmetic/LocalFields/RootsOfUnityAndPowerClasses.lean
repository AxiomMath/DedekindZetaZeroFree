module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.Algebra.PowerQuotientModules

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F]

def IsLocalRootOrder (n : ℕ) : Prop := n = 2 ∨ n = 3 ∨ n = 6

theorem primitive_root (A : SArithmeticData F) (n : ℕ) (hn : IsLocalRootOrder n) :
    IsPrimitiveRoot (A.zeta12 ^ (12 / n)) n := by
  rcases hn with rfl | rfl | rfl
  · exact A.primitive_zeta12.pow (by decide) (by decide : 12 = 12 / 2 * 2)
  · exact A.primitive_zeta12.pow (by decide) (by decide : 12 = 12 / 3 * 3)
  · exact A.primitive_zeta12.pow (by decide) (by decide : 12 = 12 / 6 * 6)

theorem finite_primitive_root (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (hn : IsLocalRootOrder n) :
    IsPrimitiveRoot ((algebraMap F (v.adicCompletion F)) (A.zeta12 ^ (12 / n))) n :=
  (A.primitive_root n hn).map_of_injective (RingHom.injective (algebraMap F (v.adicCompletion F)))

def finiteRootsEquiv (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (hn : IsLocalRootOrder n) :
    rootsOfUnity n F ≃* rootsOfUnity n (v.adicCompletion F) := by
  haveI : NeZero n := ⟨by rcases hn with rfl | rfl | rfl <;> decide⟩
  exact rootsOfUnityEquivOfPrimitiveRoots
    (RingHom.injective (algebraMap F (v.adicCompletion F)))
    ⟨_, (mem_primitiveRoots (NeZero.pos n)).2 (A.primitive_root n hn)⟩

theorem finiteRootsEquiv_apply (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (hn : IsLocalRootOrder n) (η : rootsOfUnity n F) :
    ((A.finiteRootsEquiv v n hn η : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      (algebraMap F (v.adicCompletion F)) ((η : Fˣ) : F) := by
  haveI : NeZero n := ⟨by rcases hn with rfl | rfl | rfl <;> decide⟩
  exact val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe
    (RingHom.injective (algebraMap F (v.adicCompletion F)))
    ⟨_, (mem_primitiveRoots (NeZero.pos n)).2 (A.primitive_root n hn)⟩ η

theorem neg_one_isPower (A : SArithmeticData F) (n : ℕ) (hn : IsLocalRootOrder n) :
    ∃ x : F, x ^ n = -1 := by
  refine ⟨A.zeta12 ^ (6 / n), ?_⟩
  rcases hn with rfl | rfl | rfl
  · rw [← pow_mul, show 6 / 2 * 2 = 6 from rfl, A.zeta12_pow_six]
  · rw [← pow_mul, show 6 / 3 * 3 = 6 from rfl, A.zeta12_pow_six]
  · rw [← pow_mul, show 6 / 6 * 6 = 6 from rfl, A.zeta12_pow_six]

theorem finite_neg_one_isPower (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (hn : IsLocalRootOrder n) :
    ∃ x : v.adicCompletion F, x ^ n = -1 := by
  obtain ⟨x, hx⟩ := A.neg_one_isPower n hn
  refine ⟨algebraMap F (v.adicCompletion F) x, ?_⟩
  rw [← map_pow, hx, map_neg, map_one]

theorem infinite_isComplex (A : SArithmeticData F) (w : InfinitePlace F) : w.IsComplex :=
  A.complex_place w

theorem infinite_unit_isPower (A : SArithmeticData F) (w : InfinitePlace F) (n : ℕ)
    (hn : IsLocalRootOrder n) (u : w.Completionˣ) :
    ∃ x : w.Completionˣ, x ^ n = u := by
  haveI hw : w.IsComplex := A.infinite_isComplex w
  have hn0 : 0 < n := by rcases hn with rfl | rfl | rfl <;> decide
  set e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw with he
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (e (u : w.Completion)) hn0
  have hroot : (e.symm y) ^ n = (u : w.Completion) := by
    rw [← map_pow, hy, RingEquiv.symm_apply_apply]
  have hne : e.symm y ≠ 0 := by
    intro h0
    have hzero : (e.symm y) ^ n = 0 := by rw [h0, zero_pow hn0.ne']
    rw [hroot] at hzero
    exact Units.ne_zero u hzero
  refine ⟨Units.mk0 (e.symm y) hne, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact hroot

theorem infinite_power_quotient_subsingleton (A : SArithmeticData F) (w : InfinitePlace F) (n : ℕ)
    (hn : IsLocalRootOrder n) :
    Subsingleton (PowerQuotient w.Completionˣ n) := by
  rw [QuotientGroup.subsingleton_iff, Subgroup.eq_top_iff']
  intro u
  obtain ⟨x, hx⟩ := A.infinite_unit_isPower w n hn u
  exact MonoidHom.mem_range.mpr ⟨x, hx⟩

theorem finite_natCast_ne_zero (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (hn : IsLocalRootOrder n) :
    (n : v.adicCompletion F) ≠ 0 := by
  have hn0 : n ≠ 0 := by rcases hn with rfl | rfl | rfl <;> decide
  intro h
  have h' : (n : F) = 0 :=
    RingHom.injective (algebraMap F (v.adicCompletion F)) (by
      rw [map_natCast, h, map_zero])
  exact Nat.cast_ne_zero.mpr hn0 h'

end
end SArithmeticData
end DedekindZetaZeroFree
