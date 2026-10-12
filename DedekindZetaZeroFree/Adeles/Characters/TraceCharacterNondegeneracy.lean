module

public import DedekindZetaZeroFree.Adeles.Characters.TraceCharacter

@[expose] public section

noncomputable section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

theorem archTraceCharacter_nondegenerate {F : Type*} [Field F] [NumberField F]
    (v : InfinitePlace F) (x : v.Completion) :
    (∀ y : v.Completion, archTraceCharacter v (x * y) = 1) ↔ x = 0 := by
  classical
  constructor
  · intro h
    by_contra hx
    by_cases hv : v.IsReal
    · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hv
      have he := h (e.symm (1 / 2) / x)
      rw [mul_div_cancel₀ _ hx] at he
      have ht : archTrace v (e.symm (1 / 2)) = 1 / 2 := by
        rw [archTrace_of_isReal v hv]
        exact e.apply_symm_apply _
      change Circle.exp (2 * Real.pi * archTrace v (e.symm (1 / 2))) = 1 at he
      rw [ht] at he
      have hp : 2 * Real.pi * (1 / 2) = Real.pi := by ring
      exact Circle.exp_pi_ne_one (hp ▸ he)
    · have hv' : v.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hv'
      have he := h (e.symm (1 / 4) / x)
      rw [mul_div_cancel₀ _ hx] at he
      have ht : archTrace v (e.symm (1 / 4)) = 1 / 2 := by
        rw [archTrace_of_isComplex v hv']
        change 2 * (e (e.symm (1 / 4))).re = 1 / 2
        rw [e.apply_symm_apply]
        norm_num
      change Circle.exp (2 * Real.pi * archTrace v (e.symm (1 / 4))) = 1 at he
      rw [ht] at he
      have hp : 2 * Real.pi * (1 / 2) = Real.pi := by ring
      exact Circle.exp_pi_ne_one (hp ▸ he)
  · rintro rfl y
    simp

theorem localFiniteCharacter_nondegenerate (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    (∀ y : v.adicCompletion F, localFiniteCharacter F v (x * y) = 1) ↔
      x = 0 := by
  constructor
  · intro h
    by_contra hx
    let K := ℚ_[PlaceTraceAdapter.prime F v]
    let L := v.adicCompletion F
    let n := Module.finrank K L
    have hn : (n : K) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      exact ne_of_gt (Module.finrank_pos (R := K) (M := L))
    let s : K := (PlaceTraceAdapter.prime F v : K)⁻¹
    have he := h (algebraMap K L (s / n) / x)
    rw [mul_div_cancel₀ _ hx, localFiniteCharacter_apply] at he
    have ht : PlaceTraceAdapter.trace F v (algebraMap K L (s / n)) = s := by
      change Algebra.trace K L (algebraMap K L (s / n)) = s
      rw [Algebra.trace_algebraMap]
      change n • (s / (n : K)) = s
      rw [nsmul_eq_mul]
      exact mul_div_cancel₀ s hn
    rw [ht] at he
    exact rationalPadicCharacter_inv_prime_ne_one (PlaceTraceAdapter.prime F v) he
  · rintro rfl y
    simp

theorem adelicTraceCharacter_nondegenerate (F : Type) [Field F] [NumberField F]
    (x : AdeleRing (𝓞 F) F) :
    (∀ y : AdeleRing (𝓞 F) F, adelicTraceCharacter F (x * y) = 1) ↔
      x = 0 := by
  classical
  constructor
  · intro h
    apply Prod.ext
    · funext v
      apply (archTraceCharacter_nondegenerate v (x.1 v)).mp
      intro z
      let y : AdeleRing (𝓞 F) F := (Pi.single v z, 0)
      have he := h y
      have hm : x * y =
          ((Pi.single v (x.1 v * z), 0) : AdeleRing (𝓞 F) F) := by
        apply Prod.ext
        · exact (Pi.single_mul_right z).symm
        · exact mul_zero _
      rw [hm, adelicTraceCharacter_arch_single] at he
      exact he
    · apply RestrictedProduct.ext
      intro v
      apply (localFiniteCharacter_nondegenerate F v (x.2 v)).mp
      intro z
      let a := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F
      let y : AdeleRing (𝓞 F) F := (0, RestrictedProduct.single a v z)
      have he := h y
      have hm : x * y =
          ((0, RestrictedProduct.single a v (x.2 v * z)) : AdeleRing (𝓞 F) F) := by
        apply Prod.ext
        · exact mul_zero _
        · exact (RestrictedProduct.mul_single a v z x.2).symm
      rw [hm, adelicTraceCharacter_finite_single] at he
      exact he
  · rintro rfl y
    simp

end DedekindZetaZeroFree

end
