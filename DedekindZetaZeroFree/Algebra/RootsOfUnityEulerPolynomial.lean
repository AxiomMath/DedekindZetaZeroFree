module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Character

@[expose] public section

namespace DedekindZetaZeroFree.AbelianQuotient

open scoped BigOperators

theorem rootsEulerPolynomial (f : ℕ) (hf : 0 < f) (x : ℂ) :
    letI : NeZero f := ⟨Nat.ne_of_gt hf⟩
    letI : Fintype (rootsOfUnity f ℂ) := Fintype.ofFinite _
    ∏ ζ : rootsOfUnity f ℂ, (1 - (ζ.val : ℂ) * x) = 1 - x ^ f := by
  classical
  letI : NeZero f := ⟨Nat.ne_of_gt hf⟩
  letI : Fintype (rootsOfUnity f ℂ) := Fintype.ofFinite _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ f
  let g : Fin f → rootsOfUnity f ℂ := fun i => hζ.toRootsOfUnity ^ (i : ℕ)
  have hg (i : Fin f) : ((g i).val : ℂ) = ζ ^ (i : ℕ) := by
    simp [g, IsPrimitiveRoot.toRootsOfUnity]
  have hbij : Function.Bijective g := by
    constructor
    · intro i j hij
      apply Fin.ext
      apply hζ.pow_inj i.isLt j.isLt
      simpa only [hg] using congrArg (fun z : rootsOfUnity f ℂ => (z.val : ℂ)) hij
    · intro z
      have hz : (z.val : ℂ) ^ f = 1 := by
        simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
          congrArg Units.val ((mem_rootsOfUnity f z.val).mp z.property)
      obtain ⟨i, hi, he⟩ := hζ.eq_pow_of_pow_eq_one hz
      refine ⟨⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simpa only [hg] using he
  let e : Fin f ≃ rootsOfUnity f ℂ := Equiv.ofBijective g hbij
  have hp := congrArg (Polynomial.eval (1 : ℂ)) (X_pow_sub_C_eq_prod hζ hf (rfl : x ^ f = x ^ f))
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, one_pow,
    Polynomial.eval_C, Polynomial.eval_prod] at hp
  calc
    _ = ∏ i : Fin f, (1 - ζ ^ (i : ℕ) * x) := by
      symm
      apply Fintype.prod_equiv e
      intro i
      simp only [e, Equiv.ofBijective_apply, hg]
    _ = ∏ i ∈ Finset.range f, (1 - ζ ^ i * x) := Fin.prod_univ_eq_prod_range (fun i => 1 - ζ ^ i * x) f
    _ = 1 - x ^ f := hp.symm

end DedekindZetaZeroFree.AbelianQuotient
