module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData

@[expose] public section

open scoped NumberField
open NumberField

namespace DedekindZetaZeroFree.ArithGaussCRT

variable {F : Type} [Field F] [NumberField F]

 def denominatorIdeal (x : F) : Ideal (𝓞 F) where
  carrier := {a | ∃ b : 𝓞 F, x * algebraMap (𝓞 F) F a = algebraMap (𝓞 F) F b}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by simp [map_add, mul_add, hc, hd]⟩
  smul_mem' := by
    rintro a b ⟨c, hc⟩
    exact ⟨a * c, by simpa [map_mul, mul_left_comm, mul_assoc] using congrArg (algebraMap (𝓞 F) F a * ·) hc⟩

private theorem denominatorIdeal_sup (A : SArithmeticData F) (I : A.Exterior) (x : A.R) :
    denominatorIdeal (x : F) ⊔ I.val = ⊤ := by
  classical
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩
  have hi : I.val ≤ v.asIdeal := le_sup_right.trans hle
  have hv : v ∉ A.Sf := by
    intro hv
    have hc : A.cS ≤ v.asIdeal := by
      exact Ideal.prod_le_inf.trans (Finset.inf_le hv)
    have ht : (⊤ : Ideal (𝓞 F)) ≤ M := by
      rw [← I.property.2]
      exact sup_le hi hc
    exact hM.ne_top (top_unique ht)
  obtain ⟨n, d, hd⟩ := v.exists_primeCompl_mul_eq_of_integer (x : F) (x.property v hv)
  have hm : (d : 𝓞 F) ∈ denominatorIdeal (x : F) := ⟨n, hd⟩
  exact d.property ((le_sup_left.trans hle) hm)

theorem exteriorQuotientMap_surjective (A : SArithmeticData F) (I : A.Exterior) :
    Function.Surjective
      (Ideal.quotientMap (A.extendIdeal I) (algebraMap (𝓞 F) A.R)
        (show I.val ≤ (A.extendIdeal I).comap (algebraMap (𝓞 F) A.R) from
          Ideal.le_comap_map)) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨d, hd, i, hi, hdi⟩ := Submodule.mem_sup.mp
    ((Ideal.eq_top_iff_one _).mp (denominatorIdeal_sup A I x))
  obtain ⟨r, hr⟩ := hd
  refine ⟨Ideal.Quotient.mk I.val r, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have he : algebraMap (𝓞 F) A.R r - x = -(algebraMap (𝓞 F) A.R i * x) := by
    apply Subtype.ext
    change algebraMap (𝓞 F) F r - (x : F) = -(algebraMap (𝓞 F) F i * (x : F))
    have hh := congrArg (algebraMap (𝓞 F) F) hdi
    simp only [map_add, map_one] at hh
    rw [← hr]
    linear_combination (x : F) * hh
  rw [he]
  exact (A.extendIdeal I).neg_mem (Ideal.mul_mem_right x (A.extendIdeal I) (Ideal.mem_map_of_mem _ hi))

end DedekindZetaZeroFree.ArithGaussCRT
