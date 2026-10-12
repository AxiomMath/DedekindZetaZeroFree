module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.LocalSeriesDefinitions

@[expose] public section

noncomputable section
open scoped NumberField Classical
open UniqueFactorizationMonoid
namespace DedekindZetaZeroFree.CorrectionFactors.Exponent
open LocalFiniteSums
variable {F : Type} [Field F] [NumberField F] {A : SArithmeticData F}

theorem exists_primeFree (I : A.Exterior) (p : ExteriorPrime A) :
    ∃ J : A.Exterior,
      I.val = p.val.asIdeal ^ idealPrimeExponent p.val.asIdeal I.val * J.val ∧
      ¬p.val.asIdeal ∣ J.val := by
  obtain ⟨n, J, hnot, heq⟩ := WfDvdMonoid.max_power_factor'
    I.property.1 p.val.prime.not_isUnit
  have hJ : J ≠ 0 := by
    intro h
    simp [h] at heq
    exact I.property.1 heq
  have hnf : (normalizedFactors J).count p.val.asIdeal = 0 := by
    apply Multiset.count_eq_zero.mpr
    intro hmem
    exact hnot (dvd_of_mem_normalizedFactors hmem)
  have hn : idealPrimeExponent p.val.asIdeal I.val = n := by
    rw [idealPrimeExponent, heq, normalizedFactors_mul
      (pow_ne_zero n p.val.prime.ne_zero) hJ,
      p.val.irreducible.normalizedFactors_pow, Multiset.count_add]
    simp [hnf]
  have hcop : J ⊔ A.cS = ⊤ := by
    apply top_unique
    rw [← I.property.2]
    apply sup_le_sup_right
    rw [heq]
    exact Ideal.mul_le_right
  exact ⟨⟨J, hJ, hcop⟩, hn ▸ heq, hnot⟩

end DedekindZetaZeroFree.CorrectionFactors.Exponent

end
