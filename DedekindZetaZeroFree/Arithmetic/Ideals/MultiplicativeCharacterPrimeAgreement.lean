module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CharacterOperations

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.RootNumber

open scoped NumberField
open IsDedekindDomain

theorem prime_agreement {F : Type} [Field F] [NumberField F]
    {m n r : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hn : n ≠ ⊥) (hr : r ≠ ⊥)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (θ : DedekindZetaZeroFree.RayClassCharacter F n)
    (hprime : ∀ p : HeightOneSpectrum (𝓞 F),
      p.asIdeal ⊔ r = ⊤ → η p.asIdeal = θ p.asIdeal) :
    ∀ I : Ideal (𝓞 F), I ≠ ⊥ → I ⊔ r = ⊤ → η I = θ I := by
  classical
  intro I hI hrI
  have hI0 : I ≠ 0 := by simpa using hI
  have hfac : ∏ᶠ v : HeightOneSpectrum (𝓞 F), v.maxPowDividing I = I :=
    Ideal.finprod_heightOneSpectrum_factorization hI0
  have hfin : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing I :=
    Ideal.hasFiniteMulSupport hI0

  have hpow : ∀ {M : Ideal (𝓞 F)} (ψ : DedekindZetaZeroFree.RayClassCharacter F M)
      (a : Ideal (𝓞 F)) (k : ℕ), ψ (a ^ k) = ψ a ^ k := by
    intro M ψ a k
    induction k with
    | zero => simp [RayOperations.map_top]
    | succ k ih => rw [pow_succ, pow_succ, RayOperations.map_mul, ih]

  have hprod : ∀ {M : Ideal (𝓞 F)} (ψ : DedekindZetaZeroFree.RayClassCharacter F M)
      (s : Finset (HeightOneSpectrum (𝓞 F))),
      ψ (∏ v ∈ s, v.maxPowDividing I) = ∏ v ∈ s, ψ (v.maxPowDividing I) := by
    intro M ψ s
    induction s using Finset.induction_on with
    | empty => simp [RayOperations.map_top]
    | insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha, RayOperations.map_mul, ih]

  have hpt : ∀ v ∈ hfin.toFinset, η (v.maxPowDividing I) = θ (v.maxPowDividing I) := by
    intro v hv
    have hne1 : v.maxPowDividing I ≠ 1 :=
      Function.mem_mulSupport.mp ((hfin.mem_toFinset).1 hv)
    have hk : (Associates.mk v.asIdeal).count (Associates.mk I).factors ≠ 0 := by
      intro h0
      exact hne1 (by rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, h0, pow_zero])
    have hdvd : v.asIdeal ∣ I := by
      have h1 : v.maxPowDividing I ∣ I := by
        have h2 := finprod_mem_dvd (f := fun w : HeightOneSpectrum (𝓞 F) => w.maxPowDividing I)
          v hfin
        rwa [hfac] at h2
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at h1
      exact dvd_trans (dvd_pow_self _ hk) h1
    have hsup : v.asIdeal ⊔ r = ⊤ := by
      have hle : I ≤ v.asIdeal := Ideal.dvd_iff_le.1 hdvd
      have h : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal ⊔ r := by
        rw [← hrI]
        exact sup_le_sup_right hle r
      exact le_antisymm le_top h
    rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing,
      hpow (ψ := η) v.asIdeal _, hpow (ψ := θ) v.asIdeal _, hprime v hsup]
  rw [← hfac]
  rw [finprod_eq_prod _ hfin]
  rw [hprod η hfin.toFinset, hprod θ hfin.toFinset]
  exact Finset.prod_congr rfl hpt

end DedekindZetaZeroFree.LargeSieve.RootNumber
