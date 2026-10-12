module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.PrimeToFractionalIdeals.IntegralRatios

@[expose] public section

noncomputable section
open scoped NumberField Classical

namespace DedekindZetaZeroFree.RayClassBridge

@[simp] theorem rayClassCharacter_bot
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (η : RayClassCharacter F 𝔪) : η ⊥ = 0 := by
  exact (η.eq_zero_iff' ⊥).mpr (Or.inl rfl)

theorem rayClassCharacter_ne_zero_iff
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (η : RayClassCharacter F 𝔪) (I : Ideal (𝓞 F)) :
    η I ≠ 0 ↔ I ≠ ⊥ ∧ I ⊔ 𝔪 = ⊤ := by
  rw [Ne, η.eq_zero_iff' I]
  simp only [not_or, not_not]

section Construction

variable (F : Type) [Field F] [NumberField F]
variable (𝔪 : Ideal (𝓞 F))
variable (η : RayClassCharacter F 𝔪)

 def primeVal (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ℂ :=
  if v.asIdeal ⊔ 𝔪 = ⊤ then η v.asIdeal else 1

 lemma primeVal_ne_zero (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    primeVal F 𝔪 η v ≠ 0 := by
  unfold primeVal
  split_ifs with h
  · rw [ne_eq, η.eq_zero_iff']
    push_neg
    exact ⟨v.ne_bot, h⟩
  · exact one_ne_zero

 def primeUnit (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : ℂˣ :=
  Units.mk0 (primeVal F 𝔪 η v) (primeVal_ne_zero F 𝔪 η v)

private lemma primeUnit_val (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    (primeUnit F 𝔪 η v : ℂ) = primeVal F 𝔪 η v := Units.val_mk0 _

private lemma primeVal_eq_eta (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (h : v.asIdeal ⊔ 𝔪 = ⊤) : primeVal F 𝔪 η v = η v.asIdeal := by
  unfold primeVal
  rw [if_pos h]

 def freeChar :
    Multiplicative (IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℤ) →* ℂˣ :=
  MonoidHom.mk' (fun e => e.toAdd.prod fun v n => primeUnit F 𝔪 η v ^ n) (by
    intro a b
    rw [toAdd_mul]
    exact Finsupp.prod_add_index' (fun v => zpow_zero _) (fun v m n => zpow_add _ m n))

 def totalChar : ClassFieldTheory.NumberFieldFractionalIdealGroup F →* ℂˣ :=
  (freeChar F 𝔪 η).comp
    (ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).symm.toMonoidHom

 def subgroupChar (h𝔪 : 𝔪 ≠ ⊥) :
    ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) →* ℂˣ :=
  (totalChar F 𝔪 η).comp
    (ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪)).subtype

private lemma symm_factorization_toAdd
    (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
    ((ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).symm x).toAdd =
      ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector x := by
  have h1 : ClassFieldTheory.NumberFieldFractionalIdealGroup.factorization
      (Multiplicative.ofAdd
        (ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector x)) = x := by
    apply ClassFieldTheory.NumberFieldFractionalIdealGroup.ext_count
    intro v
    rw [ClassFieldTheory.NumberFieldFractionalIdealGroup.count_factorization]
    exact ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply x v
  have h2 : (ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).symm x =
      Multiplicative.ofAdd
        (ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector x) := by
    apply (ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).injective
    rw [MulEquiv.apply_symm_apply]
    exact h1.symm
  rw [h2]
  rfl

private lemma freeChar_apply (e : IsDedekindDomain.HeightOneSpectrum (𝓞 F) →₀ ℤ) :
    ((e.prod fun v n => primeUnit F 𝔪 η v ^ n : ℂˣ) : ℂ) =
      ∏ᶠ v, primeVal F 𝔪 η v ^ (e v) := by
  have hcoe : ((e.prod fun v n => primeUnit F 𝔪 η v ^ n : ℂˣ) : ℂ) =
      ∏ v ∈ e.support, primeVal F 𝔪 η v ^ (e v) := by
    rw [Finsupp.prod]
    rw [show ((∏ v ∈ e.support, primeUnit F 𝔪 η v ^ e v : ℂˣ) : ℂ) =
        ∏ v ∈ e.support, ((primeUnit F 𝔪 η v ^ e v : ℂˣ) : ℂ) from
      map_prod (Units.coeHom ℂ) _ _]
    exact Finset.prod_congr rfl fun v _ => by
      rw [Units.val_zpow_eq_zpow_val, primeUnit_val]
  rw [hcoe]
  rw [← finprod_eq_prod_of_mulSupport_subset (fun v => primeVal F 𝔪 η v ^ (e v))
    (s := e.support) ?_]
  · intro v hv
    rw [Function.mem_mulSupport] at hv
    by_contra hmem
    exact hv (by rw [Finsupp.notMem_support_iff.mp hmem, zpow_zero])

private lemma totalChar_apply (x : ClassFieldTheory.NumberFieldFractionalIdealGroup F) :
    (totalChar F 𝔪 η x : ℂ) =
      ∏ᶠ v, primeVal F 𝔪 η v
        ^ (ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector x v) := by
  have h1 : totalChar F 𝔪 η x =
      freeChar F 𝔪 η
        ((ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).symm x) :=
    rfl
  rw [h1]
  have h2 : freeChar F 𝔪 η
      ((ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).symm x) =
      ((ClassFieldTheory.NumberFieldFractionalIdealGroup.factorizationEquiv (K := F)).symm
        x).toAdd.prod (fun v n => primeUnit F 𝔪 η v ^ n) := rfl
  rw [h2, symm_factorization_toAdd F x]
  exact freeChar_apply F 𝔪 η
    (ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector x)

private lemma eta_top : η (⊤ : Ideal (𝓞 F)) = 1 := η.map_top'

private lemma eta_pow (J : Ideal (𝓞 F)) (n : ℕ) : η (J ^ n) = η J ^ n := by
  induction n with
  | zero => simp [Ideal.one_eq_top, eta_top F 𝔪 η]
  | succ n ih =>
      rw [pow_succ, show η (J ^ n * J) = η (J ^ n) * η J from η.map_mul' _ _, ih,
        pow_succ]

private lemma eta_prod_finset (s : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (f : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Ideal (𝓞 F)) :
    η (∏ v ∈ s, f v) = ∏ v ∈ s, η (f v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top, eta_top F 𝔪 η]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        show η (f a * ∏ v ∈ s, f v) = η (f a) * η (∏ v ∈ s, f v) from η.map_mul' _ _, ih]

private lemma eta_map_finprod (f : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → Ideal (𝓞 F))
    (hf : Function.HasFiniteMulSupport f) :
    η (∏ᶠ v, f v) = ∏ᶠ v, η (f v) := by
  classical
  have hfF : (Function.mulSupport f).Finite := hf
  have hsub : Function.mulSupport (fun v => η (f v)) ⊆ hfF.toFinset := by
    intro v hv
    rw [Function.mem_mulSupport] at hv
    refine (Set.Finite.mem_toFinset hfF).mpr ?_
    rw [Function.mem_mulSupport]
    intro hfv
    exact hv (by rw [hfv, Ideal.one_eq_top, eta_top F 𝔪 η])
  rw [finprod_eq_prod f hfF,
    finprod_eq_prod_of_mulSupport_subset (fun v => η (f v)) (s := hfF.toFinset) hsub]
  exact eta_prod_finset F 𝔪 η hfF.toFinset f

private lemma eta_eq_finprod_count (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) :
    η I = ∏ᶠ v, (η v.asIdeal : ℂ)
      ^ (FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
  have hI0 : I ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hI
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI0]
  rw [eta_map_finprod F 𝔪 η (fun v => v.maxPowDividing I) (Ideal.hasFiniteMulSupport hI0)]
  refine finprod_congr fun v => ?_
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing]
  rw [show η (v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) =
    η v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors from
      eta_pow F 𝔪 η v.asIdeal _]
  rw [← zpow_natCast, ← FractionalIdeal.count_coe F v hI0]

private lemma coprime_of_count_ne_zero (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hcop : I ⊔ 𝔪 = ⊤) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hv : FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0) :
    v.asIdeal ⊔ 𝔪 = ⊤ := by
  classical
  have hI0 : I ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hI
  by_contra hne
  have hdv : v.asIdeal ∣ I := by
    rw [← Associates.count_ne_zero_iff_dvd hI0 v.irreducible]
    intro h
    have hz : ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0 := by simp [h]
    rw [← FractionalIdeal.count_coe F v hI0] at hz
    exact hv hz
  have hle : I ≤ v.asIdeal := (Ideal.dvd_iff_le.mp hdv)
  have hmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have heq : v.asIdeal = v.asIdeal ⊔ 𝔪 := hmax.eq_of_le hne le_sup_left
  have hmle : 𝔪 ≤ v.asIdeal := heq.symm ▸ le_sup_right
  exact v.isPrime.ne_top (le_antisymm le_top (by
    rw [← hcop]
    exact sup_le hle hmle))

private lemma totalChar_integralUnit (I : Ideal (𝓞 F)) (hI : I ≠ ⊥)
    (hcop : I ⊔ 𝔪 = ⊤) :
    (totalChar F 𝔪 η (integralUnit F I hI) : ℂ) = η I := by
  rw [totalChar_apply F 𝔪 η (integralUnit F I hI)]
  have hcv : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector (integralUnit F I hI) v =
      FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    intro v
    rw [ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector_apply]
    rfl
  have hpoint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      primeVal F 𝔪 η v ^
          (ClassFieldTheory.NumberFieldFractionalIdealGroup.countVector (integralUnit F I hI) v) =
      (η v.asIdeal : ℂ)
        ^ (FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)) := by
    intro v
    rw [hcv v]
    by_cases h : v.asIdeal ⊔ 𝔪 = ⊤
    · rw [primeVal_eq_eta F 𝔪 η v h]
    · have hz : FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
        by_contra hc
        exact h (coprime_of_count_ne_zero F 𝔪 I hI hcop v hc)
      rw [hz, zpow_zero, zpow_zero]
  rw [finprod_congr hpoint]
  exact (eta_eq_finprod_count F 𝔪 η I hI).symm

end Construction

theorem exists_fractionalCharacter
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    ∃ χ : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) →* ℂˣ,
      ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤),
        (χ (integralPrimeTo F 𝔪 h𝔪 I hI hcop) : ℂ) = η I := by
  refine ⟨subgroupChar F 𝔪 η h𝔪, ?_⟩
  intro I hI hcop
  change (totalChar F 𝔪 η (integralUnit F I hI) : ℂ) = η I
  exact totalChar_integralUnit F 𝔪 η I hI hcop

def fractionalCharacter
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪) :
    ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) →* ℂˣ :=
  (exists_fractionalCharacter F 𝔪 h𝔪 η).choose

@[simp] theorem fractionalCharacter_integral
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤) :
    (fractionalCharacter F 𝔪 h𝔪 η (integralPrimeTo F 𝔪 h𝔪 I hI hcop) : ℂ) = η I :=
  (exists_fractionalCharacter F 𝔪 h𝔪 η).choose_spec I hI hcop

theorem fractionalCharacter_unique
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (χ : ClassFieldTheory.rayClassPrimeToIdeals (narrowIdealModulus F 𝔪 h𝔪) →* ℂˣ)
    (hχ : ∀ (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (hcop : I ⊔ 𝔪 = ⊤),
      (χ (integralPrimeTo F 𝔪 h𝔪 I hI hcop) : ℂ) = η I) :
    χ = fractionalCharacter F 𝔪 h𝔪 η :=
  RayFractional.eq_of_integral_values F 𝔪 h𝔪 χ (fractionalCharacter F 𝔪 h𝔪 η)
    (fun I hI hcop => by rw [hχ I hI hcop, fractionalCharacter_integral F 𝔪 h𝔪 η I hI hcop])

theorem fractionalCharacter_quotient
    (F : Type) [Field F] [NumberField F]
    (𝔪 : Ideal (𝓞 F)) (h𝔪 : 𝔪 ≠ ⊥) (η : RayClassCharacter F 𝔪)
    (A B : Ideal (𝓞 F)) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hcA : A ⊔ 𝔪 = ⊤) (hcB : B ⊔ 𝔪 = ⊤) :
    (fractionalCharacter F 𝔪 h𝔪 η
      (integralPrimeTo F 𝔪 h𝔪 A hA hcA *
        (integralPrimeTo F 𝔪 h𝔪 B hB hcB)⁻¹) : ℂ) = η A / η B := by
  rw [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val,
    fractionalCharacter_integral F 𝔪 h𝔪 η A hA hcA,
    fractionalCharacter_integral F 𝔪 h𝔪 η B hB hcB]
  rfl

end DedekindZetaZeroFree.RayClassBridge

end
