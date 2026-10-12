module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ReciprocityPrefixOperator
public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.WeightedGramBound
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdmissibleRangeBoundaryCases
public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoprimeForms.PrimeSupportEpsilonEnergyBound
public import DedekindZetaZeroFree.Analysis.FinitePartitionQuadraticBounds
public import DedekindZetaZeroFree.LargeSieve.Bilinear.Divisors.IdealDivisorRectangleOperatorBound

@[expose] public section

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

theorem core_prefix_operator
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) :
    ∃ H : ℝ, 1 ≤ H ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
      ∀ R S : Finset (Ideal (𝓞 F)),
        R ⊆ idealAdmissibleFinset F D.bad X →
        S ⊆ idealAdmissibleFinset F D.bad (2 * N) →
      ∀ z : Ideal (𝓞 F) → ℂ,
        (∑ a ∈ R, ‖∑ u ∈ S, z u * (Q.χ u) a‖ ^ 2) ≤
          H * MainBoundaryBound.shellPrefixEnvelope F c Q X N *
            ∑ u ∈ S, ‖z u‖ ^ 2 := by
  obtain ⟨H, hH, hbound⟩ := core_prefix_operator_bound Q D
  refine ⟨max 1 H, le_max_left _ _, ?_⟩
  intro X N hX hN R S hR hS z
  have henv : 0 ≤ MainBoundaryBound.shellPrefixEnvelope F c Q X N := by
    unfold MainBoundaryBound.shellPrefixEnvelope
    have hsum : 0 ≤ ∑ i ∈ Finset.range (Vendor.dyadicLength X),
        ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
          B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => B1_nonneg Q _ _
    positivity
  calc
    _ ≤ H * MainBoundaryBound.shellPrefixEnvelope F c Q X N *
        ∑ u ∈ S, ‖z u‖ ^ 2 := hbound X N hX hN R S hR hS z
    _ ≤ max 1 H * MainBoundaryBound.shellPrefixEnvelope F c Q X N *
        ∑ u ∈ S, ‖z u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) henv)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

private lemma density_interval (a : Ideal (𝓞 F)) :
    0 ≤ Vendor.CutoffDifference.density (MainBoundaryBound.idealSize F) a ∧
    Vendor.CutoffDifference.density (MainBoundaryBound.idealSize F) a ≤ 1 := by
  have hp : ∀ p ∈ (UniqueFactorizationMonoid.factors a).toFinset,
      (1 : ℝ) ≤ (Ideal.absNorm p : ℝ) := by
    intro p hp
    have hp' := UniqueFactorizationMonoid.prime_of_factor p (Multiset.mem_toFinset.mp hp)
    have hp0 : p ≠ ⊥ := hp'.ne_zero
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by simpa [Ideal.absNorm_eq_zero_iff] using hp0)
  have he : ∀ p ∈ (UniqueFactorizationMonoid.factors a).toFinset,
      0 ≤ 1 - 1 / ((MainBoundaryBound.idealSize F) p : ℝ) ∧
      1 - 1 / ((MainBoundaryBound.idealSize F) p : ℝ) ≤ 1 := by
    intro p hpMem
    have hp1 := hp p hpMem
    change 0 ≤ 1 - 1 / (Ideal.absNorm p : ℝ) ∧
      1 - 1 / (Ideal.absNorm p : ℝ) ≤ 1
    constructor
    · have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp1
      simp only [one_div_one, ← one_div] at this
      linarith
    · have : 0 ≤ 1 / (Ideal.absNorm p : ℝ) := by positivity
      linarith
  constructor
  · exact Finset.prod_nonneg (fun p hp => (he p hp).1)
  · exact (Finset.prod_le_prod₀ (fun p hp => (he p hp).1)
      (fun p hp => (he p hp).2)).trans (by simp)

private lemma density_mul (a b : Ideal (𝓞 F)) (ha : a ≠ ⊥) (hb : b ≠ ⊥)
    (hab : a ⊔ b = ⊤) :
    Vendor.CutoffDifference.density (MainBoundaryBound.idealSize F) (a * b) =
      Vendor.CutoffDifference.density (MainBoundaryBound.idealSize F) a *
      Vendor.CutoffDifference.density (MainBoundaryBound.idealSize F) b := by
  classical
  have hprod : UniqueFactorizationMonoid.factors (a * b) =
      UniqueFactorizationMonoid.factors a + UniqueFactorizationMonoid.factors b := by
    simp only [UniqueFactorizationMonoid.factors_eq_normalizedFactors]
    exact UniqueFactorizationMonoid.normalizedFactors_mul ha hb
  simp only [Vendor.CutoffDifference.density, hprod, Multiset.toFinset_add]
  apply Finset.prod_union
  rw [Finset.disjoint_left]
  intro p hp hq
  have hpa : p ∣ a := UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hp)
  have hpb : p ∣ b := UniqueFactorizationMonoid.dvd_of_mem_factors (Multiset.mem_toFinset.mp hq)
  have hpab : p ∣ a ⊔ b := Ideal.dvd_iff_le.mpr
    (sup_le (Ideal.dvd_iff_le.mp hpa) (Ideal.dvd_iff_le.mp hpb))
  rw [hab, ← Ideal.one_eq_top] at hpab
  exact (UniqueFactorizationMonoid.prime_of_factor p (Multiset.mem_toFinset.mp hp)).not_isUnit
    (isUnit_of_dvd_one hpab)

private lemma coprime_rows_bound (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (R S : Finset (Ideal (𝓞 F))) (hS : ∀ u ∈ S, u ≠ ⊥)
    (U : ℝ) (hU : 0 ≤ U)
    (hop : ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ u ∈ S, z u * (Q.χ u) a‖ ^ 2) ≤ U * ∑ u ∈ S, ‖z u‖ ^ 2)
    (z : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖) ≤
      U * ∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2 := by
  have hm : ∀ e ∈ ({⊤} : Finset (Ideal (𝓞 F))), ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ u ∈ S, if e ∣ u then z u * (Q.χ u) a else 0‖ ^ 2) ≤
        U * ∑ u ∈ S, ‖z u‖ ^ 2 := by
    intro e he z
    have he' : e = ⊤ := Finset.mem_singleton.mp he
    subst e
    simpa only [← Ideal.one_eq_top, one_dvd, if_true] using hop z
  have h := DivisorSeparation.rectangle_operator_bound Q {⊤} {⊤} R S S
    hS hS U U hU hU hm hm z z
  simp only [DivisorSeparation.idealDivisorRectangle, Finset.sum_singleton,
    Finset.card_singleton, Nat.cast_one, one_mul, ← Ideal.one_eq_top, one_dvd,
    and_true, Finset.filter_true_of_mem, mul_one] at h
  simp only [Finset.filter_singleton, one_dvd, if_true, Finset.card_singleton,
    Nat.cast_one, mul_one, Ideal.one_eq_top] at h
  have htopdvd : ∀ u : Ideal (𝓞 F), (⊤ : Ideal (𝓞 F)) ∣ u := by
    intro u
    exact Ideal.dvd_iff_le.mpr le_top
  simp only [htopdvd, if_true, Finset.card_singleton, Nat.cast_one, mul_one] at h
  change (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖) ^ 2 ≤
      U * U * (∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2) *
        (∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2) at h
  have h0 : 0 ≤ ∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2 := by
    unfold GcdTail.primeSupportCost
    positivity
  have hsq : (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖) ^ 2 ≤
      (U * ∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2) ^ 2 := by
    calc _ ≤ _ := h
         _ = _ := by ring
  exact (sq_le_sq₀ (by positivity) (mul_nonneg hU h0)).mp hsq

private lemma nonunit_rows_bound (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (R S : Finset (Ideal (𝓞 F))) (hS : ∀ u ∈ S, u ≠ ⊥)
    (U : ℝ) (hU : 0 ≤ U)
    (hop : ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ R, ‖∑ u ∈ S, z u * (Q.χ u) a‖ ^ 2) ≤ U * ∑ u ∈ S, ‖z u‖ ^ 2)
    (z : Ideal (𝓞 F) → ℂ) :
    (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖) ≤
      2 * U * ∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2 := by
  classical
  let z0 : Ideal (𝓞 F) → ℂ := fun u => if u = ⊤ then z u else 0
  have heq : ∀ a : Ideal (𝓞 F),
    (∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0) =
    (∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0) -
    (∑ u ∈ S, z0 u * (Q.χ u) a) * star (∑ u ∈ S, z0 u * (Q.χ u) a) := by
    intro a
    rw [star_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    have ht : u * v = ⊤ ↔ u = ⊤ ∧ v = ⊤ := by
      constructor
      · intro h
        exact ⟨top_le_iff.mp (h ▸ Ideal.mul_le_left),
          top_le_iff.mp (h ▸ Ideal.mul_le_right)⟩
      · rintro ⟨rfl, rfl⟩
        simp
    by_cases hu1 : u = ⊤ <;> by_cases hv1 : v = ⊤
    · subst u; subst v
      simp [z0, star_mul, mul_assoc, mul_left_comm, mul_comm]
    · simp [z0, hu1, hv1, ht, star_mul]
    · simp [z0, hu1, hv1, ht, star_mul]
    · simp [z0, hu1, hv1, ht, star_mul]
  have henergy : (∑ u ∈ S, ‖z0 u‖ ^ 2) ≤
      ∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro u hu
    have hcost : 1 ≤ GcdTail.primeSupportCost u := by
      unfold GcdTail.primeSupportCost
      exact one_le_pow₀ (by norm_num)
    by_cases h : u = ⊤
    · simp only [z0, if_pos h]
      exact le_mul_of_one_le_left (sq_nonneg _) hcost
    · simp only [z0, if_neg h, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      positivity
  calc (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
      z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖)
      ≤ (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ then
        z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖) +
        (∑ a ∈ R, ‖∑ u ∈ S, z0 u * (Q.χ u) a‖ ^ 2) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro a ha
        rw [heq]
        simpa only [norm_mul, norm_star, pow_two] using norm_sub_le
          (∑ u ∈ S, ∑ v ∈ S, if u ⊔ v = ⊤ then
          z u * star (z v) * (Q.χ u) a * star ((Q.χ v) a) else 0)
          ((∑ u ∈ S, z0 u * (Q.χ u) a) * star (∑ u ∈ S, z0 u * (Q.χ u) a))
    _ ≤ U * (∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2) +
        U * (∑ u ∈ S, GcdTail.primeSupportCost u * ‖z u‖ ^ 2) :=
      add_le_add (coprime_rows_bound Q R S hS U hU hop z)
        ((hop z0).trans (mul_le_mul_of_nonneg_left henergy hU))
    _ = _ := by ring

theorem density_rows_of_operator
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q)
    (X N : ℝ) (hX : 1 ≤ X) (hN : 1 ≤ N)
    (d : Ideal (𝓞 F)) (hd : Squarefree d) (hdb : d ⊔ D.bad = ⊤)
    (g : Q.G) (U : ℝ) (hU : 1 ≤ U)
    (hop : ∀ z : Ideal (𝓞 F) → ℂ,
      (∑ a ∈ idealAdmissibleFinset F D.bad X,
        ‖∑ u ∈ MainBoundaryBound.quotientColumns Q D.bad d N g,
          z u * (Q.χ u) a‖ ^ 2) ≤
        U * ∑ u ∈ MainBoundaryBound.quotientColumns Q D.bad d N g, ‖z u‖ ^ 2)
    (lam : Ideal (𝓞 F) → ℂ) :
    MainBoundaryBound.squarefreeRows Q D.bad d X N g lam ≤
      2 * ((Vendor.CutoffDifference.divisors d).card : ℝ) * U *
        ∑ u ∈ MainBoundaryBound.quotientColumns Q D.bad d N g,
          GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2 := by
  classical
  let R := idealAdmissibleFinset F D.bad X
  let S := MainBoundaryBound.quotientColumns Q D.bad d N g
  let rho := fun u : Ideal (𝓞 F) =>
    Vendor.CutoffDifference.density (MainBoundaryBound.idealSize F) u
  have hSdata : ∀ u ∈ S, Squarefree u ∧ u ⊔ D.bad = ⊤ := by
    intro u hu
    exact ⟨((mem_idealAdmissibleFinset F D.bad _ u).mp (Finset.mem_filter.mp hu).1).1,
      ((mem_idealAdmissibleFinset F D.bad _ u).mp (Finset.mem_filter.mp hu).1).2.1⟩
  have hSne : ∀ u ∈ S, u ≠ ⊥ := by
    intro u hu
    exact (hSdata u hu).1.ne_zero
  have hSc : ∀ u ∈ S, u ⊔ c = ⊤ := by
    intro u hu
    exact eq_top_iff.mpr ((hSdata u hu).2 ▸
      sup_le_sup_left (Ideal.le_of_dvd D.original_dvd_bad) u)
  have hU0 : 0 ≤ U := by linarith
  let beta := fun (t u : Ideal (𝓞 F)) => lam (d * u) * (rho u : ℂ) * (Q.χ u) (t ^ 2)
  have hbeta : ∀ t, ∀ u ∈ S, ‖beta t u‖ ≤ ‖lam (d * u)‖ := by
    intro t u hu
    have hr : 0 ≤ rho u ∧ rho u ≤ 1 := density_interval u
    have hc := DedekindZetaZeroFree.LargeSieve.quadraticFamily_norm_le_one Q (hSdata u hu).1 (hSc u hu) (t ^ 2)
    simp only [beta, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr.1]
    calc ‖lam (d * u)‖ * rho u * ‖(Q.χ u) (t ^ 2)‖ ≤
          ‖lam (d * u)‖ * rho u :=
        mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) hr.1) hc
      _ ≤ ‖lam (d * u)‖ := mul_le_of_le_one_right (norm_nonneg _) hr.2
  have hpair : ∀ t a, ∀ u ∈ S, ∀ v ∈ S, u ⊔ v = ⊤ →
      lam (d * u) * star (lam (d * v)) * (rho (D.bad * u * v) : ℂ) *
        MainBoundaryBound.pairCharacter Q u v (a * t ^ 2) =
      (rho D.bad : ℂ) *
        (beta t u * star (beta t v) * (Q.χ u) a * star ((Q.χ v) a)) := by
    intro t a u hu v hv huv
    have hqu : D.bad ⊔ u = ⊤ := by simpa [sup_comm] using (hSdata u hu).2
    have hqv : D.bad ⊔ v = ⊤ := by simpa [sup_comm] using (hSdata v hv).2
    have hquv : D.bad * u ⊔ v = ⊤ := by
      rw [sup_comm, Ideal.sup_mul_eq_of_coprime_left (hSdata v hv).2]
      simpa [sup_comm] using huv
    have hf : rho (D.bad * u * v) = rho D.bad * rho u * rho v := by
      dsimp only [rho]
      rw [density_mul (D.bad * u) v (mul_ne_zero D.bad_ne_bot (hSne u hu)) (hSne v hv) hquv,
        density_mul D.bad u D.bad_ne_bot (hSne u hu) hqu]
    change lam (d * u) * star (lam (d * v)) * (rho (D.bad * u * v) : ℂ) *
      ((Q.χ u) (a * t ^ 2) * star ((Q.χ v) (a * t ^ 2))) = _
    simp only [hf, MainBoundaryBound.pairCharacter, MonoidHom.coe_mk,
      MonoidHom.coe_coe, (Q.χ u).map_mul', (Q.χ v).map_mul', beta,
      star_mul, Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
    ring
  have hrow : ∀ t a,
      MainBoundaryBound.densityRow Q D.bad d N g lam (a * t ^ 2) =
      (rho D.bad : ℂ) * (∑ u ∈ S, ∑ v ∈ S,
        if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
          beta t u * star (beta t v) * (Q.χ u) a * star ((Q.χ v) a) else 0) := by
    intro t a
    unfold MainBoundaryBound.densityRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u hu
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases h : u ⊔ v = ⊤ ∧ u * v ≠ ⊤
    · simp only [if_pos h]
      exact hpair t a u hu v hv h.1
    · simp only [if_neg h, mul_zero]
  have hweighted : ∀ t,
      (∑ u ∈ S, GcdTail.primeSupportCost u * ‖beta t u‖ ^ 2) ≤
      ∑ u ∈ S, GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2 := by
    intro t
    apply Finset.sum_le_sum
    intro u hu
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hbeta t u hu) 2) (by
        unfold GcdTail.primeSupportCost; positivity)
  have hfixed : ∀ t,
      (∑ a ∈ R, ‖MainBoundaryBound.densityRow Q D.bad d N g lam (a * t ^ 2)‖) ≤
      2 * U * ∑ u ∈ S, GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2 := by
    intro t
    calc (∑ a ∈ R, ‖MainBoundaryBound.densityRow Q D.bad d N g lam (a * t ^ 2)‖)
        ≤ (∑ a ∈ R, ‖∑ u ∈ S, ∑ v ∈ S,
        if u ⊔ v = ⊤ ∧ u * v ≠ ⊤ then
          beta t u * star (beta t v) * (Q.χ u) a * star ((Q.χ v) a) else 0‖) := by
          apply Finset.sum_le_sum
          intro a ha
          rw [hrow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (show 0 ≤ rho D.bad from (density_interval D.bad).1)]
          exact mul_le_of_le_one_left (norm_nonneg _) (density_interval D.bad).2
      _ ≤ 2 * U * ∑ u ∈ S, GcdTail.primeSupportCost u * ‖beta t u‖ ^ 2 :=
        nonunit_rows_bound Q R S hSne U hU0 hop (beta t)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hweighted t) (by positivity)
  unfold MainBoundaryBound.squarefreeRows
  calc _ ≤ ∑ t ∈ Vendor.CutoffDifference.divisors d,
      2 * U * ∑ u ∈ S, GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2 :=
        Finset.sum_le_sum (fun t ht => hfixed t)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}

private lemma primeSupportCost_le_divisorCount {F : Type} [Field F] [NumberField F]
    (u : Ideal (𝓞 F)) (hu : u ≠ ⊥) :
    (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount u : ℝ) := by
  classical
  set m := UniqueFactorizationMonoid.normalizedFactors u with hm
  set S := m.toFinset with hS
  have hmem : ∀ p : Ideal (𝓞 F), p ∈ S ↔ p ∈ m := fun p => Multiset.mem_toFinset
  have hprime : ∀ p ∈ S, Irreducible p := fun p hp =>
    UniqueFactorizationMonoid.irreducible_of_normalized_factor p ((hmem p).mp hp)
  have hnorm : ∀ p ∈ S, normalize p = p := fun p hp =>
    UniqueFactorizationMonoid.normalize_normalized_factor p ((hmem p).mp hp)
  have key : ∀ s : Finset (Ideal (𝓞 F)), s ⊆ S →
      UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val := by
    intro s hs
    have hirr : ∀ p ∈ s.val, Irreducible p := by
      intro p hp
      exact hprime p (hs (by simpa using hp))
    have h1 := UniqueFactorizationMonoid.normalizedFactors_prod_eq s.val hirr
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, h1]
    rw [Multiset.map_congr rfl (fun p hp => hnorm p (hs (by simpa using hp))),
      Multiset.map_id']
  have hinj : Set.InjOn (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F)))) := by
    intro s hs t ht hst
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have htsub : t ⊆ S := Finset.mem_powerset.mp ht
    have hsval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ s, p) = s.val :=
      key s hssub
    have htval : UniqueFactorizationMonoid.normalizedFactors (∏ p ∈ t, p) = t.val :=
      key t htsub
    have hst' : (∏ p ∈ s, p) = (∏ p ∈ t, p) := hst
    rw [hst'] at hsval
    exact Finset.val_inj.mp (hsval.symm.trans htval)
  have hmaps : Set.MapsTo (fun s : Finset (Ideal (𝓞 F)) => ∏ p ∈ s, p)
      (↑S.powerset : Set (Finset (Ideal (𝓞 F))))
      (↑(DedekindZetaZeroFree.LargeSieve.idealDivisors u) : Set (Ideal (𝓞 F))) := by
    intro s hs
    change (∏ p ∈ s, p) ∈ DedekindZetaZeroFree.LargeSieve.idealDivisors u
    rw [DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hu]
    have hssub : s ⊆ S := Finset.mem_powerset.mp hs
    have hle : s.val ≤ m := by
      rw [Multiset.le_iff_subset s.nodup]
      intro p hp
      exact (hmem p).mp (hssub (by simpa using hp))
    have hprod : (∏ p ∈ s, p) = s.val.prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id']
    rw [hprod, ← Ideal.prod_normalizedFactors_eq_self hu]
    exact Multiset.prod_dvd_prod_of_le hle
  have hcard : S.powerset.card ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisors u).card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hcost : (2 : ℝ) ^ (UniqueFactorizationMonoid.normalizedFactors u).toFinset.card = (2 : ℝ) ^ S.card := by
    rw [hS, ← hm]
  rw [hcost]
  have hpc : ((S.powerset.card : ℕ) : ℝ) = (2 : ℝ) ^ S.card := by
    rw [Finset.card_powerset]
    push_cast
    ring
  rw [← hpc]
  exact_mod_cast hcard

private lemma cutoff_divisors_le_count (d : Ideal (𝓞 F)) (hd0 : d ≠ ⊥) :
    ((Vendor.CutoffDifference.divisors d).card : ℝ) ≤ (DedekindZetaZeroFree.LargeSieve.idealDivisorCount d : ℝ) := by
  have hsub : Vendor.CutoffDifference.divisors d ⊆ DedekindZetaZeroFree.LargeSieve.idealDivisors d := by
    intro t ht
    rw [DedekindZetaZeroFree.LargeSieve.mem_idealDivisors hd0]
    unfold Vendor.CutoffDifference.divisors at ht
    rw [if_neg (by simpa using hd0 : d ≠ 0)] at ht
    simp only [Finset.mem_image, Multiset.mem_toFinset, Multiset.mem_powerset] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    have heq : (UniqueFactorizationMonoid.factors d).prod = d :=
      associated_iff_eq.mp (UniqueFactorizationMonoid.factors_prod hd0)
    exact heq ▸ Multiset.prod_dvd_prod_of_le hs
  exact_mod_cast Finset.card_le_card hsub

theorem quotient_incidence_energy
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℝ, 1 ≤ N →
      ∀ q d : Ideal (𝓞 F), Squarefree d →
      ∀ g : Q.G, ∀ lam : Ideal (𝓞 F) → ℂ,
        ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 3 *
          (∑ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
            GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2) ≤
          C * (N * (Ideal.absNorm d : ℝ)) ^ η * energy F c N lam := by
  intro η hη
  have he : 0 < η / 3 := by linarith
  obtain ⟨A, hA, hcnt⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F (η / 3) he
  obtain ⟨B, hB, hcntB⟩ := DedekindZetaZeroFree.LargeSieve.ideal_divisor_count_le_rpow F η hη
  refine ⟨A ^ 3 * B * 2 ^ η, by positivity, ?_⟩
  intro N hN q d hd g lam
  have hd0 : d ≠ ⊥ := by simpa using hd.ne_zero
  have hn0 : 0 < (Ideal.absNorm d : ℝ) := by
    have h : Ideal.absNorm d ≠ 0 := fun h => hd0 (Ideal.absNorm_eq_zero_iff.mp h)
    exact_mod_cast Nat.pos_of_ne_zero h
  have hn1 : (1 : ℝ) ≤ (Ideal.absNorm d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun h => hd0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hτ : ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 3 ≤
      A ^ 3 * (Ideal.absNorm d : ℝ) ^ η := by
    have hh := (cutoff_divisors_le_count d hd0).trans (hcnt d)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hh 3
    rw [mul_pow] at hp
    have heq : ((Ideal.absNorm d : ℝ) ^ (η / 3)) ^ 3 = (Ideal.absNorm d : ℝ) ^ η := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
      congr 1
      norm_num
    rwa [heq] at hp
  have hcols : ∀ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
      u ≠ ⊥ ∧ (Ideal.absNorm u : ℝ) ≤ 2 * N ∧ d * u ∈ paperShell F c N := by
    intro u hu
    obtain ⟨hbase, hdu, hshell, hclass⟩ := Finset.mem_filter.mp hu
    obtain ⟨hsf, hcop, hnorm⟩ := (mem_idealAdmissibleFinset _ _ _ _).mp hbase
    exact ⟨by simpa using hsf.ne_zero, hnorm.trans (div_le_self (by linarith) hn1), hshell⟩
  have hcost : ∀ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
      GcdTail.primeSupportCost u ≤ B * (2 * N) ^ η := by
    intro u hu
    exact (primeSupportCost_le_divisorCount u (hcols u hu).1).trans
      ((hcntB u).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hcols u hu).2.1 hη.le)
        (by linarith)))
  have henergy : (∑ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
      ‖lam (d * u)‖ ^ 2) ≤ energy F c N lam := by
    apply Finset.sum_le_sum_of_injOn (fun u => d * u)
    · intro u _ v _ huv
      exact mul_left_cancel₀ (by simpa using hd0 : d ≠ 0) huv
    · intro b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
      exact (hcols u hu).2.2
    · intro u hu
      exact le_rfl
    · intro b _ _
      exact sq_nonneg _
  have hw : (∑ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
      GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2) ≤
      B * (2 * N) ^ η * energy F c N lam := by
    calc _ ≤ ∑ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
          (B * (2 * N) ^ η) * ‖lam (d * u)‖ ^ 2 :=
        Finset.sum_le_sum fun u hu => mul_le_mul_of_nonneg_right (hcost u hu) (sq_nonneg _)
      _ = B * (2 * N) ^ η * ∑ u ∈ MainBoundaryBound.quotientColumns Q q d N g,
          ‖lam (d * u)‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left henergy (by positivity)
  have hp : (Ideal.absNorm d : ℝ) ^ η * (2 * N) ^ η =
      2 ^ η * (N * (Ideal.absNorm d : ℝ)) ^ η := by
    rw [Real.mul_rpow (by norm_num) (by linarith : (0 : ℝ) ≤ N),
      Real.mul_rpow (by linarith : (0 : ℝ) ≤ N) hn0.le]
    ring
  calc _ ≤ (A ^ 3 * (Ideal.absNorm d : ℝ) ^ η) *
        (B * (2 * N) ^ η * energy F c N lam) :=
      mul_le_mul hτ hw (Finset.sum_nonneg fun _ _ => by unfold GcdTail.primeSupportCost; positivity)
        (by positivity)
    _ = (A ^ 3 * B) * ((Ideal.absNorm d : ℝ) ^ η * (2 * N) ^ η) *
        energy F c N lam := by ring
    _ = _ := by rw [hp]; ring

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryPrefix

end

end

section

noncomputable section
open scoped NumberField Classical NNReal
namespace DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound
variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

theorem squarefree_rows_le_prefix
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (D : NormalizedFamilyData Q) :
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
      ∀ d : Ideal (𝓞 F), Squarefree d → d ⊔ D.bad = ⊤ →
        (Ideal.absNorm d : ℝ) ≤ 2 * N →
      ∀ g : Q.G, ∀ lam : Ideal (𝓞 F) → ℂ,
        ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
          squarefreeRows Q D.bad d X N g lam ≤
          C * (X * N * (Ideal.absNorm d : ℝ)) ^ η *
            shellPrefixEnvelope F c Q X N * energy F c N lam := by
  intro η hη
  obtain ⟨H, hH, hop⟩ := MainBoundaryPrefix.core_prefix_operator Q D
  obtain ⟨C, hC, hinc⟩ := MainBoundaryPrefix.quotient_incidence_energy Q η hη
  refine ⟨2 * H * C, by positivity, ?_⟩
  intro X N hX hN d hd hdb hdn g lam
  have henv1 : 1 ≤ shellPrefixEnvelope F c Q X N := by
    have hsum : 0 ≤ ∑ i ∈ Finset.range (Vendor.dyadicLength X),
        ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
          B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i) :=
      Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => B1_nonneg Q _ _
    unfold shellPrefixEnvelope
    have hc : (1 : ℝ) ≤ ((Vendor.dyadicLength (2 * N) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
    have hb : 1 ≤ 1 + X + N + ∑ i ∈ Finset.range (Vendor.dyadicLength X),
        ∑ j ∈ Finset.range (Vendor.dyadicLength (2 * N)),
          B1 F c Q ((2 : ℝ) ^ j) ((2 : ℝ) ^ i) := by linarith
    nlinarith
  have hU : 1 ≤ H * shellPrefixEnvelope F c Q X N := by nlinarith
  have hd0 : d ≠ ⊥ := by simpa using hd.ne_zero
  have hn1 : (1 : ℝ) ≤ (Ideal.absNorm d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun h => hd0 (Ideal.absNorm_eq_zero_iff.mp h))
  have hcols : quotientColumns Q D.bad d N g ⊆ idealAdmissibleFinset F D.bad (2 * N) := by
    intro u hu
    obtain ⟨hsf, hcop, hn⟩ :=
      (mem_idealAdmissibleFinset F D.bad (2 * N / (Ideal.absNorm d : ℝ)) u).mp
        (Finset.mem_filter.mp hu).1
    exact (mem_idealAdmissibleFinset F D.bad (2 * N) u).mpr
      ⟨hsf, hcop, hn.trans (div_le_self (by linarith) hn1)⟩
  have hr := MainBoundaryPrefix.density_rows_of_operator Q D X N hX hN d hd hdb g
    (H * shellPrefixEnvelope F c Q X N) hU
    (fun z => hop X N hX hN _ _ (Finset.Subset.refl _) hcols z) lam
  have hi := hinc N hN D.bad d hd g lam
  have he : 0 ≤ shellPrefixEnvelope F c Q X N := le_trans zero_le_one henv1
  have hp : (N * (Ideal.absNorm d : ℝ)) ^ η ≤
      (X * N * (Ideal.absNorm d : ℝ)) ^ η := by
    apply Real.rpow_le_rpow (by positivity) _ hη.le
    calc N * (Ideal.absNorm d : ℝ) = 1 * (N * (Ideal.absNorm d : ℝ)) := by ring
      _ ≤ X * (N * (Ideal.absNorm d : ℝ)) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      _ = _ := by ring
  have henergy : 0 ≤ energy F c N lam := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
        squarefreeRows Q D.bad d X N g lam
      ≤ ((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 2 *
          (2 * ((Vendor.CutoffDifference.divisors d).card : ℝ) *
            (H * shellPrefixEnvelope F c Q X N) *
            ∑ u ∈ quotientColumns Q D.bad d N g,
              GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hr (sq_nonneg _)
    _ = (2 * H * shellPrefixEnvelope F c Q X N) *
        (((Vendor.CutoffDifference.divisors d).card : ℝ) ^ 3 *
          ∑ u ∈ quotientColumns Q D.bad d N g,
            GcdTail.primeSupportCost u * ‖lam (d * u)‖ ^ 2) := by ring
    _ ≤ (2 * H * shellPrefixEnvelope F c Q X N) *
        (C * (N * (Ideal.absNorm d : ℝ)) ^ η * energy F c N lam) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ (2 * H * shellPrefixEnvelope F c Q X N) *
        (C * (X * N * (Ideal.absNorm d : ℝ)) ^ η * energy F c N lam) := by
      gcongr
    _ = _ := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve.MainBoundaryBound

end

end
