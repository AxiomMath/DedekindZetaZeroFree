module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.GcdPairCharacterIdentities

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve

open scoped NumberField Classical
open DedekindZetaZeroFree

private theorem mul_dvd_of_sup_eq_top {R : Type*} [CommRing R] [IsDedekindDomain R]
    {d u m : Ideal R} (h : d ⊔ u = ⊤) (hd : d ∣ m) (hu : u ∣ m) : d * u ∣ m := by
  rw [Ideal.dvd_iff_le]
  rw [Ideal.mul_eq_inf_of_coprime h]
  exact le_inf (Ideal.le_of_dvd hd) (Ideal.le_of_dvd hu)

private theorem dvd_of_dvd_mul_of_sup_eq_top {R : Type*} [CommRing R] [IsDedekindDomain R]
    {a q m : Ideal R} (h : a ⊔ q = ⊤) (hm : a ∣ m * q) : a ∣ m := by
  rw [Ideal.dvd_iff_le] at hm ⊢
  calc m = m * ⊤ := by rw [Ideal.mul_top]
    _ = m * (a ⊔ q) := by rw [h]
    _ = m * a ⊔ m * q := Ideal.mul_sup m a q
    _ ≤ a := sup_le (Ideal.mul_le_right (I := m) (J := a)) hm

private theorem dvd_or_dvd_of_isPrime {R : Type*} [CommRing R] [IsDedekindDomain R]
    {p m q : Ideal R} (hp : p.IsPrime) (h : p ∣ m * q) : p ∣ m ∨ p ∣ q := by
  by_cases hpm : p ∣ m
  · exact Or.inl hpm
  · right
    rw [Ideal.dvd_iff_le] at h ⊢
    have hnot : ¬ (m ≤ p) := fun hle => hpm (Ideal.dvd_iff_le.mpr hle)
    obtain ⟨x, hxm, hxp⟩ : ∃ x, x ∈ m ∧ x ∉ p := by
      by_contra hc
      push Not at hc
      exact hnot fun x hx => hc x hx
    intro y hy
    exact (hp.mem_or_mem (h (Ideal.mul_mem_mul hxm hy))).resolve_left hxp

variable {F : Type} [Field F] [NumberField F]
variable {c : Ideal (𝓞 F)}

theorem allIndexConductorControl
    (hc : c ≠ ⊥) (Q : QuadraticHeckeFamily F c) :
    ∃ q : Ideal (𝓞 F), q ≠ ⊥ ∧ c ∣ q ∧
      (∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
        Q.cond a ∣ a * q ∧ a ∣ Q.cond a * q) ∧
      (∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ →
        a ∣ Q.cond a) ∧
      (∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
        ∀ p : Ideal (𝓞 F), p.IsPrime → p ∣ a → ¬ p ∣ q →
          p ∣ Q.cond a) := by
  classical
  haveI : Finite Q.G := Q.instFinite
  haveI : Fintype Q.G := Fintype.ofFinite Q.G

  let P : Q.G → Prop := fun g =>
    ∃ a : Ideal (𝓞 F), Squarefree a ∧ a ⊔ c = ⊤ ∧ Q.cls a = g

  let fac : Q.G → Ideal (𝓞 F) := fun g =>
    if h : P g then (Classical.choose h) * Q.cond (Classical.choose h) else ⊤
  let q : Ideal (𝓞 F) := c * ∏ g : Q.G, fac g
  have hq_eq : q = c * ∏ g : Q.G, fac g := rfl

  have hfac_ne : ∀ g : Q.G, fac g ≠ ⊥ := by
    intro g
    by_cases h : P g
    · obtain ⟨hsq, hcop, -⟩ := Classical.choose_spec h
      have hfac : fac g = (Classical.choose h) * Q.cond (Classical.choose h) := dif_pos h
      rw [hfac]
      intro hcon
      rw [Ideal.mul_eq_bot] at hcon
      exact hcon.elim (SquarefreeGcd.ne_bot_of_squarefree hsq) (Q.primitive _ hsq hcop).1
    · have hfac : fac g = ⊤ := dif_neg h
      rw [hfac]
      exact top_ne_bot
  have hprod_ne : ∀ s : Finset Q.G, (∏ g ∈ s, fac g) ≠ ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.prod_insert ha]
        intro hcon
        rw [Ideal.mul_eq_bot] at hcon
        exact hcon.elim (hfac_ne a) ih
  have hq_ne : q ≠ ⊥ := by
    rw [hq_eq]
    intro hcon
    rw [Ideal.mul_eq_bot] at hcon
    exact hcon.elim hc (hprod_ne Finset.univ)
  have hc_dvd_q : c ∣ q := by
    rw [hq_eq]
    exact dvd_mul_right c _

  have hpart1 : ∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
      Q.cond a ∣ a * q ∧ a ∣ Q.cond a * q := by
    intro a ha hac
    have hmem : P (Q.cls a) := ⟨a, ha, hac, rfl⟩
    obtain ⟨hsq, hcop, hcls⟩ := Classical.choose_spec hmem
    let r : Ideal (𝓞 F) := Classical.choose hmem
    have hrsq : Squarefree r := hsq
    have hrc : r ⊔ c = ⊤ := hcop
    have hclass : Q.cls a = Q.cls r := hcls.symm

    obtain ⟨⟨u, v⟩, ⟨hau, hrv⟩, -⟩ := SquarefreeGcd.existsUnique_strip ha hrsq
    have htr := rawGcdPairTransport hc Q ha hrsq hac hrc hclass hau hrv
    obtain ⟨-, -, -, huv, hconda⟩ := htr

    have hfac_eq : fac (Q.cls a) = r * Q.cond r := dif_pos hmem
    have hfac_dvd : r * Q.cond r ∣ q := by
      have hmem' : fac (Q.cls a) ∣ ∏ g : Q.G, fac g :=
        Finset.dvd_prod_of_mem fac (Finset.mem_univ (Q.cls a))
      rw [hfac_eq] at hmem'
      rw [hq_eq]
      exact dvd_mul_of_dvd_right hmem' c
    have ht' : ∃ t, q = (r * Q.cond r) * t := hfac_dvd
    obtain ⟨t, ht⟩ := ht'
    have hr_dvd_q : r ∣ q :=
      dvd_trans (dvd_mul_right r (Q.cond r)) hfac_dvd
    have hcondr_dvd_q : Q.cond r ∣ q :=
      dvd_trans (dvd_mul_left (Q.cond r) r) hfac_dvd

    set d : Ideal (𝓞 F) := a ⊔ r with hd
    have hau' : a = d * u := hau
    have hrv' : r = d * v := hrv
    have hstrip := SquarefreeGcd.strip_squarefree_and_coprime ha hrsq hau hrv
    have hdu : d ⊔ u = ⊤ := hstrip.2.2.2.2.1
    refine ⟨?_, ?_⟩
    ·
      refine dvd_trans hconda ?_
      refine ⟨d * d * t, ?_⟩
      rw [ht, hau', hrv']
      ring
    ·
      have hd_dvd : d ∣ Q.cond a * q :=
        dvd_mul_of_dvd_right (dvd_trans (by rw [hrv']; exact dvd_mul_right d v) hr_dvd_q)
          (Q.cond a)
      have hu_dvd : u ∣ Q.cond a * q :=
        dvd_trans (dvd_trans (dvd_mul_right u v) huv) (mul_dvd_mul_left (Q.cond a) hcondr_dvd_q)
      have hdu_dvd : d * u ∣ Q.cond a * q := mul_dvd_of_sup_eq_top hdu hd_dvd hu_dvd
      rw [← hau'] at hdu_dvd
      exact hdu_dvd

  have hpart2 : ∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ q = ⊤ → a ∣ Q.cond a := by
    intro a ha haq
    have hac : a ⊔ c = ⊤ := by
      have hqc : q ≤ c := Ideal.le_of_dvd hc_dvd_q
      exact top_le_iff.mp (le_trans (le_of_eq haq.symm) (sup_le le_sup_left (hqc.trans le_sup_right)))
    exact dvd_of_dvd_mul_of_sup_eq_top haq (hpart1 a ha hac).2

  have hpart3 : ∀ a : Ideal (𝓞 F), Squarefree a → a ⊔ c = ⊤ →
      ∀ p : Ideal (𝓞 F), p.IsPrime → p ∣ a → ¬ p ∣ q → p ∣ Q.cond a := by
    intro a ha hac p hp hpa hpq
    exact (dvd_or_dvd_of_isPrime hp (dvd_trans hpa (hpart1 a ha hac).2)).resolve_right hpq
  exact ⟨q, hq_ne, hc_dvd_q, hpart1, hpart2, hpart3⟩

end DedekindZetaZeroFree.LargeSieve
