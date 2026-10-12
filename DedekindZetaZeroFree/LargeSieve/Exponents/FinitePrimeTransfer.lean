module

public import DedekindZetaZeroFree.Analysis.QuadraticFormRestriction

@[expose] public section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Vendor

private lemma norm_add_sq_le_two (x y : ℂ) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    sq_le_sq' (by nlinarith [norm_nonneg (x + y), norm_nonneg x, norm_nonneg y]) h1
  have h3 : (‖x‖ + ‖y‖) ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := add_sq_le
  linarith

private lemma sum_le_univ_of_injective {α β : Type*} [Fintype β] [DecidableEq β]
    (G : Finset α) (f : α → β) (hf : Function.Injective f) (φ : β → ℝ)
    (hφ : ∀ b, 0 ≤ φ b) : (∑ a ∈ G, φ (f a)) ≤ ∑ b : β, φ b := by
  have himg : (∑ a ∈ G, φ (f a)) = ∑ b ∈ G.image f, φ b :=
    (Finset.sum_image (s := G) (g := f) (f := φ) hf.injOn).symm
  rw [himg]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun b _ _ => hφ b

theorem exponent_finite_prime_transfer
    {r s t : Type*} [Fintype r] [Fintype s] [Fintype t]
    (A : Matrix r s ℂ) (H : Matrix t s ℂ) (R₀ : Finset r)
    (badRow : r → Prop) (badCol : s → Prop)
    [DecidablePred badRow] [DecidablePred badCol]
    (u : s → ℂ) (hu : ∀ b, ‖u b‖ ≤ 1)
    (f : {a : r // a ∈ R₀ ∧ ¬badRow a} → t)
    (hf : Function.Injective f)
    (htransport : ∀ (a : {a : r // a ∈ R₀ ∧ ¬badRow a}) (b : s),
      ¬badCol b → A a.val b = u b * H (f a) b)
    (Bs Bl : ℝ) (hBs : 0 ≤ Bs) (hBl : 0 ≤ Bl)
    (hA : ∀ v : s → ℂ,
      ∑ a : r, ‖∑ b : s, v b * A a b‖ ^ 2 ≤ Bs * ∑ b : s, ‖v b‖ ^ 2)
    (hH : ∀ v : s → ℂ,
      ∑ x : t, ‖∑ b : s, v b * H x b‖ ^ 2 ≤ Bl * ∑ b : s, ‖v b‖ ^ 2)
    (v : s → ℂ) :
    ∑ a ∈ R₀, ‖∑ b : s, v b * A a b‖ ^ 2 ≤
      (∑ a ∈ Finset.univ.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2) +
      2 * Bl * (∑ b : s, ‖v b‖ ^ 2) +
      2 * Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2) := by
  classical

  let good : Finset r := R₀.filter (fun a => ¬ badRow a)
  let F : {a : r // a ∈ good} → t := fun a => f ⟨a.val, Finset.mem_filter.mp a.2⟩
  let v' : s → ℂ := fun b => if badCol b then 0 else v b * u b
  let vbad : s → ℂ := fun b => if badCol b then v b else 0

  have hpoint : ∀ a : {a : r // a ∈ good},
      ‖∑ b : s, v b * A a.val b‖ ^ 2 ≤
        2 * ‖∑ b : s, v' b * H (F a) b‖ ^ 2 +
        2 * ‖∑ b : s, vbad b * A a.val b‖ ^ 2 := by
    intro a
    have hdecomp : (∑ b : s, v b * A a.val b) =
        (∑ b : s, v' b * H (F a) b) + ∑ b : s, vbad b * A a.val b := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : badCol b
      · simp [v', vbad, hb]
      · have htr := htransport ⟨a.val, Finset.mem_filter.mp a.2⟩ b hb
        simp only [v', vbad, if_neg hb]
        rw [htr]
        simp only [F]
        ring
    rw [hdecomp]
    exact norm_add_sq_le_two _ _

  have hgood_bound :
      (∑ a ∈ good, ‖∑ b : s, v b * A a b‖ ^ 2) ≤
        2 * Bl * (∑ b : s, ‖v b‖ ^ 2) +
        2 * Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2) := by
    rw [← Finset.sum_attach good (fun a => ‖∑ b : s, v b * A a b‖ ^ 2)]

    have hHpart : (∑ a ∈ good.attach, ‖∑ b : s, v' b * H (F a) b‖ ^ 2) ≤
        Bl * (∑ b : s, ‖v b‖ ^ 2) := by
      have ginj : Function.Injective
          (fun a : {a : r // a ∈ good} =>
            (⟨a.val, Finset.mem_filter.mp a.2⟩ : {a : r // a ∈ R₀ ∧ ¬badRow a})) := by
        intro x y h
        have hv : x.val = y.val :=
          congrArg (fun z : {a : r // a ∈ R₀ ∧ ¬badRow a} => z.val) h
        exact Subtype.ext hv
      have hinj : Function.Injective F := hf.comp ginj
      have h1 : (∑ a ∈ good.attach, ‖∑ b : s, v' b * H (F a) b‖ ^ 2) ≤
          ∑ x : t, ‖∑ b : s, v' b * H x b‖ ^ 2 :=
        sum_le_univ_of_injective good.attach F hinj
          (fun x => ‖∑ b : s, v' b * H x b‖ ^ 2) (fun x => sq_nonneg _)
      have h2 : (∑ x : t, ‖∑ b : s, v' b * H x b‖ ^ 2) ≤
          Bl * ∑ b : s, ‖v' b‖ ^ 2 := hH v'
      have h3 : (∑ b : s, ‖v' b‖ ^ 2) ≤ ∑ b : s, ‖v b‖ ^ 2 := by
        refine Finset.sum_le_sum fun b _ => ?_
        by_cases hb : badCol b
        · simp [v', hb]
        · simp only [v', if_neg hb]
          rw [norm_mul]
          have hc : ‖u b‖ ^ 2 ≤ 1 := by nlinarith [hu b, norm_nonneg (u b)]
          nlinarith [hc, sq_nonneg ‖v b‖]
      calc (∑ a ∈ good.attach, ‖∑ b : s, v' b * H (F a) b‖ ^ 2)
          ≤ ∑ x : t, ‖∑ b : s, v' b * H x b‖ ^ 2 := h1
        _ ≤ Bl * ∑ b : s, ‖v' b‖ ^ 2 := h2
        _ ≤ Bl * ∑ b : s, ‖v b‖ ^ 2 := mul_le_mul_of_nonneg_left h3 hBl

    have hApart : (∑ a ∈ good.attach, ‖∑ b : s, vbad b * A a b‖ ^ 2) ≤
        Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2) := by
      have h1 : (∑ a ∈ good.attach, ‖∑ b : s, vbad b * A a b‖ ^ 2) =
          ∑ a ∈ good, ‖∑ b : s, vbad b * A a b‖ ^ 2 :=
        Finset.sum_attach good (fun a => ‖∑ b : s, vbad b * A a b‖ ^ 2)
      have hvbad : (∑ b : s, ‖vbad b‖ ^ 2) =
          ∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2 := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hb : badCol b <;> simp [vbad, hb]
      rw [h1]
      calc (∑ a ∈ good, ‖∑ b : s, vbad b * A a b‖ ^ 2)
          ≤ ∑ a : r, ‖∑ b : s, vbad b * A a b‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ good)
              (fun a _ _ => sq_nonneg _)
        _ ≤ Bs * ∑ b : s, ‖vbad b‖ ^ 2 := hA vbad
        _ = Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2) := by rw [hvbad]
    calc (∑ a ∈ good.attach, ‖∑ b : s, v b * A a b‖ ^ 2)
        ≤ ∑ a ∈ good.attach, (2 * ‖∑ b : s, v' b * H (F a) b‖ ^ 2 +
            2 * ‖∑ b : s, vbad b * A a b‖ ^ 2) :=
          Finset.sum_le_sum fun a _ => hpoint a
      _ = 2 * (∑ a ∈ good.attach, ‖∑ b : s, v' b * H (F a) b‖ ^ 2) +
          2 * (∑ a ∈ good.attach, ‖∑ b : s, vbad b * A a b‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (Bl * (∑ b : s, ‖v b‖ ^ 2)) +
          2 * (Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2)) :=
          add_le_add (mul_le_mul_of_nonneg_left hHpart (by norm_num))
            (mul_le_mul_of_nonneg_left hApart (by norm_num))
      _ = 2 * Bl * (∑ b : s, ‖v b‖ ^ 2) +
          2 * Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2) := by ring

  have hbadbound : (∑ a ∈ R₀.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2) ≤
      ∑ a ∈ Finset.univ.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a _ _ => sq_nonneg _)
    intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ _, ha.2⟩

  have hsplit : (∑ a ∈ R₀, ‖∑ b : s, v b * A a b‖ ^ 2) =
      (∑ a ∈ R₀.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2) +
      (∑ a ∈ good, ‖∑ b : s, v b * A a b‖ ^ 2) := by
    have h := Finset.sum_filter_add_sum_filter_not R₀ badRow
      (fun a => ‖∑ b : s, v b * A a b‖ ^ 2)
    rw [← h]
  rw [hsplit]
  calc (∑ a ∈ R₀.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2) +
        (∑ a ∈ good, ‖∑ b : s, v b * A a b‖ ^ 2)
      ≤ (∑ a ∈ Finset.univ.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2) +
        (2 * Bl * (∑ b : s, ‖v b‖ ^ 2) +
          2 * Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2)) :=
        add_le_add hbadbound hgood_bound
    _ = (∑ a ∈ Finset.univ.filter badRow, ‖∑ b : s, v b * A a b‖ ^ 2) +
        2 * Bl * (∑ b : s, ‖v b‖ ^ 2) +
        2 * Bs * (∑ b ∈ Finset.univ.filter badCol, ‖v b‖ ^ 2) := by ring

end DedekindZetaZeroFree.LargeSieve.Vendor
