module

public import Mathlib

@[expose] public section

namespace DedekindZetaZeroFree

noncomputable section
open scoped BigOperators Classical

private theorem detector_sz_radius_bound (R : Finset ℝ) (a : ℝ → ℂ) (M c : ℝ) (w : ℝ → ℝ)
    (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hpos : ∀ x ∈ R, 0 ≤ w x)
    (hupper : ∀ x ∈ R, w x ≤ c)
    (hanti : ∀ x ∈ R, ∀ y ∈ R, x ≤ y → w y ≤ w x)
    (hp : ∀ y ∈ R, ‖∑ x ∈ R.filter (fun x => x ≤ y), a x‖ ≤ M) :
    ‖∑ x ∈ R, a x * (w x : ℂ)‖ ≤ M * c := by
  induction R using Finset.induction_on_max generalizing w c with
  | empty => simpa using mul_nonneg hM hc
  | insert z R hz ih =>
    have hznot : z ∉ R := by intro h; exact (lt_irrefl z) (hz z h)
    have hwz : 0 ≤ w z := hpos z (Finset.mem_insert_self _ _)
    have hwzc : w z ≤ c := hupper z (Finset.mem_insert_self _ _)
    have hvpos : ∀ x ∈ R, 0 ≤ w x - w z := by
      intro x hx
      exact sub_nonneg.mpr (hanti x (Finset.mem_insert_of_mem hx) z (Finset.mem_insert_self _ _) (hz x hx).le)
    have hremain := ih (c - w z) (fun x => w x - w z) (sub_nonneg.mpr hwzc) hvpos
      (by intro x hx; exact sub_le_sub_right (hupper x (Finset.mem_insert_of_mem hx)) _)
      (by intro x hx y hy hxy; exact sub_le_sub_right (hanti x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy) _)
      (by
        intro y hy
        have hn : ¬z ≤ y := not_le.mpr (hz y hy)
        simpa [Finset.filter_insert, hn] using hp y (Finset.mem_insert_of_mem hy))
    have htotal : ‖∑ x ∈ insert z R, a x‖ ≤ M := by
      have hf : (insert z R).filter (fun x => x ≤ z) = insert z R := by
        apply Finset.filter_true_of_mem
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact le_rfl
        · exact (hz x hx).le
      simpa [hf] using hp z (Finset.mem_insert_self _ _)
    have hid : (∑ x ∈ insert z R, a x * (w x : ℂ)) =
        (∑ x ∈ R, a x * ((w x - w z : ℝ) : ℂ)) + (∑ x ∈ insert z R, a x) * (w z : ℂ) := by
      simp only [Finset.sum_insert hznot, Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      ring
    rw [hid]
    calc
      _ ≤ ‖∑ x ∈ R, a x * ((w x - w z : ℝ) : ℂ)‖ + ‖(∑ x ∈ insert z R, a x) * (w z : ℂ)‖ := norm_add_le _ _
      _ ≤ M * (c - w z) + M * w z := by
        apply add_le_add hremain
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwz]
        exact mul_le_mul_of_nonneg_right htotal hwz
      _ = M * c := by ring

theorem detector_sz_antitone_prefix {ι : Type*} (S : Finset ι)
    (r : ι → ℝ) (a : ι → ℂ) (N T M : ℝ) (w : ℝ → ℝ)
    (hN : 1 ≤ N) (hNT : N ≤ T)
    (hr : ∀ i ∈ S, N < r i ∧ r i ≤ T)
    (hw_nonneg : ∀ t ∈ Set.Icc N T, 0 ≤ w t)
    (hw_antitone : AntitoneOn w (Set.Icc N T)) (hwN : w N ≤ 1)
    (hM : 0 ≤ M)
    (hprefix : ∀ y ∈ Set.Icc N T,
      ‖∑ i ∈ S.filter (fun i => r i ≤ y), a i‖ ≤ M) :
    ‖∑ i ∈ S, a i * (w (r i) : ℂ)‖ ≤ M := by
  let R := S.image r
  let b : ℝ → ℂ := fun x => ∑ i ∈ S.filter (fun i => r i = x), a i
  have hR : ∀ x ∈ R, x ∈ Set.Icc N T := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨(hr i hi).1.le, (hr i hi).2⟩
  have hcut : ∀ y : ℝ,
      (∑ x ∈ R.filter (fun x => x ≤ y), b x) =
        ∑ i ∈ S.filter (fun i => r i ≤ y), a i := by
    intro y
    rw [Finset.sum_fiberwise_eq_sum_filter S (R.filter (fun x => x ≤ y)) r a]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, _, hiy⟩
      exact ⟨hi, hiy⟩
    · rintro ⟨hi, hiy⟩
      exact ⟨hi, Finset.mem_image_of_mem r hi, hiy⟩
  have hsum : (∑ x ∈ R, b x * (w x : ℂ)) =
      ∑ i ∈ S, a i * (w (r i) : ℂ) := by
    apply Finset.sum_image'
    intro i hi
    dsimp [b]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(Finset.mem_filter.mp hj).2]
  rw [← hsum]
  simpa using detector_sz_radius_bound R b M 1 w hM zero_le_one
    (fun x hx => hw_nonneg x (hR x hx))
    (fun x hx => (hw_antitone ⟨le_rfl, hNT⟩ (hR x hx) (hR x hx).1).trans hwN)
    (fun x hx y hy hxy => hw_antitone (hR x hx) (hR y hy) hxy)
    (fun y hy => by rw [hcut]; exact hprefix y (hR y hy))

def detector_sz_normWeight (U β t : ℝ) : ℝ :=
  Real.rpow t (249 / 250 - β) * Real.exp (-t / U ^ 10)

theorem detector_sz_normWeight_properties (U β N T : ℝ)
    (hU : 2 ≤ U) (hβ : 249 / 250 ≤ β) (hN : 1 ≤ N) (hNT : N ≤ T) :
    (∀ t ∈ Set.Icc N T, 0 ≤ detector_sz_normWeight U β t) ∧
      AntitoneOn (detector_sz_normWeight U β) (Set.Icc N T) ∧
      detector_sz_normWeight U β N ≤ 1 := by
  have hpow : 0 < U ^ 10 := pow_pos (by linarith) _
  have hexp : ∀ t : ℝ, 0 ≤ t → Real.exp (-t / U ^ 10) ≤ 1 := by
    intro t ht
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) hpow.le
  have hp : 249 / 250 - β ≤ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact mul_nonneg (Real.rpow_nonneg (by linarith [ht.1]) _) (Real.exp_pos _).le
  · intro x hx y hy hxy
    have hxpos : 0 < x := by linarith [hx.1]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_nonpos hxpos hxy hp)
      (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hxy) hpow.le))
      (Real.exp_pos _).le (Real.rpow_nonneg hxpos.le _)
  · exact mul_le_one₀ (Real.rpow_le_one_of_one_le_of_nonpos hN hp)
      (Real.exp_pos _).le (hexp N (by linarith))

theorem detector_sz_normWeight_prefix_bound {ι : Type*} (S : Finset ι)
    (r : ι → ℝ) (a : ι → ℂ) (U β N T M : ℝ)
    (hU : 2 ≤ U) (hβ : 249 / 250 ≤ β) (hN : 1 ≤ N) (hNT : N ≤ T)
    (hr : ∀ i ∈ S, N < r i ∧ r i ≤ T) (hM : 0 ≤ M)
    (hprefix : ∀ y ∈ Set.Icc N T,
      ‖∑ i ∈ S.filter (fun i => r i ≤ y), a i‖ ≤ M) :
    ‖∑ i ∈ S, a i * (detector_sz_normWeight U β (r i) : ℂ)‖ ≤ M := by
  obtain ⟨hnonneg, hanti, hleft⟩ :=
    detector_sz_normWeight_properties U β N T hU hβ hN hNT
  exact detector_sz_antitone_prefix S r a N T M (detector_sz_normWeight U β)
    hN hNT hr hnonneg hanti hleft hM hprefix

end
end DedekindZetaZeroFree
