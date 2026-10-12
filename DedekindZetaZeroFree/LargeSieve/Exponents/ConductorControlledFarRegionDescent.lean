module

public import DedekindZetaZeroFree.LargeSieve.Exponents.ConductorControlledWeightedDescent
public import DedekindZetaZeroFree.LargeSieve.Exponents.FiniteScaleDescent
public import DedekindZetaZeroFree.LargeSieve.Exponents.RecursionParameterEstimates

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.LargeSieve.Sieve

private lemma rpow_add' {x : ℝ} (hx : 0 < x) (y z : ℝ) :
    Real.rpow x y * Real.rpow x z = Real.rpow x (y + z) :=
  (Real.rpow_add hx y z).symm

private lemma rpow_mul' {x : ℝ} (hx : 0 ≤ x) (y z : ℝ) :
    Real.rpow (Real.rpow x y) z = Real.rpow x (y * z) :=
  (Real.rpow_mul hx y z).symm

private lemma rpow_natCast' (x : ℝ) (n : ℕ) : x ^ n = Real.rpow x (n : ℝ) :=
  (Real.rpow_natCast x n).symm

private lemma rpow_le_rpow' {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    Real.rpow x z ≤ Real.rpow y z := Real.rpow_le_rpow hx hxy hz

private lemma rpow_le_rpow_exp' {x y z : ℝ} (hx : 1 ≤ x) (h : y ≤ z) :
    Real.rpow x y ≤ Real.rpow x z := Real.rpow_le_rpow_of_exponent_le hx h

private lemma one_le_rpow' {x z : ℝ} (hx : 1 ≤ x) (hz : 0 ≤ z) :
    1 ≤ Real.rpow x z := Real.one_le_rpow hx hz

private lemma rpow_nonneg' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ Real.rpow x y :=
  Real.rpow_nonneg hx y

private lemma rpow_mul_add (T δ α : ℝ) (hT : 0 < T) :
    Real.rpow T δ * Real.rpow T (δ * (α + 1)) = Real.rpow T (δ * (α + 2)) := by
  have h : Real.rpow T δ * Real.rpow T (δ * (α + 1)) = Real.rpow T (δ + δ * (α + 1)) :=
    rpow_add' hT δ (δ * (α + 1))
  rw [h]
  congr 1
  ring

private lemma far_iteration_absorb (α M N η : ℝ) (r : ℕ) (δ : ℝ)
    (hα : 1 ≤ α) (hM : 1 ≤ M) (hN : 1 ≤ N) (hη : 0 < η)
    (hr : 1 ≤ r) (hrη : 20 / η ≤ (r : ℝ))
    (hδ : δ = η / (8 * (r : ℝ) * (α + 1))) :
    (Real.rpow (M * N) (δ * (α + 2))) ^ r *
      Real.rpow (Real.rpow N (1 / (r : ℝ))) 5 ≤ Real.rpow (M * N) η := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hT1 : 1 ≤ M * N := by nlinarith
  have hT0 : 0 < M * N := by nlinarith
  have hH5 : Real.rpow (Real.rpow N (1 / (r : ℝ))) 5 ≤ Real.rpow (M * N) (η / 4) :=
    (recursion_parameter_basic α M N η r hα hM hN hη hr hrη).2.2
  have hα0 : 0 ≤ α := by linarith
  have hexp : δ * (α + 2) * (r : ℝ) ≤ η / 4 := by
    rw [hδ, show η / (8 * ↑r * (α + 1)) * (α + 2) * ↑r
          = η * (α + 2) * ↑r / (8 * ↑r * (α + 1)) by ring]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg (le_of_lt hη) hα0) (le_of_lt hr0)]
  have hL : (Real.rpow (M * N) (δ * (α + 2))) ^ r ≤ Real.rpow (M * N) (η / 4) := by
    rw [rpow_natCast' (Real.rpow (M * N) (δ * (α + 2))) r,
      rpow_mul' (le_of_lt hT0) (δ * (α + 2)) (r : ℝ)]
    exact rpow_le_rpow_exp' hT1 hexp
  calc (Real.rpow (M * N) (δ * (α + 2))) ^ r *
        Real.rpow (Real.rpow N (1 / (r : ℝ))) 5
      ≤ Real.rpow (M * N) (η / 4) * Real.rpow (M * N) (η / 4) :=
        mul_le_mul hL hH5 (rpow_nonneg' (rpow_nonneg' (le_of_lt hN0) _) 5)
          (rpow_nonneg' (le_of_lt hT0) _)
    _ = Real.rpow (M * N) (η / 4 + η / 4) := rpow_add' hT0 (η / 4) (η / 4)
    _ ≤ Real.rpow (M * N) η := rpow_le_rpow_exp' hT1 (by linarith)

private theorem far_core_aux
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (hGood : CoreGood Q)
    (W : ℝ → ℝ) (hW : SieveWeight W) (α : ℝ) (hα : 1 ≤ α) (hα₂ : α ≤ 2)
    (hExponent : HasSieveExponent F c Q α)
    (η : ℝ) (hη : 0 < η) (r : ℕ) (hr : r = max 1 (Nat.ceil (20 / η)))
    (δ : ℝ) (hδ : δ = η / (8 * (r : ℝ) * (α + 1))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        2 * N * (M * N) ^ δ ≤ M →
        B1 F c Q M N ≤
          C * (M * N) ^ η * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) ∧
        B2 F c Q W M N (N ^ 2 / M * (M * N) ^ δ) ≤
          C * (M * N) ^ η * (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  have hr1 : 1 ≤ r := by rw [hr]; exact le_max_left _ _
  have hrη : 20 / η ≤ (r : ℝ) := by
    rw [hr]
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right 1 (Nat.ceil (20 / η)))
  have hδpos : 0 < δ := by rw [hδ]; positivity
  obtain ⟨A, hA1, hA⟩ :=
    oneStepWeightedDescent_core F hF c hc Q hGood W hW α hα hα₂ hExponent δ hδpos
  obtain ⟨C0, hC01, htriv⟩ := B2_trivial_bound F W hW
  refine ⟨A ^ r * (C0 + (r : ℝ) * 2), ?_, ?_⟩
  · have hA0 : 0 ≤ A := le_trans zero_le_one hA1
    exact mul_nonneg (pow_nonneg hA0 r)
      (add_nonneg (le_trans zero_le_one hC01) (by positivity))
  · intro M N hM hN hfar
    change B1 F c Q M N ≤
        A ^ r * (C0 + (r : ℝ) * 2) * Real.rpow (M * N) η *
          (M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α)) ∧
      B2 F c Q W M N (N ^ 2 / M * Real.rpow (M * N) δ) ≤
        A ^ r * (C0 + (r : ℝ) * 2) * Real.rpow (M * N) η *
          (M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α))
    set H : ℝ := Real.rpow N (1 / (r : ℝ)) with hH
    set K : ℝ := N ^ 2 / M * Real.rpow (M * N) δ with hK
    set R : ℝ := M + N + Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) with hR
    have hM0 : 0 < M := by linarith
    have hN0 : 0 < N := by linarith
    have hT1 : 1 ≤ M * N := by nlinarith
    have hT0 : 0 < M * N := by nlinarith
    have hA0 : 0 ≤ A := le_trans zero_le_one hA1
    have hRnn : 0 ≤ R := by
      rw [hR]
      have h1 : 0 ≤ Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) :=
        mul_nonneg (rpow_nonneg' (le_of_lt hN0) _) (rpow_nonneg' (le_of_lt hM0) _)
      linarith
    have hMR : M ≤ R := by
      rw [hR]
      have h1 : 0 ≤ Real.rpow N (2 * α - 1) * Real.rpow M (1 - α) :=
        mul_nonneg (rpow_nonneg' (le_of_lt hN0) _) (rpow_nonneg' (le_of_lt hM0) _)
      linarith
    obtain ⟨-, hH1raw, hH5raw⟩ := recursion_parameter_basic α M N η r hα hM hN hη hr1 hrη
    have hH1 : 1 ≤ H := by rw [hH]; exact hH1raw
    have hH5 : Real.rpow H 5 ≤ Real.rpow (M * N) (η / 4) := by rw [hH]; exact hH5raw
    have hHnn : 0 ≤ H := le_trans zero_le_one hH1
    have hfar2 : 2 * N * Real.rpow (M * N) (η / (8 * (r : ℝ) * (α + 1))) ≤ M := by
      rw [hδ] at hfar
      exact hfar
    obtain ⟨hKpos0, hKM20, hparam0⟩ :=
      recursion_parameter_far α M N η r hα hM hN hη hr1 hrη hfar2
    rw [← hδ, ← hK] at hKpos0 hKM20
    rw [← hδ, ← hK, ← hR] at hparam0
    have hKpos : 0 < K := hKpos0
    have hKM2 : K < M / 2 := hKM20
    set L : ℝ := A * Real.rpow (M * N) (δ * (α + 2)) with hL
    have hL1 : 1 ≤ L := by
      rw [hL]
      exact one_le_mul_of_one_le_of_one_le hA1
        (one_le_rpow' hT1 (mul_nonneg (le_of_lt hδpos) (by linarith)))
    have hsmall : ∀ n : ℝ, 1 ≤ n → n ≤ H → B2 F c Q W M n K ≤ C0 * R * H := by
      intro n hn1 hnH
      have h1 : B2 F c Q W M n K ≤ C0 * M * n := htriv c Q M n K hM hn1 hKpos
      have h2 : C0 * M * n ≤ C0 * M * H :=
        mul_le_mul_of_nonneg_left hnH (mul_nonneg (le_trans zero_le_one hC01) (le_of_lt hM0))
      have h3 : C0 * M * H ≤ C0 * R * H :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR (le_trans zero_le_one hC01)) hHnn
      exact h1.trans (h2.trans h3)
    have hstep : ∀ n : ℝ, H < n → n ≤ N →
        ∃ n' : ℝ, 1 ≤ n' ∧ n' ≤ n / H ∧
          B2 F c Q W M n K ≤ L * B2 F c Q W M n' K + L * 2 * Real.rpow H 5 * R := by
      intro n hnH hnN
      have hn1 : 1 ≤ n := by linarith
      obtain ⟨n', hn'1, hn'le, hb⟩ :=
        hA M n H K hM hn1 hH1 hnH hKpos hKM2
          (hparam0 n hn1 hnN).1 (hparam0 n hn1 hnN).2.1
      rw [rpow_natCast' H 5] at hb
      refine ⟨n', hn'1, hn'le, ?_⟩
      have hbr : M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * n ≤
          2 * Real.rpow (M * N) (δ * (α + 1)) * R := (hparam0 n hn1 hnN).2.2
      have hbrnn : 0 ≤ M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) +
          Real.sqrt (M / K) * n := by
        have h1 : 0 ≤ M := le_of_lt hM0
        have h2 : 0 ≤ n := by linarith
        have h3 : 0 ≤ Real.sqrt M * Real.rpow K (α - 1 / 2) :=
          mul_nonneg (Real.sqrt_nonneg M) (rpow_nonneg' (le_of_lt hKpos) _)
        have h4 : 0 ≤ Real.sqrt (M / K) * n := mul_nonneg (Real.sqrt_nonneg _) h2
        linarith
      have hB2nn : 0 ≤ B2 F c Q W M n' K := B2_nonneg Q W M n' K
      have hH5nn : 0 ≤ Real.rpow H 5 := rpow_nonneg' hHnn 5
      have hrp1 : Real.rpow (M * n) δ ≤ Real.rpow (M * N) δ :=
        rpow_le_rpow' (mul_nonneg (le_of_lt hM0) (by linarith)) (by nlinarith)
          (le_of_lt hδpos)
      have t1 : A * Real.rpow (M * n) δ * B2 F c Q W M n' K ≤ L * B2 F c Q W M n' K := by
        rw [hL]
        apply mul_le_mul_of_nonneg_right _ hB2nn
        apply mul_le_mul_of_nonneg_left _ hA0
        exact hrp1.trans (rpow_le_rpow_exp' hT1 (by nlinarith [hδpos, hα]))
      have t2 : A * Real.rpow H 5 * Real.rpow (M * n) δ *
            (M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * n) ≤
          L * 2 * Real.rpow H 5 * R := by
        have hstep1 : A * Real.rpow H 5 * Real.rpow (M * n) δ ≤
            A * Real.rpow H 5 * Real.rpow (M * N) δ :=
          mul_le_mul_of_nonneg_left hrp1 (mul_nonneg hA0 hH5nn)
        have hstep2 : A * Real.rpow H 5 * Real.rpow (M * n) δ *
              (M + n + Real.sqrt M * Real.rpow K (α - 1 / 2) + Real.sqrt (M / K) * n) ≤
            A * Real.rpow H 5 * Real.rpow (M * N) δ *
              (2 * Real.rpow (M * N) (δ * (α + 1)) * R) :=
          mul_le_mul hstep1 hbr hbrnn
            (mul_nonneg (mul_nonneg hA0 hH5nn) (rpow_nonneg' (le_of_lt hT0) _))
        refine hstep2.trans ?_
        rw [hL]
        have hrpadd := rpow_mul_add (M * N) δ α hT0
        have heq : A * Real.rpow H 5 * Real.rpow (M * N) δ *
              (2 * Real.rpow (M * N) (δ * (α + 1)) * R)
            = A * Real.rpow (M * N) (δ * (α + 2)) * 2 * Real.rpow H 5 * R := by
          calc A * Real.rpow H 5 * Real.rpow (M * N) δ *
                (2 * Real.rpow (M * N) (δ * (α + 1)) * R)
              = A * Real.rpow H 5 *
                  (Real.rpow (M * N) δ * (2 * Real.rpow (M * N) (δ * (α + 1)) * R)) := by ring
            _ = A * Real.rpow H 5 *
                  (2 * (Real.rpow (M * N) δ * Real.rpow (M * N) (δ * (α + 1))) * R) := by ring
            _ = A * Real.rpow H 5 * (2 * Real.rpow (M * N) (δ * (α + 2)) * R) := by rw [hrpadd]
            _ = A * Real.rpow (M * N) (δ * (α + 2)) * 2 * Real.rpow H 5 * R := by ring
        exact heq.le
      exact hb.trans (add_le_add t1 t2)
    have hdesc : B2 F c Q W M N K ≤
        L ^ r * (C0 + (r : ℝ) * 2) * Real.rpow H 5 * R := by
      have hfd := DedekindZetaZeroFree.LargeSieve.Vendor.finiteDescent (fun n => B2 F c Q W M n K) N r L 2 R C0
        hN hr1 hL1 (by norm_num) hRnn (le_trans zero_le_one hC01)
        (fun n _ _ => B2_nonneg Q W M n K) hsmall hstep
      exact hfd
    have habs : L ^ r * Real.rpow H 5 ≤ A ^ r * Real.rpow (M * N) η := by
      have h1 : L ^ r * Real.rpow H 5 =
          A ^ r * ((Real.rpow (M * N) (δ * (α + 2))) ^ r * Real.rpow H 5) := by
        rw [hL, mul_pow]; ring
      rw [h1]
      exact mul_le_mul_of_nonneg_left
        (far_iteration_absorb α M N η r δ hα hM hN hη hr1 hrη hδ) (pow_nonneg hA0 r)
    have hfinal : B2 F c Q W M N K ≤
        A ^ r * (C0 + (r : ℝ) * 2) * Real.rpow (M * N) η * R := by
      have hcoefnn : 0 ≤ C0 + (r : ℝ) * 2 :=
        add_nonneg (le_trans zero_le_one hC01) (by positivity)
      calc B2 F c Q W M N K
          ≤ L ^ r * (C0 + (r : ℝ) * 2) * Real.rpow H 5 * R := hdesc
        _ = (L ^ r * Real.rpow H 5) * (C0 + (r : ℝ) * 2) * R := by ring
        _ ≤ (A ^ r * Real.rpow (M * N) η) * (C0 + (r : ℝ) * 2) * R :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right habs hcoefnn) hRnn
        _ = A ^ r * (C0 + (r : ℝ) * 2) * Real.rpow (M * N) η * R := by ring
    refine ⟨?_, ?_⟩
    · calc B1 F c Q M N ≤ B2 F c Q W M N K :=
          B1_le_B2 Q W hW M N K hM hN hKpos (by linarith)
        _ ≤ A ^ r * (C0 + (r : ℝ) * 2) * Real.rpow (M * N) η * R := hfinal
    · exact hfinal

theorem recursion_far_region_core
    (F : Type) [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c) (hGood : CoreGood Q)
    (W : ℝ → ℝ) (hW : SieveWeight W) (α : ℝ) (hα : 1 ≤ α)
    (hα₂ : α ≤ 2) (hExponent : HasSieveExponent F c Q α)
     :
    ∀ η : ℝ, 0 < η →
      let r : ℕ := max 1 (Nat.ceil (20 / η))
      let δ : ℝ := η / (8 * (r : ℝ) * (α + 1))
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
          2 * N * (M * N) ^ δ ≤ M →
          B1 F c Q M N ≤
            C * (M * N) ^ η *
              (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) ∧
          B2 F c Q W M N (N ^ 2 / M * (M * N) ^ δ) ≤
            C * (M * N) ^ η *
              (M + N + N ^ (2 * α - 1) * M ^ (1 - α)) := by
  intro η hη
  exact far_core_aux F hF c hc Q hGood W hW α hα hα₂ hExponent η hη
    (max 1 (Nat.ceil (20 / η))) rfl
    (η / (8 * (((max 1 (Nat.ceil (20 / η)) : ℕ)) : ℝ) * (α + 1))) rfl

end DedekindZetaZeroFree.LargeSieve.Sieve

end
