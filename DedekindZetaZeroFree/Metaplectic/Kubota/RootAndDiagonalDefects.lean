module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AlternatingSymbolDefect
public import DedekindZetaZeroFree.Metaplectic.Kubota.GL2BruhatCoordinates

@[expose] public section

namespace DedekindZetaZeroFree
namespace KubotaElementaryLastArgument

open KubotaRankTwo

noncomputable def tau
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M) (g h : KubotaRankTwo.GL2 K) : M :=
  B (KubotaRankTwo.X K (g * h) / KubotaRankTwo.X K g)
    (KubotaRankTwo.X K (g * h) /
      (KubotaRankTwo.X K h * KubotaRankTwo.det K g))

noncomputable def defect
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M) (g h k : KubotaRankTwo.GL2 K) : M :=
  tau K M B g h * tau K M B (g * h) k /
    (tau K M B h k * tau K M B g (h * k))

private lemma x_botLeft (K : Type*) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    x K g = (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  unfold x; rw [if_neg hc]

private lemma x_botRight (K : Type*) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    x K g = (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  unfold x; rw [if_pos hc]

private lemma entry_botLeft (K : Type*) [Field K] (g : GL2 K) (u v : Kˣ) :
    ((g * d K u v : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * (u : K) := by
  simp [coe_d, Matrix.mul_apply, Fin.sum_univ_two]

private lemma entry_botRight (K : Type*) [Field K] (g : GL2 K) (u v : Kˣ) :
    ((g * d K u v : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 * (v : K) := by
  simp [coe_d, Matrix.mul_apply, Fin.sum_univ_two]

private lemma entry10_mul (K : Type*) [Field K] (g h : GL2 K) :
    ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * (h : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 * (h : Matrix (Fin 2) (Fin 2) K) 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma entry11_mul (K : Type*) [Field K] (g h : GL2 K) :
    ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * (h : Matrix (Fin 2) (Fin 2) K) 0 1 +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 * (h : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

private lemma X_mul_d_closed (K : Type*) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (u v : Kˣ) :
    X K (g * d K u v) = X K g * v := by
  have hc' : ((g * d K u v : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [entry_botLeft, hc, zero_mul]
  apply Units.ext
  simp only [Units.val_mul, X, Units.val_mk0, x_botRight K _ hc', x_botRight K g hc,
    entry_botRight]

private lemma X_mul_d_open (K : Type*) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) (u v : Kˣ) :
    X K (g * d K u v) = X K g * u := by
  have hc' : ((g * d K u v : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    rw [entry_botLeft]; exact mul_ne_zero hc u.ne_zero
  apply Units.ext
  simp only [Units.val_mul, X, Units.val_mk0, x_botLeft K _ hc', x_botLeft K g hc,
    entry_botLeft]

private lemma key_open_closed (K : Type*) [Field K] (g h : GL2 K)
    (hc1 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (hc2 : ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    X K (g * h) * X K h = X K g * det K h := by
  have hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    intro h0
    exact hc2 (by rw [entry10_mul, hc1, h0]; ring)
  apply Units.ext
  simp only [Units.val_mul, X, Units.val_mk0, x_botLeft K (g * h) hc2,
    x_botRight K h hc1, x_botLeft K g hg, entry10_mul, hc1,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  ring

private lemma key_closed_open (K : Type*) [Field K] (g h : GL2 K)
    (hc1 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (hc2 : ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    X K (g * h) * X K h = -(X K g * det K h) := by
  have hg : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := by
    intro h0
    have hgh : (g : Matrix (Fin 2) (Fin 2) K) 1 1 *
        (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
      have h2 : ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hc2
      rw [entry10_mul, h0, zero_mul, zero_add] at h2
      exact h2
    have hg11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
      intro h1
      have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
      rw [Matrix.det_fin_two, h0, h1] at hdet
      simp at hdet
    exact (mul_ne_zero hg11 hc1) hgh
  have hrel : (g : Matrix (Fin 2) (Fin 2) K) 1 0 *
        (h : Matrix (Fin 2) (Fin 2) K) 0 0 +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 *
        (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
    rw [← entry10_mul]; exact hc2
  apply Units.ext
  simp only [Units.val_mul, Units.val_neg, X, Units.val_mk0,
    x_botRight K (g * h) hc2, x_botLeft K h hc1, x_botLeft K g hg,
    entry11_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  linear_combination ((h : Matrix (Fin 2) (Fin 2) K) 1 1) * hrel

private lemma neg_mul_div (K : Type*) [Field K] (A d u v : Kˣ) :
    (-(A * d)) * u / (A * v * d) = -(u / v) := by
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg]
  field_simp

private lemma div_inv_eq (K : Type*) [Field K] (u v : Kˣ) : v / u = (u / v)⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, inv_inv]

private lemma cancel_div (K : Type*) [Field K] (a b c : Kˣ) : a * b / (a * c) = b / c := by
  apply Units.ext
  simp only [Units.val_div_eq_div_val, Units.val_mul]
  field_simp

private lemma B_inv_neg (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B a⁻¹ (-a) = 1 := by
  rw [KubotaDefectSymbolAlgebra.inv_left K M B hL a (-a),
    KubotaDefectSymbolAlgebra.neg_self K M B hR hAlt hCub a]
  simp

private theorem defect_eq_factor
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (g h k : GL2 K) :
    defect K M B g h k =
      B (X K (g * h * k) * X K h / (X K (g * h) * X K (h * k)))
        (X K (g * h) * X K (h * k) / (X K g * X K k * det K h)) := by
  have hfac := kp_kubota_defect_symbol_algebra K M B hL hR hAlt
    (X K g) (X K h) (X K (h * k)) (X K (g * h)) (X K (g * h * k)) (X K k) (det K g) (det K h)
  rw [← hfac]
  unfold defect tau
  simp only [map_mul, mul_assoc]

theorem defect_n
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (g h : KubotaRankTwo.GL2 K) (t : K) :
    defect K M B g h (KubotaRankTwo.n K t) = 1 := by
  rw [defect_eq_factor K M B hL hR hAlt hCub g h (KubotaRankTwo.n K t)]
  simp only [X_n_mul, X_mul_n, X_n]
  rw [show X K (g * h) * X K h / (X K (g * h) * X K h) = 1 by
        rw [div_eq_mul_inv]; exact mul_inv_cancel _]
  exact KubotaDefectSymbolAlgebra.one_left K M B hL _

theorem defect_d
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (g h : KubotaRankTwo.GL2 K) (u v : Kˣ) :
    defect K M B g h (KubotaRankTwo.d K u v) = 1 := by
  rw [defect_eq_factor K M B hL hR hAlt hCub g h (KubotaRankTwo.d K u v), X_d]
  by_cases hc1 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [X_mul_d_closed K h hc1]
    by_cases hc2 : ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · rw [X_mul_d_closed K (g * h) hc2]
      rw [show X K (g * h) * v * X K h / (X K (g * h) * (X K h * v)) = 1 by
            rw [show X K (g * h) * v * X K h = X K (g * h) * (X K h * v) by
                  rw [mul_assoc, mul_comm v (X K h)]]
            exact div_self' _]
      exact KubotaDefectSymbolAlgebra.one_left K M B hL _
    · rw [X_mul_d_open K (g * h) hc2]
      rw [show X K (g * h) * (X K h * v) / (X K g * v * det K h) = 1 by
            rw [show X K (g * h) * (X K h * v) = (X K (g * h) * X K h) * v by
                  rw [mul_assoc],
                key_open_closed K g h hc1 hc2,
                show (X K g * det K h) * v = X K g * v * det K h by
                  rw [mul_assoc, mul_comm (det K h) v, ← mul_assoc]]
            exact div_self' _]
      rw [show X K (g * h) * u * X K h / (X K (g * h) * (X K h * v)) = u / v by
            rw [show X K (g * h) * u * X K h = (X K (g * h) * X K h) * u by
                  rw [mul_assoc, mul_comm u (X K h), ← mul_assoc],
                show X K (g * h) * (X K h * v) = (X K (g * h) * X K h) * v by
                  rw [mul_assoc],
                cancel_div K (X K (g * h) * X K h) u v]]
      exact KubotaDefectSymbolAlgebra.one_right K M B hR _
  · rw [X_mul_d_open K h hc1]
    by_cases hc2 : ((g * h : GL2 K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    · rw [X_mul_d_closed K (g * h) hc2]
      have h2 : X K (g * h) * (X K h * u) / (X K g * v * det K h) = -(u / v) := by
        rw [show X K (g * h) * (X K h * u) = (X K (g * h) * X K h) * u by
              rw [mul_assoc],
            key_closed_open K g h hc1 hc2,
            neg_mul_div K (X K g) (det K h) u v]
      have h1 : X K (g * h) * v * X K h / (X K (g * h) * (X K h * u)) = (u / v)⁻¹ := by
        rw [show X K (g * h) * v * X K h = (X K (g * h) * X K h) * v by
              rw [mul_assoc, mul_comm v (X K h), ← mul_assoc],
            show X K (g * h) * (X K h * u) = (X K (g * h) * X K h) * u by
              rw [mul_assoc],
            cancel_div K (X K (g * h) * X K h) v u,
            div_inv_eq K u v]
      rw [h1, h2]
      exact B_inv_neg K M B hL hR hAlt hCub (u / v)
    · rw [X_mul_d_open K (g * h) hc2]
      rw [show X K (g * h) * u * X K h / (X K (g * h) * (X K h * u)) = 1 by
            rw [show X K (g * h) * u * X K h = X K (g * h) * (X K h * u) by
                  rw [mul_assoc, mul_comm u (X K h)]]
            exact div_self' _]
      exact KubotaDefectSymbolAlgebra.one_left K M B hL _

theorem tau_one_right
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (g : KubotaRankTwo.GL2 K) : tau K M B g 1 = 1 := by
  unfold tau
  simp only [mul_one, X_one, one_mul]
  rw [show X K g / X K g = 1 by rw [div_eq_mul_inv]; exact mul_inv_cancel _]
  exact KubotaDefectSymbolAlgebra.one_left K M B hL _

theorem tau_n_mul_mul_n
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M) (g h : KubotaRankTwo.GL2 K) (t t' : K) :
    tau K M B (KubotaRankTwo.n K t * g) (h * KubotaRankTwo.n K t') =
      tau K M B g h := by
  unfold tau
  rw [← mul_assoc (n K t * g) h (n K t')]
  rw [X_n_mul_mul_n, X_n_mul, X_mul_n]
  simp only [map_mul, det_n, one_mul]

end KubotaElementaryLastArgument
end DedekindZetaZeroFree
