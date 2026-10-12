module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.Abel

@[expose] public section

namespace DedekindZetaZeroFree

namespace KubotaDefectSymbolAlgebra

theorem one_left
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (a : Kˣ) : B 1 a = 1 := by
  have h := hL 1 1 a
  rw [one_mul] at h
  have h2 : B 1 a * 1 = B 1 a * B 1 a := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

theorem one_right
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a : Kˣ) : B a 1 = 1 := by
  have h := hR a 1 1
  rw [mul_one] at h
  have h2 : B a 1 * 1 = B a 1 * B a 1 := by rw [mul_one]; exact h
  exact (mul_left_cancel h2).symm

theorem inv_left
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (a b : Kˣ) : B a⁻¹ b = (B a b)⁻¹ := by
  have h1 : B 1 b = 1 := one_left K M B hL b
  have h := hL a a⁻¹ b
  rw [mul_inv_cancel, h1] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem inv_right
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a b : Kˣ) : B a b⁻¹ = (B a b)⁻¹ := by
  have h1 : B a 1 = 1 := one_right K M B hR a
  have h := hR a b b⁻¹
  rw [mul_inv_cancel, h1] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem inv_inv
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a b : Kˣ) : B a⁻¹ b⁻¹ = B a b := by
  have h1 : B a⁻¹ b⁻¹ = (B a b⁻¹)⁻¹ := inv_left K M B hL a b⁻¹
  have h2 : B a b⁻¹ = (B a b)⁻¹ := inv_right K M B hR a b
  rw [h1, h2]
  simp

theorem div_left
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (a b c : Kˣ) : B (a / b) c = B a c / B b c := by
  rw [div_eq_mul_inv, hL a b⁻¹ c, inv_left K M B hL b c, div_eq_mul_inv]

theorem div_right
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (a b c : Kˣ) : B a (b / c) = B a b / B a c := by
  rw [div_eq_mul_inv, hR a b c⁻¹, inv_right K M B hR a c, div_eq_mul_inv]

theorem skew_symmetry
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (a b : Kˣ) : B a b = (B b a)⁻¹ := by
  have h := hL a b (a * b)
  rw [hAlt (a * b), hR a a b, hR b a b, hAlt a, hAlt b] at h
  simp only [one_mul, mul_one] at h
  exact (eq_inv_of_mul_eq_one_left h.symm)

theorem neg_one_right
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B a (-1) = 1 := by
  have h2 : (B a (-1)) ^ 2 = 1 := by
    rw [pow_two, ← hR a (-1) (-1), show (-1 : Kˣ) * (-1) = 1 by simp]
    exact one_right K M B hR a
  have h3 : (B a (-1)) ^ 3 = 1 := hCub a (-1)
  rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ] at h3
  rw [h2, one_mul] at h3
  exact h3

theorem neg_one_left
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B (-1) a = 1 := by
  have h2 : (B (-1) a) ^ 2 = 1 := by
    rw [pow_two, ← hL (-1) (-1) a, show (-1 : Kˣ) * (-1) = 1 by simp]
    exact one_left K M B hL a
  have h3 : (B (-1) a) ^ 3 = 1 := hCub (-1) a
  rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ] at h3
  rw [h2, one_mul] at h3
  exact h3

theorem neg_self
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (a : Kˣ) : B a (-a) = 1 := by
  rw [show -a = a * (-1) by simp, hR a a (-1), hAlt a,
    neg_one_right K M B hR hCub a, one_mul]

end KubotaDefectSymbolAlgebra

theorem kp_kubota_defect_symbol_algebra
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (r x y z t v p q : Kˣ) :
    B (z / r) (z / (x * p)) * B (t / z) (t / (v * p * q)) /
        (B (y / x) (y / (v * q)) * B (t / r) (t / (y * p))) =
      B (t * x / (z * y)) (z * y / (r * v * q)) := by
  have s_rx : B x r = (B r x)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt x r
  have s_ry : B y r = (B r y)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt y r
  have s_rz : B z r = (B r z)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt z r
  have s_rt : B t r = (B r t)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt t r
  have s_rv : B v r = (B r v)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt v r
  have s_rp : B p r = (B r p)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt p r
  have s_rq : B q r = (B r q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q r
  have s_xy : B y x = (B x y)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt y x
  have s_xz : B z x = (B x z)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt z x
  have s_xt : B t x = (B x t)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt t x
  have s_xv : B v x = (B x v)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt v x
  have s_xp : B p x = (B x p)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt p x
  have s_xq : B q x = (B x q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q x
  have s_yz : B z y = (B y z)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt z y
  have s_yt : B t y = (B y t)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt t y
  have s_yv : B v y = (B y v)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt v y
  have s_yp : B p y = (B y p)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt p y
  have s_yq : B q y = (B y q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q y
  have s_zt : B t z = (B z t)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt t z
  have s_zv : B v z = (B z v)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt v z
  have s_zp : B p z = (B z p)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt p z
  have s_zq : B q z = (B z q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q z
  have s_tv : B v t = (B t v)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt v t
  have s_tp : B p t = (B t p)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt p t
  have s_tq : B q t = (B t q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q t
  have s_vp : B p v = (B v p)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt p v
  have s_vq : B q v = (B v q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q v
  have s_pq : B q p = (B p q)⁻¹ := KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt q p
  simp only [
    div_eq_mul_inv, hL, hR,
    KubotaDefectSymbolAlgebra.one_left K M B hL, KubotaDefectSymbolAlgebra.one_right K M B hR,
    KubotaDefectSymbolAlgebra.inv_left K M B hL, KubotaDefectSymbolAlgebra.inv_right K M B hR, hAlt,
    s_rx, s_ry, s_rz, s_rt, s_rv, s_rp, s_rq, s_xy, s_xz, s_xt, s_xv, s_xp, s_xq, s_yz, s_yt, s_yv, s_yp, s_yq, s_zt, s_zv, s_zp, s_zq, s_tv, s_tp, s_tq, s_vp, s_vq, s_pq]
  apply Additive.ofMul.injective
  have omul : ∀ p q : M, Additive.ofMul (p * q) = Additive.ofMul p + Additive.ofMul q :=
    fun p q => rfl
  have oinv : ∀ p : M, Additive.ofMul p⁻¹ = - Additive.ofMul p := fun p => rfl
  have oone : Additive.ofMul (1 : M) = 0 := rfl
  simp only [div_eq_mul_inv, omul, oinv, oone, one_mul, mul_one, inv_one]
  abel

end DedekindZetaZeroFree
