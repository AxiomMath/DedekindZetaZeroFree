module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RootAndDiagonalDefects

@[expose] public section

namespace DedekindZetaZeroFree
namespace KubotaWeylBoundaryCells

open KubotaRankTwo KubotaDefectSymbolAlgebra
open scoped Classical

private theorem x_w (K : Type*) [Field K] (g : GL2 K) :
    x K (g * w K) =
      if (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 then
        -(g : Matrix (Fin 2) (Fin 2) K) 1 0 else
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by
  classical
  simp [x, Matrix.mul_apply]

private theorem factor (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1) (g h : GL2 K) :
    KubotaElementaryLastArgument.defect K M B g h (w K) =
      B (X K (g * h * w K) * X K h / (X K (g * h) * X K (h * w K)))
        (X K (g * h) * X K (h * w K) / (X K g * det K h)) := by
  unfold KubotaElementaryLastArgument.defect KubotaElementaryLastArgument.tau
  simp only [map_mul, X_w, one_mul, mul_assoc]
  simpa only [one_mul, mul_one, mul_assoc] using
    kp_kubota_defect_symbol_algebra K M B hL hR hAlt
      (X K g) (X K h) (X K (h * w K)) (X K (g * h))
      (X K (g * (h * w K))) 1 (det K g) (det K h)

theorem defect_w_boundary
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (g h : KubotaRankTwo.GL2 K)
    (hBoundary :
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨
      (h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨
      (h : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 ∨
      (g * h : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∨
      (g * h : Matrix (Fin 2) (Fin 2) K) 1 1 = 0) :
    KubotaElementaryLastArgument.defect K M B g h (KubotaRankTwo.w K) = 1 := by
  let c : K := (g : Matrix (Fin 2) (Fin 2) K) 1 0
  let d : K := (g : Matrix (Fin 2) (Fin 2) K) 1 1
  let e : K := (h : Matrix (Fin 2) (Fin 2) K) 1 0
  let f : K := (h : Matrix (Fin 2) (Fin 2) K) 1 1
  let C : K := (g * h : Matrix (Fin 2) (Fin 2) K) 1 0
  let D : K := (g * h : Matrix (Fin 2) (Fin 2) K) 1 1
  let q : K := (det K h : Kˣ)
  let r := X K g
  let x0 := X K h
  let y := X K (h * w K)
  let z := X K (g * h)
  let t := X K (g * h * w K)
  have hC : C = c * (h : Matrix (Fin 2) (Fin 2) K) 0 0 + d * e := by
    simp [C, c, d, e, Matrix.mul_apply]
  have hD : D = c * (h : Matrix (Fin 2) (Fin 2) K) 0 1 + d * f := by
    simp [D, c, d, f, Matrix.mul_apply]
  have hrel : C * f - D * e = c * q := by
    rw [hC, hD]
    simp only [q, det, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
    ring
  have hq : q ≠ 0 := (det K h).ne_zero
  have hr : (r : K) = if c = 0 then d else c := rfl
  have hx : (x0 : K) = if e = 0 then f else e := rfl
  have hy : (y : K) = if f = 0 then -e else f := by
    exact x_w K h
  have hz : (z : K) = if C = 0 then D else C := rfl
  have ht : (t : K) = if D = 0 then -C else D := by
    exact x_w K (g * h)
  have hfac : KubotaElementaryLastArgument.defect K M B g h (w K) =
      B (t * x0 / (z * y)) (z * y / (r * det K h)) := by
    exact factor K M B hL hR hAlt g h
  rw [hfac]
  by_cases hc : c = 0
  · have hd : d ≠ 0 := bottomRight_ne_zero K g hc
    have hC' : C = d * e := by rw [hC, hc]; ring
    have hD' : D = d * f := by rw [hD, hc]; ring
    have hslot : t * x0 / (z * y) = 1 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
      rw [hx, hy, hz, ht, hC', hD']
      by_cases he : e = 0 <;> by_cases hf : f = 0
      · exact False.elim ((x_ne_zero K h) (by simp [x, e, f, he, hf]))
      · simp [he, hf, hd]
      · simp [he, hf, hd]
      · simp only [if_neg he, if_neg hf, if_neg (mul_ne_zero hd he),
          if_neg (mul_ne_zero hd hf)]
        field_simp
    rw [hslot]
    exact one_left K M B hL _
  by_cases he : e = 0
  · have hf : f ≠ 0 := bottomRight_ne_zero K h he
    have hCne : C ≠ 0 := by
      intro hzero
      have hh := hrel
      rw [hzero, he] at hh
      simp only [zero_mul, mul_zero, sub_zero] at hh
      exact mul_ne_zero hc hq hh.symm
    have hslot : z * y / (r * det K h) = 1 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
      rw [hz, hy, hr, if_neg hCne, if_neg hf, if_neg hc]
      change C * f / (c * q) = 1
      apply (div_eq_one_iff_eq (mul_ne_zero hc hq)).2
      simpa [he] using hrel
    rw [hslot]
    exact one_right K M B hR _
  by_cases hf : f = 0
  · have hDne : D ≠ 0 := by
      intro hzero
      have hh := hrel
      rw [hzero, hf] at hh
      simp only [zero_mul, mul_zero, sub_zero] at hh
      exact mul_ne_zero hc hq hh.symm
    have hslot : t * x0 / (z * y) = -(z * y / (r * det K h))⁻¹ := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val]
      rw [ht, hx, hy, hr, if_neg hDne, if_neg he, if_pos hf, if_neg hc]
      change D * e / ((z : K) * -e) = -(((z : K) * -e / (c * q))⁻¹)
      have hh : -(D * e) = c * q := by simpa [hf] using hrel
      rw [← hh]
      field_simp
    rw [hslot, show -(z * y / (r * det K h))⁻¹ =
        (-1) * (z * y / (r * det K h))⁻¹ by simp,
      hL, neg_one_left K M B hL hCub, inv_left K M B hL, hAlt]
    simp
  rcases hBoundary with hzero | hzero | hzero | hCzero | hDzero
  · exact (hc hzero).elim
  · exact (he hzero).elim
  · exact (hf hzero).elim
  · change C = 0 at hCzero
    have hDne : D ≠ 0 := bottomRight_ne_zero K (g * h) hCzero
    have hslot : z * y / (r * det K h) = -(t * x0 / (z * y))⁻¹ := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
        Units.val_inv_eq_inv_val]
      rw [hz, ht, hx, hy, hr, if_pos hCzero, if_neg hDne,
        if_neg he, if_neg hf, if_neg hc]
      change D * f / (c * q) = -((D * e / (D * f))⁻¹)
      have hh : -(D * e) = c * q := by simpa [hCzero] using hrel
      rw [← hh]
      field_simp
    rw [hslot, show -(t * x0 / (z * y))⁻¹ =
        (t * x0 / (z * y))⁻¹ * (-1) by simp,
      hR, inv_right K M B hR, hAlt, neg_one_right K M B hR hCub]
    simp
  · change D = 0 at hDzero
    have hCne : C ≠ 0 := by
      intro hzero
      have hh := hrel
      rw [hzero, hDzero] at hh
      simp only [zero_mul, sub_zero] at hh
      exact mul_ne_zero hc hq hh.symm
    have hslot : z * y / (r * det K h) = 1 := by
      apply Units.ext
      simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_one]
      rw [hz, hy, hr, if_neg hCne, if_neg hf, if_neg hc]
      change C * f / (c * q) = 1
      apply (div_eq_one_iff_eq (mul_ne_zero hc hq)).2
      simpa [hDzero] using hrel
    rw [hslot]
    exact one_right K M B hR _

end KubotaWeylBoundaryCells
end DedekindZetaZeroFree
