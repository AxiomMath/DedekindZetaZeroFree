module

public import DedekindZetaZeroFree.Metaplectic.Kubota.RootAndDiagonalDefects

@[expose] public section

namespace DedekindZetaZeroFree
namespace KubotaWeylOpenCell

theorem defect_w_open
    (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c : Kˣ, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c : Kˣ, B a (b * c) = B a b * B a c)
    (hAlt : ∀ a : Kˣ, B a a = 1)
    (hCub : ∀ a b : Kˣ, (B a b) ^ 3 = 1)
    (hSt : ∀ (a : Kˣ) (ha : (a : K) ≠ 1),
      B a (Units.mk0 (1 - (a : K)) (sub_ne_zero.mpr (Ne.symm ha))) = 1)
    (g h : KubotaRankTwo.GL2 K)
    (hg21 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (hh21 : (h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (hh22 : (h : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0)
    (hgh21 : (g * h : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0)
    (hgh22 : (g * h : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0) :
    KubotaElementaryLastArgument.defect K M B g h (KubotaRankTwo.w K) = 1 := by
  classical
  let c : Kˣ := Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 1 0) hg21
  let e : Kˣ := Units.mk0 ((h : Matrix (Fin 2) (Fin 2) K) 1 0) hh21
  let f : Kˣ := Units.mk0 ((h : Matrix (Fin 2) (Fin 2) K) 1 1) hh22
  let C : Kˣ := Units.mk0 ((g * h : Matrix (Fin 2) (Fin 2) K) 1 0) hgh21
  let D : Kˣ := Units.mk0 ((g * h : Matrix (Fin 2) (Fin 2) K) 1 1) hgh22
  let q := KubotaRankTwo.det K h
  have xg : KubotaRankTwo.X K g = c := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, c, hg21]
  have xh : KubotaRankTwo.X K h = e := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, e, hh21]
  have xgh : KubotaRankTwo.X K (g * h) = C := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, C, hgh21]
  have xhw : KubotaRankTwo.X K (h * KubotaRankTwo.w K) = f := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, f, Matrix.mul_apply, hh22]
  have xghw : KubotaRankTwo.X K (g * h * KubotaRankTwo.w K) = D := by
    apply Units.ext
    have hb : ((g * h * KubotaRankTwo.w K : KubotaRankTwo.GL2 K) :
        Matrix (Fin 2) (Fin 2) K) 1 0 =
        (g * h : Matrix (Fin 2) (Fin 2) K) 1 1 := by
      simp [Matrix.mul_apply]
    change KubotaRankTwo.x K (g * h * KubotaRankTwo.w K) =
      (g * h : Matrix (Fin 2) (Fin 2) K) 1 1
    simp [KubotaRankTwo.x, hb, hgh22]
  have rel : (C : K) * (f : K) - (D : K) * (e : K) = (c : K) * (q : K) := by
    simp [C, D, c, e, f, q, KubotaRankTwo.det,
      Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.mul_apply]
    ring
  let s : Kˣ := c * q / (C * f)
  let a : Kˣ := D * e / (C * f)
  have ha : (a : K) = 1 - (s : K) := by
    dsimp [a, s]
    simp only [Units.val_div_eq_div_val, Units.val_mul]
    field_simp
    linear_combination -rel
  have hs : (s : K) ≠ 1 := by
    intro hs
    have := a.ne_zero
    rw [ha, hs, sub_self] at this
    exact this rfl
  have st : B s a = 1 := by
    have ae : a = Units.mk0 (1 - (s : K)) (sub_ne_zero.mpr (Ne.symm hs)) :=
      Units.ext ha
    rw [ae]
    exact hSt s hs
  have cancel : B a s⁻¹ = 1 := by
    rw [KubotaDefectSymbolAlgebra.inv_right K M B hR,
      KubotaDefectSymbolAlgebra.skew_symmetry K M B hL hR hAlt a s, st]
    simp
  unfold KubotaElementaryLastArgument.defect KubotaElementaryLastArgument.tau
  rw [← mul_assoc g h (KubotaRankTwo.w K)]
  rw [xg, xh, xgh, xhw, xghw, KubotaRankTwo.X_w, map_mul]
  have hf := kp_kubota_defect_symbol_algebra K M B hL hR hAlt
    c e f C D (1 : Kˣ) (KubotaRankTwo.det K g) q
  simp only [one_mul] at hf ⊢
  rw [hf]
  simpa [a, s, q] using cancel

end KubotaWeylOpenCell
end DedekindZetaZeroFree
