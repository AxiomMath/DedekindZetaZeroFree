module

public import Mathlib.Tactic

@[expose] public section

namespace DedekindZetaZeroFree
namespace KubotaRankTwo

universe u

abbrev GL2 (K : Type u) [Field K] := Matrix.GeneralLinearGroup (Fin 2) K

abbrev det (K : Type u) [Field K] : GL2 K →* Kˣ :=
  Matrix.GeneralLinearGroup.det

noncomputable def x (K : Type u) [Field K] (g : GL2 K) : K := by
  classical
  exact if (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 then
    (g : Matrix (Fin 2) (Fin 2) K) 1 1 else
    (g : Matrix (Fin 2) (Fin 2) K) 1 0

theorem x_ne_zero (K : Type u) [Field K] (g : GL2 K) : x K g ≠ 0 := by
  classical
  unfold x
  split_ifs with hc
  · intro hd
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
    simp only [Matrix.det_fin_two, hc, hd, mul_zero, zero_mul, sub_self] at hdet
    exact hdet rfl
  · exact hc

noncomputable def X (K : Type u) [Field K] (g : GL2 K) : Kˣ :=
  Units.mk0 (x K g) (x_ne_zero K g)

private theorem x_congr (K : Type u) [Field K] {g h : GL2 K}
    (h10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = (h : Matrix (Fin 2) (Fin 2) K) 1 0)
    (h11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = (h : Matrix (Fin 2) (Fin 2) K) 1 1) :
    x K g = x K h := by
  unfold x
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [if_pos hc, if_pos (h10 ▸ hc)]
    exact h11
  · rw [if_neg hc, if_neg (fun hh => hc (h10.symm ▸ hh))]
    exact h10

def n (K : Type u) [Field K] (t : K) : GL2 K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, t; 0, 1] (by
    simp [Matrix.det_fin_two])

def d (K : Type u) [Field K] (u v : Kˣ) : GL2 K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(u : K), 0; 0, (v : K)] (by
    simpa [Matrix.det_fin_two] using mul_ne_zero u.ne_zero v.ne_zero)

def w (K : Type u) [Field K] : GL2 K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; 1, 0] (by
    simp [Matrix.det_fin_two])

@[simp] theorem coe_n (K : Type u) [Field K] (t : K) :
    (n K t : Matrix (Fin 2) (Fin 2) K) = !![1, t; 0, 1] := rfl

@[simp] theorem coe_d (K : Type u) [Field K] (u v : Kˣ) :
    (d K u v : Matrix (Fin 2) (Fin 2) K) = !![(u : K), 0; 0, (v : K)] := rfl

@[simp] theorem coe_w (K : Type u) [Field K] :
    (w K : Matrix (Fin 2) (Fin 2) K) = !![0, -1; 1, 0] := rfl

@[simp] theorem det_n (K : Type u) [Field K] (t : K) : det K (n K t) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_n, Matrix.det_fin_two]

@[simp] theorem det_d (K : Type u) [Field K] (u v : Kˣ) :
    det K (d K u v) = u * v := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_d, Matrix.det_fin_two]

@[simp] theorem det_w (K : Type u) [Field K] : det K (w K) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, coe_w, Matrix.det_fin_two]

@[simp] theorem X_one (K : Type u) [Field K] : X K (1 : GL2 K) = 1 := by
  ext
  simp [X, x]

@[simp] theorem X_n (K : Type u) [Field K] (t : K) : X K (n K t) = 1 := by
  ext
  simp [X, x, coe_n]

@[simp] theorem X_d (K : Type u) [Field K] (u v : Kˣ) : X K (d K u v) = v := by
  ext
  simp [X, x, coe_d]

@[simp] theorem X_w (K : Type u) [Field K] : X K (w K) = 1 := by
  ext
  simp [X, x, coe_w]

@[simp] theorem X_n_mul (K : Type u) [Field K] (g : GL2 K) (t : K) :
    X K (n K t * g) = X K g := by
  apply Units.ext
  show x K (n K t * g) = x K g
  exact x_congr K (by simp [Matrix.mul_apply]) (by simp [Matrix.mul_apply])

@[simp] theorem X_mul_n (K : Type u) [Field K] (g : GL2 K) (t : K) :
    X K (g * n K t) = X K g := by
  apply Units.ext
  show x K (g * n K t) = x K g
  have h10 : ((g : Matrix (Fin 2) (Fin 2) K) * (n K t : Matrix (Fin 2) (Fin 2) K)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 := by simp [Matrix.mul_apply]
  have h11 : ((g : Matrix (Fin 2) (Fin 2) K) * (n K t : Matrix (Fin 2) (Fin 2) K)) 1 1 =
      (g : Matrix (Fin 2) (Fin 2) K) 1 0 * t +
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 := by simp [Matrix.mul_apply]
  unfold x
  simp only [Matrix.GeneralLinearGroup.coe_mul]
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · have hc' : ((g : Matrix (Fin 2) (Fin 2) K) *
        (n K t : Matrix (Fin 2) (Fin 2) K)) 1 0 = 0 := by rw [h10]; exact hc
    rw [if_pos hc', if_pos hc, h11, hc]
    ring
  · have hc' : ¬ (((g : Matrix (Fin 2) (Fin 2) K) *
        (n K t : Matrix (Fin 2) (Fin 2) K)) 1 0 = 0) := by rw [h10]; exact hc
    rw [if_neg hc', if_neg hc, h10]

theorem X_n_mul_mul_n (K : Type u) [Field K] (g h : GL2 K) (t t' : K) :
    X K (n K t * g * h * n K t') = X K (g * h) := by
  rw [show n K t * g * h * n K t' = n K t * (g * h) * n K t' from by group]
  rw [X_mul_n, X_n_mul]

theorem topLeft_ne_zero (K : Type u) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
  intro ha
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
  simp only [Matrix.det_fin_two, hc, ha, mul_zero, zero_mul, sub_self] at hdet
  exact hdet rfl

theorem bottomRight_ne_zero (K : Type u) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  intro hd
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero g
  simp only [Matrix.det_fin_two, hc, hd, mul_zero, zero_mul, sub_self] at hdet
  exact hdet rfl

theorem bruhat_closed (K : Type u) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    g = d K
      (Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 0 0) (topLeft_ne_zero K g hc))
      (Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 1 1) (bottomRight_ne_zero K g hc)) *
      n K (((g : Matrix (Fin 2) (Fin 2) K) 0 1) /
        ((g : Matrix (Fin 2) (Fin 2) K) 0 0)) := by
  have ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := topLeft_ne_zero K g hc
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, coe_d, coe_n, hc] <;>
    field_simp <;> ring

theorem bruhat_open (K : Type u) [Field K] (g : GL2 K)
    (hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0) :
    g = n K (((g : Matrix (Fin 2) (Fin 2) K) 0 0) /
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0)) *
      d K (det K g / Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 1 0) hc)
        (Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 1 0) hc) *
      w K *
      n K (((g : Matrix (Fin 2) (Fin 2) K) 1 1) /
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, coe_d, coe_n, coe_w, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two, Units.val_div_eq_div_val] <;>
    field_simp <;> ring

end KubotaRankTwo
end DedekindZetaZeroFree
