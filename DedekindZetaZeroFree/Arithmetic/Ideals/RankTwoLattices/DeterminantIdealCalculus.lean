module

public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.FullLatticesAndRationalLines
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

section DeterminantBilinear

variable (K : Type*) [Field K]

private lemma det₂_zero_left (x : K × K) : det₂ K 0 x = 0 := by
  simp [det₂]

private lemma det₂_zero_right (x : K × K) : det₂ K x 0 = 0 := by
  simp [det₂]

private lemma det₂_add_left (x y z : K × K) :
    det₂ K (x + y) z = det₂ K x z + det₂ K y z := by
  simp only [det₂, Prod.fst_add, Prod.snd_add]
  ring

private lemma det₂_add_right (x y z : K × K) :
    det₂ K x (y + z) = det₂ K x y + det₂ K x z := by
  simp only [det₂, Prod.fst_add, Prod.snd_add]
  ring

private lemma det₂_smul_left (a : K) (x y : K × K) :
    det₂ K (a • x) y = a * det₂ K x y := by
  simp only [det₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private lemma det₂_smul_right (b : K) (x y : K × K) :
    det₂ K x (b • y) = b * det₂ K x y := by
  simp only [det₂, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

private lemma det₂_smul_smul (a b : K) (x y : K × K) :
    det₂ K (a • x) (b • y) = (a * b) * det₂ K x y := by
  rw [det₂_smul_left, det₂_smul_right]
  ring

private lemma det₂_std : det₂ K (1, 0) (0, 1) = 1 := by
  simp [det₂]

end DeterminantBilinear

section DeterminantBilinearScalars

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]

private lemma det₂_smul_left_R (r : R) (x y : K × K) :
    det₂ K (r • x) y = r • det₂ K x y := by
  simp only [det₂, Prod.smul_fst, Prod.smul_snd]
  simp only [Algebra.smul_def]
  ring

private lemma det₂_smul_right_R (r : R) (x y : K × K) :
    det₂ K x (r • y) = r • det₂ K x y := by
  simp only [det₂, Prod.smul_fst, Prod.smul_snd]
  simp only [Algebra.smul_def]
  ring

end DeterminantBilinearScalars

section DeterminantLinearEquiv

variable (K : Type*) [Field K]

private lemma det₂_linearEquiv_std (g : (K × K) ≃ₗ[K] (K × K)) :
    det₂ K (g (1, 0)) (g (0, 1)) = LinearMap.det g.toLinearMap := by
  have hdet := LinearMap.det_toMatrix (Module.Basis.finTwoProd K) g.toLinearMap
  rw [← hdet, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, det₂]
  rw [mul_comm]

private lemma det₂_linearEquiv (g : (K × K) ≃ₗ[K] (K × K)) (x y : K × K) :
    det₂ K (g x) (g y) = LinearMap.det g.toLinearMap * det₂ K x y := by
  have hx : g x = x.1 • g (1, 0) + x.2 • g (0, 1) := by
    have h : x = x.1 • (1, 0) + x.2 • (0, 1) := by
      ext <;> simp
    conv_lhs => rw [h]
    rw [map_add, map_smul, map_smul]
  have hy : g y = y.1 • g (1, 0) + y.2 • g (0, 1) := by
    have h : y = y.1 • (1, 0) + y.2 • (0, 1) := by
      ext <;> simp
    conv_lhs => rw [h]
    rw [map_add, map_smul, map_smul]
  have key : det₂ K (g x) (g y) =
      (x.1 * y.2 - x.2 * y.1) * det₂ K (g (1, 0)) (g (0, 1)) := by
    rw [hx, hy]
    simp only [det₂, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    ring
  rw [key, det₂_linearEquiv_std K g]
  simp only [det₂]
  ring

end DeterminantLinearEquiv

theorem kp_cusp_determinantSubmodule_fg
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    (determinantSubmodule R K M.val).FG := by
  obtain ⟨S, hS⟩ := M.property.fg
  refine Submodule.fg_def.mpr
    ⟨(fun p : (K × K) × (K × K) => det₂ K p.1 p.2) ''
        ((S : Set (K × K)) ×ˢ (S : Set (K × K))), ?_, ?_⟩
  · exact (S.finite_toSet.prod S.finite_toSet).image _
  · rw [← hS, determinantSubmodule]
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro d ⟨p, hp, rfl⟩
      obtain ⟨hx, hy⟩ := Set.mem_prod.mp hp
      exact Submodule.subset_span
        ⟨p.1, Submodule.subset_span hx, p.2, Submodule.subset_span hy, rfl⟩
    · rw [Submodule.span_le]
      rintro d ⟨x, hx, y, hy, rfl⟩
      refine Submodule.span_induction₂
        (p := fun x y _ _ =>
          det₂ K x y ∈ Submodule.span R
            ((fun p : (K × K) × (K × K) => det₂ K p.1 p.2) ''
              ((S : Set (K × K)) ×ˢ (S : Set (K × K)))))
        (fun x y hx hy => Submodule.subset_span ⟨(x, y), Set.mem_prod.mpr ⟨hx, hy⟩, rfl⟩)
        (fun y _ => by rw [det₂_zero_left]; exact Submodule.zero_mem _)
        (fun x _ => by rw [det₂_zero_right]; exact Submodule.zero_mem _)
        (fun x y z _ _ _ h1 h2 => by
          rw [det₂_add_left]; exact Submodule.add_mem _ h1 h2)
        (fun x y z _ _ _ h1 h2 => by
          rw [det₂_add_right]; exact Submodule.add_mem _ h1 h2)
        (fun r x y _ _ h1 => by
          rw [det₂_smul_left_R]; exact Submodule.smul_mem _ r h1)
        (fun r x y _ _ h1 => by
          rw [det₂_smul_right_R]; exact Submodule.smul_mem _ r h1)
        hx hy

theorem kp_cusp_determinantSubmodule_isFractional
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    IsFractional R⁰ (determinantSubmodule R K M.val) := by
  exact FractionalIdeal.isFractional_of_fg (kp_cusp_determinantSubmodule_fg R K M)

theorem kp_cusp_determinantSubmodule_ne_bot
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    determinantSubmodule R K M.val ≠ ⊥ := by
  intro hbot
  have hzero : ∀ x ∈ M.val, ∀ y ∈ M.val, det₂ K x y = 0 := by
    intro x hx y hy
    have hmem : det₂ K x y ∈ determinantSubmodule R K M.val :=
      Submodule.subset_span ⟨x, hx, y, hy, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hspan1 : ∀ x ∈ M.val, ∀ y : K × K, det₂ K x y = 0 := by
    intro x hx y
    have hy : y ∈ Submodule.span K (M.val : Set (K × K)) := by
      rw [M.property.span_eq_top]; trivial
    induction hy using Submodule.span_induction with
    | mem z hz => exact hzero x hx z hz
    | zero => rw [det₂_zero_right]
    | add z w _ _ hz hw => rw [det₂_add_right, hz, hw, add_zero]
    | smul a z _ hz => rw [det₂_smul_right, hz, mul_zero]
  have hall : ∀ x y : K × K, det₂ K x y = 0 := by
    intro x y
    have hx : x ∈ Submodule.span K (M.val : Set (K × K)) := by
      rw [M.property.span_eq_top]; trivial
    induction hx using Submodule.span_induction with
    | mem z hz => exact hspan1 z hz y
    | zero => rw [det₂_zero_left]
    | add z w _ _ hz hw => rw [det₂_add_left, hz, hw, add_zero]
    | smul a z _ hz => rw [det₂_smul_left, hz, mul_zero]
  have hstd := hall (1, 0) (0, 1)
  rw [det₂_std] at hstd
  exact one_ne_zero hstd

theorem kp_cusp_determinantSubmodule_map
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Submodule R (K × K)) (g : (K × K) ≃ₗ[K] (K × K)) :
    determinantSubmodule R K (Submodule.map (g.toLinearMap.restrictScalars R) M) =
      Submodule.map (LinearMap.mulLeft R (LinearMap.det g.toLinearMap))
        (determinantSubmodule R K M) := by
  have key : ∀ x y : K × K,
      det₂ K (g x) (g y) = LinearMap.det g.toLinearMap * det₂ K x y :=
    fun x y => det₂_linearEquiv K g x y
  rw [determinantSubmodule, determinantSubmodule, Submodule.map_span]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro d ⟨x, hx, y, hy, rfl⟩
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Submodule.mem_map.mp hy
    simp only [LinearMap.restrictScalars_apply]
    have hkey : det₂ K (g.toLinearMap x₀) (g.toLinearMap y₀) =
        LinearMap.det g.toLinearMap * det₂ K x₀ y₀ := key x₀ y₀
    rw [hkey]
    exact Submodule.subset_span
      ⟨det₂ K x₀ y₀, ⟨x₀, hx₀, y₀, hy₀, rfl⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro d ⟨e, he, rfl⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := he
    rw [LinearMap.mulLeft_apply, ← key x y]
    exact Submodule.subset_span
      ⟨g x, Submodule.mem_map_of_mem hx, g y, Submodule.mem_map_of_mem hy, rfl⟩

theorem kp_cusp_determinantSubmodule_ideal_coordinates
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Submodule R (K × K))
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0)
    (v w : K × K) (hvw : det₂ K v w ≠ 0)
    (hM : ∀ x : K × K, x ∈ M ↔
      ∃ s ∈ I, ∃ t ∈ J, x = s • v + t • w) :
    determinantSubmodule R K M =
      (FractionalIdeal.spanSingleton R⁰ (det₂ K v w) * (I * J) :
        FractionalIdeal R⁰ K).val := by
  have hcoec : ((FractionalIdeal.spanSingleton R⁰ (det₂ K v w) * (I * J) :
      FractionalIdeal R⁰ K) : Submodule R K) =
      Submodule.span R {det₂ K v w} *
        ((I : Submodule R K) * (J : Submodule R K)) := by
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton]
  have hmain : determinantSubmodule R K M =
      Submodule.span R {det₂ K v w} *
        ((I : Submodule R K) * (J : Submodule R K)) := by
    refine le_antisymm ?_ ?_
    · rw [determinantSubmodule, Submodule.span_le]
      rintro d ⟨x, hx, y, hy, rfl⟩
      obtain ⟨s, hs, t, ht, rfl⟩ := (hM x).mp hx
      obtain ⟨s', hs', t', ht', rfl⟩ := (hM y).mp hy
      have key : det₂ K (s • v + t • w) (s' • v + t' • w) =
          det₂ K v w * (s * t' - s' * t) := by
        simp only [det₂, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
        ring
      rw [key]
      exact Submodule.mul_mem_mul (Submodule.mem_span_singleton_self (det₂ K v w))
        (Submodule.sub_mem _
          (Submodule.mul_mem_mul hs ht') (Submodule.mul_mem_mul hs' ht))
    · rw [Submodule.mul_le]
      intro u hu z hz
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hu
      have hIJ : (I : Submodule R K) * (J : Submodule R K) ≤
          Submodule.comap (LinearMap.mulLeft R (det₂ K v w))
            (determinantSubmodule R K M) := by
        rw [Submodule.mul_le]
        intro i hi j hj
        rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
        have key : det₂ K v w * (i * j) = det₂ K (i • v) (j • w) := by
          rw [det₂_smul_smul]
          ring
        rw [key]
        exact Submodule.subset_span
          ⟨i • v, (hM _).mpr ⟨i, hi, 0, Submodule.zero_mem _, by rw [zero_smul, add_zero]⟩,
           j • w, (hM _).mpr ⟨0, Submodule.zero_mem _, j, hj, by rw [zero_smul, zero_add]⟩,
           rfl⟩
      have hz' : det₂ K v w * z ∈ determinantSubmodule R K M :=
        Submodule.mem_comap.mp (hIJ hz)
      have hsmul : (r • det₂ K v w) * z = r • (det₂ K v w * z) := by
        simp only [Algebra.smul_def, mul_assoc]
      rw [hsmul]
      exact Submodule.smul_mem _ r hz'
  rw [hmain]
  exact hcoec.symm

theorem kp_cusp_determinantSubmodule_coordinateLattice
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) :
    determinantSubmodule R K (coordinateLattice R K I J) =
      (I * J : FractionalIdeal R⁰ K).val := by
  have hcoe : ((I * J : FractionalIdeal R⁰ K) : Submodule R K) =
      (I : Submodule R K) * (J : Submodule R K) := FractionalIdeal.coe_mul I J
  have hmain : determinantSubmodule R K (coordinateLattice R K I J) =
      (I : Submodule R K) * (J : Submodule R K) := by
    refine le_antisymm ?_ ?_
    · rw [determinantSubmodule, Submodule.span_le]
      rintro d ⟨x, hx, y, hy, rfl⟩
      rw [coordinateLattice, Submodule.mem_prod] at hx hy
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      have key : det₂ K x y = x.1 * y.2 - y.1 * x.2 := by
        simp only [det₂]; ring
      rw [key]
      exact Submodule.sub_mem _
        (Submodule.mul_mem_mul hx1 hy2) (Submodule.mul_mem_mul hy1 hx2)
    · rw [Submodule.mul_le]
      intro i hi j hj
      have key : i * j = det₂ K (i, (0 : K)) ((0 : K), j) := by
        simp [det₂]
      rw [key]
      exact Submodule.subset_span
        ⟨(i, 0), by
          rw [coordinateLattice, Submodule.mem_prod]; exact ⟨hi, Submodule.zero_mem _⟩,
         (0, j), by
          rw [coordinateLattice, Submodule.mem_prod]; exact ⟨Submodule.zero_mem _, hj⟩,
         rfl⟩
  rw [hmain]
  exact hcoe.symm

end DedekindZetaZeroFree
