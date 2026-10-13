module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConductorNormalization
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.Nonprincipality
public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.ConvexityData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.Convex

noncomputable section

open DedekindZetaZeroFree NumberField

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

private lemma rpow_conductor_le {Q q U Cc K e : ℝ} (hCc : 0 < Cc) (hK1 : 1 ≤ K)
    (hK2 : 2 * Cc ≤ K) (hU : 0 ≤ U) (hq : q < 2 * U) (hQ0 : 0 ≤ Q) (hQ : Q ≤ Cc * q)
    (he0 : 0 ≤ e) (he1 : e ≤ 1) : Q ^ e ≤ K * U ^ e := by
  have hQK : Q ≤ K * U := by
    calc Q ≤ Cc * q := hQ
      _ ≤ Cc * (2 * U) := mul_le_mul_of_nonneg_left hq.le hCc.le
      _ = (2 * Cc) * U := by ring
      _ ≤ K * U := mul_le_mul_of_nonneg_right hK2 hU
  have hKe : K ^ e ≤ K := by
    have h := Real.rpow_le_rpow_of_exponent_le hK1 he1
    rwa [Real.rpow_one] at h
  calc Q ^ e ≤ (K * U) ^ e := Real.rpow_le_rpow hQ0 hQK he0
    _ = K ^ e * U ^ e := Real.mul_rpow (by linarith) hU
    _ ≤ K * U ^ e := mul_le_mul_of_nonneg_right hKe (Real.rpow_nonneg hU e)

private lemma num_combine {m n Q q U Y Ce C1 K σ d ε : ℝ} (hCe : 0 < Ce) (hC1 : 0 < C1)
    (hK : 0 < K) (hU : 1 ≤ U) (hq : q < 2 * U) (hq0 : 0 < q) (hd : d ≤ ε) (hε : 0 < ε)
    (hY : 0 ≤ Y) (hm : m ≤ Ce * q ^ (ε / 2)) (hn0 : 0 ≤ n) (hn : n ≤ C1 * Q * Y)
    (hQ : Q ≤ K * U ^ ((1 + d - σ) / 2)) (hQ0 : 0 ≤ Q) :
    m * n ≤ (Ce * 2 ^ (ε / 2) * C1 * K) * U ^ ((1 - σ) / 2 + ε) * Y := by
  have hU0 : 0 < U := by linarith
  have h1 : q ^ (ε / 2) ≤ 2 ^ (ε / 2) * U ^ (ε / 2) := by
    calc q ^ (ε / 2) ≤ (2 * U) ^ (ε / 2) :=
          Real.rpow_le_rpow hq0.le hq.le (by positivity)
      _ = 2 ^ (ε / 2) * U ^ (ε / 2) := Real.mul_rpow (by norm_num) hU0.le
  have h2 : U ^ ((1 + d - σ) / 2) * U ^ (ε / 2) ≤ U ^ ((1 - σ) / 2 + ε) := by
    rw [← Real.rpow_add hU0]
    exact Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hA : Ce * q ^ (ε / 2) ≤ Ce * (2 ^ (ε / 2) * U ^ (ε / 2)) :=
    mul_le_mul_of_nonneg_left h1 hCe.le
  have hB : C1 * Q * Y ≤ C1 * (K * U ^ ((1 + d - σ) / 2)) * Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hC1.le) hY
  have hpow : (0 : ℝ) ≤ 2 ^ (ε / 2) := Real.rpow_nonneg (by norm_num) _
  have hc : 0 ≤ Ce * 2 ^ (ε / 2) * C1 * K :=
    mul_nonneg (mul_nonneg (mul_nonneg hCe.le hpow) hC1.le) hK.le
  calc m * n ≤ (Ce * (2 ^ (ε / 2) * U ^ (ε / 2))) * (C1 * (K * U ^ ((1 + d - σ) / 2)) * Y) :=
        mul_le_mul (hm.trans hA) (hn.trans hB) hn0
          (mul_nonneg hCe.le (mul_nonneg hpow (Real.rpow_nonneg hU0.le _)))
    _ = (Ce * 2 ^ (ε / 2) * C1 * K) * (U ^ ((1 + d - σ) / 2) * U ^ (ε / 2)) * Y := by ring
    _ ≤ (Ce * 2 ^ (ε / 2) * C1 * K) * U ^ ((1 - σ) / 2 + ε) * Y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hc) hY

private lemma det_combine {n Q U Y C1 K σ d ε : ℝ} (hC1 : 0 < C1) (hK : 0 ≤ K) (hU : 1 ≤ U)
    (hd : d ≤ ε) (hε : 0 < ε) (hY : 0 ≤ Y) (hn : n ≤ C1 * Q * Y)
    (hQ : Q ≤ K * U ^ ((1 + d - σ) / 2)) :
    n ≤ (C1 * K) * U ^ ((1 - σ) / 2 + ε) * Y := by
  have h2 : U ^ ((1 + d - σ) / 2) ≤ U ^ ((1 - σ) / 2 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hU (by linarith)
  have hB : C1 * Q * Y ≤ C1 * (K * U ^ ((1 + d - σ) / 2)) * Y :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hC1.le) hY
  calc n ≤ C1 * (K * U ^ ((1 + d - σ) / 2)) * Y := hn.trans hB
    _ = (C1 * K) * U ^ ((1 + d - σ) / 2) * Y := by ring
    _ ≤ (C1 * K) * U ^ ((1 - σ) / 2 + ε) * Y :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2 (mul_nonneg hC1.le hK)) hY

private lemma mono_const {A C P Y x : ℝ} (h : x ≤ A * P * Y) (hAC : A ≤ C) (hP : 0 ≤ P)
    (hY : 0 ≤ Y) : x ≤ C * P * Y :=
  h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hP) hY)

theorem convexity :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∀ σs : ℝ, 0 < σs → ∃ C : ℝ, 0 < C ∧
      (∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) →
        ∀ σ t : ℝ, σs ≤ σ → σ ≤ 1 →
          ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A_F) ∧
      (∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) →
        ∀ σ t : ℝ, 0 ≤ σ → σ ≤ 1 →
          ‖g ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((1 - σ) / 2 + ε) * (2 + |t|) ^ A_F) := by
  classical
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F D.recipe.A.zeta12 D.recipe.A.primitive_zeta12
  obtain ⟨A_F, hA0, hconv⟩ := convex_normalized F hF
  refine (ConvexBridge.conductor_bound' D).elim fun Cc hhc => ?_
  obtain ⟨hCc, hcb⟩ := hhc
  refine ⟨A_F, hA0, fun ε hε σs hσs => ?_⟩
  obtain ⟨d, hd0, hd1, hdε⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 10 ∧ d ≤ ε :=
    ⟨min (1 / 10) ε, lt_min (by norm_num) hε, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨C1, hC1, hnorm⟩ := hconv d hd0 hd1
  refine (EulerDeletion.euler_product_bound_with_S D σs hσs (ε / 2) (by positivity)).elim
    fun Ce hhe => ?_
  obtain ⟨hCe, heb⟩ := hhe
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℝ, 1 ≤ K ∧ 2 * Cc ≤ K :=
    ⟨max 1 (2 * Cc), le_max_left _ _, le_max_right _ _⟩
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have h2pos : (0 : ℝ) < 2 ^ (ε / 2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨Ce * 2 ^ (ε / 2) * C1 * K + C1 * K,
    add_pos (mul_pos (mul_pos (mul_pos hCe h2pos) hC1) hK0) (mul_pos hC1 hK0), ?_, ?_⟩
  · intro u hu U hU2 hUq hUq2 g hg hgs σ t hσ1 hσ2
    obtain ⟨hnpP, -⟩ := RowNonprincipal.inducers_nonprincipal D u hu
    have hq1 : 1 ≤ D.q u := (by norm_num : (1:ℝ) ≤ 2).trans (hU2.trans hUq)
    have hq0 : 0 < D.q u := lt_of_lt_of_le one_pos hq1
    have hσpos : 0 < σ := lt_of_lt_of_le hσs hσ1
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
    rw [← hs]
    have hsre : s.re = σ := by rw [hs]; simp
    have hsim : s.im = t := by rw [hs]; simp
    have hg_eq := ConvexBridge.entire_eq_mask_mul D u hnpP hg hgs s (by rw [hsre]; exact hσpos)
    have hN_eq := nonprincipalHeckeEntireContinuation_eq F hF (D.inducers u).plus.conductor
      (D.inducers u).plus.conductor_ne_zero (D.inducers u).plus.character
      (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) s (by rw [hsre]; exact hσpos)
    have hmask := (RowHeckeBridge.mask_norm_le D u (D.inducers u).plus σs hσs s
      (by rw [hsre]; exact hσ1)).1
    have hprod := (heb u hq1).1
    have hNb := hnorm (D.inducers u).plus.conductor (D.inducers u).plus.conductor_ne_zero
      (D.inducers u).plus.character (D.inducers u).plus.primitive hnpP
      (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) s (by rw [hsre]; linarith only [hd0, hσpos]) (by rw [hsre]; linarith only [hσ2, hd0])
    rw [hsre, hsim] at hNb
    have hQ := rpow_conductor_le (Q := 1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ))
      (q := D.q u) (U := U) (K := K) (e := (1 + d - σ) / 2) hCc hK1 hK2 (by linarith only [hU2]) hUq2
      (by positivity) (hcb u hq1).1 (by linarith only [hσ2, hd0]) (by linarith only [hσpos, hd1])
    have hnorm_eq : ‖g s‖ = ‖Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
        (fun v => (D.inducers u).plus.character v.asIdeal) s‖ *
        ‖nonprincipalHeckeEntireContinuation F (D.inducers u).plus.conductor
          (D.inducers u).plus.character (RowHeckeBridge.hecke D.recipe.A (D.inducers u).plus hnpP) s‖ := by
      exact (congrArg norm hg_eq).trans ((norm_mul _ _).trans
        (congrArg (fun x => _ * ‖x‖) hN_eq.symm))
    rw [hnorm_eq]
    have hY : (0 : ℝ) ≤ (2 + |t|) ^ A_F := by positivity
    have hnum := num_combine (Q := (1 + (Ideal.absNorm (D.inducers u).plus.conductor : ℝ)) ^
        ((1 + d - σ) / 2)) hCe hC1 hK0 (by linarith only [hU2]) hUq2 hq0 hdε hε hY
      (hmask.trans hprod) (norm_nonneg _) hNb hQ (by positivity)
    exact mono_const hnum (le_add_of_nonneg_right (mul_nonneg hC1.le hK0.le))
      (Real.rpow_nonneg (by linarith only [hU2]) _) hY
  · intro u hu U hU2 hUq hUq2 g hg hgs σ t hσ1 hσ2
    obtain ⟨-, hnpO⟩ := RowNonprincipal.inducers_nonprincipal D u hu
    have hq1 : 1 ≤ D.q u := (by norm_num : (1:ℝ) ≤ 2).trans (hU2.trans hUq)
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (σ : ℂ) + (t : ℂ) * Complex.I := ⟨_, rfl⟩
    rw [← hs]
    have hsre : s.re = σ := by rw [hs]; simp
    have hsim : s.im = t := by rw [hs]; simp
    have hN_eq : ∀ z : ℂ, 0 < z.re →
        nonprincipalHeckeEntireContinuation F (D.omega u).conductor (D.omega u).character
          (RowHeckeBridge.heckeOmega D u hnpO) z = (RowHeckeBridge.heckeOmega D u hnpO).L z :=
      fun z hz => nonprincipalHeckeEntireContinuation_eq F hF (D.omega u).conductor
        (D.omega u).conductor_ne_zero (D.omega u).character
        (RowHeckeBridge.heckeOmega D u hnpO) z hz
    have hgN : g = nonprincipalHeckeEntireContinuation F (D.omega u).conductor
        (D.omega u).character (RowHeckeBridge.heckeOmega D u hnpO) :=
      RowHeckeBridge.entire_eq_of_eq_right hg
        (nonprincipalHeckeEntireContinuation_differentiable F hF (D.omega u).conductor
          (D.omega u).conductor_ne_zero (D.omega u).character
          (RowHeckeBridge.heckeOmega D u hnpO))
        (fun z hz => (RowHeckeBridge.entire_eq_heckeOmega D u hnpO hg hgs z (by linarith only [hz])).trans
          (hN_eq z (by linarith only [hz])).symm)
    have hNb := hnorm (D.omega u).conductor (D.omega u).conductor_ne_zero
      (D.omega u).character (D.omega u).primitive hnpO
      (RowHeckeBridge.heckeOmega D u hnpO) s (by rw [hsre]; linarith only [hd0, hσ1])
      (by rw [hsre]; linarith only [hσ2, hd0])
    rw [hsre, hsim] at hNb
    have hcb2 : 1 + (Ideal.absNorm (D.omega u).conductor : ℝ) ≤ Cc * D.q u := (hcb u hq1).2
    have hQ := rpow_conductor_le (Q := 1 + (Ideal.absNorm (D.omega u).conductor : ℝ))
      (q := D.q u) (U := U) (K := K) (e := (1 + d - σ) / 2) hCc hK1 hK2 (by linarith only [hU2]) hUq2
      (by positivity) hcb2 (by linarith only [hσ2, hd0]) (by linarith only [hσ1, hd1])
    rw [hgN]
    have hY : (0 : ℝ) ≤ (2 + |t|) ^ A_F := by positivity
    have hdet := det_combine hC1 hK0.le (by linarith only [hU2]) hdε hε hY hNb hQ
    exact mono_const hdet (le_add_of_nonneg_left
      (mul_nonneg (mul_nonneg (mul_nonneg hCe.le h2pos.le) hC1.le) hK0.le))
      (Real.rpow_nonneg (by linarith only [hU2]) _) hY

theorem convexity_numerator_line :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g → (∀ s : ℂ, 1 < s.re → g s = D.Lpsi u s) →
        ∀ t : ℝ,
          ‖g (((3 / 25 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((11 / 25 : ℝ) + ε) * (2 + |t|) ^ A_F := by
  obtain ⟨A_F, hA0, hconv⟩ := convexity (D := D)
  refine ⟨A_F, hA0, fun ε hε => ?_⟩
  obtain ⟨C, hC, h1, -⟩ := hconv ε hε (3 / 25 : ℝ) (by norm_num)
  refine ⟨C, hC, fun u hu U hU2 hUq hUq2 g hg hgs t => ?_⟩
  have key := h1 u hu U hU2 hUq hUq2 g hg hgs (3 / 25 : ℝ) t le_rfl (by norm_num)
  have e : U ^ ((11 / 25 : ℝ) + ε) = U ^ ((1 - 3 / 25 : ℝ) / 2 + ε) := by norm_num
  rw [e]
  exact key

theorem convexity_detector_line :
    ∃ A_F : ℝ, 0 ≤ A_F ∧ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ u : D.Row, u.toFrequency.u ≠ 1 → ∀ U : ℝ, 2 ≤ U → U ≤ D.q u → D.q u < 2 * U →
        ∀ g : ℂ → ℂ, Differentiable ℂ g →
        (∀ s : ℂ, 1 < s.re → g s = Detector.idealLSeries F (D.omega u).character s) →
        ∀ t : ℝ,
          ‖g (((1 / 100 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
            C * U ^ ((99 / 200 : ℝ) + ε) * (2 + |t|) ^ A_F := by
  obtain ⟨A_F, hA0, hconv⟩ := convexity (D := D)
  refine ⟨A_F, hA0, fun ε hε => ?_⟩
  obtain ⟨C, hC, -, h2⟩ := hconv ε hε 1 (by norm_num)
  refine ⟨C, hC, fun u hu U hU2 hUq hUq2 g hg hgs t => ?_⟩
  have key := h2 u hu U hU2 hUq hUq2 g hg hgs (1 / 100 : ℝ) t (by norm_num) (by norm_num)
  have e : U ^ ((99 / 200 : ℝ) + ε) = U ^ ((1 - 1 / 100 : ℝ) / 2 + ε) := by norm_num
  rw [e]
  exact key

end

end DedekindZetaZeroFree.Quantitative.Convex
