module

public import DedekindZetaZeroFree.CharacterSums.Gauss.WeightedUnitShellIntegrals
public import DedekindZetaZeroFree.Theta.Whittaker.CubicShellVectorIdentities

@[expose] public section

open scoped BigOperators Valued ValuativeRel
open ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorActualJacquetShells

open KPExteriorUnitShellIntegrals

noncomputable section
set_option autoImplicit false

theorem finite_shell_coordinate_identity
    {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Fintype (IsLocalRing.ResidueField (valuation K).integer)]
    (χκ : MulChar (IsLocalRing.ResidueField (valuation K).integer) ℂ)
    (hχκ : orderOf χκ = 6)
    (ψbar : AddChar (IsLocalRing.ResidueField (valuation K).integer) ℂ) (e : ℕ) :
    qPower (K := K) (-2 * (e : ℝ) / 3) • KPThreeShell.basis (-(e : ℤ)) +
      ∑ l ∈ Finset.Icc 1 (e + 1),
        (qPower (K := K) (-2 * (e : ℝ) / 3) *
          qPower (K := K) ((l : ℝ) / 3) * shellValue χκ ψbar e (l : ℤ)) •
          KPThreeShell.basis (-(e : ℤ) + 2 * (l : ℤ)) =
      KPThreeShell.shell
        (Fintype.card (IsLocalRing.ResidueField (valuation K).integer) : ℝ)
        (g χκ ψbar 2) (g χκ ψbar 4) e := by
  classical
  let Q : ℝ := Fintype.card (IsLocalRing.ResidueField (valuation K).integer)
  have hq : qPower (K := K) (-1) = (Q⁻¹ : ℝ) := by
    simp [qPower, Q, Real.rpow_neg_one]
  have hg (j k : ℤ) (h : j % 6 = k % 6) : g χκ ψbar j = g χκ ψbar k := by
    have hp : χκ ^ j = χκ ^ k := by
      rw [← zpow_mod_orderOf χκ j, ← zpow_mod_orderOf χκ k, hχκ]
      exact congrArg (fun n : ℤ => χκ ^ n) h
    simp only [g, hp]
  have ht : shellValue χκ ψbar e ((e + 1 : ℕ) : ℤ) =
      KPThreeShell.tameFactor Q (g χκ ψbar 2) (g χκ ψbar 4) (e + 1) := by
    have hle : ¬ ((e + 1 : ℕ) : ℤ) ≤ (e : ℤ) := by omega
    have heq : ((e + 1 : ℕ) : ℤ) = (e : ℤ) + 1 := by push_cast; rfl
    have hd : (3 : ℤ) ∣ ((e + 1 : ℕ) : ℤ) ↔ (e + 1) % 3 = 0 := by omega
    simp only [shellValue, hle, ↓reduceIte, heq, ↓reduceIte]
    simp only [← heq, hle, ↓reduceIte, hd]
    unfold KPThreeShell.tameFactor
    split_ifs with h0 h1
    · rw [hq]
    · rw [hg (-2 * ((e + 1 : ℕ) : ℤ)) 4 (by omega)]
      simp only [qPower, Q, neg_div]
    · rw [hg (-2 * ((e + 1 : ℕ) : ℤ)) 2 (by omega)]
      simp only [qPower, Q, neg_div]
  have hi (l : ℕ) (hl : l ∈ Finset.Icc 1 e) :
      shellValue χκ ψbar e (l : ℤ) =
        if (3 : ℕ) ∣ l then (1 - (Q⁻¹ : ℝ) : ℂ) else 0 := by
    have hle : (l : ℤ) ≤ (e : ℤ) := by
      have := (Finset.mem_Icc.mp hl).2
      omega
    have hd : (3 : ℤ) ∣ (l : ℤ) ↔ (3 : ℕ) ∣ l := by omega
    simp only [shellValue, hle, ↓reduceIte, hd, hq]
  have hset : Finset.Icc 1 (e + 1) = insert (e + 1) (Finset.Icc 1 e) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : e + 1 ∉ Finset.Icc 1 e := by simp
  rw [hset, Finset.sum_insert hnot]
  have hs :
      (∑ l ∈ Finset.Icc 1 e,
        (qPower (K := K) (-2 * (e : ℝ) / 3) *
          qPower (K := K) ((l : ℝ) / 3) * shellValue χκ ψbar e (l : ℤ)) •
          KPThreeShell.basis (-(e : ℤ) + 2 * (l : ℤ))) =
      qPower (K := K) (-2 * (e : ℝ) / 3) •
        ((1 - (Q⁻¹ : ℝ) : ℂ) •
          ∑ l ∈ (Finset.range (e + 1)).filter (fun l => 1 ≤ l ∧ 3 ∣ l),
            qPower (K := K) ((l : ℝ) / 3) •
              KPThreeShell.basis (-(e : ℤ) + 2 * (l : ℤ))) := by
    have hf : (Finset.range (e + 1)).filter (fun l => 1 ≤ l ∧ 3 ∣ l) =
        (Finset.Icc 1 e).filter (fun l => 3 ∣ l) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hf, Finset.sum_filter, Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hi l hl]
    split_ifs with hd
    · simp only [smul_smul]
      congr 1
      ring
    · simp
  rw [hs, ht]
  simp only [KPThreeShell.shell, qPower, Q, smul_add, smul_smul,
    Nat.cast_add, Nat.cast_one, mul_assoc]
  abel

end
end DedekindZetaZeroFree.KPExteriorActualJacquetShells
