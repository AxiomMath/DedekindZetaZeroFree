module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.CoreGcdRestriction
public import DedekindZetaZeroFree.LargeSieve.Bilinear.WeightedIdealSectorGcdBound
public import DedekindZetaZeroFree.LargeSieve.Bilinear.ShellUnitEnvelopeComparison
public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisorIncidenceEnergy

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction
open scoped NumberField Classical

theorem core_coefficient_estimate
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hGood : CoreGood Q)
    (W : ℝ → ℝ) (hW : SieveWeight W)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N K H : ℝ, 1 ≤ M → 1 ≤ N → 0 < K → 1 ≤ H → H < N →
        ∀ lam : Ideal (𝓞 F) → ℂ,
          Q2 F c Q W M N K lam ≤
            (C * Real.rpow (M * N) δ *
              (B2env F c Q W M (N / H) K + M +
                ∑ d ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H).filter (fun d => d ≠ ⊥),
                  B3 F c Q W M N K d)) * energy F c N lam := by
  letI : Finite Q.G := Q.instFinite
  letI : Fintype Q.G := Fintype.ofFinite Q.G
  let ε := δ / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨A, hA, ha⟩ := DedekindZetaZeroFree.LargeSieve.bilinear_gcd_tail F c Q W hW c hc (dvd_refl c)
    (CoreCoefficient.gcdPairTransport hGood hc) ε hε
  obtain ⟨D, hD, hd⟩ := CoreCoefficient.divisor_incidence_sum F ε hε
  obtain ⟨U, hU, hu⟩ := CoreCoefficient.envelope_comparison F c Q W hW
  let J : ℝ := 1 + A * D * (1 + U)
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  refine ⟨(Fintype.card Q.G : ℝ) ^ 2 * J, by positivity, ?_⟩
  intro M N K H hM hN hK hH hHN lam
  have hM0 : 0 ≤ M := by linarith
  have hRε : 0 ≤ Real.rpow N ε := Real.rpow_nonneg (by linarith) ε
  have hNpos : 0 < N := by linarith
  have hHpos : 0 < H := by linarith
  have hY : 1 ≤ N / H := (le_div_iff₀ hHpos).mpr (by simpa using hHN.le)
  let pool := (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F (2 * N)).filter (fun d => d ≠ ⊥)
  let small := pool.filter (fun d => (Ideal.absNorm d : ℝ) ≤ H)
  let large := pool.filter (fun d => ¬ (Ideal.absNorm d : ℝ) ≤ H)
  let S : ℝ := ∑ d ∈ (DedekindZetaZeroFree.LargeSieve.boundedNormIdeals F H).filter (fun d => d ≠ ⊥),
    B3 F c Q W M N K d
  let B := B2env F c Q W M (N / H) K
  let E := energy F c N lam
  have hS : 0 ≤ S := Finset.sum_nonneg fun d _ => B3_nonneg Q W M N K d
  have hB : 0 ≤ B := by
    dsimp [B]; unfold B2env
    exact Real.sSup_nonneg' ⟨0, Or.inl (Or.inl rfl), le_rfl⟩
  have hE : 0 ≤ E := by dsimp [E, energy]; positivity
  have hp : ∀ b1 ∈ paperShell F c N, ∀ b2 ∈ paperShell F c N, b1 ⊔ b2 ∈ pool := by
    intro b1 hb1 b2 hb2
    have hb := (mem_paperShell F c N b1).mp hb1
    have hb0 : b1 ≠ ⊥ := by simpa [Ideal.zero_eq_bot] using hb.1.ne_zero
    have hp0 : b1 ⊔ b2 ≠ ⊥ := fun h => hb0 (le_bot_iff.mp (h ▸ le_sup_left))
    have hn : Ideal.absNorm (b1 ⊔ b2) ≤ Ideal.absNorm b1 :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hb0))
        (Ideal.absNorm_dvd_absNorm_of_le le_sup_left)
    exact Finset.mem_filter.mpr ⟨DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr
      ((Nat.cast_le.mpr hn).trans hb.2.2.2), hp0⟩
  let lam' : Ideal (𝓞 F) → ℂ := fun b => if b ∈ paperShell F c N then lam b else 0
  have hlam : ∀ b ∈ paperShell F c N, lam' b = lam b := by
    intro b hb; exact if_pos hb
  have henergy : energy F c N lam' = E := by
    unfold energy; exact Finset.sum_congr rfl fun b hb => by rw [hlam b hb]
  have htailenergy : ∀ d, gcdTailEnergy F c N d lam' = gcdTailEnergy F c N d lam := by
    intro d; unfold gcdTailEnergy
    exact Finset.sum_congr rfl fun b hb => by rw [hlam b hb]
  have hblock : ∀ d g, T3 F c Q W M N K d g lam' = T3 F c Q W M N K d g lam := by
    intro d g; unfold T3
    exact Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun b' hb' => by
      rw [hlam b hb, hlam b' hb']
  have hlarge : ∀ d ∈ large, ∀ g,
      ‖T3 F c Q W M N K d g lam‖ ≤
        A * Real.rpow N ε * (B + U * M) * gcdTailEnergy F c N d lam := by
    intro d hdlarge g
    obtain ⟨hdpool, hdH⟩ := Finset.mem_filter.mp hdlarge
    obtain ⟨hdnorm, hd0⟩ := Finset.mem_filter.mp hdpool
    have hdreal : 0 < (Ideal.absNorm d : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hd0)
    have hX : 0 < N / (Ideal.absNorm d : ℝ) := div_pos hNpos hdreal
    have hXY : N / (Ideal.absNorm d : ℝ) ≤ N / H :=
      div_le_div_of_nonneg_left hNpos.le hHpos (le_of_not_ge hdH)
    have hcomp := hu M (N / (Ideal.absNorm d : ℝ)) (N / H) K hM hX hY hXY hK
    have ht := ha M N K hM hN hK d hd0 (DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mp hdnorm)
      lam' (fun b hb => if_neg hb) g (fun _ => 1) (fun _ => 1)
      (fun _ => ⟨zero_le_one, le_rfl⟩) (fun _ => by simp)
    rw [← CoreCoefficient.T3_eq_maskedGcdBlock_core F c hc Q hGood,
      hblock d g, htailenergy d] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcomp (by positivity))
      (Finset.sum_nonneg fun b _ => by split_ifs <;> positivity))
  have hsmall : ∀ g, (∑ d ∈ small, ‖T3 F c Q W M N K d g lam‖) ≤ S * E := by
    intro g
    calc _ ≤ ∑ d ∈ small, B3 F c Q W M N K d * E :=
      Finset.sum_le_sum fun d _ => norm_T3_le_B3_mul_energy Q W M N K d g lam
      _ = (∑ d ∈ small, B3 F c Q W M N K d) * E := (Finset.sum_mul ..).symm
      _ ≤ S * E := by
        apply mul_le_mul_of_nonneg_right _ hE
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro d hds
          obtain ⟨hdp, hdH⟩ := Finset.mem_filter.mp hds
          exact Finset.mem_filter.mpr ⟨DedekindZetaZeroFree.LargeSieve.mem_boundedNormIdeals.mpr hdH,
            (Finset.mem_filter.mp hdp).2⟩
        · intro d _ _; exact B3_nonneg Q W M N K d
  have hlargeSum : ∀ g, (∑ d ∈ large, ‖T3 F c Q W M N K d g lam‖) ≤
      A * D * Real.rpow N δ * (B + U * M) * E := by
    intro g
    calc _ ≤ ∑ d ∈ large,
        (A * Real.rpow N ε * (B + U * M)) * gcdTailEnergy F c N d lam :=
          Finset.sum_le_sum fun d hd => hlarge d hd g
      _ = (A * Real.rpow N ε * (B + U * M)) *
          (∑ d ∈ large, gcdTailEnergy F c N d lam) := (Finset.mul_sum ..).symm
      _ ≤ (A * Real.rpow N ε * (B + U * M)) * (D * Real.rpow N ε * E) :=
          mul_le_mul_of_nonneg_left (hd c N hN large lam) (by positivity)
      _ = _ := by
        have hr : Real.rpow N ε * Real.rpow N ε = Real.rpow N δ := by
          change N ^ ε * N ^ ε = N ^ δ
          rw [← Real.rpow_add hNpos]; congr 1; dsimp [ε]; ring
        calc _ = A * D * (Real.rpow N ε * Real.rpow N ε) * (B + U * M) * E := by ring
          _ = _ := by rw [hr]
  have hr1 : 1 ≤ Real.rpow N δ := Real.one_le_rpow hN hδ.le
  have hsum : ∀ g, (∑ d ∈ pool, ‖T3 F c Q W M N K d g lam‖) ≤
      J * Real.rpow N δ * (B + M + S) * E := by
    intro g
    have hsplit : (∑ d ∈ pool, ‖T3 F c Q W M N K d g lam‖) =
        (∑ d ∈ small, ‖T3 F c Q W M N K d g lam‖) +
        (∑ d ∈ large, ‖T3 F c Q W M N K d g lam‖) :=
      (Finset.sum_filter_add_sum_filter_not pool _ _).symm
    rw [hsplit]
    have hT : 0 ≤ B + M + S := by positivity
    have hs : S ≤ Real.rpow N δ * (B + M + S) := by
      calc S ≤ B + M + S := by linarith
        _ ≤ Real.rpow N δ * (B + M + S) := le_mul_of_one_le_left hT hr1
    have hb : B + U * M ≤ (1 + U) * (B + M + S) := by
      nlinarith [mul_nonneg hU hB, mul_nonneg hU hS]
    calc (∑ d ∈ small, ‖T3 F c Q W M N K d g lam‖) +
          (∑ d ∈ large, ‖T3 F c Q W M N K d g lam‖)
        ≤ S * E + (A * D * Real.rpow N δ * (B + U * M)) * E :=
          add_le_add (hsmall g) (hlargeSum g)
      _ ≤ (Real.rpow N δ * (B + M + S)) * E +
          (A * D * Real.rpow N δ * ((1 + U) * (B + M + S))) * E := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hs hE
            · exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hb (by positivity)) hE
      _ = J * Real.rpow N δ * (B + M + S) * E := by dsimp [J]; ring
  have hsector := CoreCoefficient.sector_gcd_bound F c Q W hW M N K lam pool hp
  calc Q2 F c Q W M N K lam
      ≤ (Fintype.card Q.G : ℝ) * ∑ g, ∑ d ∈ pool, ‖T3 F c Q W M N K d g lam‖ := hsector
    _ ≤ (Fintype.card Q.G : ℝ) * ∑ g, J * Real.rpow N δ * (B + M + S) * E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g _ => hsum g) (Nat.cast_nonneg _)
    _ = (Fintype.card Q.G : ℝ) ^ 2 * J * Real.rpow N δ * (B + M + S) * E := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by
      have hr : Real.rpow N δ ≤ Real.rpow (M * N) δ :=
        Real.rpow_le_rpow hNpos.le (by nlinarith) hδ.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hr (by positivity)) (by positivity)) hE

end DedekindZetaZeroFree.LargeSieve.Sieve.GcdReduction

end
