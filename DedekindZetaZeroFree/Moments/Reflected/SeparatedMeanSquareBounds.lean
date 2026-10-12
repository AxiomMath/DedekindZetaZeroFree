module

public import DedekindZetaZeroFree.Theta.Profiles.GaussianContourKernel
public import DedekindZetaZeroFree.Moments.Reflected.BoundedNormExpansionBounds
public import DedekindZetaZeroFree.Moments.Reflected.BalancedDyadicRowTransfer

@[expose] public section

section

namespace DedekindZetaZeroFree.ReflectedMomentSubpowerMajorants
noncomputable section
open scoped NumberField BigOperators Classical

variable {F : Type} [Field F] [NumberField F]

theorem dyadic_square_mass_of_pointwise (A : SArithmeticData F)
    (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P D W : ℝ), 1 ≤ P → 1 ≤ D → 0 ≤ W →
      ∀ f : A.Exterior → ExteriorSquarefreeIdeal A.cS → ℂ,
        (∀ h : A.Exterior, h ∈ exteriorPowerfulDyad A.cS P →
          ∀ d : ExteriorSquarefreeIdeal A.cS, d ∈ RMRetainedAggregation.rowDyad A h D →
            ‖f h d‖ ≤ A.exteriorNorm h ^ b * W) →
        (∑' h : exteriorPowerfulDyad A.cS P,
          ∑' d : RMRetainedAggregation.rowDyad A h.val D,
            ‖f h.val d.val‖ ^ 2) ≤
          C * P ^ ((1 / 2 : ℝ) + 2 * b) * D * W ^ 2 := by
  obtain ⟨K, hK, hpower⟩ := exterior_powerful_dyad_count_bound F
  obtain ⟨L, L', hL, _, hcount⟩ := ideal_counting_harmonic_bounds F
  refine ⟨K * (2 * L) * (2 : ℝ) ^ (2 * b), by positivity, ?_⟩
  intro P D W hP hD hW f hf
  have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hP
  let M : ℝ := (2 * P) ^ (2 * b) * W ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpoint (h : exteriorPowerfulDyad A.cS P)
      (d : RMRetainedAggregation.rowDyad A h.val D) :
      ‖f h.val d.val‖ ^ 2 ≤ M := by
    have hn : A.exteriorNorm h.val ^ b ≤ (2 * P) ^ b :=
      Real.rpow_le_rpow
        (by have := idealNorm_ge_one h.val.val h.val.property.1; linarith)
        h.property.2.2.le hb.le
    have he : ‖f h.val d.val‖ ≤ (2 * P) ^ b * W :=
      (hf h.val h.property d.val d.property).trans
        (mul_le_mul_of_nonneg_right hn hW)
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr he
    simpa only [M, mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * P),
      Nat.cast_ofNat, mul_comm b (2 : ℝ)] using hs
  have hrowcard (h : A.Exterior) :
      ((RMRetainedAggregation.rowDyad A h D).ncard : ℝ) ≤ 2 * L * D := by
    let g : ExteriorSquarefreeIdeal A.cS → NonzeroIdeal F :=
      fun d => ⟨d.val.val, d.val.property.1⟩
    have hc : (RMRetainedAggregation.rowDyad A h D).ncard ≤
        (normBoundedIdeals F (2 * D)).ncard := by
      apply Set.ncard_le_ncard_of_injOn g
        (ht := normBoundedIdeals_finite F (2 * D))
      · intro d hd
        exact hd.2.1.le
      · intro d _ e _ hde
        exact Subtype.ext (Subtype.ext
          (congrArg (fun i : NonzeroIdeal F => i.val) hde))
    have hbnd : ((normBoundedIdeals F (2 * D)).ncard : ℝ) ≤ L * (2 * D) := by
      simpa using (hcount Set.univ).1 (2 * D) (by linarith)
    calc
      ((RMRetainedAggregation.rowDyad A h D).ncard : ℝ) ≤
          ((normBoundedIdeals F (2 * D)).ncard : ℝ) := by exact_mod_cast hc
      _ ≤ L * (2 * D) := hbnd
      _ = 2 * L * D := by ring
  letI := (exteriorPowerfulDyad_finite A.cS P).fintype
  letI (h : exteriorPowerfulDyad A.cS P) :=
    (RMRetainedAggregation.rowDyad_finite A h.val D).fintype
  have hrow (h : exteriorPowerfulDyad A.cS P) :
      (∑' d : RMRetainedAggregation.rowDyad A h.val D,
        ‖f h.val d.val‖ ^ 2) ≤ (2 * L * D) * M := by
    calc
      (∑' d : RMRetainedAggregation.rowDyad A h.val D,
          ‖f h.val d.val‖ ^ 2) ≤ ∑' _d : RMRetainedAggregation.rowDyad A h.val D, M := by
        simp only [tsum_fintype]
        exact Finset.sum_le_sum (fun d _ => hpoint h d)
      _ = ((RMRetainedAggregation.rowDyad A h.val D).ncard : ℝ) * M := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
      _ ≤ (2 * L * D) * M := mul_le_mul_of_nonneg_right (hrowcard h.val) hM
  have hcard : (Fintype.card (exteriorPowerfulDyad A.cS P) : ℝ) ≤ K * Real.sqrt P := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
      hpower A.cS A.cS_ne_zero P hP
  calc
    (∑' h : exteriorPowerfulDyad A.cS P,
        ∑' d : RMRetainedAggregation.rowDyad A h.val D,
          ‖f h.val d.val‖ ^ 2) ≤
        ∑' _h : exteriorPowerfulDyad A.cS P, (2 * L * D) * M := by
      simp only [tsum_fintype]
      exact Finset.sum_le_sum (fun h _ => by simpa only [tsum_fintype] using hrow h)
    _ = (Fintype.card (exteriorPowerfulDyad A.cS P) : ℝ) * ((2 * L * D) * M) := by
      simp [tsum_fintype, nsmul_eq_mul]
    _ ≤ (K * Real.sqrt P) * ((2 * L * D) * M) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (K * (2 * L) * (2 : ℝ) ^ (2 * b)) *
        P ^ ((1 / 2 : ℝ) + 2 * b) * D * W ^ 2 := by
      dsimp [M]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP0.le,
        Real.sqrt_eq_rpow, Real.rpow_add hP0]
      ring

end
end DedekindZetaZeroFree.ReflectedMomentSubpowerMajorants

end

section

namespace DedekindZetaZeroFree.ReflectedMomentSubpowerMajorants
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch ThetaPhaseSeparation RMSeparatedExpansion

variable {F : Type} [Field F] [NumberField F]

theorem joint_subpower_majorant (A : SArithmeticData F) (b : ℝ) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ h : A.Exterior, Powerful h.val →
      (Summable fun i : Index A h => positiveRowWeight (activeSupport A i.1.val) 1
        (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ∧
      (∑' i : Index A h, positiveRowWeight (activeSupport A i.1.val) 1
        (⟨i.1.val.a, i.1.val.a_supported⟩, i.2, i.1.val.n)) ≤
        K * A.exteriorNorm h ^ b := by
  obtain ⟨K, hK, hbound⟩ := RMTailCutoff.Reindex.jointWeight_subpower A b hb
  exact ⟨K, hK, fun h _ => hbound h⟩

end
end DedekindZetaZeroFree.ReflectedMomentSubpowerMajorants

end

section

namespace DedekindZetaZeroFree.ReflectedMoment
noncomputable section
open scoped NumberField BigOperators Classical
open ThetaBranch

variable {F : Type} [Field F] [NumberField F]

def separatedSquareMass (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (Z P D : ℝ) : ℝ :=
  ∑' h : exteriorPowerfulDyad A.cS P,
    ∑' d : RMRetainedAggregation.rowDyad A h.val D,
      ‖RMSeparatedExpansion.expansion A G U σ ψ L H h.val d.val.val Z‖ ^ 2

theorem cutoff_eq_threshold (Z P D θ : ℝ) :
    RMRetainedAggregation.cutoff Z P D θ = RMTailCutoff.threshold Z P D θ := by
  unfold RMRetainedAggregation.cutoff RMTailCutoff.threshold RMTailCutoff.length
  change 8 * Z ^ θ * D ^ 2 * P / Z = Z ^ θ * (8 * D ^ 2 * P / Z)
  ring

theorem retained_eq (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (h d : A.Exterior) (Z P D θ : ℝ) :
    RMRetainedAggregation.retained A G U σ ψ L H h d Z
        (RMRetainedAggregation.cutoff Z P D θ) =
      RMTailCutoff.retained A G U σ ψ L H h d Z P D θ := by
  rw [RMRetainedAggregation.retained_eq_tsum, cutoff_eq_threshold]
  rfl

theorem expansion_square_le (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (h d : A.Exterior) (Z P D θ : ℝ) :
    ‖RMSeparatedExpansion.expansion A G U σ ψ L H h d Z‖ ^ 2 ≤
      2 * ‖RMRetainedAggregation.retained A G U σ ψ L H h d Z
          (RMRetainedAggregation.cutoff Z P D θ)‖ ^ 2 +
        2 * ‖RMTailCutoff.tail A G U σ ψ L H h d Z P D θ‖ ^ 2 := by
  classical
  by_cases hs : Summable (fun i : RMSeparatedExpansion.Index A h =>
      RMSeparatedExpansion.summand A G U σ ψ L H i.1.val d i.2 Z)
  · have he : RMSeparatedExpansion.expansion A G U σ ψ L H h d Z =
        RMTailCutoff.retained A G U σ ψ L H h d Z P D θ +
          RMTailCutoff.tail A G U σ ψ L H h d Z P D θ := by
      have hr := hs.indicator {i | RMTailCutoff.frozenNorm A i.1.val i.2 ≤
        RMTailCutoff.threshold Z P D θ}
      have ht := hs.indicator {i | RMTailCutoff.threshold Z P D θ <
        RMTailCutoff.frozenNorm A i.1.val i.2}
      have he := hr.tsum_add ht
      simp only [Set.indicator_apply, Set.mem_setOf_eq] at he
      unfold RMSeparatedExpansion.expansion RMTailCutoff.retained RMTailCutoff.tail
      rw [← he]
      apply tsum_congr
      intro i
      by_cases hi : RMTailCutoff.frozenNorm A i.1.val i.2 ≤
          RMTailCutoff.threshold Z P D θ
      · simp [hi, not_lt.mpr hi]
      · simp [hi, lt_of_not_ge hi]
    rw [he, retained_eq]
    have hn := norm_add_le (RMTailCutoff.retained A G U σ ψ L H h d Z P D θ)
      (RMTailCutoff.tail A G U σ ψ L H h d Z P D θ)
    have hsq := sq_nonneg (‖RMTailCutoff.retained A G U σ ψ L H h d Z P D θ‖ -
      ‖RMTailCutoff.tail A G U σ ψ L H h d Z P D θ‖)
    have hn0 := norm_nonneg (RMTailCutoff.retained A G U σ ψ L H h d Z P D θ +
      RMTailCutoff.tail A G U σ ψ L H h d Z P D θ)
    nlinarith [norm_nonneg (RMTailCutoff.retained A G U σ ψ L H h d Z P D θ),
      norm_nonneg (RMTailCutoff.tail A G U σ ψ L H h d Z P D θ)]
  · rw [RMSeparatedExpansion.expansion, tsum_eq_zero_of_not_summable hs, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem separatedSquareMass_le (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (Z P D θ : ℝ) :
    separatedSquareMass A G U σ ψ L H Z P D ≤
      2 * RMRetainedAggregation.totalSquareMass A G U σ ψ L H Z P D
          (RMRetainedAggregation.cutoff Z P D θ) +
        2 * (∑' h : exteriorPowerfulDyad A.cS P,
          ∑' d : RMRetainedAggregation.rowDyad A h.val D,
            ‖RMTailCutoff.tail A G U σ ψ L H h.val d.val.val Z P D θ‖ ^ 2) := by
  letI := (exteriorPowerfulDyad_finite A.cS P).fintype
  have hrow : ∀ h : exteriorPowerfulDyad A.cS P,
      (∑' d : RMRetainedAggregation.rowDyad A h.val D,
        ‖RMSeparatedExpansion.expansion A G U σ ψ L H h.val d.val.val Z‖ ^ 2) ≤
      2 * RMRetainedAggregation.rowSquareMass A G U σ ψ L H h.val Z D
          (RMRetainedAggregation.cutoff Z P D θ) +
        2 * (∑' d : RMRetainedAggregation.rowDyad A h.val D,
          ‖RMTailCutoff.tail A G U σ ψ L H h.val d.val.val Z P D θ‖ ^ 2) := by
    intro h
    letI := (RMRetainedAggregation.rowDyad_finite A h.val D).fintype
    calc
      _ ≤ ∑' d : RMRetainedAggregation.rowDyad A h.val D,
          (2 * ‖RMRetainedAggregation.retained A G U σ ψ L H h.val d.val.val Z
            (RMRetainedAggregation.cutoff Z P D θ)‖ ^ 2 +
            2 * ‖RMTailCutoff.tail A G U σ ψ L H h.val d.val.val Z P D θ‖ ^ 2) :=
        Summable.tsum_le_tsum (fun d => expansion_square_le A G U σ ψ L H
          h.val d.val.val Z P D θ) (Summable.of_finite) (Summable.of_finite)
      _ = _ := by
        rw [Summable.tsum_add (Summable.of_finite) (Summable.of_finite),
          tsum_mul_left, tsum_mul_left]
        simp only [RMRetainedAggregation.rowSquareMass, finsum_eq_sum_of_fintype, tsum_fintype]
  calc
    _ ≤ ∑' h : exteriorPowerfulDyad A.cS P,
        (2 * RMRetainedAggregation.rowSquareMass A G U σ ψ L H h.val Z D
          (RMRetainedAggregation.cutoff Z P D θ) +
        2 * (∑' d : RMRetainedAggregation.rowDyad A h.val D,
          ‖RMTailCutoff.tail A G U σ ψ L H h.val d.val.val Z P D θ‖ ^ 2)) :=
      Summable.tsum_le_tsum hrow (Summable.of_finite) (Summable.of_finite)
    _ = _ := by
      rw [Summable.tsum_add (Summable.of_finite) (Summable.of_finite),
        tsum_mul_left, tsum_mul_left]
      simp only [RMRetainedAggregation.totalSquareMass, finsum_eq_sum_of_fintype, tsum_fintype]

theorem compact_separated_square_bound
    (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (M Cstar ε : ℝ) (hM : 1 < M) (hCstar : 0 < Cstar) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : A.UnitQuotient) (Z P D : ℝ),
      1 ≤ Z → Z ≤ 2 → 1 ≤ P → 1 ≤ D → P * D ≤ Cstar * Z ^ M →
      separatedSquareMass A G U σ ψ (L u) (H u) Z P D ≤
        K * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
  obtain ⟨K, hK, hk⟩ := RMParameterAbsorption.compact_expansion_square_bound
    A G U σ ψ hψ L hL H hH M Cstar hM hCstar
  refine ⟨K, hK, ?_⟩
  intro u Z P D hZ hZ2 hP hD hPD
  have hb : separatedSquareMass A G U σ ψ (L u) (H u) Z P D ≤
      K * Real.sqrt P * D := hk Z P D hZ hZ2 hP hD hPD u
  have hzpow : 1 ≤ Z ^ ε := Real.one_le_rpow hZ hε.le
  have hD' : D ≤ D + D ^ 2 * P / Z := by
    have : 0 ≤ D ^ 2 * P / Z := by positivity
    linarith
  calc
    _ ≤ K * Real.sqrt P * D := hb
    _ = K * 1 * Real.sqrt P * D := by ring
    _ ≤ _ := by gcongr

theorem separated_mean_square_bound_of_tail
    (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : RMRetainedAggregation.QuadraticFamilyCompatibility A G σ 𝓕)
    (htail : ∀ (B b : ℝ), 1 < B → 0 < b →
      ∃ K : ℝ, 0 < K ∧ ∀ (u : A.UnitQuotient) (Z P D θ : ℝ),
        2 ≤ Z → 1 ≤ P → 1 ≤ D → 0 < θ →
        (∑' h : exteriorPowerfulDyad A.cS P,
          ∑' d : RMRetainedAggregation.rowDyad A h.val D,
            ‖RMTailCutoff.tail A G U σ ψ (L u) (H u) h.val d.val.val Z P D θ‖ ^ 2) ≤
          K * P ^ ((1 / 2 : ℝ) + 2 * b) * D * RMTailCutoff.length Z P D ^ 2 *
            RMTailCutoff.gain Z P D θ ^ (-2 * (B - 1)))
    (M Cstar ε : ℝ) (hM : 1 < M) (hCstar : 0 < Cstar) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : A.UnitQuotient) (Z P D : ℝ),
      1 ≤ Z → 1 ≤ P → 1 ≤ D → P * D ≤ Cstar * Z ^ M →
      separatedSquareMass A G U σ ψ (L u) (H u) Z P D ≤
        K * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
  obtain ⟨θ, b₁, b₂, b₃, b, B, Ka, hθ, hb₁, hb₂, hb₃, hb, hB, hKa,
    _, _, ha⟩ := RMParameterAbsorption.scalar_parameter_absorption M Cstar ε hM hCstar hε
  obtain ⟨Kr, hKr, hr⟩ := RMRetainedAggregation.retained_total_square_bound
    A G U σ ψ hψ L hL H hH 𝓕 h𝓕 b₁ b₂ hb₁ hb₂
  obtain ⟨Kt, hKt, ht⟩ := htail B b hB hb
  obtain ⟨Kc, hKc, hc⟩ := compact_separated_square_bound A G U σ ψ hψ
    L hL H hH M Cstar ε hM hCstar hε
  refine ⟨Kc + 2 * (Kr + Kt) * Ka, by positivity, ?_⟩
  intro u Z P D hZ hP hD hPD
  have hscale : 0 ≤ Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by positivity
  by_cases hZ2 : 2 ≤ Z
  · have ha' := ha Z P D hZ2 hP hD hPD
    have hret : RMRetainedAggregation.totalSquareMass A G U σ ψ (L u) (H u)
        Z P D (RMRetainedAggregation.cutoff Z P D θ) ≤
        Kr * Ka * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
      by_cases hR : 1 ≤ RMRetainedAggregation.cutoff Z P D θ
      · have habs := ha'.1
        rw [← cutoff_eq_threshold] at habs
        calc
          _ ≤ Kr * (P ^ ((1 / 2 : ℝ) + 2 * b₁) *
              Real.log (2 * RMRetainedAggregation.cutoff Z P D θ) ^ 4 *
              (D + RMRetainedAggregation.cutoff Z P D θ) *
              (D * RMRetainedAggregation.cutoff Z P D θ) ^ b₂) := by
            simpa only [Real.rpow_eq_pow, mul_assoc] using hr u Z P D θ hZ2 hP hD hθ hR
          _ ≤ Kr * (Ka * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) :=
            mul_le_mul_of_nonneg_left (habs hR) hKr.le
          _ = _ := by ring
      · have hzero : RMRetainedAggregation.totalSquareMass A G U σ ψ (L u) (H u)
            Z P D (RMRetainedAggregation.cutoff Z P D θ) = 0 := by
          unfold RMRetainedAggregation.totalSquareMass RMRetainedAggregation.rowSquareMass
          simp only [RMRetainedAggregation.retained_eq_zero_of_cutoff_lt_one A G U σ ψ
            (L u) (H u) _ _ _ _ (lt_of_not_ge hR), norm_zero,
            zero_pow (by decide : 2 ≠ 0), finsum_zero]
        rw [hzero]
        positivity
    have htail' : (∑' h : exteriorPowerfulDyad A.cS P,
        ∑' d : RMRetainedAggregation.rowDyad A h.val D,
          ‖RMTailCutoff.tail A G U σ ψ (L u) (H u) h.val d.val.val Z P D θ‖ ^ 2) ≤
        Kt * Ka * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
      have hD' : D ≤ D + D ^ 2 * P / Z := by
        have : 0 ≤ D ^ 2 * P / Z := by positivity
        linarith
      calc
        _ ≤ Kt * (P ^ ((1 / 2 : ℝ) + 2 * b) * D * RMTailCutoff.length Z P D ^ 2 *
            RMTailCutoff.gain Z P D θ ^ (-2 * (B - 1))) := by
          simpa only [mul_assoc] using ht u Z P D θ hZ2 hP hD hθ
        _ ≤ Kt * (Ka * Z ^ ε * Real.sqrt P * D) :=
          mul_le_mul_of_nonneg_left ha'.2 hKt.le
        _ ≤ Kt * (Ka * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) := by gcongr
        _ = _ := by ring
    calc
      _ ≤ 2 * RMRetainedAggregation.totalSquareMass A G U σ ψ (L u) (H u) Z P D
          (RMRetainedAggregation.cutoff Z P D θ) +
          2 * (∑' h : exteriorPowerfulDyad A.cS P,
            ∑' d : RMRetainedAggregation.rowDyad A h.val D,
              ‖RMTailCutoff.tail A G U σ ψ (L u) (H u) h.val d.val.val Z P D θ‖ ^ 2) :=
        separatedSquareMass_le A G U σ ψ (L u) (H u) Z P D θ
      _ ≤ 2 * (Kr * Ka * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) +
          2 * (Kt * Ka * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) := by gcongr
      _ = 2 * (Kr + Kt) * Ka *
          (Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) := by ring
      _ ≤ (Kc + 2 * (Kr + Kt) * Ka) *
          (Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) := by
        apply mul_le_mul_of_nonneg_right (by nlinarith [mul_pos (add_pos hKr hKt) hKa]) hscale
      _ = _ := by ring
  · calc
      _ ≤ Kc * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) :=
        hc u Z P D hZ (le_of_not_ge hZ2) hP hD hPD
      _ = Kc * (Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) := by ring
      _ ≤ (Kc + 2 * (Kr + Kt) * Ka) *
          (Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z)) := by
        apply mul_le_mul_of_nonneg_right (by nlinarith [mul_pos (add_pos hKr hKt) hKa]) hscale
      _ = _ := by ring

theorem separated_mean_square_bound
    (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : ThetaBranch.UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p : ExteriorPrime A, (ψ p).IsPrimitive)
    (L : A.UnitQuotient → Fˣ →* ℂ)
    (hL : ∀ (u : A.UnitQuotient) (x : Fˣ), ‖L u x‖ = 1)
    (H : A.UnitQuotient → A.V → ℝ → ℂ)
    (hH : RMSeparatedExpansion.FiniteProfileFamily A H)
    (𝓕 : QuadraticHeckeFamily F A.cS)
    (h𝓕 : RMRetainedAggregation.QuadraticFamilyCompatibility A G σ 𝓕)
    (M Cstar ε : ℝ) (hM : 1 < M) (hCstar : 0 < Cstar) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : A.UnitQuotient) (Z P D : ℝ),
      1 ≤ Z → 1 ≤ P → 1 ≤ D → P * D ≤ Cstar * Z ^ M →
      separatedSquareMass A G U σ ψ (L u) (H u) Z P D ≤
        K * Z ^ ε * Real.sqrt P * (D + D ^ 2 * P / Z) := by
  apply separated_mean_square_bound_of_tail A G U σ ψ hψ L hL H hH 𝓕 h𝓕
    _ M Cstar ε hM hCstar hε
  intro B b hB hb
  obtain ⟨Kj, hKj, hj⟩ := ReflectedMomentSubpowerMajorants.joint_subpower_majorant A b hb
  obtain ⟨Kt, hKt, ht⟩ := RMTailCutoff.numerical_tail_from_joint_majorant
    A G U σ ψ hψ L hL H hH B b hB Kj hKj hj
  obtain ⟨Cc, hCc, hc⟩ := ReflectedMomentSubpowerMajorants.dyadic_square_mass_of_pointwise A b hb
  refine ⟨Cc * Kt ^ 2, by positivity, ?_⟩
  intro u Z P D θ hZ hP hD hθ
  have hZ0 : 0 < Z := by linarith
  have hl : 0 < RMTailCutoff.length Z P D := by
    unfold RMTailCutoff.length
    positivity
  have hg : 0 < RMTailCutoff.gain Z P D θ :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hZ0 θ) (le_max_left _ _)
  have hpoint := hc P D
    (Kt * RMTailCutoff.length Z P D *
      RMTailCutoff.gain Z P D θ ^ (-(B - 1))) hP hD (by positivity)
    (fun h d => RMTailCutoff.tail A G U σ ψ (L u) (H u) h d.val Z P D θ)
    (by
      intro h hh d hd
      have hd' : d ∈ RMTailCutoff.rowDyad A h D := hd
      have ht' := ht Z P D θ hZ hP hD hθ h hh d hd' u
      simpa only [mul_assoc, mul_left_comm, mul_comm] using ht')
  calc
    _ ≤ Cc * P ^ ((1 / 2 : ℝ) + 2 * b) * D *
        (Kt * RMTailCutoff.length Z P D *
          RMTailCutoff.gain Z P D θ ^ (-(B - 1))) ^ 2 := hpoint
    _ = _ := by
      rw [mul_pow, mul_pow,
        ← Real.rpow_two (RMTailCutoff.gain Z P D θ ^ (-(B - 1))),
        ← Real.rpow_mul hg.le (-(B - 1)) 2]
      rw [show -(B - 1) * (2 : ℝ) = -2 * (B - 1) by ring]
      ring

end
end DedekindZetaZeroFree.ReflectedMoment

end
