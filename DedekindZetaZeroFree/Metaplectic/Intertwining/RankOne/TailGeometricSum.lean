module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.TailAbsoluteConvergence

@[expose] public section

set_option maxHeartbeats 4000000

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneShellRepair

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

private theorem actualShell_disjoint (m m' : ℤ) (h : m ≠ m') :
    Disjoint (actualShell F q m) (actualShell F q m') := by
  have hQ : (1 : ℝ) < (residueCardinality (LocalField F q) : ℝ) := by
    have hnat := KPJacquetExceptionalFactorSeparation.residue_cardinality_gt_one
      (K := LocalField F q)
    exact_mod_cast hnat
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [actualShell, Set.mem_setOf_eq] at hx hx'
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hx1', hx2'⟩ := hx'
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have hle : (residueCardinality (LocalField F q) : ℝ) ^ m ≤
        (residueCardinality (LocalField F q) : ℝ) ^ (m' - 1) :=
      zpow_le_zpow_right₀ hQ.le (by omega)
    linarith
  · have hle : (residueCardinality (LocalField F q) : ℝ) ^ (m - 1) ≥
        (residueCardinality (LocalField F q) : ℝ) ^ m' :=
      zpow_le_zpow_right₀ hQ.le (by omega)
    linarith

theorem actual_tail_geometric_sum (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∃ M : ℕ, ∀ (s : ℂ), convergenceHalfPlane ε s →
      ∀ (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
        (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
        denominator (LocalField F q) ε s *
          (∫ x in (⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ)),
            actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) =
          ∑ i : Fin 3, ∫ x in actualShell F q ((M + i.val : ℕ) : ℤ),
            actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ := by
  obtain ⟨M₁, hM₁⟩ := actual_tail_shell_step F ζ hζ q S P J hJ μ hμ π hπ ε
  obtain ⟨M₂, hM₂⟩ := actual_tail_absolute_convergence F ζ hζ q S P J hJ μ hμ π hπ ε
  refine ⟨max M₁ M₂, ?_⟩
  set M : ℕ := max M₁ M₂ with hM
  have hM₁M : M₁ ≤ M := by rw [hM]; exact le_max_left _ _
  have hM₂M : M₂ ≤ M := by rw [hM]; exact le_max_right _ _
  intro s hs φ k h
  have habs : Measurable (KPCubicHaar.abs (LocalField F q)) :=
    KPRamifiedBetaConductorSeries.normalizedAbs_measurable (LocalField F q)
  have hmeas : ∀ n : ℕ, MeasurableSet (actualShell F q ((M + n : ℕ) : ℤ)) := fun n =>
    (measurableSet_lt measurable_const habs).inter (measurableSet_le habs measurable_const)
  have hdisj : Pairwise (Function.onFun Disjoint fun n : ℕ =>
      actualShell F q ((M + n : ℕ) : ℤ)) := by
    intro a b hab
    exact actualShell_disjoint F q ((M + a : ℕ) : ℤ) ((M + b : ℕ) : ℤ) (fun hh =>
      hab (Nat.add_left_cancel (Nat.cast_injective hh)))
  have hInt₂ : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h)
      (⋃ n : ℕ, actualShell F q ((M₂ + n : ℕ) : ℤ)) μ := hM₂ s hs φ k h
  have hsub : (⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ)) ⊆
      (⋃ n : ℕ, actualShell F q ((M₂ + n : ℕ) : ℤ)) := by
    intro x hx
    simp only [Set.mem_iUnion] at hx ⊢
    obtain ⟨n, hn⟩ := hx
    refine ⟨M + n - M₂, ?_⟩
    have hcast : (M₂ + (M + n - M₂) : ℕ) = M + n := by omega
    rw [hcast]
    exact hn
  have hInt : IntegrableOn (actualStandardIntegrand F ζ hζ q S P ε s φ.val k h)
      (⋃ n : ℕ, actualShell F q ((M + n : ℕ) : ℤ)) μ := hInt₂.mono_set hsub
  have hsum := hasSum_integral_iUnion hmeas hdisj hInt
  rw [← hsum.tsum_eq]
  set A : ℕ → ℂ := fun n =>
    ∫ x in actualShell F q ((M + n : ℕ) : ℤ),
      actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ with hA
  have hsumA : Summable A := by rw [hA]; exact hsum.summable
  have hrec : ∀ n : ℕ, A (n + 3) = actualShellRatio F q ε s * A n := by
    intro n
    have hmn : M₁ ≤ M + n := le_trans hM₁M (Nat.le_add_right M n)
    have hstep := hM₁ (M + n) hmn s φ k h
    have hidx : ((M + (n + 3) : ℕ) : ℤ) = ((M + n : ℕ) : ℤ) + 3 := by push_cast; ring
    simp only [hA]
    rw [hidx]
    exact hstep
  have hsplit := hsumA.sum_add_tsum_nat_add 3
  have hA012 : (∑ i ∈ Finset.range 3, A i) = A 0 + A 1 + A 2 := by
    simp [Finset.sum_range_succ]
  have hB : (∑' i : ℕ, A (i + 3)) = actualShellRatio F q ε s * (∑' i : ℕ, A i) := by
    rw [← tsum_mul_left]
    exact tsum_congr hrec
  have hsplit' : (∑ i ∈ Finset.range 3, A i) +
      actualShellRatio F q ε s * (∑' i : ℕ, A i) = ∑' i : ℕ, A i := by
    rw [← hB]
    exact hsplit
  have hrel : (∑' i : ℕ, A i) = (A 0 + A 1 + A 2) +
      actualShellRatio F q ε s * (∑' i : ℕ, A i) := by
    have h1 := hsplit'
    rw [hA012] at h1
    exact h1.symm
  have hden : denominator (LocalField F q) ε s = 1 - actualShellRatio F q ε s := by
    simp only [denominator, actualShellRatio]
    by_cases hε : ε = Sign.plus <;> simp [hε]
  have hlin : (1 - actualShellRatio F q ε s) * (∑' i : ℕ, A i) = A 0 + A 1 + A 2 := by
    rw [sub_mul, one_mul, sub_eq_iff_eq_add]
    exact hrel
  have hgoal : denominator (LocalField F q) ε s * (∑' i : ℕ, A i) = A 0 + A 1 + A 2 := by
    rw [hden, hlin]
  have hfin : (∑ i : Fin 3, A i.val) = A 0 + A 1 + A 2 := by
    simp [Fin.sum_univ_three]
  simpa only [hA] using hgoal.trans hfin.symm

end DedekindZetaZeroFree.KPRankOneShellRepair

end
