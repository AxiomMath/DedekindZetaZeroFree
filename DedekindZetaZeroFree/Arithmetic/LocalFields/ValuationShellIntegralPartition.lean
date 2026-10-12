module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.SphericalTruncations

@[expose] public section

open scoped NumberField Valued ValuativeRel BigOperators
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExteriorActualJacquetShells

open KPLocalExceptionalConstruction KPExteriorActualJacquetShellsRaw

noncomputable section
set_option autoImplicit false

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
 def B (p : K) (k : ℤ) : Set K := {x | ∃ u : (valuation K).integer, x = p ^ k * (u : K)}
 def S (p : K) (k : ℤ) : Set K := {x | ∃ u ∈ KPTameGauss.integerUnitShell K, x = p ^ k * u}
private lemma B_mem (p : K) (hp : p ≠ 0) (k : ℤ) (x : K) :
    x ∈ B p k ↔ p ^ (-k) * x ∈ ((valuation K).integer : Set K) := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [← mul_assoc, ← zpow_add₀ hp, neg_add_cancel, zpow_zero, one_mul]
    exact u.property
  · intro hx
    refine ⟨⟨p ^ (-k) * x, hx⟩, ?_⟩
    rw [← mul_assoc, ← zpow_add₀ hp, add_neg_cancel, zpow_zero, one_mul]
private lemma B_measurable (p : K) (hp : p ≠ 0) (k : ℤ) : MeasurableSet (B p k) := by
  have he : B p k = (fun x : K => p ^ (-k) * x) ⁻¹' ((valuation K).integer : Set K) := by
    ext x; exact B_mem p hp k x
  rw [he]
  exact (valuation K).isClosed_integer.measurableSet.preimage (by fun_prop)
private lemma parts (π : (valuation K).integer) (hπ : Irreducible π) (k : ℤ) :
    B (π : K) k = B (π : K) (k + 1) ∪ S (π : K) k ∧
    Disjoint (B (π : K) (k + 1)) (S (π : K) k) := by
  have hp : (π : K) ≠ 0 := by intro h; exact hπ.ne_zero (Subtype.ext h)
  have hval : valuation K (π : K) < 1 :=
    (Valuation.integer.integers (valuation K)).valuation_irreducible_lt_one hπ
  constructor
  · ext x
    constructor
    · rintro ⟨u, rfl⟩
      by_cases hu : IsUnit u
      · exact Or.inr ⟨u, ⟨u, rfl, hu⟩, rfl⟩
      · have hd : π ∣ u := by
          have hm : u ∈ IsLocalRing.maximalIdeal ((valuation K).integer) := hu
          rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨w, rfl⟩ := hd
        left
        refine ⟨w, ?_⟩
        simp [zpow_add₀ hp, mul_assoc]
    · rintro (⟨u, rfl⟩ | ⟨u, ⟨w, rfl, hw⟩, rfl⟩)
      · refine ⟨π * u, ?_⟩
        simp [zpow_add₀ hp, mul_assoc]
      · exact ⟨w, rfl⟩
  · apply Set.disjoint_left.mpr
    rintro x ⟨u, hx⟩ ⟨w, ⟨t, rfl, ht⟩, hx'⟩
    have he : (π : K) * (u : K) = (t : K) := by
      have he := hx.symm.trans hx'
      rw [zpow_add₀ hp, zpow_one, mul_assoc] at he
      exact mul_left_cancel₀ (zpow_ne_zero _ hp) he
    have htval : valuation K (t : K) = 1 :=
      (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp ht
    have hv : valuation K ((π : K) * (u : K)) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le u.property) hval
    rw [he, htval] at hv
    exact (lt_irrefl _ hv)
private lemma S_measurable (π : (valuation K).integer) (hπ : Irreducible π) (k : ℤ) :
    MeasurableSet (S (π : K) k) := by
  have hp : (π : K) ≠ 0 := by intro h; exact hπ.ne_zero (Subtype.ext h)
  have he : S (π : K) k = B (π : K) k \ B (π : K) (k+1) := by
    rw [(parts π hπ k).1]
    ext x
    have hd := Set.disjoint_left.mp (parts π hπ k).2
    simp only [Set.mem_diff, Set.mem_union]
    constructor
    · intro hx; exact ⟨Or.inr hx, fun hb => hd hb hx⟩
    · rintro ⟨h | h, hn⟩
      · exact (hn h).elim
      · exact h
  rw [he]
  exact (B_measurable _ hp k).diff (B_measurable _ hp (k+1))
private lemma integral_partition {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure K) (π : (valuation K).integer) (hπ : Irreducible π)
    (f : K → V) (e : ℤ) (n : ℕ) (hf : IntegrableOn f (B (π : K) (e - n)) μ) :
    (∫ x in B (π : K) (e - n), f x ∂μ) =
      (∫ x in B (π : K) e, f x ∂μ) +
        ∑ l ∈ Finset.Icc 1 n, ∫ x in S (π : K) (e - l), f x ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hk : e - ((n + 1 : ℕ) : ℤ) + 1 = e - n := by omega
    have hu := (parts π hπ (e - ((n + 1 : ℕ) : ℤ))).1
    rw [hk] at hu
    have hf' := hf
    rw [hu] at hf'
    rw [hu, setIntegral_union]
    · rw [ih hf'.left_of_union]
      rw [Finset.sum_Icc_succ_top (by omega)]
      exact add_assoc _ _ _
    · have hd := (parts π hπ (e - ((n + 1 : ℕ) : ℤ))).2
      rw [hk] at hd
      exact hd
    · exact S_measurable π hπ _
    · exact hf'.left_of_union
    · exact hf'.right_of_union

theorem spherical_partition_integral
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure (LocalField F v))
    (π : (valuation (LocalField F v)).integer) (hπ : Irreducible π)
    (f : LocalField F v → V) (e R : ℕ)
    (hf : IntegrableOn f (truncationBall F v π R) μ) :
    (∫ x in truncationBall F v π R, f x ∂μ) =
      (∫ x in sphericalBall F v π e, f x ∂μ) +
        ∑ l ∈ Finset.Icc 1 (R + e),
          ∫ x in sphericalShell F v π e (l : ℤ), f x ∂μ := by
  have hk : (e : ℤ) - ((R + e : ℕ) : ℤ) = -(R : ℤ) := by omega
  have h := integral_partition μ π hπ f (e : ℤ) (R + e) (by
    simpa only [hk, B, truncationBall] using hf)
  simpa only [hk, B, S, zpow_natCast, truncationBall, sphericalBall, sphericalShell] using h

end
end DedekindZetaZeroFree.KPExteriorActualJacquetShells
