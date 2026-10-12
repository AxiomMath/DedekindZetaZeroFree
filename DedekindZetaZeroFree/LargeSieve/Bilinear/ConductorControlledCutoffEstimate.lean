module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.OperatorBounds.NormalizedCubicKernelsAndLargeCutoffEnergy
public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.ConductorControlledRestriction

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical

theorem T3_eq_normalizedMasked_core
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hGood : CoreGood Q) (W : ℝ → ℝ)
    (M N K : ℝ) (d : Ideal (𝓞 F)) (g : Q.G)
    (lam : Ideal (𝓞 F) → ℂ) :
    let D := hGood.allIndexData hc
    T3 F c Q W M N K d g lam =
      NormalizedKernelProfiles.T3normalizedMasked F c Q D.bad W M N K d g
        (paperShell F c N) (fun _ => 1) lam := by
  have hrows : NormalizedKernelProfiles.normalizedKernelRows F c c M K = kernelRows F c M K := by
    ext a
    simp only [NormalizedKernelProfiles.normalizedKernelRows, kernelRows, Finset.mem_filter]
    tauto
  simp only [CoreGood.allIndexNormalizedFamilyData_bad]
  unfold T3 NormalizedKernelProfiles.T3normalizedMasked
  refine Finset.sum_congr rfl fun u hu => ?_
  refine Finset.sum_congr rfl fun v hv => ?_
  by_cases h0 : u ⊔ v = d ∧ Q.cls u = g ∧ Q.cls v = g
  · rw [if_pos h0, if_pos h0, if_pos hu, if_pos hv, hrows]
    simp only [one_mul, map_one, map_mul]
  · rw [if_neg h0, if_neg h0]

theorem B3_eq_normalizedMasked_core
    (F : Type) [Field F] [NumberField F]
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hGood : CoreGood Q) (W : ℝ → ℝ)
    (M N K : ℝ) (d : Ideal (𝓞 F)) :
    let D := hGood.allIndexData hc
    B3 F c Q W M N K d =
      NormalizedKernelProfiles.B3normalizedMasked F c Q D.bad W M N K d
        (paperShell F c N) (fun _ => 1) := by
  have hT : ∀ (g : Q.G) (lam : Ideal (𝓞 F) → ℂ),
      T3 F c Q W M N K d g lam =
        NormalizedKernelProfiles.T3normalizedMasked F c Q (hGood.allIndexData hc).bad W M N K d g
          (paperShell F c N) (fun _ => 1) lam :=
    fun g lam => T3_eq_normalizedMasked_core F c hc Q hGood W M N K d g lam
  unfold B3 NormalizedKernelProfiles.B3normalizedMasked
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | ⟨g, lam, he, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨g, lam, he, by rw [hT g lam]⟩
  · rintro (rfl | ⟨g, lam, he, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨g, lam, he, by rw [hT g lam]⟩

theorem bilinear_prop51_core
    {F : Type} [Field F] [NumberField F]
    (hF : NumberField.IsTotallyComplex F)
    (c : Ideal (𝓞 F)) (hc : c ≠ ⊥)
    (Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c)
    (hGood : CoreGood Q) (W : ℝ → ℝ) (hW : SieveWeight W)
    {α : ℝ} (hα₁ : 1 ≤ α) (hα₂ : α ≤ 2)
    (hE : HasSieveExponent F c Q α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ M N K : ℝ, 1 ≤ M → 1 ≤ N → 0 < K →
      N ^ 2 / M * Real.rpow (M * N) ε ≤ K →
      K ≤ M * Real.rpow (M * N) (-ε) →
      ∀ d : Ideal (𝓞 F), B3 F c Q W M N K d ≤
        C * ((Ideal.absNorm d : ℝ) ^ 4) * Real.rpow (M * N) ε *
          (M + N + Real.sqrt M * Real.rpow K (α - 1 / 2) +
            Real.sqrt (M / K) * N) := by
  intro ε hε
  obtain ⟨C, hC, H⟩ :=
    bilinear_prop51_core_normalized_masked hF Q (hGood.allIndexData hc) rfl
      W hW hα₁ hα₂ hE ε hε
  refine ⟨C, hC, ?_⟩
  intro M N K hM hN hK hK1 hK2 d
  rw [B3_eq_normalizedMasked_core F c hc Q hGood W M N K d]
  exact H M N K hM hN hK hK1 hK2 d (paperShell F c N) (fun _ => 1)
    (fun _ hx => hx) (fun _ => by simp)

end DedekindZetaZeroFree.LargeSieve.Sieve

end
