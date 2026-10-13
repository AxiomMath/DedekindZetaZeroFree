module

public import DedekindZetaZeroFree.LFunctions.Dedekind.AbelianRayCharacterFactorization
public import DedekindZetaZeroFree.LFunctions.Hecke.RayCharacterEntireContinuation

@[expose] public section

namespace DedekindZetaZeroFree.HeckeCorollary

open scoped NumberField Topology
open Filter

theorem zetaFactorization_product_at_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ContinuousAt (f i) 1)
    (hfactor : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s =
        (∏ i, f i s) * NumberField.dedekindZeta K s) :
    (NumberField.dedekindZeta_residue L : ℂ) =
      (∏ i, f i 1) * (NumberField.dedekindZeta_residue K : ℂ) := by
  have hp : Tendsto (fun x : ℝ => ∏ i, f i (x : ℂ)) (𝓝[>] 1)
      (𝓝 (∏ i, f i 1)) := by
    apply tendsto_finsetProd
    intro i _
    exact (hf i).tendsto.comp
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hlim := hp.mul (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  apply tendsto_nhds_unique (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT L)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 1 < (x : ℂ).re := hx
  rw [hfactor (x : ℂ) hx']
  ring

theorem zetaFactorization_factor_one_ne_zero
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (hf : ∀ i, ContinuousAt (f i) 1)
    (hfactor : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s =
        (∏ i, f i s) * NumberField.dedekindZeta K s)
    (i : ι) : f i 1 ≠ 0 := by
  have hres : (NumberField.dedekindZeta_residue L : ℂ) ≠ 0 := by
    exact_mod_cast NumberField.dedekindZeta_residue_ne_zero L
  rw [zetaFactorization_product_at_one K L f hf hfactor] at hres
  exact (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hres).1) i (Finset.mem_univ i)

theorem abelianFactorization_entire_nonzero_at_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ) :
    ∃ (n : ℕ) (m : Fin n → Ideal (𝓞 K))
      (χ : (i : Fin n) → RayClassCharacter K (m i)) (f : Fin n → ℂ → ℂ),
      (∀ i, m i ≠ ⊥ ∧ ¬ (χ i).IsPrincipal) ∧
      (∀ i, Differentiable ℂ (f i)) ∧
      (∀ i s, 1 < s.re → HasSum (fun I : Ideal (𝓞 K) =>
        χ i I * (Ideal.absNorm I : ℂ) ^ (-s)) (f i s)) ∧
      (∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta L s =
        (∏ i, f i s) * NumberField.dedekindZeta K s) ∧
      (∀ i, f i 1 ≠ 0) := by
  obtain ⟨n, m, χ, hχ, hfactor⟩ := AbelianQuotient.abelianFactorization K L hcomm
  choose f hf hseries using fun i =>
    AbelianQuotient.rayCharacterEntire K (m i) (hχ i).1 (χ i) (hχ i).2
  have hfactor' : ∀ s : ℂ, 1 < s.re → NumberField.dedekindZeta L s =
      (∏ i, f i s) * NumberField.dedekindZeta K s := by
    intro s hs
    rw [hfactor s hs]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact (hseries i s hs).tsum_eq
  exact ⟨n, m, χ, f, hχ, hf, hseries, hfactor',
    zetaFactorization_factor_one_ne_zero K L f (fun i => (hf i).continuous.continuousAt)
      hfactor'⟩

end DedekindZetaZeroFree.HeckeCorollary
