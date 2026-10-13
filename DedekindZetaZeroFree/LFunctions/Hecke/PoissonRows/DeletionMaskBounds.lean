module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyData
public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencyCount

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawDeletionMask31

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation
open DedekindZetaZeroFree.Quantitative.RawFixed
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem rawDeletionSet_subset (R : PrincipalMellin.ActualRecipe S η)
    (U : AllRowEuler.InitialSeparation.RawFrequency R.A) :
    RawHeckeRows.rawDeletionSet U ⊆
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ∪
        Detector.exteriorFrequencyPrimeSupport F
          (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) U.u := by
  intro v hv
  by_cases hvS : v ∈ R.A.Sf
  · exact Or.inl (Finset.mem_coe.mpr hvS)
  · have hv' : U.ideal.val ≤ v.asIdeal := by
      rcases hv with h | h
      · exact absurd (Finset.mem_coe.mp h) hvS
      · exact h
    refine Or.inr ⟨by simpa only [Finset.mem_coe] using hvS, ?_⟩
    let M : Ideal R.A.R :=
      { carrier := {x | v.valuation F (x : F) < 1}
        zero_mem' := by simp
        add_mem' := by
          intro x y hx hy
          refine lt_of_le_of_lt (by
            simpa only [Subalgebra.coe_add] using
              Valuation.map_add (v.valuation F) (x : F) (y : F)) (max_lt hx hy)
        smul_mem' := by
          intro x y hy
          show v.valuation F ((x * y : R.A.R) : F) < 1
          have hx : v.valuation F (x : F) ≤ 1 := x.property v hvS
          have hxy : v.valuation F ((x * y : R.A.R) : F) =
              v.valuation F (x : F) * v.valuation F (y : F) := by
            rw [show ((x * y : R.A.R) : F) = (x : F) * (y : F) from by
              simp only [Subalgebra.coe_mul], map_mul]
          rw [hxy]
          exact (mul_le_of_le_one_left' hx).trans_lt hy }
    have hmapM : Ideal.map (algebraMap (𝓞 F) R.A.R) v.asIdeal ≤ M := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change v.valuation F (((algebraMap (𝓞 F) R.A.R) x : R.A.R) : F) < 1
      rw [show (((algebraMap (𝓞 F) R.A.R) x : R.A.R) : F) = (x : F) from by
        simp only [Subalgebra.coe_algebraMap]]
      exact (v.valuation_lt_one_iff_mem (K := F) x).mpr hx
    have hspan : U.u ∈ R.A.extendIdeal U.ideal := by
      rw [← U.generates.2]
      exact Ideal.mem_span_singleton_self _
    have hmem : U.u ∈ Ideal.map (algebraMap (𝓞 F) R.A.R) v.asIdeal :=
      Ideal.map_mono hv' (by simpa [SArithmeticData.extendIdeal] using hspan)
    exact hmapM hmem

variable (D : DedekindZetaZeroFree.Quantitative.FixedData S η)

theorem deletion_mask_subpower (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe)
      (a : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℂ),
      (∀ v ∈ RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u), ‖a v‖ ≤ 1) →
      ∀ s : ℂ, σ ≤ s.re →
        Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u)) a s ≠ 0 ∧
        ‖Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u)) a s‖ ≤
            C * frequencyNorm D.recipe u ^ ε ∧
        ‖(Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u)) a s)⁻¹‖ ≤
            C * frequencyNorm D.recipe u ^ ε := by
  obtain ⟨C, hC, hb⟩ := Detector.frequency_finite_euler_masks_subpower F
    (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    D.recipe.A.Sf.finite_toSet σ ε hσ hε
  refine ⟨C, hC, ?_⟩
  intro u a ha s hs
  have hu : (FixedData.rawFrequency D u).u ≠ 0 := (FixedData.rawFrequency D u).generates.1
  have hfreq : (Detector.frequencyNorm F
      (D.recipe.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (FixedData.rawFrequency D u).u : ℝ) = frequencyNorm D.recipe u := by
    rw [frequencyNorm, Detector.frequencyNorm, FixedData.rawFrequency_u D u]
    rfl
  obtain ⟨-, -, h⟩ := hb ((FixedData.rawFrequency D u).u) hu
  obtain ⟨hne, hnorm, hinv⟩ := h (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
    (rawDeletionSet_subset D.recipe (FixedData.rawFrequency D u)) a s ha hs
  rw [hfreq] at hnorm hinv
  exact ⟨hne, hnorm, hinv⟩

theorem plus_mask_subpower (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe) (s : ℂ), σ ≤ s.re →
      Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primPlus D u).character v.asIdeal) s ≠ 0 ∧
        ‖Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primPlus D u).character v.asIdeal) s‖ ≤
            C * frequencyNorm D.recipe u ^ ε ∧
        ‖(Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primPlus D u).character v.asIdeal) s)⁻¹‖ ≤
            C * frequencyNorm D.recipe u ^ ε := by
  obtain ⟨C, hC, h⟩ := deletion_mask_subpower D σ ε hσ hε
  exact ⟨C, hC, fun u s hs => h u _ (fun v _ =>
    RayUnitary.ray_character_norm_le_one F (FixedData.primPlus D u).conductor
      (FixedData.primPlus D u).conductor_ne_zero (FixedData.primPlus D u).character
      v.asIdeal) s hs⟩

theorem minus_mask_subpower (σ ε : ℝ) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Frequency D.recipe) (s : ℂ), σ ≤ s.re →
      Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) s ≠ 0 ∧
        ‖Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) s‖ ≤
            C * frequencyNorm D.recipe u ^ ε ∧
        ‖(Detector.finiteEulerDeletionMask F
          (RawHeckeRows.rawDeletionSet (FixedData.rawFrequency D u))
          (fun v => (FixedData.primMinus D u).character v.asIdeal) s)⁻¹‖ ≤
            C * frequencyNorm D.recipe u ^ ε := by
  obtain ⟨C, hC, h⟩ := deletion_mask_subpower D σ ε hσ hε
  exact ⟨C, hC, fun u s hs => h u _ (fun v _ =>
    RayUnitary.ray_character_norm_le_one F (FixedData.primMinus D u).conductor
      (FixedData.primMinus D u).conductor_ne_zero (FixedData.primMinus D u).character
      v.asIdeal) s hs⟩

end

end DedekindZetaZeroFree.Quantitative.RawDeletionMask31
