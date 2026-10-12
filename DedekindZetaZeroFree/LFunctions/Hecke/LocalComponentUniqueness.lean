module

public import DedekindZetaZeroFree.ZeroDetection.Conductors.FrequencyLocalComponents
public import DedekindZetaZeroFree.Arithmetic.LocalFields.IntegralCompletionDensity

@[expose] public section

open scoped UniqueFactorizationMonoid

open scoped NumberField
open IsDedekindDomain

namespace DedekindZetaZeroFree.Detector.Conductor.LocalTwistSteps

open UniqueFactorizationMonoid Topology

private theorem away_coprime (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (I : Ideal (𝓞 F)) :
    v.asIdeal ⊔ Raw.idealAwayPrimePart F v I = ⊤ := by
  classical
  unfold Raw.idealAwayPrimePart
  apply v.asIdeal.sup_multiset_prod_eq_top
  intro p hp
  have hprime : Prime p := prime_of_normalized_factor p
    (Multiset.filter_subset _ _ hp)
  exact v.isMaximal.coprime_of_ne ((Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero)
    (Multiset.mem_filter.mp hp).2.symm

private theorem coset_dense (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (b : 𝓞 F) (hb : b ∉ v.asIdeal) :
    DenseRange (fun a : 𝓞 F =>
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) (1 + b * a)) := by
  let b' : v.adicCompletionIntegers F := algebraMap _ _ b
  have hb' : IsUnit b' := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    change Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) b) = 1
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    exact (v.valuedAdicCompletion_eq_valuation' (K := F) (b : F)).trans
      (v.valuation_eq_one_iff_notMem.mpr hb)
  let e := (ContinuousAddEquiv.mulLeft hb'.unit).toHomeomorph
  have hd := (denseRange_ringOfIntegers_adicCompletionIntegers F v)
  have h := (Homeomorph.addLeft (1 : v.adicCompletionIntegers F)).surjective.denseRange.comp
    (e.surjective.denseRange.comp hd e.continuous)
    (Homeomorph.addLeft (1 : v.adicCompletionIntegers F)).continuous
  change DenseRange (fun a : 𝓞 F =>
    1 + (hb'.unit : v.adicCompletionIntegers F) * algebraMap _ _ a) at h
  simpa only [hb'.unit_spec, b', map_add, map_one, map_mul] using h

theorem raw_local_component_unique
    (F : Type) [Field F] [NumberField F]
    (χ : PrimitiveFrequencyCharacter F) (v : HeightOneSpectrum (𝓞 F))
    (δ δ' : (v.adicCompletion F)ˣ →ₜ* ℂˣ)
    (hδ : Raw.IsFrequencyLocalComponent F χ v δ)
    (hδ' : Raw.IsFrequencyLocalComponent F χ v δ') :
    δ = δ' := by
  classical
  let I := Raw.idealAwayPrimePart F v χ.conductor
  have hcop : v.asIdeal ⊔ I = ⊤ := away_coprime F v χ.conductor
  obtain ⟨c, hc, b, hb, hcb⟩ := Submodule.mem_sup.mp
    (show (1 : 𝓞 F) ∈ v.asIdeal ⊔ I by rw [hcop]; trivial)
  have hbp : b ∉ v.asIdeal := by
    intro h
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr
      (hcb ▸ v.asIdeal.add_mem hc h))
  let s : Set (v.adicCompletion F)ˣ :=
    {u | ∃ (a : 𝓞 F) (ha : a ≠ 0), a - 1 ∈ I ∧
      u = Raw.integralElementLocalUnit F v a ha}
  have heq : Set.EqOn δ δ' s := by
    rintro u ⟨a, ha, haI, rfl⟩
    apply Units.ext
    exact (hδ a ha haI).trans (hδ' a ha haI).symm
  have hlocal : ∀ u : (v.adicCompletion F)ˣ,
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F → δ u = δ' u := by
    intro u hu
    let x : v.adicCompletionIntegers F := ⟨u, hu⟩
    have hd := coset_dense F v b hbp
    have hcl : (u : v.adicCompletion F) ∈ closure
        (Set.range (fun a : 𝓞 F => algebraMap (𝓞 F) (v.adicCompletion F) (1 + b * a))) := by
      have h := mem_closure_image
        (continuous_subtype_val : Continuous (Subtype.val : v.adicCompletionIntegers F →
          v.adicCompletion F)).continuousAt (hd x)
      convert h using 1
      congr 1
      ext y
      simp only [Set.mem_image, Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨algebraMap _ _ (1 + b * a), ⟨a, rfl⟩,
          rfl⟩
      · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, rfl⟩
    have hcl' : (u : v.adicCompletion F) ∈ closure
        (Set.range (fun a : 𝓞 F => algebraMap (𝓞 F) (v.adicCompletion F) (1 + b * a)) \ {0}) := by
      apply closure_sdiff
      exact ⟨hcl, by simpa using u.ne_zero⟩
    have hs : Set.range (fun a : 𝓞 F =>
        algebraMap (𝓞 F) (v.adicCompletion F) (1 + b * a)) \ {0} ⊆
        Units.val '' s := by
      rintro y ⟨⟨a, rfl⟩, hy⟩
      have ha : (1 + b * a : 𝓞 F) ≠ 0 := by
        intro h
        exact hy (by simp [h])
      refine ⟨Raw.integralElementLocalUnit F v (1 + b * a) ha,
        ⟨1 + b * a, ha, ?_, rfl⟩, ?_⟩
      · simpa using I.mul_mem_right a hb
      · rfl
    have hucl : u ∈ closure s := by
      rw [Units.isEmbedding_val₀.closure_eq_preimage_closure_image]
      exact closure_mono hs hcl'
    exact heq.closure δ.continuous δ'.continuous hucl
  apply ContinuousMonoidHom.ext
  intro u
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (u : v.adicCompletion F) with h | h
  · exact hlocal u h
  · have hi := hlocal u⁻¹ (by simpa only [Units.val_inv_eq_inv_val] using h)
    simpa only [map_inv, inv_inj] using hi

end DedekindZetaZeroFree.Detector.Conductor.LocalTwistSteps
