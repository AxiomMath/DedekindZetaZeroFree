module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.LocalSchwartzInversion

@[expose] public section

noncomputable section

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

local instance compactOpenDualCompletionMeasurable
    (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance compactOpenDualCompletionBorel
    (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

private theorem dual_antitone (v : HeightOneSpectrum (𝓞 F))
    {U V : AddSubgroup (v.adicCompletion F)} (h : U ≤ V) :
    localFiniteAnnihilator F v V ≤ localFiniteAnnihilator F v U := by
  intro y hy u hu
  exact hy u (h hu)

private theorem dual_closed (v : HeightOneSpectrum (𝓞 F))
    (U : AddSubgroup (v.adicCompletion F)) :
    IsClosed (localFiniteAnnihilator F v U : Set (v.adicCompletion F)) := by
  have he : (localFiniteAnnihilator F v U : Set (v.adicCompletion F)) =
      ⋂ u : U, {y | localFiniteCharacter F v (u.val * y) = 1} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, mem_localFiniteAnnihilator]
    exact ⟨fun h u => h u u.property, fun h u hu => h ⟨u, hu⟩⟩
  rw [he]
  apply isClosed_iInter
  intro u
  exact isClosed_eq ((continuous_localFiniteCharacter F v).comp
    (continuous_const.mul continuous_id)) continuous_const

private theorem dual_inner_ball (v : HeightOneSpectrum (𝓞 F))
    (U : AddSubgroup (v.adicCompletion F)) (ho : IsOpen (U : Set (v.adicCompletion F))) :
    ∃ n : ℤ, finiteCompletionBall F v n ≤ U := by
  obtain ⟨n, _, hn⟩ := (finiteCompletionBall_hasBasis_nhds F v 0).mem_iff.mp
    (ho.mem_nhds U.zero_mem)
  exact ⟨n, fun x hx => hn (by simpa using hx)⟩

private theorem dual_outer_ball (v : HeightOneSpectrum (𝓞 F))
    (U : AddSubgroup (v.adicCompletion F)) (hc : IsCompact (U : Set (v.adicCompletion F))) :
    ∃ n : ℤ, U ≤ finiteCompletionBall F v n := by
  obtain ⟨k, hk⟩ := hc.elim_directed_cover
    (fun k : ℕ => (finiteCompletionBall F v (-(k : ℤ)) : Set _))
    (fun k => isOpen_finiteCompletionBall F v _)
    (by rw [iUnion_finiteCompletionBall_neg_nat]; exact Set.subset_univ _)
    (by
      intro i j
      refine ⟨max i j, ?_, ?_⟩ <;>
        apply (finiteCompletionBall_le_iff F v _ _).mpr <;> omega)
  exact ⟨-(k : ℤ), hk⟩

theorem isCompact_localFiniteAnnihilator
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hUcompact : IsCompact (U : Set (v.adicCompletion F)))
    (hUopen : IsOpen (U : Set (v.adicCompletion F))) :
    IsCompact (localFiniteAnnihilator F v U : Set (v.adicCompletion F)) := by
  obtain ⟨n, hn⟩ := dual_inner_ball F v U hUopen
  have h := dual_antitone F v hn
  rw [localFiniteAnnihilator_finiteCompletionBall] at h
  exact (isCompact_finiteCompletionBall F v _).of_isClosed_subset
    (dual_closed F v U) h

theorem isOpen_localFiniteAnnihilator
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hUcompact : IsCompact (U : Set (v.adicCompletion F)))
    (hUopen : IsOpen (U : Set (v.adicCompletion F))) :
    IsOpen (localFiniteAnnihilator F v U : Set (v.adicCompletion F)) := by
  obtain ⟨n, hn⟩ := dual_outer_ball F v U hUcompact
  have h := dual_antitone F v hn
  rw [localFiniteAnnihilator_finiteCompletionBall] at h
  apply AddSubgroup.isOpen_of_zero_mem_interior
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset
    ((isOpen_finiteCompletionBall F v _).mem_nhds (AddSubgroup.zero_mem _)) h)

private theorem dual_indicator_identity
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hc : IsCompact (U : Set (v.adicCompletion F)))
    (ho : IsOpen (U : Set (v.adicCompletion F))) (x : v.adicCompletion F) :
    ((localNormalizedHaar F v (U : Set (v.adicCompletion F))).toReal : ℂ) *
      ((localNormalizedHaar F v
        (localFiniteAnnihilator F v U : Set (v.adicCompletion F))).toReal : ℂ) *
      localCosetIndicator F v 0
        (localFiniteAnnihilator F v (localFiniteAnnihilator F v U)) x =
      localCosetIndicator F v 0 U (-x) := by
  have he : localFourierIntegral F v (localCosetIndicator F v 0 U) =
      ((localNormalizedHaar F v (U : Set (v.adicCompletion F))).toReal : ℂ) •
        localCosetIndicator F v 0 (localFiniteAnnihilator F v U) := by
    funext y
    simpa using localFourierIntegral_localCosetIndicator F v U hc ho 0 y
  have hi := localFourierIntegral_fourierIntegral F v
    (localCosetIndicator F v 0 U) (localCosetIndicator_mem_localSchwartz F v U hc ho 0) x
  rw [he, localFourierIntegral_smul] at hi
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  rw [localFourierIntegral_localCosetIndicator F v _
    (isCompact_localFiniteAnnihilator F v U hc ho)
    (isOpen_localFiniteAnnihilator F v U hc ho)] at hi
  simpa [mul_assoc] using hi

private theorem dual_mass_complex
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hc : IsCompact (U : Set (v.adicCompletion F)))
    (ho : IsOpen (U : Set (v.adicCompletion F))) :
    ((localNormalizedHaar F v (U : Set (v.adicCompletion F))).toReal : ℂ) *
      ((localNormalizedHaar F v
        (localFiniteAnnihilator F v U : Set (v.adicCompletion F))).toReal : ℂ) = 1 := by
  simpa using dual_indicator_identity F v U hc ho 0

theorem localFiniteAnnihilator_localFiniteAnnihilator
    (v : HeightOneSpectrum (𝓞 F)) (U : AddSubgroup (v.adicCompletion F))
    (hUcompact : IsCompact (U : Set (v.adicCompletion F)))
    (hUopen : IsOpen (U : Set (v.adicCompletion F))) :
    localFiniteAnnihilator F v (localFiniteAnnihilator F v U) = U := by
  ext x
  have h := dual_indicator_identity F v U hUcompact hUopen x
  rw [dual_mass_complex F v U hUcompact hUopen, one_mul] at h
  simp only [localCosetIndicator_apply, sub_zero, AddSubgroup.neg_mem_iff] at h
  by_cases ha : x ∈ localFiniteAnnihilator F v (localFiniteAnnihilator F v U) <;>
    by_cases hb : x ∈ U <;> simp_all

theorem localNormalizedHaar_integerRing_of_not_mem
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : localDifferentSupport F ⊆ (S : Set (HeightOneSpectrum (𝓞 F))))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    localNormalizedHaar F v
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = 1 := by
  rw [localNormalizedHaar_integerRing]
  simp [localHalfDifferentFactor, localDifferentExponent_eq_zero_of_not_mem F S hS v hv]

end DedekindZetaZeroFree

end
