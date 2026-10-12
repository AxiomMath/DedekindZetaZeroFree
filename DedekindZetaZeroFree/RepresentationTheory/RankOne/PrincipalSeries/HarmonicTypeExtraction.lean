module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.HolomorphicKTypeGeneration
public import DedekindZetaZeroFree.Theta.Profiles.LocalTensorActions

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
open scoped Classical BigOperators Topology
open DedekindZetaZeroFree KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCAlgebraic

 theorem harmonic_sum_kFinite (s : ℝ) (f : PrincipalSeries s)
    (hf : f ∈ ⨆ ℓ : ℕ, harmonicKType s ℓ) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f))) := by
  classical
  obtain ⟨I, hI⟩ := Submodule.exists_finset_of_mem_iSup (fun ℓ => harmonicKType s ℓ) hf
  let S := I.sup (fun ℓ => harmonicKType s ℓ)
  have hS : IsKInvariant s S := by
    intro k v hv
    change v ∈ I.sup (fun ℓ => harmonicKType s ℓ) at hv
    change KPCplxPrincipalSeriesCharts.pi s k v ∈ I.sup (fun ℓ => harmonicKType s ℓ)
    clear hI S hf f
    induction I using Finset.induction_on generalizing v with
    | empty =>
      simp only [Finset.sup_empty, Submodule.mem_bot] at hv ⊢
      rw [hv, KPGlobalResidualConstruction.pi_zero]
    | @insert a I ha ih =>
      rw [Finset.sup_insert] at hv ⊢
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
      rw [KPGlobalResidualConstruction.pi_add]
      exact Submodule.mem_sup.mpr ⟨_, (harmonicKType_multiplicity_one s a).1 k u hu,
        _, ih w hw, rfl⟩
  have hfS : f ∈ S := by simpa only [S, Finset.sup_eq_iSup] using hI
  have hle : Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hS k f hfS
  letI (ℓ : ℕ) : FiniteDimensional ℂ (harmonicKType s ℓ) :=
    KPCplxHarmonicIntertwinerSpectrum.harmonicKType_finite s ℓ
  letI : FiniteDimensional ℂ S := inferInstanceAs
    (FiniteDimensional ℂ ↥(I.sup (fun ℓ => harmonicKType s ℓ)))
  exact Submodule.finiteDimensional_of_le hle

 theorem nonzero_harmonic_in_invariant (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (f : PrincipalSeries s) (hfU : f ∈ U)
    (hf : f ∈ ⨆ ℓ : ℕ, harmonicKType s ℓ) (hne : f ≠ 0) :
    ∃ ℓ v, v ∈ U ∧ v ∈ harmonicKType s ℓ ∧ v ≠ 0 := by
  let W := Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f))
  letI : FiniteDimensional ℂ W := harmonic_sum_kFinite s f hf
  letI : T2Space (PrincipalSeries s) := principalSeries_t2 s
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  have hclosed : IsClosed (W : Set (PrincipalSeries s)) := W.closed_of_finiteDimensional
  have hWU : W ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hU k f hfU
  obtain ⟨μ, hhaar, hprob⟩ := KPCplxHarmonicExtraction.exists_su2_probability_haar
  obtain ⟨a, hint, havg, htype, hlim⟩ :=
    KPCplxHarmonicExtraction.character_average_harmonic_expansion s μ hhaar hprob f
  have haW (ℓ : ℕ) : a ℓ ∈ W := by
    have h := KPCplxHarmonicExtraction.character_average_mem_orbit_closure
      s μ hhaar hprob ℓ f (a ℓ) (hint ℓ) (havg ℓ)
    rwa [hclosed.closure_eq] at h
  have hex : ∃ ℓ, a ℓ ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (fun N : ℕ => ∑ ℓ ∈ Finset.range N, a ℓ) = fun _ => 0 := by
      funext N
      simp [h]
    rw [hz] at hlim
    exact hne (tendsto_nhds_unique hlim tendsto_const_nhds)
  obtain ⟨ℓ, hℓ⟩ := hex
  exact ⟨ℓ, a ℓ, hWU (haW ℓ), htype ℓ, hℓ⟩

def coreHarmonic (ℓ : ℕ) : Submodule ℂ complexCore :=
  (harmonicKType negativeParameter ℓ).comap complexCore.subtype

 theorem harmonic_le_core (ℓ : ℕ) : harmonicKType negativeParameter ℓ ≤ complexCore := by
  intro f hf
  exact ⟨by rw [KPCplxActualImage.imageSubmodule_eq_top]; trivial,
    Submodule.mem_iSup_of_mem ℓ hf⟩

 theorem coreHarmonic_finrank (ℓ : ℕ) :
    Module.finrank ℂ (coreHarmonic ℓ) = 2 * ℓ + 1 := by
  have e := Submodule.comapSubtypeEquivOfLe (harmonic_le_core ℓ)
  exact e.finrank_eq.trans (harmonicKType_multiplicity_one negativeParameter ℓ).2.1

 theorem coreHarmonic_zero_fixed (f : complexCore) (hf : f ∈ coreHarmonic 0)
    (k : KPCplxCharacterHaar.ComplexSU2) : complexCoreCompactLinearMap k f = f := by
  apply Subtype.ext
  exact KPCplxHarmonicIntertwinerSpectrum.harmonicKType_zero_fixed negativeParameter
    f.val hf ⟨_, ⟨k, rfl⟩⟩

 theorem coreHarmonic_zero_of_fixed (f : complexCore)
    (hf : ∀ k : KPCplxCharacterHaar.ComplexSU2, complexCoreCompactLinearMap k f = f) :
    f ∈ coreHarmonic 0 := by
  change f.val ∈ harmonicKType negativeParameter 0
  rw [show harmonicKType negativeParameter 0 = ℂ ∙ sphericalSection negativeParameter from
    KPCplxHarmonicIntertwinerSpectrum.harmonicKType_zero_eq_span negativeParameter]
  have hfixed (k : compactSubgroup) : KPCplxPrincipalSeriesCharts.pi negativeParameter k f.val = f.val := by
    obtain ⟨l, hl⟩ := k.property
    rw [← hl]
    exact congrArg Subtype.val (hf l)
  rw [sphericalSection_spans_fixed negativeParameter f.val hfixed]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

 theorem commutant_preserves_lowest (T : Module.End ℂ complexCore)
    (hT : ∀ k f, T (complexCoreCompactLinearMap k f) = complexCoreCompactLinearMap k (T f))
    (f : complexCore) (hf : f ∈ coreHarmonic 0) : T f ∈ coreHarmonic 0 := by
  apply coreHarmonic_zero_of_fixed
  intro k
  rw [← hT, coreHarmonic_zero_fixed f hf k]

 theorem commutant_scalar_on_lowest (T : Module.End ℂ complexCore)
    (hT : ∀ k f, T (complexCoreCompactLinearMap k f) = complexCoreCompactLinearMap k (T f)) :
    ∃ c : ℂ, ∀ f ∈ coreHarmonic 0, T f = c • f := by
  have hdim : Module.finrank ℂ (coreHarmonic 0) = 1 := by
    simpa using coreHarmonic_finrank 0
  haveI : Nontrivial (coreHarmonic 0) := Module.nontrivial_of_finrank_pos (by rw [hdim]; exact Nat.zero_lt_one)
  letI : AddCommGroup ↥(coreHarmonic 0) := Submodule.addCommGroup (R := ℂ) (M := ↥complexCore) (coreHarmonic 0)
  obtain ⟨v, hv⟩ := exists_ne (0 : coreHarmonic 0)
  let Tv : coreHarmonic 0 := ⟨T v.val, commutant_preserves_lowest T hT v.val v.property⟩
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := ℂ) (V := ↥(coreHarmonic 0)) hdim hv Tv
  have hcv : T v.val = c • v.val := (congrArg Subtype.val hc).symm
  refine ⟨c, ?_⟩
  intro f hf
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one (K := ℂ) (V := ↥(coreHarmonic 0)) hdim hv (⟨f, hf⟩ : coreHarmonic 0)
  have haf : a • v.val = f := congrArg Subtype.val ha
  rw [← haf, map_smul, hcv, smul_smul, smul_smul, mul_comm a c]

 theorem nonzero_core_harmonic_in_invariant
    (U : Submodule ℂ complexCore)
    (hU : ∀ k f, f ∈ U → complexCoreCompactLinearMap k f ∈ U)
    (f : complexCore) (hfU : f ∈ U) (hne : f ≠ 0) :
    ∃ ℓ v, v ∈ U ∧ v ∈ coreHarmonic ℓ ∧ v ≠ 0 := by
  let W := U.map complexCore.subtype
  have hW : IsKInvariant negativeParameter W := by
    intro k v hv
    obtain ⟨l, hl⟩ := k.property
    obtain ⟨x, hx, rfl⟩ := hv
    exact ⟨complexCoreCompactLinearMap l x, hU l x hx,
      by change KPCplxPrincipalSeriesCharts.pi negativeParameter
           (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding l)) x.val =
           KPCplxPrincipalSeriesCharts.pi negativeParameter k x.val
         change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding l) =
           (k : KPCplxCharacterHaar.ComplexPGL2) at hl
         rw [hl]⟩
  obtain ⟨ℓ, v, hvW, hvtype, hvne⟩ := nonzero_harmonic_in_invariant negativeParameter W hW
    f.val ⟨f, hfU, rfl⟩ f.property.2 (by intro h; exact hne (Subtype.ext h))
  obtain ⟨x, hx, rfl⟩ := hvW
  exact ⟨ℓ, x, hx, hvtype, by intro h; exact hvne (congrArg Subtype.val h)⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCAlgebraic
noncomputable section
open scoped Classical Topology
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCExtraction
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxIntertwinerEigenvalues

private theorem pi_add' (s : ℝ) (k : ComplexPGL2) (f h : PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.pi s k (f+h) = KPCplxPrincipalSeriesCharts.pi s k f + KPCplxPrincipalSeriesCharts.pi s k h := by
  induction k using Quotient.inductionOn with
  | h k => rfl

private theorem pi_smul' (s : ℝ) (k : ComplexPGL2) (c : ℂ) (f : PrincipalSeries s) :
    KPCplxPrincipalSeriesCharts.pi s k (c • f) = c • KPCplxPrincipalSeriesCharts.pi s k f := by
  induction k using Quotient.inductionOn with
  | h k => rfl

theorem finite_band_of_mem (s : ℝ) (f : PrincipalSeries s)
    (hf : f ∈ ⨆ n : ℕ, harmonicKType s n) :
    ∃ I : Finset ℕ, f ∈ I.sup (harmonicKType s) := by
  refine Submodule.iSup_induction (harmonicKType s)
    (motive := fun f => ∃ I : Finset ℕ, f ∈ I.sup (harmonicKType s)) hf ?_ ?_ ?_
  · intro i f hf
    exact ⟨{i}, by simpa using hf⟩
  · exact ⟨∅, by simp⟩
  · intro f h hf hh
    obtain ⟨I, hI⟩ := hf
    obtain ⟨J, hJ⟩ := hh
    refine ⟨I ∪ J, ?_⟩
    rw [Finset.sup_union]
    exact (I.sup (harmonicKType s) ⊔ J.sup (harmonicKType s)).add_mem
      (Submodule.mem_sup_left hI) (Submodule.mem_sup_right hJ)

private theorem finite_band_invariant (s : ℝ) (I : Finset ℕ) :
    IsKInvariant s (I.sup (harmonicKType s)) := by
  induction I using Finset.induction_on with
  | empty =>
    intro k f hf
    have hf0 : f = 0 := by simpa using hf
    subst f
    simpa using (pi_smul' s k 0 (sphericalSection s))
  | @insert n I hn ih =>
    rw [Finset.sup_insert]
    intro k f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
    rw [pi_add']
    exact (harmonicKType s n ⊔ I.sup (harmonicKType s)).add_mem
      (Submodule.mem_sup_left ((harmonicKType_multiplicity_one s n).1 k a ha))
      (Submodule.mem_sup_right (ih k b hb))

theorem finite_compact_orbit (s : ℝ) (f : PrincipalSeries s)
    (hf : f ∈ ⨆ n : ℕ, harmonicKType s n) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f))) := by
  obtain ⟨I, hI⟩ := finite_band_of_mem s f hf
  letI (n : ℕ) : FiniteDimensional ℂ (harmonicKType s n) :=
    KPCplxHarmonicIntertwinerSpectrum.harmonicKType_finite s n
  apply Submodule.finiteDimensional_of_le (S₂ := I.sup (harmonicKType s))
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  exact finite_band_invariant s I k f hI

theorem harmonic_type_of_nonzero (s : ℝ)
    (U : Submodule ℂ (PrincipalSeries s)) (hU : IsKInvariant s U)
    (f : PrincipalSeries s) (hfU : f ∈ U)
    (hf : f ∈ ⨆ n : ℕ, harmonicKType s n) (hf0 : f ≠ 0) :
    ∃ n : ℕ, harmonicKType s n ≤ U := by
  let O := Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi s k f))
  letI : FiniteDimensional ℂ O := finite_compact_orbit s f hf
  letI : T2Space (PrincipalSeries s) := principalSeries_t2 s
  letI : ContinuousSMul ℂ (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).continuousSMul
  have hclosed : IsClosed (O : Set (PrincipalSeries s)) := O.closed_of_finiteDimensional
  have hOU : O ≤ U := Submodule.span_le.mpr (by
    rintro _ ⟨k, rfl⟩
    exact hU k f hfU)
  obtain ⟨μ, hhaar, hprob⟩ := KPCplxHarmonicExtraction.exists_su2_probability_haar
  obtain ⟨a, hint, havg, htype, hlim⟩ :=
    KPCplxHarmonicExtraction.character_average_harmonic_expansion s μ hhaar hprob f
  have haU (n : ℕ) : a n ∈ U := by
    have hn := KPCplxHarmonicExtraction.character_average_mem_orbit_closure
      s μ hhaar hprob n f (a n) (hint n) (havg n)
    rw [hclosed.closure_eq] at hn
    exact hOU hn
  have hnonzero : ∃ n, a n ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hzero : Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, a n)
        Filter.atTop (𝓝 (0 : PrincipalSeries s)) := by
      simpa only [hn, Finset.sum_const_zero] using
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : PrincipalSeries s))
          Filter.atTop (𝓝 (0 : PrincipalSeries s)))
    exact hf0 (tendsto_nhds_unique hlim hzero)
  obtain ⟨n, hn⟩ := hnonzero
  exact ⟨n, KPCplxHarmonicPropagation.harmonic_le_of_nonzero_vector
    s U hU n (a n) (haU n) (htype n) hn⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeComplexHCExtraction

end
end
