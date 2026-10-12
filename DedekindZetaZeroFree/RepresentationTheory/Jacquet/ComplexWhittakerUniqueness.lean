module

public import DedekindZetaZeroFree.RepresentationTheory.Jacquet.OpenCellDistributionsAndDivergence

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxWhittakerUnique

open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage MeasureTheory

def whittakerSpace (β : ℂˣ) (ψ : AddChar ℂ Circle) :
    Submodule ℂ (Theta β →L[ℂ] ℂ) where
  carrier := {L | ∀ (t : ℂ) (h : Theta β),
    L (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) h) =
      (ψ t : ℂ) * L h}
  zero_mem' := by simp
  add_mem' := by
    intro L M hL hM t h
    simp only [ContinuousLinearMap.add_apply, hL t h, hM t h, mul_add]
  smul_mem' := by
    intro c L hL t h
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hL t h]
    ring

@[simp] theorem mem_whittakerSpace (β : ℂˣ) (ψ : AddChar ℂ Circle)
    (L : Theta β →L[ℂ] ℂ) :
    L ∈ whittakerSpace β ψ ↔ ∀ (t : ℂ) (h : Theta β),
      L (imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) h) =
        (ψ t : ℂ) * L h := Iff.rfl

noncomputable def jacquetIntegrand (ψ : AddChar ℂ Circle)
    (f : PrincipalSeries positiveParameter) (x : ℂ) : ℂ :=
  (ψ (-x) : ℂ) * openCoordinate f x

noncomputable def jacquetIntegral (β : ℂˣ) (ψ : AddChar ℂ Circle)
    (f : PrincipalSeries positiveParameter) : ℂ :=
  ∫ x : ℂ, jacquetIntegrand ψ f x ∂characterHaar β

private theorem source_whittaker_spanning (γ : ℂˣ) (hne : character (γ : ℂ) ≠ 1)
    (L : PrincipalSeries positiveParameter →L[ℂ] ℂ)
    (hL : KPCplxClosedCellJets.IsEigenDistribution positiveParameter (character (γ : ℂ)) L) :
    ∃ a : ℂ, L = a • KPCplxJacquetFunctional.jacquetFunctional γ := by
  obtain ⟨a, _, hs⟩ := KPCplxOpenCellDistributions.equivariant_functional_open_cell γ L hL
  have he : KPCplxClosedCellJets.IsEigenDistribution positiveParameter (character (γ : ℂ))
      (L - a • KPCplxJacquetFunctional.jacquetFunctional γ) := by
    intro t f
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      hL t f, KPCplxJacquetFunctional.jacquetFunctional_covariance]
    ring
  exact ⟨a, sub_eq_zero.mp
    (KPCplxClosedCellJets.closed_cell_no_nontrivial_eigen_distribution _ hne _ hs he)⟩

private theorem jacquet_rescale (β γ : ℂˣ) (f : PrincipalSeries positiveParameter) :
    jacquetIntegral β (character (γ : ℂ)) f =
      ((characterScale β / characterScale γ : ℝ) : ℂ) *
        KPCplxJacquetFunctional.jacquetFunctional γ f := by
  have hdβ : 0 ≤ characterScale β / (2 * Real.pi) :=
    le_of_lt (div_pos (characterScale_pos β) (by positivity))
  have hdγ : 0 ≤ characterScale γ / (2 * Real.pi) :=
    le_of_lt (div_pos (characterScale_pos γ) (by positivity))
  change (∫ x : ℂ, (character (γ : ℂ) (-x) : ℂ) * f (weyl * upperUnipotent x)
    ∂(ENNReal.ofReal (characterScale β / (2 * Real.pi)) • euclideanArea)) = _
  rw [KPCplxJacquetFunctional.jacquetFunctional_apply]
  unfold characterHaar
  rw [integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hdβ,
    ENNReal.toReal_ofReal hdγ]
  change ((characterScale β / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ x : ℂ, (character (γ : ℂ) (-x) : ℂ) * f (weyl * upperUnipotent x) ∂euclideanArea) =
    ((characterScale β / characterScale γ : ℝ) : ℂ) *
    (((characterScale γ / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ x : ℂ, f (weyl * upperUnipotent x) * (character (γ : ℂ) (-x) : ℂ) ∂euclideanArea)
  rw [show (fun x : ℂ => (character (γ : ℂ) (-x) : ℂ) * f (weyl * upperUnipotent x)) =
    (fun x : ℂ => f (weyl * upperUnipotent x) * (character (γ : ℂ) (-x) : ℂ)) by
      funext x; exact mul_comm _ _]
  push_cast
  have hg : (characterScale γ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (characterScale_pos γ).ne'
  field_simp

theorem transported_jacquet_generator (β : ℂˣ) (ψ : AddChar ℂ Circle)
    (hψ : Continuous ψ) (hne : ψ ≠ 1) :
    ∃ lambdaTheta : Theta β →L[ℂ] ℂ,
      lambdaTheta ≠ 0 ∧
      lambdaTheta ∈ whittakerSpace β ψ ∧
      (∀ f : PrincipalSeries positiveParameter,
        lambdaTheta (intertwinerToImage β f) = jacquetIntegral β ψ f) ∧
      whittakerSpace β ψ = Submodule.span ℂ {lambdaTheta} := by
  obtain ⟨γ, hγ⟩ := character_classification ψ hψ hne
  have hchar : ψ = character (γ : ℂ) := by
    ext x
    exact congrArg (fun z : Circle => (z : ℂ)) (hγ x)
  subst ψ
  obtain ⟨e, he, _⟩ := standardIntertwiner_topological_image_isomorphism β
  let c : ℂ := ((characterScale β / characterScale γ : ℝ) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (div_pos
    (characterScale_pos β) (characterScale_pos γ)).ne'
  let J := KPCplxJacquetFunctional.jacquetFunctional γ
  let L0 : Theta β →L[ℂ] ℂ := (c • J).comp e.symm.toContinuousLinearMap
  have hnorm (f : PrincipalSeries positiveParameter) : L0 (e f) = c * J f := by
    simp [L0, smul_eq_mul]
  have hequiv (t : ℂ) (f : PrincipalSeries positiveParameter) :
      imageAction β (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) (e f) =
        e (pi positiveParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) := by
    rw [he f, he]
    exact (intertwinerToImage_equivariant β _ f).symm
  have hmem : L0 ∈ whittakerSpace β (character (γ : ℂ)) := by
    intro t h
    obtain ⟨f, rfl⟩ := e.surjective h
    rw [hequiv, hnorm, hnorm]
    change c * KPCplxJacquetFunctional.jacquetFunctional γ
      (pi positiveParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) =
      (character (γ : ℂ) t : ℂ) * (c * KPCplxJacquetFunctional.jacquetFunctional γ f)
    rw [KPCplxJacquetFunctional.jacquetFunctional_covariance]
    ring
  have hnonzero : L0 ≠ 0 := by
    intro hz
    apply KPCplxJacquetFunctional.jacquetFunctional_ne_zero γ
    ext f
    have hh := hnorm f
    rw [hz, ContinuousLinearMap.zero_apply] at hh
    have hJ := (mul_eq_zero.mp hh.symm).resolve_left hc
    exact hJ
  refine ⟨L0, hnonzero, hmem, ?_, ?_⟩
  · intro f
    rw [← he f, hnorm]
    exact (jacquet_rescale β γ f).symm
  · apply le_antisymm
    · intro L hL
      let Ls : PrincipalSeries positiveParameter →L[ℂ] ℂ := L.comp e.toContinuousLinearMap
      have hs : KPCplxClosedCellJets.IsEigenDistribution positiveParameter (character (γ : ℂ)) Ls := by
        intro t f
        change L (e (pi positiveParameter (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)) =
          (character (γ : ℂ) t : ℂ) * L (e f)
        rw [← hequiv]
        exact hL t (e f)
      obtain ⟨a, ha⟩ := source_whittaker_spanning γ hne Ls hs
      have hLa : L = (a / c) • L0 := by
        ext h
        obtain ⟨f, rfl⟩ := e.surjective h
        have hh := congrArg (fun T : PrincipalSeries positiveParameter →L[ℂ] ℂ => T f) ha
        change L (e f) = a * J f at hh
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hnorm, hh]
        field_simp
      rw [hLa]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton L0))
    · exact Submodule.span_le.mpr (by
        intro L hL
        rw [Set.mem_singleton_iff] at hL
        subst L
        exact hmem)

private theorem dimension_span_singleton {V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : V) (hv : v ≠ 0) :
    Module.rank ℂ (Submodule.span ℂ {v}) = 1 ∧
      Module.finrank ℂ (Submodule.span ℂ {v}) = 1 := by
  have hf := finrank_span_singleton (K := ℂ) hv
  exact ⟨Module.rank_eq_one_iff_finrank_eq_one.mpr hf, hf⟩

theorem whittaker_dimension_one (β : ℂˣ) (ψ : AddChar ℂ Circle)
    (hψ : Continuous ψ) (hne : ψ ≠ 1) :
    Module.rank ℂ (whittakerSpace β ψ) = 1 ∧
      Module.finrank ℂ (whittakerSpace β ψ) = 1 := by
  obtain ⟨L, hL, _, _, hspan⟩ := transported_jacquet_generator β ψ hψ hne
  letI : AddCommGroup (Theta β →L[ℂ] ℂ) :=
    @ContinuousLinearMap.addCommGroup ℂ _ ℂ _ (Theta β) _ _ ℂ _ _ _ _ (RingHom.id ℂ) _
  rw [hspan]
  exact dimension_span_singleton L hL

end DedekindZetaZeroFree.KPCplxWhittakerUnique
