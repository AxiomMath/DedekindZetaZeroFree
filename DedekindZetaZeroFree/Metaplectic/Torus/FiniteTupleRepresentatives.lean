module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorFunctionalsAndSmoothLevels

@[expose] public section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalTorusTensorFibers

def FiniteRawRepresentatives (S : Finset (HeightOneSpectrum (𝓞 F)))
    (R : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) →
      RawEvaluationPoint F ζ hζ) : Prop :=
  ∀ t, (∀ q : S, (R t).t q.val = t q) ∧
    ∀ q, q ∉ S → (R t).raw (Sum.inr q) = 1

open KPAdelicCoverRestrictedProduct
 def localRaw (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q) :=
  KPLocalCover.centralInjection F ζ hζ (Sum.inr q) (ActualFiniteTorus.sheet F ζ hζ q t) *
    KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (ActualFiniteTorus.coordinate F ζ hζ q t)
private theorem localRaw_spec (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (localRaw F ζ hζ q t) = t.val := by
  rw [localRaw, map_mul]
  exact ((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 t).symm
private theorem localRaw_diagonal (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    (localRaw F ζ hζ q t).g 1 0 = 0 ∧ (localRaw F ζ hζ q t).g 0 1 = 0 := by
  simp [localRaw, KPLocalCover.centralInjection, KPStandardLocalRootLifts.A,
    KPLocalCover.projection, KubotaRankTwo.d, Matrix.mul_apply,
    MonoidHom.coe_mk, OneHom.coe_mk]
  exact ⟨rfl, rfl⟩
 def finiteRawTuple (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q) : RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl _ => 1
    | Sum.inr q => if q ∈ S then localRaw F ζ hζ q (t q) else 1,
    by
      apply Filter.eventually_cofinite.mpr
      apply (S.finite_toSet.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).subset
      intro v hv
      cases v with
      | inl w => exact False.elim (hv (Subgroup.one_mem _))
      | inr q =>
        by_cases hq : q ∈ S
        · exact ⟨q, hq, rfl⟩
        · apply False.elim
          apply hv
          change (if q ∈ S then localRaw F ζ hζ q (t q) else 1) ∈ compact F ζ hζ (Sum.inr q)
          rw [if_neg hq]
          exact (compact F ζ hζ (Sum.inr q)).one_mem⟩
private theorem finiteRawTuple_diagonal (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    restrictedProjection F ζ hζ (finiteRawTuple F ζ hζ S t) 1 0 = 0 ∧
      restrictedProjection F ζ hζ (finiteRawTuple F ζ hζ S t) 0 1 = 0 := by
  have hd (i j : Fin 2) (hij : i ≠ j) :
      restrictedProjection F ζ hζ (finiteRawTuple F ζ hζ S t) i j = 0 := by
    apply Prod.ext
    · funext w
      simp [restrictedProjection, matrixValue, KPAdelicCoverCertificatesRaw.matrixValue,
        KPAdelicCoverCertificatesRaw.matrixEntry, matrixEntry, finiteRawTuple, hij]
      rfl
    · apply RestrictedProduct.ext
      intro q
      change (if q ∈ S then localRaw F ζ hζ q (t q) else 1).g i j = 0
      by_cases hq : q ∈ S
      · rw [if_pos hq]
        fin_cases i <;> fin_cases j <;> simp_all [localRaw_diagonal F ζ hζ q (t q)]
      · simp [hq, hij]
  exact ⟨hd 1 0 (by decide), hd 0 1 (by decide)⟩

theorem finite_raw_representatives_exist
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ R : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) →
      RawEvaluationPoint F ζ hζ,
      FiniteRawRepresentatives F ζ hζ S R := by
  classical
  let extend (t : ∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) :
      ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q :=
    fun q => if h : q ∈ S then t ⟨q, h⟩ else 1
  have hpoint (t : ∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) :
      ∃ a : RawEvaluationPoint F ζ hζ,
        (∀ q : S, a.t q.val = t q) ∧ ∀ q, q ∉ S → a.raw (Sum.inr q) = 1 := by
    let raw := finiteRawTuple F ζ hζ S (extend t)
    let g := scalarQuotient F ζ hζ (amalgamation F ζ hζ raw)
    have hg : g ∈ KPGlobalTorusFunctionData.torus F ζ hζ := by
      refine ⟨restrictedProjection F ζ hζ raw, ?_,
        (finiteRawTuple_diagonal F ζ hζ S (extend t)).1,
        (finiteRawTuple_diagonal F ζ hζ S (extend t)).2⟩
      rfl
    have hlocal : ∀ q, (extend t q).val =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)) := by
      intro q
      change (extend t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (if q ∈ S then localRaw F ζ hζ q (extend t q) else 1)
      by_cases hq : q ∈ S
      · rw [if_pos hq, localRaw_spec]
      · simp [extend, hq]
    refine ⟨⟨raw, extend t, ⟨g, hg⟩, fun w => rfl, hlocal, rfl⟩, ?_, ?_⟩
    · intro q
      simp [extend, q.property]
    · intro q hq
      change (if q ∈ S then localRaw F ζ hζ q (extend t q) else 1) = 1
      exact if_neg hq
  choose R hR using hpoint
  exact ⟨R, hR⟩

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification
