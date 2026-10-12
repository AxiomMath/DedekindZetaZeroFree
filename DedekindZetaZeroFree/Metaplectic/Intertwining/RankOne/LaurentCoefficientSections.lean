module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.LaurentCoefficientBorelCovariance

@[expose] public section

set_option maxHeartbeats 8000000

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_scalar_coefficients_target_level
    (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∀ (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) (n : ℤ),
      ∃ ψ : compactLevel S.borel P S.iwasawa (targetSign ε) J,
        ∀ (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
          (ψ.val.val k).val h =
            actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h n := by
  classical
  intro φ n
  let v : S.iwasawa.compact.toOpenSubgroup → InducedModule P := fun k =>
    ⟨fun h => actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h n,
      actual_scalar_coefficient_fiber F ζ hζ q S P J hJ μ hμ π hπ ε φ k n⟩
  have hvJ (j : J.toOpenSubgroup) (k k' : S.iwasawa.compact.toOpenSubgroup)
      (hk : (k' : ActualCover F ζ hζ q) = (k : ActualCover F ζ hζ q) * j) :
      v k' = v k := by
    apply Subtype.ext
    funext h
    exact congrArg (fun p : ℤ →₀ ℂ => p n)
      (actual_scalar_numerator_right_level F ζ hζ q S P J hJ ε μ hμ π hπ φ j k k' hk h)
  have hsmooth : SmoothVector (vectorRightTranslation (G := S.iwasawa.compact.toOpenSubgroup)) v := by
    refine ⟨J.toOpenSubgroup.comap S.iwasawa.compact.toOpenSubgroup.toSubgroup.subtype continuous_subtype_val, ?_⟩
    intro j hj
    funext k
    exact hvJ ⟨j, hj⟩ k (k * j) rfl
  have hborel : ∀ (b : S.borel.B) (k k' : S.iwasawa.compact.toOpenSubgroup),
      (k' : ActualCover F ζ hζ q) = (b : ActualCover F ζ hζ q) * k →
      v k' = inducingAction S.borel P (targetSign ε) 0 b (v k) := by
    intro b k k' hk
    have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
      have he : (b : ActualCover F ζ hζ q) = (k' : ActualCover F ζ hζ q) * (k : ActualCover F ζ hζ q)⁻¹ := by
        rw [hk, mul_inv_cancel_right]
      rw [he]
      exact S.iwasawa.compact.toOpenSubgroup.mul_mem k'.property
        (S.iwasawa.compact.toOpenSubgroup.inv_mem k.property)
    apply Subtype.ext
    funext h
    rw [actual_compact_action_eval F ζ hζ q S P (targetSign ε) b hb]
    exact congrArg (fun p : ℤ →₀ ℂ => p n)
      (actual_scalar_coefficient_borel F ζ hζ q S P J hJ μ hμ π hπ ε φ b k k' hk h)
  let ψ : compactPicture S.borel P S.iwasawa (targetSign ε) := ⟨v, hborel, hsmooth⟩
  refine ⟨⟨ψ, ?_⟩, ?_⟩
  · exact hvJ
  · intro k h
    rfl

end DedekindZetaZeroFree.KPRankOneShellRepair

end
