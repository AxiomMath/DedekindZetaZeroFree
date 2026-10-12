module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ScalarLaurentNumerator
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CoordinateIntegrability
public import DedekindZetaZeroFree.Analysis.FiniteSpectrumLaurentNumerators

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair

set_option maxHeartbeats 1000000

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)
  (P : Polarization S.heisenberg)
  (J : CompactOpenLevel (ActualCover F ζ hζ q))
  (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
    S.iwasawa.compact.toOpenSubgroup)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

def actualScalarNumerator
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) : ℤ →₀ ℂ :=
  Classical.choose
    (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k h)

private lemma standardIntegralCoordinate_eq_integral
    (s : ℂ) (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ
        (k : ActualCover F ζ hζ q) h =
      ∫ x, actualStandardIntegrand F ζ hζ q S P ε s φ k h x ∂μ :=
  rfl

private lemma actualStandardIntegrand_add_smul
    (s : ℂ) (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q)
    (a b : ℂ)
    (φ ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    actualStandardIntegrand F ζ hζ q S P ε s
        ((a • φ + b • ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
          compactPicture S.borel P S.iwasawa (sourceSign ε)) k h =
      a • actualStandardIntegrand F ζ hζ q S P ε s
          (φ : compactPicture S.borel P S.iwasawa (sourceSign ε)) k h +
      b • actualStandardIntegrand F ζ hζ q S P ε s
          (ψ : compactPicture S.borel P S.iwasawa (sourceSign ε)) k h := by
  funext x
  have hcoe : ((a • φ + b • ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
      compactPicture S.borel P S.iwasawa (sourceSign ε)) =
      a • (φ : compactPicture S.borel P S.iwasawa (sourceSign ε)) +
        b • (ψ : compactPicture S.borel P S.iwasawa (sourceSign ε)) := rfl
  simp only [actualStandardIntegrand, hcoe, map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  try simp

private lemma standardIntegralCoordinate_add_smul
    (hJ' : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup)
    (hμ' : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π' : (LocalField F q)ˣ)
    (hπ' : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π' : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q)
    (a b : ℂ)
    (φ ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (s : ℂ) (hs : convergenceHalfPlane ε s) :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
        ((a • φ + b • ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
          compactPicture S.borel P S.iwasawa (sourceSign ε))
        (k : ActualCover F ζ hζ q) h =
      a * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
          (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
          (k : ActualCover F ζ hζ q) h +
      b * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
          (ψ : compactPicture S.borel P S.iwasawa (sourceSign ε))
          (k : ActualCover F ζ hζ q) h := by
  have h1 := actual_standard_integral_coordinate_integrable F ζ hζ q S P J hJ' μ hμ' π' hπ'
    ε s hs φ k h
  have h2 := actual_standard_integral_coordinate_integrable F ζ hζ q S P J hJ' μ hμ' π' hπ'
    ε s hs ψ k h
  have hlin := actualStandardIntegrand_add_smul F ζ hζ q S P J ε s k h a b φ ψ
  have hcongr : (fun x => actualStandardIntegrand F ζ hζ q S P ε s
        ((a • φ + b • ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
          compactPicture S.borel P S.iwasawa (sourceSign ε)) k h x) =
      fun x => a * actualStandardIntegrand F ζ hζ q S P ε s
          (φ : compactPicture S.borel P S.iwasawa (sourceSign ε)) k h x +
        b * actualStandardIntegrand F ζ hζ q S P ε s
          (ψ : compactPicture S.borel P S.iwasawa (sourceSign ε)) k h x := by
    funext x
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrFun hlin x
  rw [standardIntegralCoordinate_eq_integral, standardIntegralCoordinate_eq_integral,
    standardIntegralCoordinate_eq_integral, hcongr,
    integral_add (h1.const_mul a) (h2.const_mul b), integral_const_mul, integral_const_mul]

private lemma finsupp_eval_add_smul (u : ℂ) (a b : ℂ) (p1 p2 : ℤ →₀ ℂ) :
    (a • p1 + b • p2).sum (fun n c => u ^ n * c) =
      a * p1.sum (fun n c => u ^ n * c) + b * p2.sum (fun n c => u ^ n * c) := by
  let ev : (ℤ →₀ ℂ) →ₗ[ℂ] ℂ :=
    Finsupp.lsum ℂ fun n : ℤ => LinearMap.mulLeft ℂ (u ^ n)
  have hev : ∀ p : ℤ →₀ ℂ, ev p = p.sum (fun n c => u ^ n * c) := by
    intro p
    rw [Finsupp.lsum_apply]
    rfl
  rw [← hev (a • p1 + b • p2), ← hev p1, ← hev p2, map_add, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul]

private theorem actualScalarNumerator_add_smul
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q)
    (a b : ℂ)
    (φ ψ : compactLevel S.borel P S.iwasawa (sourceSign ε) J) :
    actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε (a • φ + b • ψ) k h =
      a • actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h +
      b • actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε ψ k h := by
  have hp := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ
    π hπ ε φ k h)
  have hp' := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ
    π hπ ε ψ k h)
  have hpq := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ
    π hπ ε (a • φ + b • ψ) k h)
  refine DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps.Augmentation.scalar_laurent_chamber_unique
    (LocalField F q) ε _ _ ?_
  intro s hs
  simp only [actualScalarNumerator]
  rw [← hpq s hs, finsupp_eval_add_smul, ← hp s hs, ← hp' s hs,
    standardIntegralCoordinate_add_smul (hJ' := hJ) (hμ' := hμ) (π' := π) (hπ' := hπ)
      (k := k) (h := h) (a := a) (b := b) (φ := φ) (ψ := ψ) (s := s) (hs := hs)]
  ring

theorem actual_scalar_numerator_linear
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    IsLinearMap ℂ
      (fun φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J =>
        actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h) := by
  refine ⟨?_, ?_⟩
  · intro φ ψ
    simpa using actualScalarNumerator_add_smul F ζ hζ q S P J hJ μ hμ π hπ ε k h 1 1 φ ψ
  · intro c φ
    simpa using actualScalarNumerator_add_smul F ζ hζ q S P J hJ μ hμ π hπ ε k h c 0 φ φ

end DedekindZetaZeroFree.KPRankOneShellRepair

end
