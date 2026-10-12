module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CompactBorelIntegralCovariance
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RightLevelInvariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)

theorem actual_compact_action_eval (δ : Sign) (b : S.borel.B)
    (hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup)
    (v : InducedModule P) (h : actualTorus F ζ hζ q) :
    (inducingAction S.borel P δ 0 b v).val h =
      v.val (h * (if δ = .plus then S.borel.retract b else S.borel.weyl (S.borel.retract b))) := by
  have hn := S.iwasawa.intersection_norm b hb
  cases δ <;> simp [inducingAction, inducingScalar, deltaHalf, normPower, hn,
    borelAction, weylConjugate]
  all_goals rfl

variable (J : CompactOpenLevel (ActualCover F ζ hζ q))
  (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
  (π : (LocalField F q)ˣ)
  (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
  (ε : Sign)

theorem actual_scalar_coefficient_fiber
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (k : S.iwasawa.compact.toOpenSubgroup) (n : ℤ) :
    (fun h => actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h n) ∈
      InducedModule P := by
  intro a h
  let c : ℂ := P.ωL a
  have he : actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k ((a : actualTorus F ζ hζ q) * h) =
      c • actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h := by
    apply KPTameTransposeUnitNumeratorSteps.Augmentation.scalar_laurent_chamber_unique (LocalField F q) ε
    intro s hs
    have h1 := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k ((a : actualTorus F ζ hζ q) * h)) s hs
    have h2 := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k h) s hs
    have hi : standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ.val k
        ((a : actualTorus F ζ hζ q) * h) =
        c * standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s φ.val k h := by
      change (∫ x, _ ∂μ) = c * ∫ x, _ ∂μ
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      exact (compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ.val).val
        (kernelW (LocalField F q) S.borel ε * (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * k) |>.property a h
    change _ = (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k ((a : actualTorus F ζ hζ q) * h)).sum _ at h1
    change _ = (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h).sum _ at h2
    rw [Finsupp.sum_smul_index (by intro i; simp)]
    simp_rw [mul_left_comm _ c]
    simp only [Finsupp.sum]
    rw [← Finset.mul_sum]
    change (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k ((a : actualTorus F ζ hζ q) * h)).sum _ =
      c * (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k h).sum _
    rw [← h1, ← h2, hi]
    ring
  have H := congrArg (fun p : ℤ →₀ ℂ => p n) he
  exact H

theorem actual_scalar_coefficient_borel
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (b : S.borel.B) (k k' : S.iwasawa.compact.toOpenSubgroup)
    (hk : (k' : ActualCover F ζ hζ q) = (b : ActualCover F ζ hζ q) * k)
    (h : actualTorus F ζ hζ q) :
    actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k' h =
      actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k
        (h * (if targetSign ε = .plus then S.borel.retract b else S.borel.weyl (S.borel.retract b))) := by
  have hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    have he : (b : ActualCover F ζ hζ q) = (k' : ActualCover F ζ hζ q) * (k : ActualCover F ζ hζ q)⁻¹ := by
      rw [hk, mul_inv_cancel_right]
    rw [he]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem k'.property
      (S.iwasawa.compact.toOpenSubgroup.inv_mem k.property)
  apply KPTameTransposeUnitNumeratorSteps.Augmentation.scalar_laurent_chamber_unique (LocalField F q) ε
  intro s hs
  have h1 := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k' h) s hs
  have h2 := Classical.choose_spec (actual_scalar_numerator_coordinate F ζ hζ q S P J hJ μ hμ π hπ ε φ k
    (h * (if targetSign ε = .plus then S.borel.retract b else S.borel.weyl (S.borel.retract b)))) s hs
  change _ = (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k' h).sum _ at h1
  change _ = (actualScalarNumerator F ζ hζ q S P J hJ μ hμ π hπ ε φ k
    (h * (if targetSign ε = .plus then S.borel.retract b else S.borel.weyl (S.borel.retract b)))).sum _ at h2
  rw [← h1, ← h2, hk,
    actual_standard_integral_compact_borel_covariance F ζ hζ q S P J hJ μ hμ ε s hs φ b hb k h]
  simp_rw [actual_compact_action_eval F ζ hζ q S P (targetSign ε) b hb]
  rfl

end DedekindZetaZeroFree.KPRankOneShellRepair

end
