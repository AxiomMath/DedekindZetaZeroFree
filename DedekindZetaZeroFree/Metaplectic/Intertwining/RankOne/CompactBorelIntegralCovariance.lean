module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CoordinateIntegrability
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CompactBorelHeisenbergAction
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.AffineInvariance

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

theorem actual_standard_integral_compact_borel_covariance
    (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤
      S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ε : Sign) (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
    (b : S.borel.B)
    (hb : (b : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup)
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ ε s
        (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
        ((b : ActualCover F ζ hζ q) * (k : ActualCover F ζ hζ q)) h =
      ∫ x : LocalField F q,
        (inducingAction S.borel P (targetSign ε) 0 b
          ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
              (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))).val
            (kernelW (LocalField F q) S.borel ε *
              (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) *
              (k : ActualCover F ζ hζ q)))).val h ∂μ := by
  let f := compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition b
  let a : (LocalField F q)ˣ := (S.borel.coordinate (S.borel.retract b))⁻¹
  have ha : localAbs (LocalField F q) a = 1 := by
    have HH := localAbs_mul (LocalField F q)
      (S.borel.coordinate (S.borel.retract b)) (S.borel.coordinate (S.borel.retract b))⁻¹
    simpa [a, S.iwasawa.intersection_norm b hb, localAbs_one] using HH.symm
  let T : LocalField F q → ℂ := fun x =>
    (inducingAction S.borel P (targetSign ε) 0 b
      (f.val (kernelW (LocalField F q) S.borel ε *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * k))).val h
  have hp (x : LocalField F q) :
      (f.val (kernelW (LocalField F q) S.borel ε *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) *
        ((b : ActualCover F ζ hζ q) * k))).val h =
        T ((a : LocalField F q) * x + Multiplicative.toAdd t) := by
    have H := CompactBorel.kernel_borel F ζ hζ q S P ε b t ht x
    have Hk := congrArg (fun z : ActualCover F ζ hζ q => z * k) H
    simp only [mul_assoc] at Hk ⊢
    rw [Hk, f.property.1]
    rw [CompactBorel.source_weyl_action F ζ hζ q S P ε (sourceParameter ε s) b hb]
    simp only [T, a, mul_assoc]
  change (∫ x : LocalField F q, (f.val (kernelW (LocalField F q) S.borel ε *
    (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) *
    ((b : ActualCover F ζ hζ q) * k))).val h ∂μ) = ∫ x, T x ∂μ
  simp_rw [hp]
  exact CompactBorel.integral_affine F q μ a ha (Multiplicative.toAdd t) T

end DedekindZetaZeroFree.KPRankOneShellRepair

end
