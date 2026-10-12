module

public import DedekindZetaZeroFree.Metaplectic.Torus.NormalizedResidueCharacterExtensions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteral
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneRootParameter KPTameJacquetTestDuality
open KPTameTransposeKernelUnfolding KPTameValuationCoordinates
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (hP : IsTamePolarization F ζ hζ q S P)

theorem transport_test (h : HL F ζ hζ q S P)
    (a : ActualCover F ζ hζ q) (m : ℕ)
    (f : scalarSections F ζ hζ q S P hP .minus)
    (c : ℂ) (hc : chiH F ζ hζ q S P hP .minus h = c) (hc0 : c ≠ 0)
    (hf : IsMinusTest F ζ hζ q S P hP a m f) :
    IsMinusTest F ζ hζ q S P hP
      ((S.borel.torus h : ActualCover F ζ hζ q) * a) m (c⁻¹ • f) := by
  let b : BL F ζ hζ q S P :=
    ⟨(S.borel.torus h : ActualCover F ζ hζ q),
      ⟨S.borel.torus h, by
        change S.borel.retract (S.borel.torus h) ∈ HL F ζ hζ q S P
        rw [S.borel.retract_torus]
        exact h.property, rfl⟩⟩
  have hb : retractL F ζ hζ q S P b = h := by
    apply Subtype.ext
    change S.borel.retract (inBorel F ζ hζ q S P b) = h
    have hi : inBorel F ζ hζ q S P b = S.borel.torus h := Subtype.ext rfl
    rw [hi, S.borel.retract_torus]
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [map_smul, hf.1 k hk]
  · intro g hg
    have hg' : g ∈ Function.support f.val := by
      simpa only [Function.mem_support, Submodule.coe_smul, Pi.smul_apply,
        smul_eq_mul] using (show f.val g ≠ 0 from fun hz => hg (by simp [hz]))
    obtain ⟨b', k, hk, he⟩ := hf.2.1 hg'
    refine ⟨b' * b⁻¹, k, hk, ?_⟩
    rw [he]
    change (b' : ActualCover F ζ hζ q) * a * k * _ =
      ((b' : ActualCover F ζ hζ q) * (b : ActualCover F ζ hζ q)⁻¹) *
        ((b : ActualCover F ζ hζ q) * a) * k * _
    group
  · change c⁻¹ * f.val (((b : ActualCover F ζ hζ q) * a) * _) = 1
    rw [mul_assoc, f.property.1 b, chi, hb, hc, hf.2.2]
    simp [hc0]

end DedekindZetaZeroFree.KPTameTransposeLiteral

end
