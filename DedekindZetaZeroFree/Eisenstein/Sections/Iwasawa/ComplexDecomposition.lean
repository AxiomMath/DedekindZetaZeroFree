module

public import DedekindZetaZeroFree.Eisenstein.Sections.Iwasawa.FullCompactProduct
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.NormalizedPauliFlows

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.PrincipalOfKP

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem complexLocal_borel_compact (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)) :
    ∃ (b : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w))
      (k : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w)),
      (∃ A : KPLocalCover.LocalGL2 F (Sum.inl w),
        A = KPLocalCover.projection F ζ hζ (Sum.inl w) b ∧ A 1 0 = 0) ∧
      k ∈ archimedeanLocalCompact F ζ hζ w ∧ g = b * k := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)
  let G := Matrix.GeneralLinearGroup.map e.toRingHom g.g
  obtain ⟨a,d,x,hG⟩ := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2_factor G
  let u := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2 G
  let B := Matrix.GeneralLinearGroup.map e.symm.toRingHom
    (KPCplxPrincipalSeriesCharts.upperTriangular a d x)
  let K := Matrix.GeneralLinearGroup.map e.symm.toRingHom
    (KPCplxCharacterHaar.complexSU2Embedding u)
  have hg : g.g = B * K := by
    have hi : Matrix.GeneralLinearGroup.map e.symm.toRingHom G = g.g := by
      dsimp [G]
      rw [← MonoidHom.comp_apply, ← Matrix.GeneralLinearGroup.map_comp]
      simp
    rw [← hi, hG, map_mul]
  refine ⟨⟨B,g.epsilon⟩, KPLocalCover.sectionMap F ζ hζ (Sum.inl w) K, ?_, ?_, ?_⟩
  · refine ⟨B,rfl,?_⟩
    simp [B, Matrix.GeneralLinearGroup.map_apply, KPCplxPrincipalSeriesCharts.upperTriangular]
  · apply Subgroup.subset_closure
    exact ⟨u,rfl⟩
  · change g = KPLocalCover.CubicGL2Raw.mk (B * K)
      (g.epsilon * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) B K)
    simp only [mul_one, KPLocalChartTopology.complex_sigmaTwo_eq_one]
    cases g
    congr 1

end DedekindZetaZeroFree.PrincipalOfKP

end
