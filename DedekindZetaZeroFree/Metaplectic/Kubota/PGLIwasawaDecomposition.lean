module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicMaximalCompactSubgroup
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.NormalizedPauliFlows
public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources NumberField
open scoped Classical NumberField Topology
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem complex_borel_compact_decomposition (R : PrincipalMellin.ActualRecipe S η)
    (w : InfinitePlace F)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)) :
    ∃ (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w))
      (k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w)),
      (∃ A : KPLocalCover.LocalGL2 F (Sum.inl w),
        A = KPLocalCover.projection F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) b ∧ A 1 0 = 0) ∧
      k ∈ complexSU2Compact R w ∧ g = b * k := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F R.A.zeta12 R.A.primitive_zeta12 w)
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
  refine ⟨⟨B,g.epsilon⟩, KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) K, ?_, ?_, ?_⟩
  · refine ⟨B,rfl,?_⟩
    simp [B, Matrix.GeneralLinearGroup.map_apply, KPCplxPrincipalSeriesCharts.upperTriangular]
  · apply Subgroup.subset_closure
    exact ⟨u,rfl⟩
  · change g = KPLocalCover.CubicGL2Raw.mk (B * K)
      (g.epsilon * 1 * KPLocalCover.sigmaTwo F R.A.zeta12 R.A.primitive_zeta12 (Sum.inl w) B K)
    simp only [mul_one, KPLocalChartTopology.complex_sigmaTwo_eq_one]
    cases g
    congr 1

theorem local_triangularize_by_iwasawa_compact (R : PrincipalMellin.ActualRecipe S η)
    (v : KPHilbert.Place F) (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v) :
    ∃ k : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 v,
      k ∈ iwasawaCompactFactor R v ∧ (g.g * k.g⁻¹) 1 0 = 0 := by
  cases v with
  | inl w =>
    obtain ⟨b,k,⟨A,hA,h10⟩,hk,hg⟩ := complex_borel_compact_decomposition R w g
    refine ⟨k,hk,?_⟩
    have he : g.g = b.g * k.g := congrArg KPLocalCover.CubicGL2Raw.g hg
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
    change A = b.g at hA
    rw [← hA]
    exact h10
  | inr q =>
    obtain ⟨r,hr⟩ := ActualFiniteBorel.IwasawaProof.triangularize F q g.g
    by_cases hb : KPAdelicCoverRestrictedProduct.Bad F q
    · refine ⟨KPLocalCover.sectionMap F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)
        (KPTameCompact.inclusion F q r⁻¹), ?_, ?_⟩
      · simp only [iwasawaCompactFactor, if_pos hb]
        exact ⟨r⁻¹,rfl⟩
      · simpa only [KPLocalCover.sectionMap_g, map_inv, inv_inv] using hr
    · let k := KPGoodCompactSplitting.kStar F R.A.zeta12 R.A.primitive_zeta12 q
        (fun h3 => hb (Or.inr h3)) r⁻¹
      refine ⟨k,?_,?_⟩
      · simp only [iwasawaCompactFactor, if_neg hb, KPAdelicCoverRestrictedProduct.finiteCompact]
        rw [dif_neg hb]
        exact ⟨r⁻¹,rfl⟩
      · have he : k.g = KPTameCompact.inclusion F q r⁻¹ := rfl
        rw [he, map_inv, inv_inv]
        exact hr

private theorem adele_ext {a b : KPAdelicCoverRestrictedProduct.Adeles F}
    (h : ∀ v, KPAdelicCoverRestrictedProduct.adeleEval F v a =
      KPAdelicCoverRestrictedProduct.adeleEval F v b) : a = b := by
  apply Prod.ext
  · funext w
    exact h (Sum.inl w)
  · apply RestrictedProduct.ext
    intro q
    exact h (Sum.inr q)

theorem adelic_pgl_iwasawa_decomposition (R : PrincipalMellin.ActualRecipe S η)
    (g : KPAdelicCoverRestrictedProduct.AdelicPGL2 F) :
    ∃ b : KPGlobalTorusFunctionData.ordinaryBorel F,
      ∃ k : fullProductCompact R,
        g = b.val * KPAdelicCoverRestrictedProduct.pglProjection F R.A.zeta12 R.A.primitive_zeta12 k.val := by
  obtain ⟨G,rfl⟩ := QuotientGroup.mk'_surjective (KPAdelicCoverRestrictedProduct.scalarSubgroup F) g
  obtain ⟨x,hx⟩ := KPAdelicCoverRestrictedProduct.restrictedProjection_surjective F R.A.zeta12 R.A.primitive_zeta12 G
  choose k hk ht using (fun v => local_triangularize_by_iwasawa_compact R v (x v))
  let y : KPAdelicCoverRestrictedProduct.RestrictedCover F R.A.zeta12 R.A.primitive_zeta12 :=
    ⟨k, by
      filter_upwards [iwasawa_compact_factor_eq_arithmetic_compact_eventually R] with v hv
      rw [← hv]
      exact hk v⟩
  have hy : y ∈ fullProductCompactPreimage R := hk
  let K := (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
    (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 y)
  have hK : K ∈ fullProductCompact R := ⟨y,hy,rfl⟩
  let B := G * (KPAdelicCoverRestrictedProduct.restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 y)⁻¹
  have hB : B 1 0 = 0 := by
    apply adele_ext
    intro v
    change (KPAdelicCoverRestrictedProduct.matrixEval F v B) 1 0 =
      KPAdelicCoverRestrictedProduct.adeleEval F v 0
    dsimp only [B]
    rw [map_mul, map_inv,
      KPAdelicCoverRestrictedProduct.restrictedProjection_eval]
    rw [← hx, KPAdelicCoverRestrictedProduct.restrictedProjection_eval]
    simpa only [KPLocalCover.projection_apply, map_zero, y, RestrictedProduct.mk_apply] using ht v
  refine ⟨⟨QuotientGroup.mk' _ B,⟨B,rfl,hB⟩⟩,⟨K,hK⟩,?_⟩
  change QuotientGroup.mk' _ G = QuotientGroup.mk' _ B *
    QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.restrictedProjection F R.A.zeta12 R.A.primitive_zeta12 y)
  rw [← map_mul]
  congr 1
  simp only [B, mul_assoc, inv_mul_cancel, mul_one]

theorem covered_iwasawa_decomposition (R : PrincipalMellin.ActualRecipe S η) (g : Group R) :
    ∃ (t : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) (x : KPAdeles F)
      (k : fullProductCompact R),
      g = (t.val * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x) * k.val := by
  obtain ⟨b,k,hbk⟩ := adelic_pgl_iwasawa_decomposition R
    (KPAdelicCoverRestrictedProduct.pglProjection F R.A.zeta12 R.A.primitive_zeta12 g)
  have hmem : g * k.val⁻¹ ∈ KPGlobalTorusFunctionData.borel F R.A.zeta12 R.A.primitive_zeta12 := by
    rw [KPGlobalTorusFunctionData.borel, Subgroup.mem_comap]
    rw [map_mul, map_inv, hbk, mul_assoc, mul_inv_cancel, mul_one]
    exact b.property
  obtain ⟨t,x,htx⟩ := KPGlobalTorusBorelTwistCompatibility.actual_borel_factorization
    F R.A.zeta12 R.A.primitive_zeta12 ⟨g * k.val⁻¹,hmem⟩
  refine ⟨t,x,k,?_⟩
  rw [← htx, mul_assoc, inv_mul_cancel, mul_one]

end DedekindZetaZeroFree.ThetaExpansion

end
