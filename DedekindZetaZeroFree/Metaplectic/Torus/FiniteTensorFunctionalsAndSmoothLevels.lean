module

public import DedekindZetaZeroFree.Metaplectic.Torus.ProductScalarDescent
public import DedekindZetaZeroFree.Metaplectic.Torus.ScalarPhaseLevelsAndAnnihilatorSaturation

@[expose] public section

section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct
private theorem raw_diagonal (g : KPGlobalTorusFunctionData.E F ζ hζ)
    (x : RestrictedCover F ζ hζ)
    (hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) = g.val) :
    ∀ v, (x v).g 1 0 = 0 ∧ (x v).g 0 1 = 0 := by
  obtain ⟨A, hA, h10, h01⟩ := g.property
  have he : QuotientGroup.mk' (scalarSubgroup F) (restrictedProjection F ζ hζ x) =
      QuotientGroup.mk' (scalarSubgroup F) A := by
    change pglProjection F ζ hζ (scalarQuotient F ζ hζ (amalgamation F ζ hζ x)) = _
    rw [hx, hA]
  obtain ⟨s, ⟨u, hu⟩, hs⟩ := (QuotientGroup.mk'_eq_mk' (scalarSubgroup F)).mp he
  have hm : restrictedProjection F ζ hζ x = A * (Matrix.GeneralLinearGroup.scalar (Fin 2) u)⁻¹ := by
    rw [← hu] at hs
    exact eq_mul_inv_of_mul_eq hs
  have hd : (restrictedProjection F ζ hζ x) 1 0 = 0 ∧
      (restrictedProjection F ζ hζ x) 0 1 = 0 := by
    rw [hm]
    simp [Matrix.GeneralLinearGroup.coe_mul, ← map_inv,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.scalar, h10, h01]
  intro v
  have h := congrArg (adeleEval F v) hd.1
  have h' := congrArg (adeleEval F v) hd.2
  have hev := restrictedProjection_eval F ζ hζ x v
  have hh := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 1 0) hev
  have hh' := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 0 1) hev
  exact ⟨hh.symm.trans (by simpa [matrixEval] using h),
    hh'.symm.trans (by simpa [matrixEval] using h')⟩

private theorem raw_image_torus (x : RestrictedCover F ζ hζ)
    (hd : ∀ v, (x v).g 1 0 = 0 ∧ (x v).g 0 1 = 0) :
    scalarQuotient F ζ hζ (amalgamation F ζ hζ x) ∈ KPGlobalTorusFunctionData.E F ζ hζ := by
  refine ⟨restrictedProjection F ζ hζ x, rfl, ?_, ?_⟩
  · apply Prod.ext
    · funext w; exact (hd (Sum.inl w)).1
    · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).1
  · apply Prod.ext
    · funext w; exact (hd (Sum.inl w)).2
    · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).2

private theorem arch_mem_B
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ) (x : RestrictedCover F ζ hζ)
    (hd : ∀ v, (x v).g 1 0 = 0 ∧ (x v).g 0 1 = 0)
    (hf : ∀ q, x (Sum.inr q) = 1) :
    (⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ x), raw_image_torus F ζ hζ x hd⟩ :
      KPGlobalTorusFunctionData.E F ζ hζ) ∈ KPGlobalProductPolarizationCharacter.B F ζ hζ P := by
  let e : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ x), raw_image_torus F ζ hζ x hd⟩
  change ∀ v, KPGlobalCubicIdelePairing.classComparison F
    (KPGlobalProductPolarizationCharacter.pD F ζ hζ e) v ∈ (P.localData v).L
  intro v
  cases v with
  | inl w => rw [P.complex_full]; trivial
  | inr q =>
    change KPGlobalCubicIdelePairing.localClass F (Sum.inr q)
      (KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (KPGlobalTorusFunctionData.p F ζ hζ e)) ∈ _
    have hmat : (restrictedProjection F ζ hζ x) 1 0 = 0 ∧
        (restrictedProjection F ζ hζ x) 0 1 = 0 := by
      constructor
      · apply Prod.ext
        · funext w; exact (hd (Sum.inl w)).1
        · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).1
      · apply Prod.ext
        · funext w; exact (hd (Sum.inl w)).2
        · apply RestrictedProduct.ext; intro q; exact (hd (Sum.inr q)).2
    have hr := KPGlobalTorusFunctionData.ratio_formula F
      ⟨_, e.property⟩ (restrictedProjection F ζ hζ x) rfl hmat.1 hmat.2
    have heval : KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q)
        (KPGlobalTorusFunctionData.p F ζ hζ e) = 1 := by
      apply Units.ext
      have h := congrArg (adeleEval F (Sum.inr q)) hr
      have hev := restrictedProjection_eval F ζ hζ x (Sum.inr q)
      rw [hf q, map_one] at hev
      have h00 := congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M 0 0) hev
      have h11 := congrArg (fun M : KPLocalCover.LocalGL2 F (Sum.inr q) => M 1 1) hev
      have h00' : adeleEval F (Sum.inr q) ((restrictedProjection F ζ hζ x) 0 0) = 1 := by
        simpa [matrixEval] using h00
      have h11' : adeleEval F (Sum.inr q) ((restrictedProjection F ζ hζ x) 1 1) = 1 := by
        simpa [matrixEval] using h11
      change adeleEval F (Sum.inr q)
        ((KPGlobalTorusFunctionData.torusRatio F ⟨_, e.property⟩ : Ideles F) : Adeles F) = 1
      simpa [map_mul, IsUnit.unit_spec, h00', h11'] using h
    rw [heval, map_one]
    exact (P.localData (Sum.inr q)).L.one_mem

theorem raw_product_polarization_finite_coset_cover
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hH : Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P)
    (g : KPGlobalTorusFunctionData.E F ζ hζ) :
    ∃ (b : Q.H) (a : KPGlobalTorusFunctionData.E F ζ hζ)
      (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
      (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
      g = b.val * a ∧
      (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
      (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ
        (Sum.inr q) (raw (Sum.inr q))) ∧
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = a.val := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (splitScalarSubgroup F ζ hζ) g.val
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (M F ζ hζ) u
  have hxg : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) = g.val :=
    (congrArg (scalarQuotient F ζ hζ) hx).trans hu
  have hd := raw_diagonal F ζ hζ g x hxg
  let xi : RestrictedCover F ζ hζ :=
    ⟨fun v => match v with | Sum.inl w => x (Sum.inl w) | Sum.inr _ => 1,
      Filter.Eventually.of_forall (by intro v; cases v <;> simp [compact, Subgroup.one_mem])⟩
  let xf : RestrictedCover F ζ hζ :=
    ⟨fun v => match v with | Sum.inl _ => 1 | Sum.inr q => x (Sum.inr q),
      x.property.mono (by
        intro v hv
        cases v with
        | inl w => trivial
        | inr q => exact hv)⟩
  have hdi : ∀ v, (xi v).g 1 0 = 0 ∧ (xi v).g 0 1 = 0 := by
    intro v; cases v with
    | inl w => exact hd (Sum.inl w)
    | inr q => simp [xi, KPLocalCover.one_g]
  have hdf : ∀ v, (xf v).g 1 0 = 0 ∧ (xf v).g 0 1 = 0 := by
    intro v; cases v with
    | inl w => simp [xf, KPLocalCover.one_g]
    | inr q => exact hd (Sum.inr q)
  let bi : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ xi), raw_image_torus F ζ hζ xi hdi⟩
  have hb : bi ∈ Q.H := by
    rw [hH]
    exact arch_mem_B F ζ hζ P xi hdi (fun _ => rfl)
  let af : KPGlobalTorusFunctionData.E F ζ hζ :=
    ⟨scalarQuotient F ζ hζ (amalgamation F ζ hζ xf), raw_image_torus F ζ hζ xf hdf⟩
  have ht : ∀ q, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (xf (Sum.inr q)) ∈
      KPLocalExceptionalConstruction.actualTorus F ζ hζ q := by
    intro q
    refine ⟨(xf (Sum.inr q)).g, rfl, (hdf (Sum.inr q)).1, (hdf (Sum.inr q)).2⟩
  refine ⟨⟨bi, hb⟩, af, xf, fun q => ⟨_, ht q⟩, ?_,
    (fun _ => rfl), (fun _ => rfl), rfl⟩
  apply Subtype.ext
  change g.val = scalarQuotient F ζ hζ (amalgamation F ζ hζ xi) *
    scalarQuotient F ζ hζ (amalgamation F ζ hζ xf)
  rw [← map_mul, ← map_mul, ← hxg]
  congr 2
  apply RestrictedProduct.ext
  intro v
  change x v = xi v * xf v
  cases v <;> simp [xi, xf]

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end

section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section

private theorem diagonal_torus_closed
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) :
    IsClosed (KPRankOneInduction.diagonalTorus F q : Set (KPRankOneInduction.PGL2 F q)) := by
  apply (QuotientGroup.isQuotientMap_mk
    (Subgroup.center (KPRankOneInduction.GL2 F q))).isClosed_preimage.mp
  have he : Matrix.ProjGenLinGroup.mk ⁻¹'
      (KPRankOneInduction.diagonalTorus F q : Set _) =
      {A : KPRankOneInduction.GL2 F q | A 1 0 = 0 ∧ A 0 1 = 0} := by
    ext A
    constructor
    · rintro ⟨B, hB, h10, h01⟩
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
      rw [← hu]
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
    · intro h
      exact ⟨A, rfl, h⟩
  change IsClosed ((Matrix.ProjGenLinGroup.mk :
    KPRankOneInduction.GL2 F q → KPRankOneInduction.PGL2 F q) ⁻¹'
    (KPRankOneInduction.diagonalTorus F q : Set (KPRankOneInduction.PGL2 F q)))
  rw [he]
  have hc (i j : Fin 2) : Continuous (fun A : KPRankOneInduction.GL2 F q => A i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_val : Continuous (fun A : KPRankOneInduction.GL2 F q =>
        (A : Matrix (Fin 2) (Fin 2) (q.adicCompletion F)))))
  exact (isClosed_eq (hc 1 0) continuous_const).inter
    (isClosed_eq (hc 0 1) continuous_const)

theorem raw_local_vector_compact_norm_one_stabilizer
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F))
    (f : KPLocalStoneVonNeumann.InducedModule (C.polarization q)) :
    ∃ K : OpenSubgroup (KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
      IsCompact (K : Set (KPLocalExceptionalConstruction.actualTorus F ζ hζ q)) ∧
      (∀ k : K, KPLocalStoneVonNeumann.tau (C.polarization q) k.val f = f) ∧
      (∀ k : K, KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate k.val) = 1) := by
  let S := C.canonical q
  let ht := KPPGLLocalCover.finite_topological_cover F ζ hζ q
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)
  have hp : Continuous (KPLocalSmoothRepresentation.projection F ζ hζ q) :=
    (by
      letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
      apply (QuotientGroup.isQuotientMap_mk
        (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))).continuous_iff.mpr
      exact QuotientGroup.continuous_mk :
        Continuous (KPLocalSmoothRepresentation.ordinaryPGLMap F q)).comp
          ht.2.2.2.1.continuous
  have hclosed : IsClosed
      (KPLocalExceptionalConstruction.actualTorus F ζ hζ q : Set
        (KPLocalExceptionalConstruction.ActualCover F ζ hζ q)) :=
    (diagonal_torus_closed F q).preimage hp
  let U := OpenSubgroup.comap
    (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype
    continuous_subtype_val S.iwasawa.compact.toOpenSubgroup
  have hUc : IsCompact (U : Set (KPLocalExceptionalConstruction.actualTorus F ζ hζ q)) :=
    hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage S.iwasawa.compact.isCompact
  obtain ⟨J, hJ⟩ := KPLocalStoneVonNeumann.tau_smooth S.heisenberg (C.polarization q) f
  refine ⟨J ⊓ U, hUc.inter_left J.isClosed, ?_, ?_⟩
  · intro k
    exact hJ k.val k.property.1
  · intro k
    have hnorm : KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
        (S.borel.coordinate k.val) = 1 := by
      have h := S.iwasawa.intersection_norm (S.borel.torus k.val) (by
        rw [S.torus_full]
        exact k.property.2)
      change KPLocalPrincipalSeries.localAbs (q.adicCompletion F)
        (S.borel.coordinate (S.borel.retract (S.borel.torus k.val))) = 1 at h
      simpa only [S.borel.retract_torus] using h
    have hroot : Real.rpow
        (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          (S.borel.coordinate k.val)) (1 / 6 : ℝ) = 1 := by
      have h := congrArg (fun u : ℂˣ => (u : ℂ))
        (ProductPolarization.fullnorm_bridgefinite F q (S.borel.coordinate k.val))
      have hc : (Real.rpow
          (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
            (S.borel.coordinate k.val)) (1 / 6 : ℝ) : ℂ) = 1 := by
        simpa [KPGlobalCenterRationalCharacter.positiveComplex,
          KPGlobalCenterRationalCharacter.sixthPower, ActualFiniteTorus.normUnit,
          KPLocalPrincipalSeries.normPower, hnorm, NNReal.coe_rpow] using h
      exact_mod_cast hc
    apply NNReal.eq
    exact (Real.rpow_left_inj (by positivity) (by positivity)
      (by norm_num : (1 / 6 : ℝ) ≠ 0)).mp (by simpa using hroot)

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end

section

open scoped NumberField Classical ComplexOrder Topology NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
attribute [local instance] KPAdelicCoverRestrictedProduct.pglLocalTopology

private theorem local_subordinate (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    (K : OpenSubgroup (KPLocalExceptionalConstruction.actualTorus F ζ hζ q)) :
    ∃ L : CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F ζ hζ q),
      ∀ t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q,
        t.val ∈ L.toOpenSubgroup → t ∈ K := by
  obtain ⟨V, hV, he⟩ := isOpen_induced_iff.mp K.isOpen
  have h1 : (1 : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈ V := by
    change (1 : KPLocalExceptionalConstruction.actualTorus F ζ hζ q).val ∈ V
    rw [← Set.mem_preimage, he]
    exact K.one_mem
  obtain ⟨L, hL⟩ := KPLocalPrincipalSeriesCuspidalExclusion.actual_cover_compact_open_basis
    F ζ hζ q (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q) V (hV.mem_nhds h1)
  refine ⟨L, ?_⟩
  intro t ht
  change t ∈ (K : Set _)
  rw [← he]
  exact hL ht
private theorem norm_one_bridge (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F)) (y : (q.adicCompletion F)ˣ)
    (h : KPLocalPrincipalSeries.localAbs (q.adicCompletion F) y = 1) :
    KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y = 1 := by
  have hb := congrArg (fun u : ℂˣ => (u : ℂ))
    (ProductPolarization.fullnorm_bridgefinite F q y)
  have he : ((KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) y ^
      (1 / 6 : ℝ) : ℝ≥0) : ℂ) = 1 := by
    simpa [KPGlobalCenterRationalCharacter.positiveComplex,
      KPGlobalCenterRationalCharacter.sixthPower, ActualFiniteTorus.normUnit,
      KPLocalPrincipalSeries.normPower, h, NNReal.coe_rpow] using hb
  apply NNReal.rpow_left_injective (by norm_num : (1 / 6 : ℝ) ≠ 0)
  apply NNReal.eq
  apply Complex.ofReal_injective
  simpa using he

theorem raw_finite_level_subordinate_to_local_torus_subgroups
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (K : ∀ q : S, OpenSubgroup
      (KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val))
    (hcompact : ∀ q : S, IsCompact
      (K q : Set (KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val)))
    (hnorm : ∀ (q : S) (k : K q),
      KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate k.val) = 1) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ j : KPGlobalTorusFunctionData.E F ζ hζ,
        j ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype →
        ∃ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
          (k : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
          (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
          (∀ q, (k q).val = KPPGLLocalCover.coverQuotient F ζ hζ
            (Sum.inr q) (raw (Sum.inr q))) ∧
          KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
            (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = j.val ∧
          (∀ q : S, k q.val ∈ K q) ∧
          (∀ q, q ∉ S → k q ∈ KPLocalGoodSphericalImage.compactTorus
            (C.canonical q).borel (C.canonical q).iwasawa) ∧
          (∀ q, KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
            ((C.canonical q).borel.coordinate (k q)) = 1) := by
  classical
  obtain ⟨L, hL⟩ := Classical.axiomOfChoice (fun q : S =>
    local_subordinate F ζ hζ q.val (K q))
  let D : ActualFiniteFactor.ProductLevelData F ζ hζ :=
    ⟨fun q => if h : q ∈ S then
      ⟨⟨(L ⟨q, h⟩).toOpenSubgroup.toSubgroup, (L ⟨q, h⟩).toOpenSubgroup.isOpen⟩,
        (L ⟨q, h⟩).isCompact⟩ else
      ⟨⟨(C.canonical q).iwasawa.compact.toOpenSubgroup.toSubgroup,
        (C.canonical q).iwasawa.compact.toOpenSubgroup.isOpen⟩,
        (C.canonical q).iwasawa.compact.isCompact⟩, by
      filter_upwards [S.eventually_cofinite_notMem,
        (KPAdelicCoverRestrictedProduct.bad_finite F).eventually_cofinite_notMem] with q hq hb
      simp only [dif_neg hq]
      obtain ⟨ht, hc⟩ := C.actual_compact q (fun he => hq (hS he))
      rw [hc]
      change (KPLocalExceptionalConstruction.actualGoodCompactSplit F ζ hζ q ht).range =
        (KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q).map
          (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q))
      simp only [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hb]
      rw [KPLocalExceptionalConstruction.actualGoodCompactSplit, MonoidHom.range_comp]⟩
  have hf := KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ
  have hc := ActualFiniteFactor.productSubgroup_compact_open F ζ hζ D
  rw [← hf] at hc
  let J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨⟨(ActualFiniteFactor.productSubgroup F ζ hζ D).comap
      (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype, hc.2⟩, hc.1⟩
  refine ⟨J, ?_⟩
  intro j hj
  obtain ⟨u, hu, heu⟩ := hj
  obtain ⟨raw, hr, he⟩ := hu
  have heglobal : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = j.val :=
    he.trans heu
  have hd : ∀ v, (raw v).g 1 0 = 0 ∧ (raw v).g 0 1 = 0 := by
    obtain ⟨A, hA, h10, h01⟩ := j.property
    have heq : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
        (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ raw) =
        QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A := by
      change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
        (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw)) = _
      rw [heglobal, hA]
    obtain ⟨s, ⟨a, ha⟩, hs⟩ :=
      (QuotientGroup.mk'_eq_mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).mp heq
    have hm : KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ raw =
        A * (Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ := by
      rw [← ha] at hs
      exact eq_mul_inv_of_mul_eq hs
    have hdiag : (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ raw) 1 0 = 0 ∧
        (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ raw) 0 1 = 0 := by
      rw [hm]
      simp [Matrix.GeneralLinearGroup.coe_mul, ← map_inv,
        Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Matrix.scalar, h10, h01]
    intro v
    have hv := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ raw v
    have hv10 := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 1 0) hv
    have hv01 := congrArg (fun M : KPLocalCover.LocalGL2 F v => M 0 1) hv
    exact ⟨hv10.symm.trans (by simpa [KPAdelicCoverRestrictedProduct.matrixEval] using
      (congrArg (KPAdelicCoverRestrictedProduct.adeleEval F v) hdiag.1)),
      hv01.symm.trans (by simpa [KPAdelicCoverRestrictedProduct.matrixEval] using
        (congrArg (KPAdelicCoverRestrictedProduct.adeleEval F v) hdiag.2))⟩
  let k (q : HeightOneSpectrum (𝓞 F)) :
      KPLocalExceptionalConstruction.actualTorus F ζ hζ q :=
    ⟨KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)),
      ⟨(raw (Sum.inr q)).g, rfl, (hd (Sum.inr q)).1, (hd (Sum.inr q)).2⟩⟩
  have hk : ∀ q, (k q).val ∈ (D.localLevel q).toOpenSubgroup :=
    fun q => Subgroup.mem_iInf.mp hr.2 q
  have hkS : ∀ q : S, k q.val ∈ K q := by
    intro q
    apply hL q
    have ht := hk q.val
    change (k q.val).val ∈ ((D.localLevel q.val).toOpenSubgroup : Subgroup _) at ht
    change (k q.val).val ∈ ((L q).toOpenSubgroup : Subgroup _)
    simpa only [D, dif_pos q.property] using ht
  have hkI : ∀ q, q ∉ S → (k q).val ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup := by
    intro q hq
    have ht := hk q
    change (k q).val ∈ ((D.localLevel q).toOpenSubgroup : Subgroup _) at ht
    change (k q).val ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup _)
    simpa only [D, dif_neg hq] using ht
  refine ⟨raw, k, hr.1, fun _ => rfl, heglobal, hkS, ?_, ?_⟩
  · intro q hq
    change ((C.canonical q).borel.torus (k q) :
      KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
        (C.canonical q).iwasawa.compact.toOpenSubgroup
    rw [(C.canonical q).torus_full]
    exact hkI q hq
  · intro q
    by_cases hq : q ∈ S
    · exact hnorm ⟨q, hq⟩ ⟨k q, hkS ⟨q, hq⟩⟩
    · apply norm_one_bridge F ζ hζ q
      have hn := (C.canonical q).iwasawa.intersection_norm
        ((C.canonical q).borel.torus (k q)) (by
          rw [(C.canonical q).torus_full]
          exact hkI q hq)
      simpa only [(C.canonical q).borel.retract_torus] using hn

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end

section

open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

theorem raw_pure_scalar_archSmooth
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : RawUnitProductModel F ζ hζ P T Q)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q) :
    v ∈ KPGlobalTorusFunctionData.ArchSmooth Q.H Q.character.toMonoidHom
      (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
      (KPGlobalTorusFunctionData.torusArchDomain F) := by
  apply archSmooth_of_chart_character_one F ζ hζ Q
  exact KPGlobalTorusFiniteStagesCofinality.normalized_arch_chart_character_one
    F ζ hζ P T Q (Or.inr hQ)

theorem raw_local_evaluation_right_invariant
    (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F))
    (f : KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (k : KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (hfix : KPLocalStoneVonNeumann.tau (C.polarization q) k f = f)
    (hnorm : KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate k) = 1)
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    C.evaluation q f (t * k) = C.evaluation q f t := by
  have hf : f.val (t * k) = f.val t :=
    congrArg (fun v : KPLocalStoneVonNeumann.InducedModule (C.polarization q) => v.val t)
      hfix
  rw [C.evaluation_formula, C.evaluation_formula, hf, map_mul]
  have hn : KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
      ((C.canonical q).borel.coordinate t * (C.canonical q).borel.coordinate k) =
      KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
        ((C.canonical q).borel.coordinate t) := by
    change ‖((C.canonical q).borel.coordinate t *
      (C.canonical q).borel.coordinate k : (q.adicCompletion F)ˣ).val‖₊ = _
    change ‖((C.canonical q).borel.coordinate k).val‖₊ = 1 at hnorm
    simp only [Units.val_mul, nnnorm_mul, hnorm, mul_one]
    rfl
  rw [hn]

theorem raw_reference_fixed_of_character_one
    (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F))
    (k : (C.polarization q).L.comap (C.canonical q).heisenberg.π)
    (hk : (C.polarization q).ωL k = 1) :
    KPLocalStoneVonNeumann.tau (C.polarization q) k.val (C.reference q) =
      C.reference q := by
  apply Subtype.ext
  funext t
  change (C.reference q).val (t * k.val) = (C.reference q).val t
  have hmem : (C.canonical q).heisenberg.π (t * k.val) ∈ (C.polarization q).L ↔
      (C.canonical q).heisenberg.π t ∈ (C.polarization q).L := by
    rw [map_mul]
    exact (C.polarization q).L.mul_mem_cancel_right k.property
  rw [C.reference_formula, C.reference_formula]
  split_ifs with htk ht ht
  · have he : (⟨t * k.val, htk⟩ :
        (C.polarization q).L.comap (C.canonical q).heisenberg.π) =
        ⟨t, ht⟩ * k := rfl
    rw [he, map_mul, hk, mul_one]
  · exact False.elim (ht (hmem.mp htk))
  · exact False.elim (htk (hmem.mpr ht))
  · rfl

theorem raw_reference_compact_fixed
    (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional) :
    C.reference q ∈ fixedSubmodule (KPLocalStoneVonNeumann.tau (C.polarization q))
      (KPLocalGoodSphericalImage.compactTorus (C.canonical q).borel
        (C.canonical q).iwasawa) := by
  intro k
  have hpol : (C.canonical q).heisenberg.π k.val ∈ (C.polarization q).L := by
    rw [← (C.unramified q hq).polarization_image]
    exact Subgroup.mem_map.mpr ⟨k.val, k.property, rfl⟩
  exact raw_reference_fixed_of_character_one F ζ hζ P T C q ⟨k.val, hpol⟩
    ((C.unramified q hq).character_trivial k hpol)

theorem raw_pure_scalar_smooth_level_of_raw_lifts
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : RawUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hv : RawPureScalarFormula F ζ hζ P T C Q S f v)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hcover : ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
      ∃ (b : Q.H) (a : KPGlobalTorusFunctionData.E F ζ hζ)
        (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
        g = b.val * a ∧
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
        (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ
          (Sum.inr q) (raw (Sum.inr q))) ∧
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = a.val)
    (hlifts : ∀ j : KPGlobalTorusFunctionData.E F ζ hζ,
      j ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ J).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype →
      ∃ (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
        (k : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
        (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) ∧
        (∀ q, (k q).val = KPPGLLocalCover.coverQuotient F ζ hζ
          (Sum.inr q) (raw (Sum.inr q))) ∧
        KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = j.val ∧
        (∀ q, KPLocalStoneVonNeumann.tau (C.polarization q) (k q)
          (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) =
          (if h : q ∈ S then f ⟨q, h⟩ else C.reference q)) ∧
        (∀ q, KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          ((C.canonical q).borel.coordinate (k q)) = 1)) :
    v ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J := by
  refine ⟨raw_pure_scalar_archSmooth F ζ hζ P T Q hQ v, ?_⟩
  intro j
  ext g
  change v.val (g * j.val) = v.val g
  obtain ⟨b, a, raw, t, rfl, hraw, ht, ha⟩ := hcover g
  obtain ⟨rj, k, hrj, hk, hj, hfix, hnorm⟩ := hlifts j.val j.property
  rw [mul_assoc, v.property b, v.property b]
  congr 1
  rw [hv raw t a hraw ht ha]
  have harch : ∀ w : InfinitePlace F, (raw * rj) (Sum.inl w) = 1 := by
    intro w
    change raw (Sum.inl w) * rj (Sum.inl w) = 1
    rw [hraw, hrj, one_mul]
  have hlocal : ∀ q, (t q * k q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        ((raw * rj) (Sum.inr q)) := by
    intro q
    change (t q).val * (k q).val = _
    rw [ht, hk, ← map_mul]
    rfl
  have hglobal : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (raw * rj)) =
      (a * j.val).val := by
    rw [map_mul, map_mul, ha, hj]
    rfl
  rw [hv (raw * rj) (fun q => t q * k q) (a * j.val) harch hlocal hglobal]
  apply finprod_congr
  intro q
  exact raw_local_evaluation_right_invariant F ζ hζ P T C q _ (k q)
    (hfix q) (hnorm q) (t q)

theorem raw_pure_scalar_has_smooth_level
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : RawUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hv : RawPureScalarFormula F ζ hζ P T C Q S f v) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      v ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J := by
  classical
  have hlocal := fun q : S =>
    raw_local_vector_compact_norm_one_stabilizer F ζ hζ P T C q.val (f q)
  choose K hcompact hfix hnorm using hlocal
  obtain ⟨J, hlifts⟩ := raw_finite_level_subordinate_to_local_torus_subgroups
    F ζ hζ P T C S hS K hcompact hnorm
  refine ⟨J, raw_pure_scalar_smooth_level_of_raw_lifts F ζ hζ P T C Q hQ
    S f v hv J (raw_product_polarization_finite_coset_cover F ζ hζ P Q hQ.1) ?_⟩
  intro j hj
  obtain ⟨raw, k, harch, htorus, hglobal, hKS, hgood, hkNorm⟩ := hlifts j hj
  refine ⟨raw, k, harch, htorus, hglobal, ?_, hkNorm⟩
  intro q
  by_cases hq : q ∈ S
  · rw [dif_pos hq]
    exact hfix ⟨q, hq⟩ ⟨k q, hKS ⟨q, hq⟩⟩
  · rw [dif_neg hq]
    exact raw_reference_compact_fixed F ζ hζ P T C q
      (fun he => hq (hS he)) ⟨k q, hgood q hq⟩

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

private theorem finprod_finite_modification {ι : Type*} (S : Finset ι)
    (a : S → ℂ) (b : ι → ℂ)
    (hf : Function.HasFiniteMulSupport (fun q => if h : q ∈ S then a ⟨q,h⟩ else b q)) :
    (∏ᶠ q, if h : q ∈ S then a ⟨q,h⟩ else b q) =
      (∏ q : S, a q) * (∏ᶠ q, if q ∈ S then 1 else b q) := by
  classical
  let f := fun q => if h : q ∈ S then a ⟨q,h⟩ else b q
  have hsplit := finprod_mem_inter_mul_sdiff' (f := f) (s := Set.univ) (S : Set ι)
    (by simpa only [Set.univ_inter, Function.HasFiniteMulSupport, f] using hf)
  simp only [Set.univ_inter, finprod_mem_univ] at hsplit
  have hin : (∏ᶠ q ∈ (S : Set ι), f q) = ∏ q : S, a q := by
    rw [← finprod_subtype_eq_finprod_cond, finprod_eq_prod_of_fintype]
    simp [f]
  have hout : (∏ᶠ q ∈ Set.univ \ (S : Set ι), f q) = ∏ᶠ q, if q ∈ S then 1 else b q := by
    rw [finprod_mem_def]
    apply finprod_congr
    intro q
    by_cases hq : q ∈ S <;> simp [Set.mulIndicator, hq, f]
  rw [hin, hout] at hsplit
  exact hsplit.symm

def IsUnitProductModel (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) : Prop :=
  Q.H = KPGlobalProductPolarizationCharacter.B F ζ hζ P ∧
  ∀ (r : Q.H) (s : KPGlobalProductPolarizationCharacter.B F ζ hζ P), r.val = s.val →
    Q.character r = KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T s /
      KPGlobalCenterRationalCharacter.positiveComplex
        (KPGlobalCenterRationalCharacter.nu F ζ hζ s.val)

def RawTensorFormula
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q) : Prop :=
  ∀ (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (g : KPGlobalTorusFunctionData.E F ζ hζ),
    (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) →
    (∀ q, (t q).val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) →
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val →
    (R (PiTensorProduct.tprod ℂ f)).val.val g =
      ∏ᶠ q, C.evaluation q (if h : q ∈ S then f ⟨q, h⟩ else C.reference q) (t q)

def rawEvaluationLinear (C : RawLocalScalarData F ζ hζ P T)
    (q : HeightOneSpectrum (𝓞 F)) (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    KPLocalStoneVonNeumann.InducedModule (C.polarization q) →ₗ[ℂ] ℂ where
  toFun f := C.evaluation q f t
  map_add' f k := by
    simp only [C.evaluation_formula, Submodule.coe_add, Pi.add_apply, add_div]
  map_smul' c f := by
    simp only [C.evaluation_formula, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_div_assoc c _ _

def rawFiniteTensorFunctional (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ] ℂ :=
  PiTensorProduct.lift ((∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (t q)) •
    ((MultilinearMap.mkPiAlgebra ℂ S ℂ).compLinearMap
      (fun q => rawEvaluationLinear F ζ hζ P T C q.val (t q.val))))

theorem rawFiniteTensorFunctional_tprod
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))) :
    rawFiniteTensorFunctional F ζ hζ P T C S t (PiTensorProduct.tprod ℂ f) =
      ∏ᶠ q, C.evaluation q (if h : q ∈ S then f ⟨q,h⟩ else C.reference q) (t q) := by
  have hf := restricted_local_evaluations_finite_support F ζ hζ P T C S hS f raw t ht
  have he : (fun q => C.evaluation q
      (if h : q ∈ S then f ⟨q,h⟩ else C.reference q) (t q)) =
      (fun q => if h : q ∈ S then C.evaluation q (f ⟨q,h⟩) (t q)
        else C.evaluation q (C.reference q) (t q)) := by
    funext q
    split <;> rfl
  rw [he] at hf ⊢
  rw [finprod_finite_modification S
    (fun q : S => C.evaluation q.val (f q) (t q.val))
    (fun q => C.evaluation q (C.reference q) (t q)) hf]
  simp only [rawFiniteTensorFunctional, PiTensorProduct.lift.tprod,
    MultilinearMap.smul_apply, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, rawEvaluationLinear, LinearMap.coe_mk,
    AddHom.coe_mk, smul_eq_mul]
  exact mul_comm _ _

theorem rawTensorFormula_eq_functional
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q)
    (hR : RawTensorFormula F ζ hζ P T C Q S R)
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q)
    (g : KPGlobalTorusFunctionData.E F ζ hζ)
    (hraw : ∀ w : InfinitePlace F, raw (Sum.inl w) = 1)
    (ht : ∀ q, (t q).val =
      KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)))
    (hg : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val)
    (x : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S) :
    (R x).val.val g = rawFiniteTensorFunctional F ζ hζ P T C S t x := by
  let ev : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q →ₗ[ℂ] ℂ :=
    (KPGlobalTorusFunctionData.evaluation Q.H Q.character.toMonoidHom g).comp
      (KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q).subtype
  have he : ev.comp R = rawFiniteTensorFunctional F ζ hζ P T C S t := by
    apply PiTensorProduct.ext
    ext f
    change (R (PiTensorProduct.tprod ℂ f)).val.val g =
      rawFiniteTensorFunctional F ζ hζ P T C S t (PiTensorProduct.tprod ℂ f)
    rw [rawFiniteTensorFunctional_tprod F ζ hζ P T C S hS f raw t ht]
    exact hR f raw t g hraw ht hg
  exact LinearMap.congr_fun he x

structure RawEvaluationPoint where
  raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ
  t : ∀ q, KPLocalExceptionalConstruction.actualTorus F ζ hζ q
  g : KPGlobalTorusFunctionData.E F ζ hζ
  infinite_one : ∀ w : InfinitePlace F, raw (Sum.inl w) = 1
  local_lift : ∀ q, (t q).val =
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q))
  global_lift : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = g.val

def rawSmoothRestriction (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q →ₗ[ℂ]
      (RawEvaluationPoint F ζ hζ → ℂ) where
  toFun u a := u.val.val a.g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rawTensorRestriction (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        (RawEvaluationPoint F ζ hζ → ℂ) where
  toFun x a := rawFiniteTensorFunctional F ζ hζ P T C S a.t x
  map_add' x y := by
    funext a
    exact (rawFiniteTensorFunctional F ζ hζ P T C S a.t).map_add x y
  map_smul' c x := by
    funext a
    exact (rawFiniteTensorFunctional F ζ hζ P T C S a.t).map_smul c x

theorem rawTensorFormula_iff_restriction_comp
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q) :
    RawTensorFormula F ζ hζ P T C Q S R ↔
      (rawSmoothRestriction F ζ hζ Q).comp R = rawTensorRestriction F ζ hζ P T C S := by
  constructor
  · intro hR
    apply LinearMap.ext
    intro x
    funext a
    exact rawTensorFormula_eq_functional F ζ hζ P T C Q S hS R hR
      a.raw a.t a.g a.infinite_one a.local_lift a.global_lift x
  · intro hR f raw t g hraw ht hg
    let a : RawEvaluationPoint F ζ hζ := ⟨raw, t, g, hraw, ht, hg⟩
    have h := congrFun (LinearMap.congr_fun hR (PiTensorProduct.tprod ℂ f)) a
    change (R (PiTensorProduct.tprod ℂ f)).val.val g =
      rawFiniteTensorFunctional F ζ hζ P T C S t (PiTensorProduct.tprod ℂ f) at h
    rw [rawFiniteTensorFunctional_tprod F ζ hζ P T C S hS f raw t ht] at h
    exact h

set_option backward.isDefEq.respectTransparency false in

theorem raw_finite_tensor_realization_iff_pure_extensions
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) :
    (∃ R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q,
      RawTensorFormula F ζ hζ P T C Q S R) ↔
    ∀ f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q),
      ∃ u : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q,
        ∀ a : RawEvaluationPoint F ζ hζ, u.val.val a.g =
          ∏ᶠ q, C.evaluation q (if h : q ∈ S then f ⟨q,h⟩ else C.reference q) (a.t q) := by
  constructor
  · rintro ⟨R, hR⟩ f
    exact ⟨R (PiTensorProduct.tprod ℂ f), fun a =>
      hR f a.raw a.t a.g a.infinite_one a.local_lift a.global_lift⟩
  · intro hext
    let A := rawSmoothRestriction F ζ hζ Q
    let B := rawTensorRestriction F ζ hζ P T C S
    have hpure (f : ∀ q : S, KPLocalStoneVonNeumann.InducedModule (C.polarization q)) :
        B (PiTensorProduct.tprod ℂ f) ∈ A.range := by
      obtain ⟨u, hu⟩ := hext f
      refine ⟨u, ?_⟩
      funext a
      change u.val.val a.g =
        rawFiniteTensorFunctional F ζ hζ P T C S a.t (PiTensorProduct.tprod ℂ f)
      rw [rawFiniteTensorFunctional_tprod F ζ hζ P T C S hS f a.raw a.t a.local_lift]
      exact hu a
    have hmem (x : RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S) :
        B x ∈ A.range := by
      induction x using PiTensorProduct.induction_on with
      | smul_tprod c f =>
        rw [B.map_smul]
        exact A.range.smul_mem c (hpure f)
      | add x y hx hy =>
        rw [B.map_add]
        exact A.range.add_mem hx hy
    letI : Module.Free ℂ (RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S) :=
        Module.Free.of_divisionRing ℂ (RestrictedTensorSimple.Stage
          (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S)
    letI : Module.Projective ℂ (RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S) :=
        Module.Projective.of_free
    obtain ⟨R, hR⟩ := Module.projective_lifting_property A.rangeRestrict
      (B.codRestrict A.range hmem) A.surjective_rangeRestrict
    refine ⟨R, (rawTensorFormula_iff_restriction_comp F ζ hζ P T C Q S hS R).mpr ?_⟩
    apply LinearMap.ext
    intro x
    funext a
    exact congrArg (fun z : A.range => z.val a) (LinearMap.congr_fun hR x)

theorem raw_finite_tensor_realization_exists
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S) :
    ∃ R : RestrictedTensorSimple.Stage
      (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S →ₗ[ℂ]
        KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q,
      RawTensorFormula F ζ hζ P T C Q S R := by
  apply (raw_finite_tensor_realization_iff_pure_extensions F ζ hζ P T C Q S hS).mpr
  intro f
  have hQraw : RawUnitProductModel F ζ hζ P T Q := hQ
  obtain ⟨v, hv⟩ := raw_pure_scalar_descent_exists F ζ hζ P T C Q hQraw S hS f
  obtain ⟨J, hJ⟩ := raw_pure_scalar_has_smooth_level F ζ hζ P T C Q hQraw S hS f v hv
  have hmem : v ∈ KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q :=
    (le_iSup (fun J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ =>
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J) J) hJ
  refine ⟨⟨v, hmem⟩, ?_⟩
  intro a
  exact hv a.raw a.t a.g a.infinite_one a.local_lift a.global_lift
end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end
