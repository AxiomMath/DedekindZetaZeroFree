module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.Metaplectic.Torus.ProductPolarizationCharacter

@[expose] public section

section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem canonical_good_compact_model_exists (q : HeightOneSpectrum (𝓞 F)) :
    ∃ S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q,
      ∀ hg : ¬ KPAdelicCoverRestrictedProduct.Bad F q,
        ∃ ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3,
          (S.iwasawa.compact.toOpenSubgroup :
            Subgroup (KPLocalExceptionalConstruction.ActualCover F ζ hζ q)) =
            (KPLocalExceptionalConstruction.actualGoodCompactSplit F ζ hζ q ht).range ∧
          ∀ b : S.borel.B,
            (b : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
                S.iwasawa.compact.toOpenSubgroup →
              S.borel.retract b ∈
                KPLocalGoodSphericalImage.compactTorus S.borel S.iwasawa := by
  classical
  obtain ⟨S⟩ := KPExceptionalRaw.exists_rawFiniteInducingData F ζ hζ q
  by_cases hbad : KPAdelicCoverRestrictedProduct.Bad F q
  · refine ⟨?_, ?_⟩
    · exact
        { D := S.D, groupD := S.groupD, finiteD := S.finiteD,
          cubeClassEquiv := S.cubeClassEquiv, heisenberg := S.heisenberg,
          borel := S.borel, borel_eq := S.borel_eq, torus_full := S.torus_full,
          coordinate_lift := S.coordinate_lift, cube_class := S.cube_class,
          center_exact := S.center_exact, cube_actual := S.cube_actual,
          central := S.central, central_actual := S.central_actual,
          central_character := S.central_character,
          center_parameterization := S.center_parameterization,
          prescribed_center := S.prescribed_center, split_scalars := S.split_scalars,
          polarization := S.polarization, iwasawa := S.iwasawa,
          openCell := S.openCell, openCell_ordinary := S.openCell_ordinary }
    · intro hg
      exact absurd hbad hg
  · have ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3 :=
      (not_or.mp hbad).2
    obtain ⟨I, hI⟩ :=
      KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_split_compact_iwasawa
        F ζ hζ q S ht
    refine ⟨?_, ?_⟩
    · exact
        { D := S.D, groupD := S.groupD, finiteD := S.finiteD,
          cubeClassEquiv := S.cubeClassEquiv, heisenberg := S.heisenberg,
          borel := S.borel, borel_eq := S.borel_eq, torus_full := S.torus_full,
          coordinate_lift := S.coordinate_lift, cube_class := S.cube_class,
          center_exact := S.center_exact, cube_actual := S.cube_actual,
          central := S.central, central_actual := S.central_actual,
          central_character := S.central_character,
          center_parameterization := S.center_parameterization,
          prescribed_center := S.prescribed_center, split_scalars := S.split_scalars,
          polarization := S.polarization, iwasawa := I,
          openCell := S.openCell, openCell_ordinary := S.openCell_ordinary }
    · intro hg
      refine ⟨ht, ?_, ?_⟩
      · simpa [KPLocalExceptionalConstruction.actualGoodCompactSplit] using hI
      · intro b hb
        have hbSubI : (b : KPExceptionalRaw.ActualCover F ζ hζ q) ∈
            (I.compact.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) := hb
        have hS : ((KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_split_compact_level
            F ζ hζ q ht).toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) =
            (I.compact.toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) := by
          rw [KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_split_compact_level_subgroup, hI]
        have hbSub : (b : KPExceptionalRaw.ActualCover F ζ hζ q) ∈
            ((KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_split_compact_level
              F ζ hζ q ht).toOpenSubgroup : Subgroup (KPExceptionalRaw.ActualCover F ζ hζ q)) := by
          rw [hS]; exact hbSubI
        have hb' : (b : KPExceptionalRaw.ActualCover F ζ hζ q) ∈
            (KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_split_compact_level
              F ζ hζ q ht).toOpenSubgroup := hbSub
        have hret :=
          KPExceptionalRaw.FiniteSource.GoodSphericalVector.actual_split_compact_retract
            F ζ hζ q S ht b hb'
        rw [KPLocalGoodSphericalImage.compactTorus, hI]
        simp only [Subgroup.mem_comap] at hret ⊢
        show (S.borel.torus (S.borel.retract b) : KPExceptionalRaw.ActualCover F ζ hζ q) ∈ _
        rw [S.torus_full]
        simpa [Subgroup.subtype] using hret

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps

end

section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps
noncomputable section
attribute [local instance] KPGlobalProductPolarizationCharacter.localCoverTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem continuous_of_isOpen_ker {G H : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : Continuous f := by
  rw [continuous_discrete_rng]
  intro b
  by_cases hb : b ∈ Set.range f
  · obtain ⟨g, hg⟩ := hb
    have heq : f ⁻¹' {b} = (fun x => g⁻¹ * x) ⁻¹' (f.ker : Set G) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker]
      constructor
      · intro hx
        rw [map_mul, map_inv, hx, hg, inv_mul_cancel]
      · intro hx
        rw [map_mul, map_inv] at hx
        rw [← inv_mul_eq_one.mp hx, hg]
    rw [heq]
    exact h.preimage (continuous_const.mul continuous_id)
  · rw [show f ⁻¹' {b} = ∅ from ?_]
    · exact isOpen_empty
    · ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hb ⟨x, hx⟩

private theorem local_discrete (v : KPHilbert.Place F) :
    DiscreteTopology (KPGlobalCubicIdelePairing.LocalD F v) := by
  cases v with
  | inl w =>
    letI := KPGlobalCubicIdelePairing.local_complex_trivial F w
    infer_instance
  | inr q =>
    let K := q.adicCompletion F
    letI : ValuativeRel K := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : IsNonarchimedeanLocalField K :=
      ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q
    obtain ⟨E, hE⟩ :=
      LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range K 3
        (Nat.cast_ne_zero.mpr (by decide))
    letI : FiniteDimensional K (E : IntermediateField K (SeparableClosure K)) := E.finiteDimensional
    letI : IsGalois K (E : IntermediateField K (SeparableClosure K)) := E.isGalois
    have hopen : IsOpen ((powMonoidHom 3 : Kˣ →* Kˣ).range : Set Kˣ) :=
      Subgroup.isOpen_mono hE (LocalClassFieldTheory.localNormSubgroup_isOpen K
        (E : IntermediateField K (SeparableClosure K)))
    exact QuotientGroup.discreteTopology hopen

private theorem localProjection_continuous (v : KPHilbert.Place F) :
    Continuous (KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v) := by
  cases v with
  | inl w =>
    haveI : Subsingleton (KPGlobalCubicIdelePairing.LocalD F (Sum.inl w)) :=
      KPGlobalCubicIdelePairing.local_complex_trivial F w
    rw [show ⇑(KPGlobalProductPolarizationCharacter.localProjection F ζ hζ (Sum.inl w)) =
        fun _ => 1 from funext fun x => Subsingleton.elim _ _]
    exact continuous_const
  | inr q =>
    haveI : DiscreteTopology (KPGlobalCubicIdelePairing.LocalD F (Sum.inr q)) :=
      local_discrete F (Sum.inr q)
    exact continuous_of_isOpen_ker
      (KPGlobalProductPolarizationCharacter.localProjection F ζ hζ (Sum.inr q))
      (ProductPolarization.finite_local_center_open F ζ hζ q)

theorem adjusted_local_character_exists (v : KPHilbert.Place F)
    (Q : KPGlobalProductPolarizationCharacter.LocalPolarization F ζ hζ v)
    (χ : Q.L →ₜ* ℂˣ) :
    ∃ psi : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ v Q.L →ₜ* ℂˣ,
      ∀ b, psi b = Q.lambda b *
        χ ⟨KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v b.val,
          b.property⟩ := by
  let φ : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ v Q.L →ₜ* Q.L :=
    { toFun := fun b => ⟨KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v b.val,
        b.property⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp
      continuous_toFun := Continuous.subtype_mk
        ((localProjection_continuous F ζ hζ v).comp continuous_subtype_val) (fun b => b.property) }
  exact ⟨Q.lambda * (χ.comp φ), fun b => rfl⟩

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps

end

section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps
noncomputable section
attribute [local instance] KPGlobalProductPolarizationCharacter.localCoverTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem actual_eq (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalExceptionalConstruction.actualTorus F ζ hζ q =
      KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q) := by
  letI : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
    KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  symm
  apply le_antisymm
  · intro g hg
    obtain ⟨y, hy⟩ := hg
    change KPLocalSmoothRepresentation.projection F ζ hζ q g ∈ KPRankOneInduction.diagonalTorus F q
    refine ⟨KPGlobalProductPolarizationCharacter.diagonalHom F (Sum.inr q) y, ?_, ?_, ?_⟩
    · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q) hy
    · simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d]
    · simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d]
  · intro g hg
    let h : ActualFiniteTorus.H F ζ hζ q := ⟨g,hg⟩
    have hn := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.1 h
    change KPPGLLocalCover.projection F ζ hζ (Sum.inr q) g ∈ KPGlobalProductPolarizationCharacter.localOrdinaryTorus F (Sum.inr q)
    rw [show g = ActualFiniteTorus.normalWord F ζ hζ q _ _ from hn]
    refine ⟨ActualFiniteTorus.coordinate F ζ hζ q h, ?_⟩
    simp only [ActualFiniteTorus.normalWord, map_mul]
    have hp : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (ActualFiniteTorus.sheet F ζ hζ q h)) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
      exact ⟨_, rfl⟩
    rw [hp, one_mul]
    rfl
 def torusEquiv (q : HeightOneSpectrum (𝓞 F)) :=
  MulEquiv.subgroupCongr (actual_eq F ζ hζ q)
private theorem coordinate_ratio (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    ActualFiniteTorus.coordinate F ζ hζ q t =
      KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) (torusEquiv F ζ hζ q t) := by
  apply Units.ext
  change (KPRankOneInduction.borelRatio F q _ : ActualFiniteTorus.K F q) = _
  rw [KPRankOneInduction.borelRatio_eq _ _ _ (KPGlobalProductPolarizationCharacter.diagonalHom F (Sum.inr q) (KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) (torusEquiv F ζ hζ q t)))]
  · simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d]
  · exact congrArg (KPLocalSmoothRepresentation.ordinaryPGLMap F q)
      (ProductPolarization.localRatioValue_spec F ζ hζ (Sum.inr q) (torusEquiv F ζ hζ q t))
  · simp [KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.d]
private theorem projection_eq (q : HeightOneSpectrum (𝓞 F))
    (t : KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :
    ActualFiniteTorus.π F ζ hζ q t =
      KPGlobalProductPolarizationCharacter.localProjection F ζ hζ (Sum.inr q) (torusEquiv F ζ hζ q t) := by
  change QuotientGroup.mk' _ (ActualFiniteTorus.coordinate F ζ hζ q t) = _
  rw [coordinate_ratio]
  rfl
private theorem pairing_eq (q : HeightOneSpectrum (𝓞 F))
    (x y : KPGlobalCubicIdelePairing.LocalD F (Sum.inr q)) :
    ActualFiniteTorus.pairing F ζ hζ q x y =
      ActualFiniteTorus.ordinaryMu3 F ζ hζ (KPGlobalCubicIdelePairing.localPairing F ζ hζ (Sum.inr q) x y) := by
  induction x using QuotientGroup.induction_on with | H x =>
    induction y using QuotientGroup.induction_on with | H y =>
      change ActualFiniteTorus.ordinaryMu3 F ζ hζ
        (KPHilbert.finiteThreePairing F ζ hζ q _ _) =
        ActualFiniteTorus.ordinaryMu3 F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q) x y)
      rw [KPHilbert.B3_canonical]
      rfl
private theorem mu3_eq_one (e : rootsOfUnity 3 F) :
    ActualFiniteTorus.ordinaryMu3 F ζ hζ e = 1 ↔ e = 1 := by
  constructor
  · intro h
    have hh : KPLocalCover.threeToSix F e = KPLocalCover.threeToSix F 1 :=
      KPLocalCover.coefficientEmbedding_injective F ζ hζ (by
        simpa [ActualFiniteTorus.ordinaryMu3, ActualFiniteTorus.ordinaryIota] using
          congrArg (fun x : rootsOfUnity 3 ℂ => x.val) h)
    apply Subtype.ext
    simpa [KPLocalCover.threeToSix] using congrArg (fun x : rootsOfUnity 6 F => (x.val : F)) hh
  · rintro rfl
    exact map_one _
private theorem preimage_maximal (q : HeightOneSpectrum (𝓞 F))
    (Q : KPGlobalProductPolarizationCharacter.LocalPolarization F ζ hζ (Sum.inr q)) :
    KPLocalPolarization.IsMaximalAbelian
      (Q.L.comap (ActualFiniteTorus.π F ζ hζ q)) := by
  apply KPLocalPolarization.preimage_maximal_abelian
    (ActualFiniteTorus.π F ζ hζ q)
    (ActualFiniteTorus.actual_cube_quotient_pairing F ζ hζ q).2.1
    (ActualFiniteTorus.pairing F ζ hζ q)
    (ActualFiniteTorus.actual_cube_quotient_pairing F ζ hζ q).2.2.2.2.2.2.1
  constructor
  · intro x hx y hy
    rw [pairing_eq, (Q.maximal.1 x hx y hy), map_one]
  · intro N hLN hN
    apply Q.maximal.2 N hLN
    intro x hx y hy
    apply (mu3_eq_one F ζ hζ _).mp
    rw [← pairing_eq]
    exact hN x hx y hy
private theorem center_value (q : HeightOneSpectrum (𝓞 F))
    (S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
    (a : S.heisenberg.C)
    (z : KPGlobalProductPolarizationCharacter.localCenter F ζ hζ (Sum.inr q))
    (haz : a.val.val = z.val.val) :
    S.heisenberg.ω a = KPGlobalProductPolarizationCharacter.localOmega F ζ hζ (Sum.inr q) z := by
  obtain ⟨e, x, y, rfl⟩ := S.center_parameterization a
  let u : (q.adicCompletion F)ˣ := x / y
  let g := KPLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
    KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (u ^ 3)
  have hg : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g = z.val.val := by
    rw [← haz]
    change _ = (S.central e).val.val * (S.borel.cubeLift u).val.val
    rw [S.central_actual, S.cube_actual]
    exact map_mul _ _ _
  rw [KPGlobalProductPolarizationCharacter.localOmega_raw_formula F ζ hζ _ z g hg]
  have hu : u ^ 3 ∈ CubicCharacters.cubes (KPHilbert.Completion F (Sum.inr q))ˣ := ⟨u, rfl⟩
  rw [show g = KPLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
    KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) (⟨u ^ 3, hu⟩ : CubicCharacters.cubes (KPHilbert.Completion F (Sum.inr q))ˣ).val from rfl,
    KPGlobalCenterRationalCharacter.localValue_finite_cube,
    ProductPolarization.fullnorm_bridgefinite]
  apply Units.ext
  rw [S.prescribed_center]
  change _ = (KPLocalExceptionalConstruction.ordinaryIota F ζ hζ e : ℂ) *
    KPLocalPrincipalSeries.normPower (q.adicCompletion F) (u ^ 3) (1 / 6)
  congr 1
  congr 1
  dsimp [u]
  exact (div_pow x y 3).symm

theorem transport_local_polarization_character
    (q : HeightOneSpectrum (𝓞 F))
    (S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
    (Q : KPGlobalProductPolarizationCharacter.LocalPolarization F ζ hζ (Sum.inr q))
    (psi : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      Q.L →ₜ* ℂˣ)
    (hpsi : ∀ (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ
        (Sum.inr q) Q.L)
      (z : KPGlobalProductPolarizationCharacter.localCenter F ζ hζ (Sum.inr q)),
      b.val = z.val → psi b =
        KPGlobalProductPolarizationCharacter.localOmega F ζ hζ (Sum.inr q) z) :
    ∃ A : Subgroup (KPLocalExceptionalConstruction.actualTorus F ζ hζ q),
      KPLocalPolarization.IsMaximalAbelian A ∧ S.heisenberg.C ≤ A ∧
      ∃ chi : A →ₜ* ℂˣ,
        (∀ (a : A) (ha : a.val ∈ S.heisenberg.C),
          chi a = S.heisenberg.ω ⟨a.val, ha⟩) ∧
        A.map (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype =
          (KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
            Q.L).map
            (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype ∧
        ∀ (a : A)
          (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q) Q.L),
          a.val.val = b.val.val → chi a = psi b := by
  let A : Subgroup (KPLocalExceptionalConstruction.actualTorus F ζ hζ q) :=
    Q.L.comap (ActualFiniteTorus.π F ζ hζ q)
  have hCA : S.heisenberg.C ≤ A := by
    intro t ht
    have ht' : t ∈ (ActualFiniteTorus.π F ζ hζ q).ker := by
      rw [(ActualFiniteTorus.actual_center_cube_normal_form F ζ hζ q).1]
      change t ∈ Subgroup.center _
      rw [← S.center_exact]
      exact ht
    change ActualFiniteTorus.π F ζ hζ q t ∈ Q.L
    rw [MonoidHom.mem_ker.mp ht']
    exact Q.L.one_mem
  let f : A →* KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q) Q.L :=
    { toFun := fun a => ⟨torusEquiv F ζ hζ q a.val, by
        change KPGlobalProductPolarizationCharacter.localProjection F ζ hζ (Sum.inr q)
          (torusEquiv F ζ hζ q a.val) ∈ Q.L
        rw [← projection_eq]
        exact a.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b => Subtype.ext (map_mul _ _ _) }
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  let chi : A →ₜ* ℂˣ := psi.comp ⟨f, hf⟩
  refine ⟨A, preimage_maximal F ζ hζ q Q, hCA, chi, ?_, ?_, ?_⟩
  · intro a ha
    let z : KPGlobalProductPolarizationCharacter.localCenter F ζ hζ (Sum.inr q) :=
      ⟨torusEquiv F ζ hζ q a.val, by
        change KPGlobalProductPolarizationCharacter.localProjection F ζ hζ (Sum.inr q)
          (torusEquiv F ζ hζ q a.val) = 1
        rw [← projection_eq]
        have hc : a.val ∈ (ActualFiniteTorus.π F ζ hζ q).ker := by
          rw [(ActualFiniteTorus.actual_center_cube_normal_form F ζ hζ q).1]
          change a.val ∈ Subgroup.center _
          rw [← S.center_exact]
          exact ha
        exact hc⟩
    change psi (f a) = _
    rw [hpsi (f a) z rfl]
    exact (center_value F ζ hζ q S ⟨a.val, ha⟩ z rfl).symm
  · ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact Subgroup.mem_map.mpr ⟨torusEquiv F ζ hζ q a,
        by change _ ∈ Q.L; rw [← projection_eq]; exact ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      let a := (torusEquiv F ζ hζ q).symm b
      have ha : a ∈ A := by
        change ActualFiniteTorus.π F ζ hζ q a ∈ Q.L
        rw [projection_eq, (torusEquiv F ζ hζ q).apply_symm_apply]
        exact hb
      exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  · intro a b hab
    change psi (f a) = psi b
    apply congrArg psi
    apply Subtype.ext
    apply Subtype.ext
    exact hab

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps

end

section
open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps
noncomputable section
attribute [local instance] KPGlobalProductPolarizationCharacter.localCoverTopology
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPLocalExceptionalConstruction

 def diagonalLift (q : HeightOneSpectrum (𝓞 F)) (y : (LocalField F q)ˣ) :
    actualTorus F ζ hζ q :=
  ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) y, by
    refine ⟨KubotaRankTwo.d (LocalField F q) y 1, ?_, ?_, ?_⟩
    · rfl
    · simp [KubotaRankTwo.d]
    · simp [KubotaRankTwo.d]⟩

private theorem pgl_diagonal_injective (K : Type*) [Field K] (u v : Kˣ)
    (huv : Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K u 1) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d K v 1)) : u = v := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp huv
  have h11 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 1 1) hc
  have h00 := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply] at h11 h00
  apply Units.ext
  calc
    (u : K) = (u : K) * (c : K) := by simp [h11]
    _ = (v : K) := h00

private lemma unit_lift_compact (v : HeightOneSpectrum (𝓞 F))
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (u : (KPTameCompact.O F v)ˣ) :
    diagonalLift F ζ hζ v (KPTameCompact.unitInclusion F v u) ∈ ((actualGoodCompactSplit F ζ hζ v ht).range.comap (actualTorus F ζ hζ v).subtype) := by
  let g : KPTameCompact.K0 F v := ⟨Matrix.diagonal ![(u : KPTameCompact.O F v), 1],
    Matrix.diagonal ![((u⁻¹ : (KPTameCompact.O F v)ˣ) : KPTameCompact.O F v), 1],
    by simp [Matrix.diagonal_mul_diagonal]; ext i; fin_cases i <;> simp,
    by simp [Matrix.diagonal_mul_diagonal]; ext i; fin_cases i <;> simp⟩
  have hg : (g : Matrix (Fin 2) (Fin 2) (KPTameCompact.O F v)) =
      !![(u : KPTameCompact.O F v), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  change (diagonalLift F ζ hζ v (KPTameCompact.unitInclusion F v u) : ActualCover F ζ hζ v) ∈
    (actualGoodCompactSplit F ζ hζ v ht).range
  refine ⟨g, ?_⟩
  change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr v)
    (KPGoodCompactSplitting.kStar F ζ hζ v ht g) = _
  rw [KPGoodCompactSplitting.kStar_unit_diagonal F ζ hζ v ht u 1 g (by simpa using hg)]
  congr 1
  apply congrArg (KPLocalCover.sectionMap F ζ hζ (Sum.inr v))
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma compact_coordinate_unit (v : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ v)
    (ht : ringChar (KPTameCompact.O F v ⧸ KPTameCompact.p F v) ≠ 3)
    (t : actualTorus F ζ hζ v) (htc : t ∈ ((actualGoodCompactSplit F ζ hζ v ht).range.comap (actualTorus F ζ hζ v).subtype)) :
    S.borel.coordinate t ∈ (KPRamifiedBeta.unitsInclusion (LocalField F v)).range := by
  obtain ⟨k, hk⟩ := htc
  have hp : Matrix.ProjGenLinGroup.mk (KPTameCompact.inclusion F v k) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F v) (S.borel.coordinate t) 1) := by
    rw [← S.borel.torus_projection, S.torus_full]
    obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective (t : ActualCover F ζ hζ v)
    have hpr := (S.openCell S.polarization).projection_eq r
    change S.borel.projection (QuotientGroup.mk r) = _ at hpr
    have he : S.borel.projection (t : ActualCover F ζ hζ v) =
        KPLocalSmoothRepresentation.projection F ζ hζ v (t : ActualCover F ζ hζ v) := by
      rw [← hr]
      exact hpr
    change (actualGoodCompactSplit F ζ hζ v ht) k = (t : ActualCover F ζ hζ v) at hk
    rw [he, ← hk]
    rfl
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h10 := congrArg (fun g : GL (Fin 2) (LocalField F v) => g 1 0) hc
  have h00 := congrArg (fun g : GL (Fin 2) (LocalField F v) => g 0 0) hc
  have h11 := congrArg (fun g : GL (Fin 2) (LocalField F v) => g 1 1) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.diagonal_apply] at h10 h00 h11
  have hk10 : k 1 0 = 0 := by
    apply Subtype.ext
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using h10
  have hdet : IsUnit (k 0 0 * k 1 1) := by
    simpa [Matrix.det_fin_two, hk10] using k.det.isUnit
  let a := (isUnit_of_mul_isUnit_left hdet).unit
  let b := (isUnit_of_mul_isUnit_right hdet).unit
  refine ⟨a / b, ?_⟩
  apply Units.ext
  simp only [map_div, Units.val_div_eq_div_val]
  change ((a : KPTameCompact.O F v) : LocalField F v) /
    ((b : KPTameCompact.O F v) : LocalField F v) = (S.borel.coordinate t : LocalField F v)
  rw [(isUnit_of_mul_isUnit_left hdet).unit_spec,
    (isUnit_of_mul_isUnit_right hdet).unit_spec]
  have ha : ((k 0 0 : KPTameCompact.O F v) : LocalField F v) * (c : LocalField F v) =
      (S.borel.coordinate t : LocalField F v) := by
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using h00
  have hb : ((k 1 1 : KPTameCompact.O F v) : LocalField F v) * (c : LocalField F v) = 1 := by
    simpa [KPTameCompact.inclusion, KPLocalCube.integerInclusion,
      Matrix.GeneralLinearGroup.map_apply] using h11
  calc
    _ = (((k 0 0 : KPTameCompact.O F v) : LocalField F v) * (c : LocalField F v)) /
        (((k 1 1 : KPTameCompact.O F v) : LocalField F v) * (c : LocalField F v)) :=
      (mul_div_mul_right _ _ c.ne_zero).symm
    _ = _ := by rw [ha, hb, div_one]

private lemma matching_coordinate (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q)
    (a : actualTorus F ζ hζ q)
    (b : KPGlobalProductPolarizationCharacter.LocalE F ζ hζ (Sum.inr q))
    (hab : a.val = b.val) :
    S.borel.coordinate a = KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) b := by
  apply pgl_diagonal_injective
  rw [← S.borel.torus_projection, S.torus_full]
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective a.val
  have hp := (S.openCell S.polarization).projection_eq r
  change S.borel.projection (QuotientGroup.mk r) = _ at hp
  rw [← hr, hp]
  change KPLocalSmoothRepresentation.ordinaryPGLMap F q
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr q) (QuotientGroup.mk r)) = _
  rw [hr, hab]
  have hs : KPPGLLocalCover.baseQuotient F (Sum.inr q)
      (KPGlobalProductPolarizationCharacter.diagonalHom F (Sum.inr q)
        (KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) b)) =
      KPPGLLocalCover.projection F ζ hζ (Sum.inr q) b.val :=
    Classical.choose_spec b.property
  rw [← hs]
  rfl

theorem unramified_of_local_matching (q : HeightOneSpectrum (𝓞 F))
    (S : KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q)
    (R : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (Q : KPGlobalProductPolarizationCharacter.LocalPolarization F ζ hζ (Sum.inr q))
    (psi : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      Q.L →ₜ* ℂˣ)
    (hg : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (hL : Q.L = KPGlobalCubicIdelePairing.U F (Sum.inr q))
    (hcompact : ∃ ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3,
      (S.iwasawa.compact.toOpenSubgroup :
        Subgroup (KPLocalExceptionalConstruction.ActualCover F ζ hζ q)) =
        (KPLocalExceptionalConstruction.actualGoodCompactSplit F ζ hζ q ht).range)
    (hretract : ∀ b : S.borel.B,
      (b : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
          S.iwasawa.compact.toOpenSubgroup →
        S.borel.retract b ∈ KPLocalGoodSphericalImage.compactTorus S.borel S.iwasawa)
    (hsubgroup : (R.L.comap S.heisenberg.π).map
        (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype =
      (KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q) Q.L).map
        (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype)
    (hcharacter : ∀ (a : R.L.comap S.heisenberg.π)
      (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q) Q.L),
      a.val.val = b.val.val → R.ωL a = psi b)
    (htrivial : ∀ b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ
      (Sum.inr q) Q.L,
      b.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) →
        psi b = 1) :
    KPLocalGoodSphericalImage.UnramifiedCompactInducingData S.borel R S.iwasawa := by
  obtain ⟨ht, hcompact⟩ := hcompact
  have hcomp (t : actualTorus F ζ hζ q) :
      t ∈ KPLocalGoodSphericalImage.compactTorus S.borel S.iwasawa ↔
      t.val ∈ (actualGoodCompactSplit F ζ hζ q ht).range := by
    change (S.borel.torus t : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup ↔ _
    rw [S.torus_full]
    change t.val ∈ (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ↔ _
    rw [hcompact]
  have hclass (a : R.L.comap S.heisenberg.π) :
      S.cubeClassEquiv (S.heisenberg.π a.val) ∈ Q.L := by
    have hm : a.val.val ∈ (R.L.comap S.heisenberg.π).map
        (actualTorus F ζ hζ q).subtype := ⟨a.val, a.property, rfl⟩
    rw [hsubgroup] at hm
    obtain ⟨b, hb, hab⟩ := hm
    have hc := matching_coordinate F ζ hζ q S a.val b hab.symm
    rw [S.cube_class, hc]
    exact hb
  have hunit (u : (KPTameCompact.O F q)ˣ) :
      S.heisenberg.π (diagonalLift F ζ hζ q (KPTameCompact.unitInclusion F q u)) ∈ R.L := by
    let y := KPTameCompact.unitInclusion F q u
    let b : KPGlobalProductPolarizationCharacter.LocalE F ζ hζ (Sum.inr q) :=
      ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr q) y, ⟨y, rfl⟩⟩
    have hc : KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) b = y := by
      exact (matching_coordinate F ζ hζ q S (diagonalLift F ζ hζ q y) b rfl).symm.trans
        (S.coordinate_lift _ _ rfl)
    have hb : b ∈ KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q) Q.L := by
      change KPGlobalProductPolarizationCharacter.localProjection F ζ hζ (Sum.inr q) b ∈ Q.L
      rw [hL]
      change KPGlobalCubicIdelePairing.localClass F (Sum.inr q)
        (KPGlobalProductPolarizationCharacter.localRatio F ζ hζ (Sum.inr q) b) ∈ _
      rw [hc]
      exact ⟨y, ⟨u, rfl⟩, rfl⟩
    have hm : b.val ∈ (KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q) Q.L).map
        (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype := ⟨b, hb, rfl⟩
    rw [← hsubgroup] at hm
    obtain ⟨a, ha, hab⟩ := hm
    have he : a = diagonalLift F ζ hζ q y := Subtype.ext hab
    change S.heisenberg.π a ∈ R.L at ha
    rw [he] at ha
    exact ha
  refine ⟨?_, ?_, ?_, hretract⟩
  · letI : (KPTameCompact.p F q).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
    letI : Field (KPTameCompact.O F q ⧸ KPTameCompact.p F q) := Ideal.Quotient.field _
    let m := Ideal.Quotient.mk (KPTameCompact.p F q)
    letI : IsLocalHom m := IsLocalHom.of_surjective m Ideal.Quotient.mk_surjective
    have hu : IsUnit (3 : KPTameCompact.O F q) := by
      apply isUnit_of_map_unit m
      apply isUnit_iff_ne_zero.mpr
      simpa only [m, map_ofNat, Nat.cast_ofNat] using
        CharP.cast_ne_zero_of_ne_of_prime (KPTameCompact.O F q ⧸ KPTameCompact.p F q) Nat.prime_three ht
    exact IsLocalRing.notMem_maximalIdeal.mpr hu
  · apply le_antisymm
    · rintro d ⟨t, ht', rfl⟩
      obtain ⟨u, hu⟩ := compact_coordinate_unit F ζ hζ q S ht t ((hcomp t).mp ht')
      have he : S.heisenberg.π t =
          S.heisenberg.π (diagonalLift F ζ hζ q (KPTameCompact.unitInclusion F q u)) := by
        apply S.cubeClassEquiv.injective
        rw [S.cube_class, S.cube_class,
          S.coordinate_lift (diagonalLift F ζ hζ q (KPTameCompact.unitInclusion F q u)) _ rfl]
        rw [← hu]
        rfl
      rw [he]
      exact hunit u
    · intro d hd
      obtain ⟨a, ha⟩ := S.heisenberg.quotient_surjective d
      have hc := hclass ⟨a, by simpa [ha] using hd⟩
      rw [hL, ha] at hc
      obtain ⟨y, ⟨u, rfl⟩, hy⟩ := hc
      refine ⟨diagonalLift F ζ hζ q (KPTameCompact.unitInclusion F q u),
        (hcomp _).mpr (unit_lift_compact F ζ hζ q ht u), ?_⟩
      apply S.cubeClassEquiv.injective
      rw [S.cube_class, S.coordinate_lift _ _ rfl]
      exact hy
  · intro u hu
    have hm : u.val.val ∈ (R.L.comap S.heisenberg.π).map
        (actualTorus F ζ hζ q).subtype := ⟨u.val, hu, rfl⟩
    rw [hsubgroup] at hm
    obtain ⟨b, hb, hbu⟩ := hm
    rw [hcharacter ⟨u.val, hu⟩ ⟨b, hb⟩ hbu.symm]
    apply htrivial
    change b.val = u.val.val at hbu
    change b.val ∈ _
    rw [hbu]
    have hc := (hcomp u.val).mp u.property
    change u.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q)
    rw [KPAdelicCoverRestrictedProduct.pglCompact, KPAdelicCoverRestrictedProduct.compact,
      KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hg]
    rw [actualGoodCompactSplit, MonoidHom.range_comp] at hc
    exact hc

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesLocalSteps

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusTensorFibers
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

structure RawLocalFiberData
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P) where
  canonical : ∀ q : HeightOneSpectrum (𝓞 F),
    KPLocalExceptionalConstruction.CanonicalFiniteInducingData F ζ hζ q
  polarization : ∀ q, KPLocalStoneVonNeumann.Polarization (canonical q).heisenberg
  subgroup_matches : ∀ q,
    ((polarization q).L.comap (canonical q).heisenberg.π).map
      (KPLocalExceptionalConstruction.actualTorus F ζ hζ q).subtype =
    (KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      (P.localData (Sum.inr q)).L).map
      (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype
  character_matches : ∀ q
    (a : (polarization q).L.comap (canonical q).heisenberg.π)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
      (P.localData (Sum.inr q)).L),
    a.val.val = b.val.val → (polarization q).ωL a =
      KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ
        P T (Sum.inr q) b
  exceptional : Finset (HeightOneSpectrum (𝓞 F))
  unramified : ∀ q, q ∉ exceptional →
    KPLocalGoodSphericalImage.UnramifiedCompactInducingData
      (canonical q).borel (polarization q) (canonical q).iwasawa
  actual_compact : ∀ q, q ∉ exceptional →
    ∃ ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3,
      ((canonical q).iwasawa.compact.toOpenSubgroup :
        Subgroup (KPLocalExceptionalConstruction.ActualCover F ζ hζ q)) =
      (KPLocalExceptionalConstruction.actualGoodCompactSplit F ζ hζ q ht).range

theorem adjustedLocalValue_preserves_center
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (v : KPHilbert.Place F)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ v
      (P.localData v).L)
    (z : KPGlobalProductPolarizationCharacter.localCenter F ζ hζ v)
    (hbz : b.val = z.val) :
    KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T v b =
      KPGlobalProductPolarizationCharacter.localOmega F ζ hζ v z := by
  have hz : KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v b.val = 1 := by
    rw [hbz]
    exact z.property
  have hclass : (⟨KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v b.val,
      b.property⟩ : (P.localData v).L) = 1 := Subtype.ext hz
  rw [KPGlobalProductPolarizationCharacter.adjustedLocalValue, hclass, map_one, mul_one]
  exact (P.localData v).extends_center b z hbz

theorem adjustedLocalValue_preserves_modulus
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)
    (v : KPHilbert.Place F)
    (b : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ v
      (P.localData v).L) :
    ‖(KPGlobalProductPolarizationCharacter.adjustedLocalValue F ζ hζ P T v b : ℂ)‖ =
      Real.rpow (KPGlobalCenterRationalCharacter.localAbs F v
        (KPGlobalProductPolarizationCharacter.localRatio F ζ hζ v b.val)) (1 / 6 : ℝ) := by
  simp only [KPGlobalProductPolarizationCharacter.adjustedLocalValue,
    Units.val_mul, norm_mul, T.unitary, mul_one]
  exact (P.localData v).modulus b

open KPLocalStoneVonNeumann

theorem maximal_abelian_image_isotropic
    {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommGroup D] [Finite D] (U : LocalHeisenbergData H D)
    (A : Subgroup H) (hA : KPLocalPolarization.IsMaximalAbelian A)
    (hCA : U.C ≤ A) :
    FinitePolarization.IsMaximalIsotropic U.pairing (A.map U.π) ∧
      (A.map U.π).comap U.π = A := by
  have hpre : (A.map U.π).comap U.π = A := by
    rw [Subgroup.comap_map_eq, U.quotient_kernel, sup_eq_left.mpr hCA]
  refine ⟨⟨?_, ?_⟩, hpre⟩
  · intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact (U.detects_commutation a b).mp (hA.1 a ha b hb)
  · intro N hN hNI
    have hAN : A ≤ N.comap U.π := by
      rw [← hpre]
      exact Subgroup.comap_mono hN
    have he : N.comap U.π = A := hA.2 _ hAN (by
      intro x hx y hy
      exact (U.detects_commutation x y).mpr (hNI _ hx _ hy))
    apply le_antisymm ?_ hN
    intro d hd
    obtain ⟨x, rfl⟩ := U.quotient_surjective d
    exact Subgroup.mem_map.mpr ⟨x, (show x ∈ A from he ▸ hd), rfl⟩

theorem polarization_matching_maximal_abelian
    {H D : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CommGroup D] [Finite D] (U : LocalHeisenbergData H D)
    (A : Subgroup H) (hA : KPLocalPolarization.IsMaximalAbelian A)
    (hCA : U.C ≤ A) (χ : A →ₜ* ℂˣ)
    (hχ : ∀ a : A, ∀ ha : (a : H) ∈ U.C,
      χ a = U.ω ⟨(a : H), ha⟩) :
    ∃ P : Polarization U, P.L.comap U.π = A ∧
      ∀ (a : P.L.comap U.π) (b : A), a.val = b.val → P.ωL a = χ b := by
  obtain ⟨hL, hpre⟩ := maximal_abelian_image_isotropic U A hA hCA
  let e : (A.map U.π).comap U.π →* A :=
    { toFun := fun a => ⟨a.val, (le_of_eq hpre) a.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  let χL : (A.map U.π).comap U.π →ₜ* ℂˣ :=
    χ.comp ⟨e, he⟩
  let P : Polarization U :=
    { L := A.map U.π
      maximal := hL
      ωL := χL
      extends_center := fun a ha => hχ (e a) ha }
  refine ⟨P, hpre, ?_⟩
  intro a b hab
  change χ (e a) = χ b
  exact congrArg χ (Subtype.ext hab)

end
end DedekindZetaZeroFree.KPGlobalTorusTensorFibers

end
