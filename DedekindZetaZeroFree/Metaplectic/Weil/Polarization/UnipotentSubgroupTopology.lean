module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationSubgroupCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPSpatialSmoothing
open KPGlobalTorusFunctionData
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming inBorel → inBorel
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming cToBorel → cToBorel
open _root_.DedekindZetaZeroFree.ActualBorelRetraction renaming projected_root → projected_root
open _root_.DedekindZetaZeroFree.ActualBorelRetraction renaming upper_entries → upper_entries
open _root_.DedekindZetaZeroFree.ActualBorelRetraction renaming upper → upper
open _root_.DedekindZetaZeroFree.ActualBorelRetraction renaming factor_torus → factor_torus
open _root_.DedekindZetaZeroFree.ActualBorelRetraction renaming factor → factor

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem root_continuous : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
  letI : ∀ v : KPHilbert.Place F, TopologicalSpace (KPLocalCover.CubicGL2Raw F ζ hζ v) :=
    KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : TopologicalSpace (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) :=
    KPAdelicCoverRestrictedProduct.restrictedTopology F ζ hζ
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have hcoord (v : KPHilbert.Place F) :
      Continuous (fun x : KPGlobalTorusFunctionData.Adeles F =>
        KPStandardLocalRootLifts.N F ζ hζ v
          (KPAdelicCoverRestrictedProduct.adeleEval F v x)) := by
    cases v with
    | inl w =>
      exact (KPStandardLocalRootLifts.complex_N_continuous F ζ hζ w).comp
        ((continuous_apply w).comp continuous_fst)
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).comp
        ((RestrictedProduct.continuous_eval q).comp continuous_snd)
  let U : Set (KPGlobalTorusFunctionData.Adeles F) :=
    {x | ∀ q, ¬ KPAdelicCoverRestrictedProduct.Bad F q →
      x.2 q ∈ q.adicCompletionIntegers F}
  have hU : IsOpen U :=
    (RestrictedProduct.isOpen_forall_imp_mem
      (fun q : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring
        (q.adicCompletion F))).preimage continuous_snd
  have h0 : (0 : KPGlobalTorusFunctionData.Adeles F) ∈ U := by
    intro q hq
    exact zero_mem _
  let S : Set (KPHilbert.Place F) :=
    {v | match v with | .inl _ => True | .inr q => ¬ KPAdelicCoverRestrictedProduct.Bad F q}
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff]
    change ∀ᶠ v in Filter.cofinite, v ∈ S
    rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
    exact ⟨Set.toFinite _, by simpa [S] using KPAdelicCoverRestrictedProduct.bad_finite F⟩
  have hmem (x : U) (v : KPHilbert.Place F) (hv : v ∈ S) :
      KPStandardLocalRootLifts.N F ζ hζ v
        (KPAdelicCoverRestrictedProduct.adeleEval F v x) ∈
          KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q =>
      have hi (t : q.adicCompletion F) :
          t ∈ KPTameCompact.O F q ↔ t ∈ q.adicCompletionIntegers F := by
        letI : ValuativeRel (q.adicCompletion F) :=
          ClassFieldTheory.finitePlaceCompletionValuativeRel F q
        change (ValuativeRel.valuation (q.adicCompletion F)) t ≤ 1 ↔ Valued.v t ≤ 1
        rw [← Valuation.vle_one_iff]
        letI : Valued.v.Compatible := Valuation.Compatible.ofValuation
          (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))
        exact Valuation.vle_one_iff Valued.v
      have hx : x.val.2 q ∈ KPTameCompact.O F q := (hi _).mpr (x.property q hv)
      simp only [KPAdelicCoverRestrictedProduct.compact,
        KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hv]
      refine ⟨KPStandardLocalRootLifts.integralN F q ⟨_, hx⟩, ?_⟩
      exact (KPStandardLocalRootLifts.N_eq_compact F ζ hζ q
        (fun h3 => hv (Or.inr h3)) ⟨_, hx⟩).symm
  let f : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (KPAdelicCoverRestrictedProduct.compact F ζ hζ v : Set _))
      (Filter.principal S) :=
    fun x => ⟨fun v => KPStandardLocalRootLifts.N F ζ hζ v
      (KPAdelicCoverRestrictedProduct.adeleEval F v x), hmem x⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (hcoord v).comp continuous_subtype_val))
  have hrt : ContinuousAt (KPGlobalTorusFunctionData.rootTuple F ζ hζ) 0 := by
    have hr : Continuous (U.domRestrict (KPGlobalTorusFunctionData.rootTuple F ζ hζ)) :=
      (RestrictedProduct.continuous_inclusion hS).comp hf
    exact (continuousOn_iff_continuous_restrict.mpr hr).continuousAt (hU.mem_nhds h0)
  have hN : Continuous (KPGlobalTorusFunctionData.N F ζ hζ) := by
    have hh : Continuous (KPGlobalTorusFunctionData.Nhom F ζ hζ) := by
      apply continuous_of_continuousAt_one
      exact QuotientGroup.continuous_mk.continuousAt.comp
        (QuotientGroup.continuous_mk.continuousAt.comp hrt)
    exact hh
  exact hN

private theorem upper_preimage_zero (A : AdelicMatrixGroup F)
    (h : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈ ordinaryBorel F) :
    A 1 0 = 0 := by
  obtain ⟨B, hB, h10⟩ := h
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp hB
  have he : A = B * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = B⁻¹ * A at hz
    rw [hz]; group
  rw [he]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, h10]

private theorem borel_closed : IsClosed (borel F ζ hζ : Set (G F ζ hζ)) := by
  have ho : IsClosed (ordinaryBorel F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)) := by
    rw [← (QuotientGroup.isQuotientMap_mk
      (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).isClosed_preimage]
    have he : (QuotientGroup.mk (s := KPAdelicCoverRestrictedProduct.scalarSubgroup F)) ⁻¹'
        (ordinaryBorel F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)) =
        {A : AdelicMatrixGroup F | A 1 0 = 0} := by
      ext A
      exact ⟨upper_preimage_zero F A, fun h => ⟨A, rfl, h⟩⟩
    rw [he]
    exact isClosed_eq (by fun_prop) continuous_const
  exact ho.preimage
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

 def matrixX (A : AdelicMatrixGroup F) (h : A 1 0 = 0) : Adeles F :=
  ↑((KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit⁻¹) * A 0 1

private theorem matrixX_spec (A : AdelicMatrixGroup F) (h : A 1 0 = 0) :
    A 0 0 * matrixX F A h = A 0 1 := by
  let u := (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit
  have hu : (u : Adeles F) = A 0 0 := (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit_spec
  change A 0 0 * (↑u⁻¹ * A 0 1) = _
  rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]

private theorem matrixX_formula (A : AdelicMatrixGroup F) (h : A 1 0 = 0) :
    matrixX F A h = A 1 1 * ((Matrix.GeneralLinearGroup.det A)⁻¹ : (Adeles F)ˣ).val * A 0 1 := by
  let u := (KPGlobalTorusMatrixCertificates.diagonal_units A h).1.unit
  let v := (KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit
  have hd : Matrix.GeneralLinearGroup.det A = u * v := by
    apply Units.ext
    simp [Matrix.det_fin_two, h, u, v, IsUnit.unit_spec]
  rw [hd]
  change (u⁻¹ : (Adeles F)ˣ).val * A 0 1 = _
  rw [← (KPGlobalTorusMatrixCertificates.diagonal_units A h).2.unit_spec]
  change _ = v.val * ((u * v)⁻¹).val * A 0 1
  simp [mul_inv_rev, ← mul_assoc]

private theorem matrixX_continuous :
    Continuous (fun A : {A : AdelicMatrixGroup F | A 1 0 = 0} => matrixX F A.val A.property) := by
  simp_rw [matrixX_formula]
  have hc (i j : Fin 2) : Continuous (fun A : {A : AdelicMatrixGroup F | A 1 0 = 0} => A.val i j) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  exact ((hc 1 1).mul (Units.continuous_coe_inv.comp
    (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val))).mul (hc 0 1)

private theorem matrixX_same (A B : AdelicMatrixGroup F) (hA : A 1 0 = 0) (hB : B 1 0 = 0)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A =
      QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) B) :
    matrixX F A hA = matrixX F B hB := by
  obtain ⟨z, hz⟩ := QuotientGroup.eq.mp he
  have heB : B = A * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = A⁻¹ * B at hz
    rw [hz]; group
  have hx : B 0 0 * matrixX F A hA = B 0 1 := by
    rw [heB]
    simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar]
    calc A 0 0 * ↑z * matrixX F A hA = (A 0 0 * matrixX F A hA) * ↑z := by ring
         _ = A 0 1 * ↑z := by rw [matrixX_spec]
  exact ((KPGlobalTorusMatrixCertificates.diagonal_units B hB).1.mul_left_cancel
    (hx.trans (matrixX_spec F B hB).symm))

 def ordinaryX (b : ordinaryBorel F) : Adeles F :=
  matrixX F (Classical.choose b.property) (Classical.choose_spec b.property).2

private theorem ordinaryX_formula (b : ordinaryBorel F) (A : AdelicMatrixGroup F)
    (he : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = b.val)
    (h : A 1 0 = 0) : ordinaryX F b = matrixX F A h :=
  matrixX_same F _ A _ h ((Classical.choose_spec b.property).1.trans he.symm)

private theorem ordinaryX_continuous : Continuous (ordinaryX F) := by
  let q : AdelicMatrixGroup F → KPAdelicCoverRestrictedProduct.AdelicPGL2 F :=
    QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  let S : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F) := ordinaryBorel F
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
    (N := KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u : (q ⁻¹' S) → {A : AdelicMatrixGroup F | A 1 0 = 0} :=
    fun A => ⟨A.val, upper_preimage_zero F A.val A.property⟩
  have he : (ordinaryX F) ∘ S.restrictPreimage q =
      (fun A : {A : AdelicMatrixGroup F | A 1 0 = 0} => matrixX F A.val A.property) ∘ u := by
    funext A
    exact ordinaryX_formula F _ _ rfl (u A).property
  rw [he]
  exact (matrixX_continuous F).comp (continuous_subtype_val.subtype_mk _)

 def coveredX (b : borel F ζ hζ) : Adeles F :=
  ordinaryX F ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ b.val, b.property⟩

private theorem coveredX_continuous : Continuous (coveredX F ζ hζ) :=
  (ordinaryX_continuous F).comp
    (((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
      continuous_subtype_val).subtype_mk _)

private theorem retraction_formula (b : borel F ζ hζ) :
    (ActualBorelRetraction.retraction F ζ hζ b).val = b.val * N F ζ hζ (-coveredX F ζ hζ b) := by
  obtain ⟨A, hA, h10⟩ := b.property
  have hx : coveredX F ζ hζ b = matrixX F A h10 :=
    ordinaryX_formula F _ A hA h10
  let x := coveredX F ζ hζ b
  have hm : b.val * N F ζ hζ (-x) ∈ E F ζ hζ := by
    refine ⟨A * upper F (-x), ?_, ?_, ?_⟩
    · simp only [map_mul, projected_root, hA]
    · simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        upper_entries, h10]
    · have hspec : A 0 0 * x = A 0 1 := by change A 0 0 * coveredX F ζ hζ b = _; rw [hx]; exact matrixX_spec F A h10
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
        upper_entries, hspec]
  let t : E F ζ hζ := ⟨b.val * N F ζ hζ (-x), hm⟩
  have hb : b.val = t.val * N F ζ hζ x := by
    change b.val = (b.val * N F ζ hζ (-x)) * N F ζ hζ x
    rw [mul_assoc, ← N_add, neg_add_cancel]
    have h0 : N F ζ hζ 0 = 1 := (Nhom F ζ hζ).map_one
    rw [h0, mul_one]
  exact congrArg Subtype.val (factor_torus F ζ hζ b t x hb)

private theorem retraction_continuous : Continuous (ActualBorelRetraction.retraction F ζ hζ) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  apply Continuous.subtype_mk
  change Continuous (fun b : borel F ζ hζ => (ActualBorelRetraction.retraction F ζ hζ b).val)
  simp_rw [retraction_formula]
  exact continuous_subtype_val.mul ((root_continuous F ζ hζ).comp (coveredX_continuous F ζ hζ).neg)

theorem actual_HN_closed_character_continuous
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) :
    IsClosed (actualC F ζ hζ : Set (G F ζ hζ)) ∧
      Continuous (actualChi F ζ hζ) := by
  have hB := borel_closed F ζ hζ
  have hr := retraction_continuous F ζ hζ
  have hin : IsClosed (inBorel F ζ hζ : Set (borel F ζ hζ)) :=
    (P0 F ζ hζ).closed.preimage hr
  have hC : IsClosed (actualC F ζ hζ : Set (G F ζ hζ)) := by
    unfold actualC
    rw [Subgroup.coe_map]
    exact hB.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hin
  have hh : Continuous (actualHCoordinate F ζ hζ) := by
    apply Continuous.subtype_mk
    exact hr.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hd : Continuous (fun t : E F ζ hζ =>
      (((delta F ζ hζ t : ℝ≥0) : ℝ))) := by
    have he : (fun t : E F ζ hζ => (((delta F ζ hζ t : ℝ≥0) : ℝ))) =
        (fun t => (((KPGlobalCenterRationalCharacter.nu F ζ hζ t : ℝ≥0) : ℝ)) ^ 6) := by
      funext t
      simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
        KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map,
        NNReal.rpowMonoidHom_apply, NNReal.coe_rpow]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _)]
      norm_num
    rw [he]
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ))).pow 6
  have hhalf : Continuous (deltaHalf F ζ hζ) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hd)
  have hv : Continuous (fun c : actualC F ζ hζ =>
      (actualChi F ζ hζ c : ℂ)) := by
    change Continuous (fun c : actualC F ζ hζ =>
      deltaHalf F ζ hζ (actualHCoordinate F ζ hζ c).val *
        ((P0 F ζ hζ).character (actualHCoordinate F ζ hζ c) : ℂ))
    exact (hhalf.comp (continuous_subtype_val.comp hh)).mul
      (Units.continuous_val.comp ((P0 F ζ hζ).character.continuous.comp hh))
  exact ⟨hC, Units.continuous_iff.mpr
    ⟨hv, hv.inv₀ (fun c => Units.ne_zero (actualChi F ζ hζ c))⟩⟩

end DedekindZetaZeroFree.KPSpatialSmoothing

end
