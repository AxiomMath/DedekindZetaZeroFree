module

public import DedekindZetaZeroFree.Metaplectic.Torus.BorelTwistCompatibility

@[expose] public section

section

namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

open scoped Pointwise

theorem continuous_of_closed_compact_factor
    {G Z : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace Z] {B K : Set G} {f : G → Z}
    (hB : IsClosed B) (hK : IsCompact K)
    (hfactor : ∀ g : G, ∃ b ∈ B, ∃ k ∈ K, g = b * k)
    (hinvariant : ∀ b ∈ B, ∀ k ∈ K, f (b * k) = f b)
    (hf : ContinuousOn f B) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro s hs
  have hpre : f ⁻¹' s = (B ∩ f ⁻¹' s) * K := by
    ext g
    constructor
    · intro hg
      obtain ⟨b, hb, k, hk, rfl⟩ := hfactor g
      refine Set.mem_mul.mpr ⟨b, ⟨hb, ?_⟩, k, hk, rfl⟩
      change f b ∈ s
      change f (b * k) ∈ s at hg
      rwa [hinvariant b hb k hk] at hg
    · intro hg
      obtain ⟨b, ⟨hb, hbs⟩, k, hk, rfl⟩ := Set.mem_mul.mp hg
      change f (b * k) ∈ s
      rwa [hinvariant b hb k hk]
  rw [hpre]
  exact (hf.preimage_isClosed_of_isClosed hB hs).mul_right_of_isCompact hK

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

end

section

noncomputable section
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct

theorem fullCusp_isClosed_ordinaryBorel :
    IsClosed (KPGlobalTorusFunctionData.ordinaryBorel F : Set (AdelicPGL2 F)) := by
  letI : IsTopologicalGroup (AdelicGL2 F) := inferInstance
  rw [← (QuotientGroup.isQuotientMap_mk (scalarSubgroup F)).isClosed_preimage]
  have he : (QuotientGroup.mk (s := scalarSubgroup F)) ⁻¹'
      (KPGlobalTorusFunctionData.ordinaryBorel F : Set (AdelicPGL2 F)) =
      {A : AdelicGL2 F | A 1 0 = 0} := by
    ext A
    constructor
    · rintro ⟨B,hB,h10⟩
      have hm := QuotientGroup.eq.mp hB
      obtain ⟨z,hz⟩ := hm
      have he : A = B * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
        change Matrix.GeneralLinearGroup.scalar (Fin 2) z = B⁻¹ * A at hz
        rw [hz]
        group
      rw [he]
      simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.scalar, h10]
    · intro h
      exact ⟨A,rfl,h⟩
  rw [he]
  exact isClosed_eq (by fun_prop) continuous_const
theorem fullCusp_isClosed_borel :
    IsClosed (KPGlobalTorusFunctionData.borel F ζ hζ : Set (KPGlobalTorusFunctionData.G F ζ hζ)) := by
  exact (fullCusp_isClosed_ordinaryBorel F).preimage
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

theorem fullCusp_iwasawaNorm_continuous_of_borel
    (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ)
    (hcont : ContinuousOn (fun g =>
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))
      (KPGlobalTorusFunctionData.borel F ζ hζ : Set _)) :
    Continuous (fun g =>
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))) := by
  letI : IsTopologicalGroup (KPGlobalTorusFunctionData.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let raw : KPGlobalTorusBorelNormTwistTransport.IwasawaData F ζ hζ :=
    { K := D.K, compact := D.compact, decomposition := D.decomposition, overlap := D.overlap }
  apply continuous_of_closed_compact_factor (fullCusp_isClosed_borel F ζ hζ) D.compact
  · intro g
    obtain ⟨t,x,k,hg⟩ := D.decomposition g
    refine ⟨t.val * KPGlobalTorusFunctionData.N F ζ hζ x, ?_, k.val, k.property, hg⟩
    have ht : t.val ∈ KPGlobalTorusFunctionData.borel F ζ hζ := by
      obtain ⟨A,hA,h10,h01⟩ := t.property
      exact ⟨A,hA,h10⟩
    apply Subgroup.mul_mem _ ht
    refine ⟨KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ
      (KPGlobalTorusFunctionData.rootTuple F ζ hζ x), rfl, ?_⟩
    apply Prod.ext
    · funext w
      simp [KPAdelicCoverRestrictedProduct.restrictedProjection,
        KPAdelicCoverRestrictedProduct.matrixValue, KPAdelicCoverRestrictedProduct.matrixEntry,
        KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N]
      rfl
    · apply RestrictedProduct.ext
      intro q
      simp [KPAdelicCoverRestrictedProduct.restrictedProjection,
        KPAdelicCoverRestrictedProduct.matrixValue, KPAdelicCoverRestrictedProduct.matrixEntry,
        KPGlobalTorusFunctionData.rootTuple, KPStandardLocalRootLifts.N]
      rfl
  · intro b hb k hk
    obtain ⟨t,x,hb⟩ := KPGlobalTorusBorelNormTwistTransport.actual_borel_factorization F ζ hζ ⟨b,hb⟩
    change b = t.val * KPGlobalTorusFunctionData.N F ζ hζ x at hb
    rw [hb]
    have hk' := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_formula F ζ hζ raw t x ⟨k,hk⟩
    have h1 := KPGlobalTorusBorelNormTwistTransport.iwasawaNorm_formula F ζ hζ raw t x 1
    simp only [OneMemClass.coe_one, mul_one] at h1
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x * k) = _ at hk'
    change KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D
      (t.val * KPGlobalTorusFunctionData.N F ζ hζ x) = _ at h1
    rw [hk',h1]
  · exact hcont

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

end

end

section

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField NNReal
namespace DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
open KPAdelicCoverRestrictedProduct
open KPGlobalTorusBorelNormTwistTransport

private theorem upperRatio_det (A : AdelicGL2 F) (h : A 1 0 = 0) :
    iwasawaUpperRatio F A h = (iwasawaUpperUnits F A h).1.unit ^ 2 * (Matrix.GeneralLinearGroup.det A)⁻¹ ∧
    (iwasawaUpperRatio F A h)⁻¹ = (iwasawaUpperUnits F A h).2.unit ^ 2 * (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  have hd : Matrix.GeneralLinearGroup.det A =
      (iwasawaUpperUnits F A h).1.unit * (iwasawaUpperUnits F A h).2.unit := by
    apply Units.ext
    change (A : Matrix (Fin 2) (Fin 2) (Adeles F)).det = _
    simp [Matrix.det_fin_two, h, IsUnit.unit_spec]
  rw [hd]
  unfold iwasawaUpperRatio
  constructor <;> simp [pow_two, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

private theorem upperRatio_continuous :
    Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} => iwasawaUpperRatio F A.val A.property) := by
  apply Units.continuous_iff.mpr
  have hc (i j : Fin 2) : Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} => A.val i j) :=
    (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j
  have hd : Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} =>
      ((Matrix.GeneralLinearGroup.det A.val)⁻¹ : (Adeles F)ˣ).val) := by
    exact Units.continuous_coe_inv.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)
  constructor
  · have he : (fun A : {A : AdelicGL2 F | A 1 0 = 0} =>
        (iwasawaUpperRatio F A.val A.property).val) =
        fun A => (A.val 0 0)^2 * ((Matrix.GeneralLinearGroup.det A.val)⁻¹ : (Adeles F)ˣ).val := by
      funext A
      rw [(upperRatio_det F A.val A.property).1]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    change Continuous (fun A : {A : AdelicGL2 F | A 1 0 = 0} => (iwasawaUpperRatio F A.val A.property).val)
    rw [he]
    exact (hc 0 0).pow 2 |>.mul hd
  · have he : (fun A : {A : AdelicGL2 F | A 1 0 = 0} =>
        ((iwasawaUpperRatio F A.val A.property)⁻¹).val) =
        fun A => (A.val 1 1)^2 * ((Matrix.GeneralLinearGroup.det A.val)⁻¹ : (Adeles F)ˣ).val := by
      funext A
      rw [(upperRatio_det F A.val A.property).2]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [he]
    exact (hc 1 1).pow 2 |>.mul hd

 def ordinaryUpperRatio (b : KPGlobalTorusFunctionData.ordinaryBorel F) : (Adeles F)ˣ :=
  iwasawaUpperRatio F (Classical.choose b.property) (Classical.choose_spec b.property).2

private theorem ordinaryUpperRatio_formula (b : KPGlobalTorusFunctionData.ordinaryBorel F)
    (A : AdelicGL2 F) (hA : QuotientGroup.mk' (scalarSubgroup F) A = b.val) (h : A 1 0 = 0) :
    ordinaryUpperRatio F b = iwasawaUpperRatio F A h := by
  apply iwasawaUpperRatio_scalar
  exact (Classical.choose_spec b.property).1.trans hA.symm

private theorem upper_preimage_zero (A : AdelicGL2 F)
    (h : QuotientGroup.mk' (scalarSubgroup F) A ∈ KPGlobalTorusFunctionData.ordinaryBorel F) :
    A 1 0 = 0 := by
  obtain ⟨B,hB,h10⟩ := h
  have hm := QuotientGroup.eq.mp hB
  obtain ⟨z,hz⟩ := hm
  have he : A = B * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by
    change Matrix.GeneralLinearGroup.scalar (Fin 2) z = B⁻¹ * A at hz
    rw [hz]; group
  rw [he]
  simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, h10]

private theorem ordinaryUpperRatio_continuous : Continuous (ordinaryUpperRatio F) := by
  let q : AdelicGL2 F → AdelicPGL2 F := QuotientGroup.mk' (scalarSubgroup F)
  let S : Set (AdelicPGL2 F) := KPGlobalTorusFunctionData.ordinaryBorel F
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk (N := scalarSubgroup F)
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u : (q ⁻¹' S) → {A : AdelicGL2 F | A 1 0 = 0} :=
    fun A => ⟨A.val, upper_preimage_zero F A.val A.property⟩
  have he : (ordinaryUpperRatio F) ∘ S.restrictPreimage q =
      (fun A : {A : AdelicGL2 F | A 1 0 = 0} => iwasawaUpperRatio F A.val A.property) ∘ u := by
    funext A
    exact ordinaryUpperRatio_formula F _ _ rfl (u A).property
  rw [he]
  exact (upperRatio_continuous F).comp (continuous_subtype_val.subtype_mk _)

private theorem fullCusp_ideleAbs_continuous : Continuous (KPGlobalTorusFunctionData.ideleAbs F) := by
  have hfinite : Continuous (FiniteIdeleGroup.absoluteNorm (K := F)) := by
    apply continuous_of_continuousAt_one
    apply (continuousAt_const (y := (1 : ℝ≥0ˣ))).congr_of_eventuallyEq
    have ho : IsOpen (FiniteIdeleGroup.integralSubgroup (K := F) : Set (FiniteIdeleGroup F)) := by
      simpa only [Finset.coe_empty, FiniteIdeleGroup.supportedAt_empty] using
        (FiniteIdeleGroup.isOpen_supportedAt (K := F) ∅)
    filter_upwards [ho.mem_nhds (Subgroup.one_mem _)] with a ha
    exact IdeleGroup.finite_absoluteNorm_eq_one_of_integral a ha
  have hidele : Continuous (IdeleGroup.absoluteNorm (K := F)) :=
    (hfinite.comp continuous_snd).mul
      ((InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst).inv)
  exact (hidele.comp (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm.continuous).inv

theorem fullCusp_iwasawaNorm_continuousOn_borel
    (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ) :
    ContinuousOn (fun g =>
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ)))
      (KPGlobalTorusFunctionData.borel F ζ hζ : Set _) := by
  apply continuousOn_iff_continuous_restrict.mpr
  let proj : KPGlobalTorusFunctionData.borel F ζ hζ → KPGlobalTorusFunctionData.ordinaryBorel F :=
    fun b => ⟨pglProjection F ζ hζ b.val, b.property⟩
  have hp : Continuous proj :=
    ((adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
      continuous_subtype_val).subtype_mk _
  have he : (KPGlobalTorusFunctionData.borel F ζ hζ : Set _).domRestrict (fun g =>
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))) =
      fun b => (((KPGlobalTorusFunctionData.ideleAbs F (ordinaryUpperRatio F (proj b)) : ℝ≥0) : ℝ)) := by
    funext b
    obtain ⟨t,x,hb⟩ := actual_borel_factorization F ζ hζ b
    obtain ⟨B,hB,h10⟩ := b.property
    have hr := iwasawaUpperRatio_torus_root F ζ hζ t x B h10 (hB.trans (congrArg (pglProjection F ζ hζ) hb))
    have hf := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ D t x 1
    simp only [OneMemClass.coe_one, mul_one] at hf
    change (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D b.val : ℝ≥0) : ℝ)) = _
    rw [hb, hf, ordinaryUpperRatio_formula F (proj b) B hB h10, hr]
    rfl
  rw [he]
  exact NNReal.continuous_coe.comp (Units.continuous_val.comp
    ((fullCusp_ideleAbs_continuous F).comp ((ordinaryUpperRatio_continuous F).comp hp)))

theorem fullCusp_iwasawaNorm_continuous
    (D : KPGlobalTorusBorelTwistCompatibility.IwasawaData F ζ hζ) :
    Continuous (fun g =>
      (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D g : ℝ≥0) : ℝ))) :=
  fullCusp_iwasawaNorm_continuous_of_borel F ζ hζ D
    (fullCusp_iwasawaNorm_continuousOn_borel F ζ hζ D)

end DedekindZetaZeroFree.KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent

end

end
