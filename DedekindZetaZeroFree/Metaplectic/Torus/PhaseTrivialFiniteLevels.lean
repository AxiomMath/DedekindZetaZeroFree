module

public import DedekindZetaZeroFree.Metaplectic.Torus.ProductPolarizationCharacter
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteProductLevels

@[expose] public section

open scoped NumberField Classical BigOperators Topology

open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private lemma diag_inverse (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit⁻¹.val = A⁻¹ 0 0 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F) => B 0 0) A.inv_mul
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h10, mul_zero, add_zero, if_pos rfl] at h
  have hu := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit_spec
  change A⁻¹ 0 0 * A 0 0 = 1 at h
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit
  have hu' : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := hu
  calc
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * (A⁻¹ 0 0 * A 0 0) := by rw [h]
    _ = A⁻¹ 0 0 := by rw [← hu']; simp [← mul_assoc, mul_comm]
private lemma diag_inverse11 (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (h10 : A 1 0 = 0) (h01 : A 0 1 = 0) :
    (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit⁻¹.val = A⁻¹ 1 1 := by
  have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) (KPAdelicCoverRestrictedProduct.Adeles F) => B 1 1) A.inv_mul
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_apply, h01, mul_zero, zero_add, if_pos rfl] at h
  have hu := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit_spec
  change A⁻¹ 1 1 * A 1 1 = 1 at h
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit
  have hu' : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := hu
  calc
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * 1 := (mul_one _).symm
    _ = (u⁻¹ : KPGlobalTorusFunctionData.Ideles F).val * (A⁻¹ 1 1 * A 1 1) := by rw [h]
    _ = A⁻¹ 1 1 := by rw [← hu']; simp [← mul_assoc, mul_comm]
private lemma preimage_diag (A : KPGlobalTorusFunctionData.AdelicMatrixGroup F)
    (hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A ∈
      KPGlobalTorusFunctionData.ordinaryTorus F) : A 1 0 = 0 ∧ A 0 1 = 0 := by
  obtain ⟨B, hB, h10, h01⟩ := hA
  rw [QuotientGroup.mk'_eq_mk'] at hB
  obtain ⟨z, hz, he⟩ := hB
  obtain ⟨u, rfl⟩ := hz
  rw [← he]
  simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
private lemma ratio_continuous : Continuous (KPGlobalTorusFunctionData.torusRatio F) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  let S := (KPGlobalTorusFunctionData.ordinaryTorus F : Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F))
  have hq : IsOpenQuotientMap q := QuotientGroup.isOpenQuotientMap_mk
  apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
  let u (A : q ⁻¹' S) := (KPGlobalTorusFunctionData.diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).1.unit
  let w (A : q ⁻¹' S) := (KPGlobalTorusFunctionData.diagonal_entries_units F A.val
    (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2).2.unit
  have hu : Continuous u := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (u A).val)
      have he : (fun A : q ⁻¹' S => (u A).val) = fun A => A.val 0 0 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A 0 0) from (continuous_apply 0).comp ((continuous_apply 0).comp (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (u A)⁻¹.val) = fun A => A.val⁻¹ 0 0 := by
        funext A; exact diag_inverse F A.val (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
      change Continuous (fun A : q ⁻¹' S => (u A)⁻¹.val)
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A⁻¹ 0 0) from (continuous_apply 0).comp ((continuous_apply 0).comp (Units.continuous_coe_inv : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F).val)))).comp continuous_subtype_val
  have hw : Continuous w := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun A : q ⁻¹' S => (w A).val)
      have he : (fun A : q ⁻¹' S => (w A).val) = fun A => A.val 1 1 := by
        funext A; exact IsUnit.unit_spec _
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A 1 1) from (continuous_apply 1).comp ((continuous_apply 1).comp (Units.continuous_val : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))).comp continuous_subtype_val
    · have he : (fun A : q ⁻¹' S => (w A)⁻¹.val) = fun A => A.val⁻¹ 1 1 := by
        funext A; exact diag_inverse11 F A.val (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
      change Continuous (fun A : q ⁻¹' S => (w A)⁻¹.val)
      rw [he]
      exact (show Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A⁻¹ 1 1) from (continuous_apply 1).comp ((continuous_apply 1).comp (Units.continuous_coe_inv : Continuous (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => (A⁻¹ : KPGlobalTorusFunctionData.AdelicMatrixGroup F).val)))).comp continuous_subtype_val
  have he : (KPGlobalTorusFunctionData.torusRatio F) ∘ S.restrictPreimage q =
      fun A => u A * (w A)⁻¹ := by
    funext A
    apply Units.ext
    exact KPGlobalTorusFunctionData.ratio_formula F _ A.val rfl
      (preimage_diag F A.val A.property).1 (preimage_diag F A.val A.property).2
  rw [he]
  exact hu.mul hw.inv

private theorem small_powers (z : ℂ) (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hp : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hl : (n : ℝ) / 2 ≤ (∑ i ∈ Finset.range n, z ^ i).re := by
    rw [Complex.re_sum]
    calc
      (n : ℝ) / 2 = ∑ i ∈ Finset.range n, (1 / 2 : ℝ) := by simp; ring
      _ ≤ ∑ i ∈ Finset.range n, (z ^ i).re := by
        apply Finset.sum_le_sum
        intro i hi
        have hr := Complex.re_le_norm (1 - z ^ i)
        have hh := h i
        rw [norm_sub_rev] at hh
        simp only [Complex.sub_re, Complex.one_re] at hr
        linarith
  have hu : ‖∑ i ∈ Finset.range n, z ^ i‖ * ‖z - 1‖ < 1 / 2 := by
    rw [← norm_mul, geom_sum_mul]
    exact h n
  have hl' := Complex.re_le_norm (∑ i ∈ Finset.range n, z ^ i)
  have hn' : 1 < (n : ℝ) * ‖z - 1‖ := (div_lt_iff₀ hp).mp hn
  have hm := mul_le_mul_of_nonneg_right (hl.trans hl') (le_of_lt hp)
  nlinarith

private lemma pD_continuous :
    Continuous (KPGlobalProductPolarizationCharacter.pD F ζ hζ) := by
  apply QuotientGroup.continuous_mk.comp
  apply (ratio_continuous F).comp
  exact ((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
    continuous_subtype_val).subtype_mk (fun t => t.property)

private lemma finite_basis (W : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ))
    (hW : W ∈ 𝓝 1) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      (U.toOpenSubgroup : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ)) ⊆ W := by
  have he : KPGlobalTorusFunctionData.finitePart F ζ hζ =
      ActualFiniteFactor.finiteSubgroup F ζ hζ := by
    rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
    apply congrArg (fun H : Subgroup (KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ) =>
      H.map ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)))
    ext x
    simp only [Subgroup.mem_iInf, MonoidHom.mem_ker]
    rfl
  suffices hb : ∀ (W : Set (ActualFiniteFactor.finiteSubgroup F ζ hζ)), W ∈ 𝓝 1 →
      ∃ U : CompactOpenLevel (ActualFiniteFactor.finiteSubgroup F ζ hζ),
        (U.toOpenSubgroup : Set (ActualFiniteFactor.finiteSubgroup F ζ hζ)) ⊆ W by
    have hb' : ∀ (W : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ)), W ∈ 𝓝 1 →
      ∃ U : CompactOpenLevel (KPGlobalTorusFunctionData.finitePart F ζ hζ),
        (U.toOpenSubgroup : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ)) ⊆ W := by
      rw [he]
      exact hb
    exact hb' W hW
  intro W hW
  obtain ⟨J, hJ⟩ := ActualFiniteFactor.productLevels_cofinal F ζ hζ W hW
  have hc := ActualFiniteFactor.productSubgroup_compact_open F ζ hζ J
  exact ⟨⟨⟨_, hc.2⟩, hc.1⟩, hJ⟩
theorem finitePart_eq_closure : KPGlobalTorusFunctionData.finitePart F ζ hζ =
    ActualFiniteFactor.finiteSubgroup F ζ hζ := by
  rw [ActualFiniteFactor.finiteSubgroup_eq_tupleFactor]
  unfold KPGlobalTorusFunctionData.finitePart ActualFiniteFactor.tupleFactor
    PGLComplex.AdelicSlicesRaw.finiteSubgroup
  congr 1
  ext x
  simp [PGLComplex.AdelicSlicesRaw.finiteTuples, Subgroup.mem_iInf, MonoidHom.mem_ker]

theorem finitePart_compactOpen_basis
    (W : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ)) (hW : W ∈ 𝓝 1) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      (U.toOpenSubgroup : Set _) ⊆ W := by
  revert W
  unfold KPGlobalTorusFunctionData.FiniteLevel
  rw [finitePart_eq_closure F ζ hζ]
  intro W hW
  obtain ⟨J, hJ⟩ := ActualFiniteFactor.productLevels_cofinal F ζ hζ W hW
  exact ⟨⟨⟨_, (ActualFiniteFactor.productSubgroup_compact_open F ζ hζ J).2⟩,
    (ActualFiniteFactor.productSubgroup_compact_open F ζ hζ J).1⟩, hJ⟩

theorem finite_level_with_trivial_phase
    (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

    (K : Subgroup (KPGlobalCubicIdelePairing.D F))
    (hKM : K ≤ KPGlobalProductPolarizationCharacter.M F ζ hζ P)
    (hopen : IsOpen (K : Set (KPGlobalCubicIdelePairing.D F))) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ j : KPGlobalTorusFunctionData.E F ζ hζ,
        j ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype →
        KPGlobalProductPolarizationCharacter.pD F ζ hζ j ∈ K ∧
        ∀ b : KPGlobalProductPolarizationCharacter.B F ζ hζ P, b.val = j →
          KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T b /
            KPGlobalCenterRationalCharacter.positiveComplex
              (KPGlobalCenterRationalCharacter.nu F ζ hζ b.val) = 1 := by
  let phase : KPGlobalProductPolarizationCharacter.B F ζ hζ P →* ℂˣ :=
    (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T).toMonoidHom /
      (KPGlobalCenterRationalCharacter.positiveComplex.comp
        ((KPGlobalCenterRationalCharacter.nu F ζ hζ).comp
          (KPGlobalProductPolarizationCharacter.B F ζ hζ P).subtype))
  have hp : Continuous phase := by
    apply (KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P T).continuous_toFun.mul
    apply Continuous.inv
    apply (show Continuous KPGlobalCenterRationalCharacter.positiveComplex from ?_).comp
    · exact (KPGlobalCenterRationalCharacter.nu_continuous F ζ hζ).comp continuous_subtype_val
    · exact ((Complex.continuous_ofReal.comp NNReal.continuous_coe).units_map _)
  let N : Set (KPGlobalProductPolarizationCharacter.B F ζ hζ P) :=
    {b | ‖(phase b : ℂ) - 1‖ < 1 / 2}
  have hoN : IsOpen N := isOpen_lt ((Units.continuous_val.comp hp).sub continuous_const).norm continuous_const
  have h1N : (1 : KPGlobalProductPolarizationCharacter.B F ζ hζ P) ∈ N := by
    change ‖(phase 1 : ℂ) - 1‖ < 1 / 2
    simp
  obtain ⟨V, hoV, heV⟩ := isOpen_induced_iff.mp hoN
  have h1V : (1 : KPGlobalTorusFunctionData.E F ζ hζ) ∈ V := by
    change (1 : KPGlobalProductPolarizationCharacter.B F ζ hζ P).val ∈ V
    rw [← Set.mem_preimage, heV]
    exact h1N
  let O := V ∩ (KPGlobalProductPolarizationCharacter.pD F ζ hζ) ⁻¹' (K : Set (KPGlobalCubicIdelePairing.D F))
  have hoO : IsOpen O := hoV.inter (hopen.preimage (pD_continuous F ζ hζ))
  have h1O : (1 : KPGlobalTorusFunctionData.E F ζ hζ) ∈ O := ⟨h1V, by simp [K.one_mem]⟩
  obtain ⟨W, hoW, heW⟩ := isOpen_induced_iff.mp hoO
  have h1W : (1 : KPGlobalTorusFunctionData.G F ζ hζ) ∈ W := by
    change (1 : KPGlobalTorusFunctionData.E F ζ hζ).val ∈ W
    rw [← Set.mem_preimage, heW]
    exact h1O
  obtain ⟨U, hU⟩ := finite_basis F ζ hζ
    ((KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype ⁻¹' W)
    ((hoW.preimage continuous_subtype_val).mem_nhds h1W)
  have hlevel (j : KPGlobalTorusFunctionData.E F ζ hζ)
      (hj : j ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) : j ∈ O := by
    obtain ⟨u, hu, heu⟩ := hj
    have huw := hU hu
    change u.val ∈ W at huw
    rw [← heW]
    change j.val ∈ W
    change u.val = j.val at heu
    exact heu ▸ huw
  refine ⟨U, ?_⟩
  intro j hj
  refine ⟨(hlevel j hj).2, ?_⟩
  intro b hb
  change phase b = 1
  apply Units.ext
  apply small_powers
  intro n
  have hjn : j ^ n ∈ (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype := Subgroup.pow_mem _ hj n
  have hn := (hlevel (j ^ n) hjn).1
  have hbn : (b ^ n).val = j ^ n := by simp [hb]
  have hmem : b ^ n ∈ N := by
    rw [← heV]
    change (b ^ n).val ∈ V
    rw [hbn]
    exact hn
  change ‖(phase (b ^ n) : ℂ) - 1‖ < 1 / 2 at hmem
  simpa only [map_pow, Units.val_pow_eq_pow_val] using hmem
end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesCofinality
