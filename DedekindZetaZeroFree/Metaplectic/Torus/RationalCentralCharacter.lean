module

public import DedekindZetaZeroFree.Adeles.Characters.NormalizedLocalNormProduct
public import DedekindZetaZeroFree.Metaplectic.Torus.StandardDiagonalIdeleLifts
public import DedekindZetaZeroFree.Metaplectic.Torus.RationalCenterProductFormula
public import DedekindZetaZeroFree.Metaplectic.Torus.PrincipalCubicLagrangianPreimage
public import DedekindZetaZeroFree.Metaplectic.Torus.RationalTrivialCharacterContinuity

@[expose] public section

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem localValue_standard_diagonal (v : KPHilbert.Place F)
    (y : (KPHilbert.Completion F v)ˣ) :
    localValue F ζ hζ v (KPStandardLocalRootLifts.A F ζ hζ v y) =
      positiveComplex (sixthPower (Units.mk0 (localAbs F v y)
        (ne_of_gt (localAbs_pos F v y)))) := by
  have h1 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) y 1 :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) := by
    rw [KubotaRankTwo.coe_d]; exact Units.isUnit y
  have h2 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) y 1 :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) := by
    rw [KubotaRankTwo.coe_d]; exact isUnit_one
  change localValue F ζ hζ v
    (⟨KubotaRankTwo.d (KPHilbert.Completion F v) y 1, 1⟩ :
      KPLocalCover.CubicGL2Raw F ζ hζ v) =
    positiveComplex (sixthPower (Units.mk0 (localAbs F v y)
      (ne_of_gt (localAbs_pos F v y))))
  rw [localValue, dif_pos ⟨h1, h2⟩]
  have hunit : h1.unit * h2.unit⁻¹ = y := by
    ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec, IsUnit.unit_spec,
      KubotaRankTwo.coe_d]
    simp
  rw [map_one, one_mul]
  congr 1
  congr 1
  congr 1
  rw [hunit]

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension.CubeDiagonalProduct

end

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus
noncomputable section
set_option autoImplicit false

theorem local_value_modulus (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (h : IsUnit (g.g 0 0) ∧ IsUnit (g.g 1 1)) :
    ‖(KPGlobalCenterRationalCharacterExtension.localValue F ζ hζ v g : ℂ)‖ =
      ((KPGlobalCenterRationalCharacterExtension.sixthPower
        (localAbsUnit F v (h.1.unit * h.2.unit⁻¹)) : ℝ≥0) : ℝ) := by

  have hiota : ‖((KPGlobalTorusFunctionData.iota F ζ hζ g.epsilon : ℂˣ) : ℂ)‖ = 1 := by
    apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by decide)
    change (KPLocalCover.coefficientEmbedding F ζ hζ
      (KPLocalCover.threeToSix F g.epsilon) : ℂ) ^ 6 = 1
    have hp : (KPLocalCover.threeToSix F g.epsilon) ^ 6 = 1 :=
      Subtype.ext (KPLocalCover.threeToSix F g.epsilon).property
    have hm := congrArg (fun z : ℂˣ => (z : ℂ))
      (congrArg (KPLocalCover.coefficientEmbedding F ζ hζ) hp)
    simpa using hm

  have hpos : ∀ u : (ℝ≥0)ˣ,
      ‖((KPGlobalCenterRationalCharacterExtension.positiveComplex u : ℂˣ) : ℂ)‖ =
        ((u : ℝ≥0) : ℝ) := by
    intro u
    simp [KPGlobalCenterRationalCharacterExtension.positiveComplex]
  rw [KPGlobalCenterRationalCharacterExtension.localValue, dif_pos h, Units.val_mul, norm_mul,
    hiota, one_mul, hpos]
  rfl

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus

end

section
open scoped Classical BigOperators NNReal
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus
noncomputable section
set_option autoImplicit false

theorem finite_product_modulus_transport {I : Type*}
    (f : I → ℂˣ) (a : I → (ℝ≥0)ˣ) (χ : (ℝ≥0)ˣ →* (ℝ≥0)ˣ)
    (hf : Function.HasFiniteMulSupport f)
    (ha : Function.HasFiniteMulSupport a)
    (h : ∀ i, ‖(f i : ℂ)‖ = ((χ (a i) : ℝ≥0) : ℝ)) :
    ‖((∏ᶠ i, f i : ℂˣ) : ℂ)‖ = ((χ (∏ᶠ i, a i) : ℝ≥0) : ℝ) := by
  classical

  set s : Finset I := hf.toFinset ∪ ha.toFinset with hs
  have hfs : hf.toFinset ⊆ s := by rw [hs]; exact Finset.subset_union_left
  have has : ha.toFinset ⊆ s := by rw [hs]; exact Finset.subset_union_right
  rw [finprod_eq_prod_of_mulSupport_toFinset_subset f hf hfs,
      finprod_eq_prod_of_mulSupport_toFinset_subset a ha has]

  have hcoe : ((∏ i ∈ s, f i : ℂˣ) : ℂ) = ∏ i ∈ s, (f i : ℂ) :=
    map_prod (Units.coeHom ℂ) f s
  rw [hcoe, norm_prod]

  have hχ : χ (∏ i ∈ s, a i) = ∏ i ∈ s, χ (a i) := map_prod χ a s
  rw [hχ]
  rw [show ((∏ i ∈ s, χ (a i) : (ℝ≥0)ˣ) : ℝ≥0) = ∏ i ∈ s, (χ (a i) : ℝ≥0) from
        map_prod (Units.coeHom ℝ≥0) (fun i => χ (a i)) s]
  rw [NNReal.coe_prod]
  exact Finset.prod_congr rfl (fun i _ => h i)

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterModulus

end

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem cube_diagonal_product (y : CubicCharacters.cubes (Ideles F))
    (x : Raw F ζ hζ)
    (hx : ∀ v, x v = KPStandardLocalRootLifts.A F ζ hζ v
      (KPGlobalCubicIdelePairing.ideleEval F v y.val)) :
    (∃ z : Z F ζ hζ, z.val.val =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x)) ∧
    (∀ hc : x ∈ rawCenter F ζ hζ,
      rawProduct F ζ hζ ⟨x, hc⟩ =
        positiveComplex (sixthPower (KPGlobalTorusFunctionData.ideleAbs F y.val))) := by
  constructor
  · obtain ⟨t, ht, hp⟩ :=
      CubeDiagonalProduct.standard_diagonal_torus_ratio F ζ hζ y.val x hx
    have hc : t ∈ Z F ζ hζ := by
      rw [CubeDiagonalProduct.covered_torus_center_eq_cubes F ζ hζ]
      change KPGlobalTorusFunctionData.p F ζ hζ t ∈ CubicCharacters.cubes (Ideles F)
      rw [hp]
      exact y.property
    exact ⟨⟨t, hc⟩, ht⟩
  · intro hc
    letI : NumberField.IsTotallyComplex F := primitive12_totallyComplex F ζ hζ
    let f : KPHilbert.Place F → (ℝ≥0)ˣ := fun v =>
      Units.mk0 (localAbs F v (KPGlobalCubicIdelePairing.ideleEval F v y.val))
        (ne_of_gt (localAbs_pos F v (KPGlobalCubicIdelePairing.ideleEval F v y.val)))
    have hf : Function.HasFiniteMulSupport f :=
      CubeDiagonalProduct.idele_localAbs_hasFiniteMulSupport F y.val
    change (∏ᶠ v, localValue F ζ hζ v (x v)) = _
    calc
      (∏ᶠ v, localValue F ζ hζ v (x v)) =
          ∏ᶠ v, (positiveComplex.comp sixthPower) (f v) := by
        apply finprod_congr
        intro v
        rw [hx v]
        exact CubeDiagonalProduct.localValue_standard_diagonal F ζ hζ v _
      _ = (positiveComplex.comp sixthPower) (∏ᶠ v, f v) :=
        ((positiveComplex.comp sixthPower).map_finprod hf).symm
      _ = positiveComplex (sixthPower (KPGlobalTorusFunctionData.ideleAbs F y.val)) := by
        rw [show (∏ᶠ v, f v) = KPGlobalTorusFunctionData.ideleAbs F y.val from
          CubeDiagonalProduct.idele_localAbs_finprod F y.val]
        rfl

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension

end

section
open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem raw_product_modulus (x : rawCenter F ζ hζ) (z : Z F ζ hζ)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = z.val.val) :
    ‖(rawProduct F ζ hζ x : ℂ)‖ =
      ((sixthPower (KPGlobalTorusFunctionData.delta F ζ hζ z.val) : ℝ≥0) : ℝ) := by
  have hF : NumberField.InfinitePlace.nrRealPlaces F = 0 :=
    NumberField.InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
      (by norm_num) hζ
  let u := KPGlobalTorusFunctionData.p F ζ hζ z.val
  obtain ⟨ha, hprod⟩ :=
    KPGlobalCenterRationalCharacterModulus.idele_abs_finite_product F hF u
  have hlocal (v : KPHilbert.Place F) :
      ‖(localValue F ζ hζ v (x.val v) : ℂ)‖ =
        ((sixthPower (KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
          (KPGlobalCubicIdelePairing.ideleEval F v u)) : ℝ≥0) : ℝ) := by
    obtain ⟨h, hr⟩ :=
      KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio
        F ζ hζ x.val z.val hx v
    rw [KPGlobalCenterRationalCharacterModulus.local_value_modulus
      F ζ hζ v (x.val v) h, hr]
  have hm := KPGlobalCenterRationalCharacterModulus.finite_product_modulus_transport
    (fun v => localValue F ζ hζ v (x.val v))
    (fun v => KPGlobalCenterRationalCharacterModulus.localAbsUnit F v
      (KPGlobalCubicIdelePairing.ideleEval F v u))
    sixthPower ((raw_character_laws F ζ hζ).1 x) ha hlocal
  rw [hprod] at hm
  simpa only [rawProduct, KPGlobalTorusFunctionData.delta,
    MonoidHom.comp_apply, u] using hm

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension

end

section

open scoped NumberField Classical BigOperators NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacter
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev E := KPGlobalTorusFunctionData.E F ζ hζ
abbrev Z := KPGlobalTorusFunctionData.Z F ζ hζ
abbrev Ideles := KPGlobalTorusFunctionData.Ideles F
abbrev Raw := KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ

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

private theorem p_continuous : Continuous (KPGlobalTorusFunctionData.p F ζ hζ) := by
  apply (ratio_continuous F).comp
  exact ((KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous.comp
    continuous_subtype_val).subtype_mk (fun t => t.property)

private theorem ideleAbs_continuous : Continuous (KPGlobalTorusFunctionData.ideleAbs F) := by
  have hfinite : Continuous (FiniteIdeleGroup.absoluteNorm (K := F)) := by
    apply continuous_of_continuousAt_one
    apply (continuousAt_const (y := (1 : ℝ≥0ˣ))).congr_of_eventuallyEq
    have ho : IsOpen (FiniteIdeleGroup.integralSubgroup (K := F) :
        Set (FiniteIdeleGroup F)) := by
      simpa only [Finset.coe_empty, FiniteIdeleGroup.supportedAt_empty] using
        (FiniteIdeleGroup.isOpen_supportedAt (K := F) ∅)
    filter_upwards [ho.mem_nhds (Subgroup.one_mem _)] with a ha
    exact IdeleGroup.finite_absoluteNorm_eq_one_of_integral a ha
  have hidele : Continuous (IdeleGroup.absoluteNorm (K := F)) :=
    (hfinite.comp continuous_snd).mul
      ((InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst).inv)
  exact (hidele.comp (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm.continuous).inv

def localAbs (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) : ℝ≥0 := by
  cases v with
  | inl w => exact ‖(y : w.Completion)‖₊ ^ 2
  | inr q => exact ‖(y : q.adicCompletion F)‖₊

theorem localAbs_pos (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) :
    0 < localAbs F v y := by
  cases v with
  | inl w => exact pow_pos (by exact_mod_cast norm_pos_iff.mpr (Units.ne_zero y)) 2
  | inr q => exact_mod_cast norm_pos_iff.mpr (Units.ne_zero y)

def positiveComplex : (ℝ≥0)ˣ →* ℂˣ :=
  Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)

def sixthPower : (ℝ≥0)ˣ →* (ℝ≥0)ˣ := Units.map (NNReal.rpowMonoidHom (1 / 6))

def localValue (v : KPHilbert.Place F) (g : KPLocalCover.CubicGL2Raw F ζ hζ v) : ℂˣ :=
  if h : IsUnit (g.g 0 0) ∧ IsUnit (g.g 1 1) then
    KPGlobalTorusFunctionData.iota F ζ hζ g.epsilon *
      positiveComplex (sixthPower (Units.mk0
        (localAbs F v (h.1.unit * h.2.unit⁻¹)) (ne_of_gt (localAbs_pos F v _))))
  else 1

private theorem central_mul_A (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F)
    (y : (KPHilbert.Completion F v)ˣ) :
    KPLocalCover.centralInjection F ζ hζ v ε * KPStandardLocalRootLifts.A F ζ hζ v y =
      (⟨KubotaRankTwo.d (KPHilbert.Completion F v) y 1, ε⟩ :
        KPLocalCover.CubicGL2Raw F ζ hζ v) := by
  have hg : (KPLocalCover.centralInjection F ζ hζ v ε *
      KPStandardLocalRootLifts.A F ζ hζ v y).g =
      KubotaRankTwo.d (KPHilbert.Completion F v) y 1 := by
    simp [KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
  have he : (KPLocalCover.centralInjection F ζ hζ v ε *
      KPStandardLocalRootLifts.A F ζ hζ v y).epsilon = ε := by
    simp [KPStandardLocalRootLifts.A, KPLocalCover.sectionMap]
  exact KPLocalCover.CubicGL2Raw.mk.injEq _ _ _ _ |>.mpr ⟨hg, he⟩

private theorem localValue_diag (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F)
    (y : (KPHilbert.Completion F v)ˣ) :
    localValue F ζ hζ v
      (⟨KubotaRankTwo.d (KPHilbert.Completion F v) y 1, ε⟩ :
        KPLocalCover.CubicGL2Raw F ζ hζ v) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε *
        positiveComplex (sixthPower (Units.mk0 (localAbs F v y)
          (ne_of_gt (localAbs_pos F v y)))) := by
  have h1 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) y 1 :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0) := by
    rw [KubotaRankTwo.coe_d]; exact Units.isUnit y
  have h2 : IsUnit ((KubotaRankTwo.d (KPHilbert.Completion F v) y 1 :
      Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) := by
    rw [KubotaRankTwo.coe_d]; exact isUnit_one
  rw [localValue, dif_pos ⟨h1, h2⟩]
  have hunit : h1.unit * h2.unit⁻¹ = y := by
    ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, IsUnit.unit_spec, IsUnit.unit_spec,
      KubotaRankTwo.coe_d]
    simp
  congr 1
  congr 1
  congr 1
  apply Units.ext
  show localAbs F v (h1.unit * h2.unit⁻¹) = localAbs F v y
  rw [hunit]

theorem localValue_complex (w : InfinitePlace F) (ε : rootsOfUnity 3 F)
    (y : (KPHilbert.Completion F (Sum.inl w))ˣ) :
    localValue F ζ hζ (Sum.inl w)
      (KPLocalCover.centralInjection F ζ hζ (Sum.inl w) ε *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) y) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε *
        positiveComplex (sixthPower (Units.mk0 (localAbs F (Sum.inl w) y)
          (ne_of_gt (localAbs_pos F (Sum.inl w) y)))) := by
  rw [central_mul_A F ζ hζ, localValue_diag F ζ hζ]

theorem localValue_finite_cube (q : HeightOneSpectrum (𝓞 F)) (ε : rootsOfUnity 3 F)
    (y : CubicCharacters.cubes (KPHilbert.Completion F (Sum.inr q))ˣ) :
    localValue F ζ hζ (Sum.inr q)
      (KPLocalCover.centralInjection F ζ hζ (Sum.inr q) ε *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q) y.val) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε *
        positiveComplex (sixthPower (Units.mk0 (localAbs F (Sum.inr q) y.val)
          (ne_of_gt (localAbs_pos F (Sum.inr q) y.val)))) := by
  rw [central_mul_A F ζ hζ, localValue_diag F ζ hζ]

def rawCenter : Subgroup (Raw F ζ hζ) :=
  ((Z F ζ hζ).map (E F ζ hζ).subtype).comap
    ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

def rawProduct (x : rawCenter F ζ hζ) : ℂˣ :=
  ∏ᶠ v, localValue F ζ hζ v (x.val v)

private theorem localAbs_one (v : KPHilbert.Place F) :
    localAbs F v (1 : (KPHilbert.Completion F v)ˣ) = 1 := by
  cases v with
  | inl w => simp [localAbs]
  | inr q => simp [localAbs]

private theorem localValue_one (v : KPHilbert.Place F) :
    localValue F ζ hζ v (1 : KPLocalCover.CubicGL2Raw F ζ hζ v) = 1 := by
  have h1 : IsUnit ((1 : KPLocalCover.CubicGL2Raw F ζ hζ v).g 0 0) := by
    rw [KPLocalCover.one_g]; exact isUnit_one
  have h2 : IsUnit ((1 : KPLocalCover.CubicGL2Raw F ζ hζ v).g 1 1) := by
    rw [KPLocalCover.one_g]; exact isUnit_one
  have hu1 : h1.unit = 1 := by
    ext
    rw [IsUnit.unit_spec, KPLocalCover.one_g]
    simp
  have hu2 : h2.unit = 1 := by
    ext
    rw [IsUnit.unit_spec, KPLocalCover.one_g]
    simp
  rw [localValue, dif_pos ⟨h1, h2⟩]
  simp only [hu1, hu2, inv_one, mul_one, localAbs_one F v]
  simp

theorem localValue_finiteSupport (x : rawCenter F ζ hζ) :
    Function.HasFiniteMulSupport (fun v => localValue F ζ hζ v (x.val v)) := by
  exact (KPGlobalCenterRationalCharacterExtension.raw_character_laws F ζ hζ).1 x

theorem rawProduct_one : rawProduct F ζ hζ 1 = 1 := by
  rw [rawProduct]
  have hf : (fun v => localValue F ζ hζ v ((1 : rawCenter F ζ hζ).val v)) =
      fun _ => 1 := by
    funext v
    rw [show (1 : rawCenter F ζ hζ).val v = 1 from rfl, localValue_one F ζ hζ]
  rw [hf]
  exact finprod_one

theorem rawProduct_mul (x y : rawCenter F ζ hζ) :
    rawProduct F ζ hζ (x * y) = rawProduct F ζ hζ x * rawProduct F ζ hζ y := by
  exact (KPGlobalCenterRationalCharacterExtension.raw_character_laws F ζ hζ).2.1 x y

theorem rawProduct_continuous : Continuous (rawProduct F ζ hζ) := by
  exact (KPGlobalCenterRationalCharacterExtension.raw_character_laws F ζ hζ).2.2

private theorem localValue_central (v : KPHilbert.Place F) (ε : rootsOfUnity 3 F) :
    localValue F ζ hζ v (KPLocalCover.centralInjection F ζ hζ v ε) =
      KPGlobalTorusFunctionData.iota F ζ hζ ε := by
  have h := localValue_diag F ζ hζ v ε 1
  have hd : KubotaRankTwo.d (KPHilbert.Completion F v) (1 : (KPHilbert.Completion F v)ˣ) 1 = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  change localValue F ζ hζ v ⟨1, ε⟩ = _
  simpa [hd, localAbs_one] using h

theorem rawProduct_productOne (x : rawCenter F ζ hζ)
    (hx : x.val ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ) :
    rawProduct F ζ hζ x = 1 := by
  obtain ⟨ε, hε, hx⟩ := hx
  unfold rawProduct
  have hf : (fun v => localValue F ζ hζ v (x.val v)) =
      fun v => KPGlobalTorusFunctionData.iota F ζ hζ (ε v) := by
    funext v
    rw [← hx]
    exact localValue_central F ζ hζ v (ε v)
  rw [hf, ← MonoidHom.map_finprod _ (KPAdelicCoverRestrictedProduct.centralTuples_finiteSupport F ε)]
  change KPGlobalTorusFunctionData.iota F ζ hζ (KPAdelicCoverRestrictedProduct.centralProduct F ε) = 1
  rw [MonoidHom.mem_ker.mp hε, map_one]

private theorem localValue_scalar (v : KPHilbert.Place F)
    (u : (KPHilbert.Completion F v)ˣ) :
    localValue F ζ hζ v (KPScalarSplitCentral.scalarHom F ζ hζ v u) = 1 := by
  have hu : (KPScalarSplitCentral.scalarHom F ζ hζ v u).g 0 0 = u := by
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap, Matrix.scalar]
  have hu' : (KPScalarSplitCentral.scalarHom F ζ hζ v u).g 1 1 = u := by
    simp [KPScalarSplitCentral.scalarHom, KPScalarSplitCentral.scalarLift,
      KPScalarSplitCentral.scalarMatrix, KPLocalCover.sectionMap, Matrix.scalar]
  have h1 : IsUnit ((KPScalarSplitCentral.scalarHom F ζ hζ v u).g 0 0) := hu ▸ u.isUnit
  have h2 : IsUnit ((KPScalarSplitCentral.scalarHom F ζ hζ v u).g 1 1) := hu' ▸ u.isUnit
  have he1 : h1.unit = u := Units.ext (h1.unit_spec.trans hu)
  have he2 : h2.unit = u := Units.ext (h2.unit_spec.trans hu')
  rw [localValue, dif_pos ⟨h1, h2⟩]
  simp [he1, he2, localAbs_one, KPScalarSplitCentral.scalarHom,
    KPScalarSplitCentral.scalarLift, KPLocalCover.sectionMap]

theorem rawProduct_splitScalar (u : Ideles F) (x : rawCenter F ζ hζ)
    (hx : x.val = KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ u) :
    rawProduct F ζ hζ x = 1 := by
  unfold rawProduct
  have hf : (fun v => localValue F ζ hζ v (x.val v)) = fun _ => 1 := by
    funext v
    rw [hx]
    exact localValue_scalar F ζ hζ v _
  rw [hf]
  exact finprod_one

theorem center_has_raw_lift (z : Z F ζ hζ) :
    ∃ x : rawCenter F ζ hζ,
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = z.val.val := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ) z.val.val
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (KPAdelicCoverRestrictedProduct.M F ζ hζ) a
  have he : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) = z.val.val := by
    change QuotientGroup.mk' _ (QuotientGroup.mk' _ x) = z.val.val
    rw [hx, ha]
  refine ⟨⟨x, ?_⟩, he⟩
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x) ∈ (Z F ζ hζ).map (E F ζ hζ).subtype
  rw [he]
  exact ⟨z.val, z.property, rfl⟩

theorem rawProduct_independent (x y : rawCenter F ζ hζ)
    (hxy : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ y.val)) :
    rawProduct F ζ hζ x = rawProduct F ζ hζ y := by
  let q := KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ
  let t := KPAdelicCoverRestrictedProduct.scalarTuple F ζ hζ
  have hd : q (x.val * y.val⁻¹) ∈ KPAdelicCoverRestrictedProduct.splitScalarSubgroup F ζ hζ := by
    apply (QuotientGroup.eq_one_iff _).mp
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (q (x.val * y.val⁻¹)) = 1
    simpa only [q, map_mul, map_inv, hxy, mul_inv_cancel]
  obtain ⟨u, hu⟩ := hd
  have ht : (t u) ∈ rawCenter F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (q (t u)) ∈
      (Z F ζ hζ).map (E F ζ hζ).subtype
    have he : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (q (t u)) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨u, rfl⟩
    rw [he]
    exact Subgroup.one_mem _
  let s : rawCenter F ζ hζ := ⟨t u, ht⟩
  have hm : ((x * y⁻¹) * s⁻¹).val ∈ KPAdelicCoverRestrictedProduct.M F ζ hζ := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((x.val * y.val⁻¹) * (t u)⁻¹) = 1
    rw [map_mul, map_inv]
    have hu' : q (t u) = q (x.val * y.val⁻¹) := hu
    rw [hu', mul_inv_cancel]
  have hunit : rawProduct F ζ hζ (x * y⁻¹) = 1 := by
    have he : x * y⁻¹ = ((x * y⁻¹) * s⁻¹) * s := by group
    rw [he, rawProduct_mul, rawProduct_productOne F ζ hζ _ hm,
      rawProduct_splitScalar F ζ hζ u s rfl, mul_one]
  have he : x = (x * y⁻¹) * y := by group
  rw [he, rawProduct_mul, hunit, one_mul]

def omegaValue (z : Z F ζ hζ) : ℂˣ :=
  rawProduct F ζ hζ (Classical.choose (center_has_raw_lift F ζ hζ z))

theorem omegaValue_one : omegaValue F ζ hζ 1 = 1 := by
  unfold omegaValue
  rw [rawProduct_independent F ζ hζ _ 1
    (by simpa using Classical.choose_spec (center_has_raw_lift F ζ hζ 1))]
  exact rawProduct_one F ζ hζ

theorem omegaValue_mul (x y : Z F ζ hζ) :
    omegaValue F ζ hζ (x * y) = omegaValue F ζ hζ x * omegaValue F ζ hζ y := by
  let rx := Classical.choose (center_has_raw_lift F ζ hζ x)
  let ry := Classical.choose (center_has_raw_lift F ζ hζ y)
  have hx := Classical.choose_spec (center_has_raw_lift F ζ hζ x)
  have hy := Classical.choose_spec (center_has_raw_lift F ζ hζ y)
  unfold omegaValue
  rw [rawProduct_independent F ζ hζ _ (rx * ry) (by
    simp only [Subgroup.coe_mul, map_mul]
    exact (Classical.choose_spec (center_has_raw_lift F ζ hζ (x * y))).trans
      (congrArg₂ (· * ·) hx hy).symm)]
  exact rawProduct_mul F ζ hζ rx ry

theorem omegaValue_continuous : Continuous (omegaValue F ζ hζ) := by
  letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : ∀ v : KPHilbert.Place F, IsTopologicalGroup (KPLocalCover.CubicGL2Raw F ζ hζ v) := by
    intro v
    cases v with
    | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
    | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2
  letI : Fact (∀ v, IsOpen (KPAdelicCoverRestrictedProduct.compact F ζ hζ v :
      Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
    ⟨KPAdelicCoverRestrictedProduct.compact_open F ζ hζ⟩
  letI : IsTopologicalGroup (Raw F ζ hζ) := RestrictedProduct.isTopologicalGroup
    (R := fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
    (B := KPAdelicCoverRestrictedProduct.compact F ζ hζ)
  letI : IsTopologicalGroup (KPAdelicCoverRestrictedProduct.CubicGL2Adelic F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_topological_cover F ζ hζ).2.2.1
  let S := ((Z F ζ hζ).map (E F ζ hζ).subtype : Set (KPGlobalTorusFunctionData.G F ζ hζ))
  let q := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)
  have hq : IsOpenQuotientMap q :=
    (QuotientGroup.isOpenQuotientMap_mk).comp QuotientGroup.isOpenQuotientMap_mk
  let fromS (g : S) : Z F ζ hζ :=
    ⟨⟨g.val, by obtain ⟨z, hz, he⟩ := g.property; exact he ▸ z.property⟩,
      by obtain ⟨z, hz, he⟩ := g.property
         have hzg : (⟨g.val, by obtain ⟨z, hz, he⟩ := g.property; exact he ▸ z.property⟩ : E F ζ hζ) = z :=
           Subtype.ext he.symm
         exact hzg ▸ hz⟩
  let f (g : S) := omegaValue F ζ hζ (fromS g)
  have hf : Continuous f := by
    apply (hq.restrictPreimage S).isQuotientMap.continuous_iff.mpr
    have he : f ∘ S.restrictPreimage q = rawProduct F ζ hζ := by
      funext x
      unfold f omegaValue
      apply rawProduct_independent F ζ hζ
      exact Classical.choose_spec (center_has_raw_lift F ζ hζ _)
    rw [he]
    exact rawProduct_continuous F ζ hζ
  let toS (z : Z F ζ hζ) : S := ⟨z.val.val, ⟨z.val, z.property, rfl⟩⟩
  have ht : Continuous toS := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have he : omegaValue F ζ hζ = f ∘ toS := by
    funext z
    congr 1
  rw [he]
  exact hf.comp ht

def omegaA : Z F ζ hζ →ₜ* ℂˣ :=
  { toFun := omegaValue F ζ hζ
    map_one' := omegaValue_one F ζ hζ
    map_mul' := omegaValue_mul F ζ hζ
    continuous_toFun := omegaValue_continuous F ζ hζ }

theorem omegaA_raw_formula (z : Z F ζ hζ) (x : rawCenter F ζ hζ)
    (hx : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = z.val.val) :
    omegaA F ζ hζ z = rawProduct F ζ hζ x := by
  exact rawProduct_independent F ζ hζ _ x
    ((Classical.choose_spec (center_has_raw_lift F ζ hζ z)).trans hx.symm)

theorem central_root_mem (ε : rootsOfUnity 3 F) :
    ∃ z : Z F ζ hζ,
      z.val.val = KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε := by
  have hker : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
    rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
    exact ⟨ε, rfl⟩
  have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε) = 1 :=
    MonoidHom.mem_ker.mp hker
  have hE : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈ E F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
      (KPGlobalTorusFunctionData.ordinaryTorus F).comap
        (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ)
    rw [Subgroup.mem_comap, hproj]
    exact Subgroup.one_mem _
  refine ⟨⟨⟨KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε, hE⟩,
    Subgroup.mem_center_iff.mpr (fun g => Subtype.ext ?_)⟩, rfl⟩
  exact Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) g.val

def centralRoot (ε : rootsOfUnity 3 F) : Z F ζ hζ :=
  Classical.choose (central_root_mem F ζ hζ ε)

theorem centralRoot_formula (ε : rootsOfUnity 3 F) :
    (centralRoot F ζ hζ ε).val.val =
      KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε :=
  Classical.choose_spec (central_root_mem F ζ hζ ε)

theorem omegaA_genuine (ε : rootsOfUnity 3 F) :
    omegaA F ζ hζ (centralRoot F ζ hζ ε) = KPGlobalTorusFunctionData.iota F ζ hζ ε := by
  let v := KPAdelicCoverRestrictedProduct.distinguishedPlace F
  let r := KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ v
    (KPLocalCover.centralInjection F ζ hζ v ε)
  have hr : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ r) =
        (centralRoot F ζ hζ ε).val.val := (centralRoot_formula F ζ hζ ε).symm
  have hm : r ∈ rawCenter F ζ hζ := by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ r) ∈ (Z F ζ hζ).map (E F ζ hζ).subtype
    rw [hr]
    exact ⟨(centralRoot F ζ hζ ε).val, (centralRoot F ζ hζ ε).property, rfl⟩
  rw [omegaA_raw_formula F ζ hζ _ ⟨r, hm⟩ hr]
  unfold rawProduct
  have hf : (fun w => localValue F ζ hζ w (r w)) =
      Pi.mulSingle v (KPGlobalTorusFunctionData.iota F ζ hζ ε) := by
    funext w
    by_cases hw : w = v
    · subst w
      simpa [r, KPAdelicCoverRestrictedProduct.localToRestricted] using
        localValue_central F ζ hζ v ε
    · simp [r, KPAdelicCoverRestrictedProduct.localToRestricted, hw, localValue_one]
  rw [hf]
  rw [finprod_eq_single _ v (by intro w hw; simp [hw])]
  simp

theorem diagonalTuple_restricted (y : Ideles F) :
    ∀ᶠ v in Filter.cofinite,
      KPStandardLocalRootLifts.A F ζ hζ v (KPGlobalCubicIdelePairing.ideleEval F v y) ∈
        KPAdelicCoverRestrictedProduct.compact F ζ hζ v := by
  have hi : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∃ u : KPHilbert.LocalIntegerUnits F q,
        KPHilbert.integerUnitInclusion F q u = KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y := by
    filter_upwards [y.val.2.property, y.inv.2.property] with q hq hqi
    letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
    letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    have mem (a : q.adicCompletion F) (ha : a ∈ q.adicCompletionIntegers F) :
        a ∈ (ValuativeRel.valuation (q.adicCompletion F)).integer := by
      rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
      exact (Valuation.vle_one_iff
        (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))).mpr ha
    let z := KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y
    let u : KPHilbert.LocalIntegerUnits F q :=
      ⟨⟨(z : q.adicCompletion F), mem _ hq⟩,
       ⟨(z⁻¹ : (q.adicCompletion F)ˣ), mem _ hqi⟩,
       by apply Subtype.ext; exact z.val_inv,
       by apply Subtype.ext; exact z.inv_val⟩
    exact ⟨u, rfl⟩
  have hf := Filter.mem_cofinite.mp hi
  have hb := KPAdelicCoverRestrictedProduct.bad_finite F
  filter_upwards [((hf.union hb).image
    (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).compl_mem_cofinite] with v hv
  cases v with
  | inl w => exact Subgroup.mem_top _
  | inr q =>
    have hq : ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro h
      exact hv ⟨q, Or.inr h, rfl⟩
    have hu : ∃ u : KPHilbert.LocalIntegerUnits F q,
        KPHilbert.integerUnitInclusion F q u = KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) y := by
      by_contra h
      exact hv ⟨q, Or.inl h, rfl⟩
    obtain ⟨u, hu⟩ := hu
    rw [KPAdelicCoverRestrictedProduct.compact, KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hq]
    refine ⟨KPStandardLocalRootLifts.integralA F q u, ?_⟩
    rw [← hu, KPStandardLocalRootLifts.A_eq_compact F ζ hζ q (fun h => hq (Or.inr h)) u]
    rfl

def diagonalTuple (y : Ideles F) : Raw F ζ hζ :=
  ⟨fun v => KPStandardLocalRootLifts.A F ζ hζ v
    (KPGlobalCubicIdelePairing.ideleEval F v y), diagonalTuple_restricted F ζ hζ y⟩

def diagonalLift (y : Ideles F) : KPGlobalTorusFunctionData.G F ζ hζ :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (diagonalTuple F ζ hζ y))

theorem cubeLift_mem (y : CubicCharacters.cubes (Ideles F)) :
    ∃ z : Z F ζ hζ, z.val.val = diagonalLift F ζ hζ y.val := by
  exact (KPGlobalCenterRationalCharacterExtension.cube_diagonal_product F ζ hζ y
    (diagonalTuple F ζ hζ y.val) (fun _ => rfl)).1

def cubeLift (y : CubicCharacters.cubes (Ideles F)) : Z F ζ hζ :=
  Classical.choose (cubeLift_mem F ζ hζ y)

theorem cubeLift_formula (y : CubicCharacters.cubes (Ideles F)) :
    (cubeLift F ζ hζ y).val.val = diagonalLift F ζ hζ y.val :=
  Classical.choose_spec (cubeLift_mem F ζ hζ y)

theorem omegaA_cube (y : CubicCharacters.cubes (Ideles F)) :
    omegaA F ζ hζ (cubeLift F ζ hζ y) =
      positiveComplex (sixthPower (KPGlobalTorusFunctionData.ideleAbs F y.val)) := by
  let x := diagonalTuple F ζ hζ y.val
  have hx : x ∈ rawCenter F ζ hζ := by
    change diagonalLift F ζ hζ y.val ∈ (Z F ζ hζ).map (E F ζ hζ).subtype
    rw [← cubeLift_formula F ζ hζ y]
    exact ⟨(cubeLift F ζ hζ y).val, (cubeLift F ζ hζ y).property, rfl⟩
  rw [omegaA_raw_formula F ζ hζ _ ⟨x, hx⟩ (cubeLift_formula F ζ hζ y).symm]
  exact (KPGlobalCenterRationalCharacterExtension.cube_diagonal_product F ζ hζ y x
    (fun _ => rfl)).2 hx

theorem omegaA_rational_intersection (a : Fˣ) (z : Z F ζ hζ)
    (hz : z.val = KPGlobalTorusFunctionData.s F ζ hζ a) : omegaA F ζ hζ z = 1 := by
  obtain ⟨x, hx⟩ := center_has_raw_lift F ζ hζ z
  rw [omegaA_raw_formula F ζ hζ z x hx]
  exact KPGlobalCenterRationalCharacterExtension.rational_raw_product F ζ hζ a x
    (hx.trans (congrArg Subtype.val hz))

def R : Subgroup (E F ζ hζ) :=
  (KPGlobalTorusFunctionData.s F ζ hζ).range ⊔ Z F ζ hζ

theorem R_eq_product (g : E F ζ hζ) :
    g ∈ R F ζ hζ ↔ ∃ (a : Fˣ) (z : Z F ζ hζ),
      KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g := by
  rw [R, Subgroup.mem_sup_of_normal_right]
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, z, hz, h⟩
    exact ⟨a, ⟨z, hz⟩, h⟩
  · rintro ⟨a, z, h⟩
    exact ⟨_, ⟨a, rfl⟩, z.val, z.property, h⟩

theorem R_eq_principal_preimage : R F ζ hζ =
    (KPGlobalPrincipalCubicLagrangian.A F).comap
      ((QuotientGroup.mk' (CubicCharacters.cubes (Ideles F))).comp
        (KPGlobalTorusFunctionData.p F ζ hζ)) := by
  exact (KPGlobalCenterRationalCharacterExtension.rational_subgroup_geometry F ζ hζ).1

theorem R_closed : IsClosed (R F ζ hζ : Set (E F ζ hζ)) := by
  exact (KPGlobalCenterRationalCharacterExtension.rational_subgroup_geometry F ζ hζ).2.1

theorem R_maximal_abelian : KPLocalPolarization.IsMaximalAbelian (R F ζ hζ) := by
  exact (KPGlobalCenterRationalCharacterExtension.rational_subgroup_geometry F ζ hζ).2.2

def rationalCenterFactor (g : R F ζ hζ) : Z F ζ hζ :=
  Classical.choose (Classical.choose_spec ((R_eq_product F ζ hζ g.val).mp g.property))

def lambdaValue (g : R F ζ hζ) : ℂˣ :=
  omegaA F ζ hζ (rationalCenterFactor F ζ hζ g)

theorem lambdaValue_formula (g : R F ζ hζ) (a : Fˣ) (z : Z F ζ hζ)
    (h : KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g.val) :
    lambdaValue F ζ hζ g = omegaA F ζ hζ z := by
  set a₀ : Fˣ := Classical.choose ((R_eq_product F ζ hζ g.val).mp g.property) with ha₀
  set z₀ : Z F ζ hζ := rationalCenterFactor F ζ hζ g with hz₀def
  have hz₀ : KPGlobalTorusFunctionData.s F ζ hζ a₀ * z₀.val = g.val := by
    rw [ha₀, hz₀def]
    exact Classical.choose_spec
      (Classical.choose_spec ((R_eq_product F ζ hζ g.val).mp g.property))
  have heq : KPGlobalTorusFunctionData.s F ζ hζ a * z.val =
      KPGlobalTorusFunctionData.s F ζ hζ a₀ * z₀.val := by rw [h, hz₀]
  have hz : z.val = KPGlobalTorusFunctionData.s F ζ hζ (a⁻¹ * a₀) * z₀.val := by
    have := congrArg (fun w => (KPGlobalTorusFunctionData.s F ζ hζ a)⁻¹ * w) heq
    simpa [map_mul, mul_assoc] using this
  have hzz : (z * z₀⁻¹).val = KPGlobalTorusFunctionData.s F ζ hζ (a⁻¹ * a₀) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hz]
    simp
  have h1 : omegaA F ζ hζ (z * z₀⁻¹) = 1 :=
    omegaA_rational_intersection F ζ hζ (a⁻¹ * a₀) (z * z₀⁻¹) hzz
  have h2 : omegaA F ζ hζ z = omegaA F ζ hζ z₀ := by
    have hsplit : z = (z * z₀⁻¹) * z₀ := by group
    rw [hsplit, map_mul, h1, one_mul]
  show omegaA F ζ hζ (rationalCenterFactor F ζ hζ g) = omegaA F ζ hζ z
  rw [← hz₀def, ← h2]

theorem lambdaValue_one : lambdaValue F ζ hζ 1 = 1 := by
  rw [lambdaValue_formula F ζ hζ 1 1 1 (by simp), map_one]

theorem lambdaValue_mul (g h : R F ζ hζ) :
    lambdaValue F ζ hζ (g * h) = lambdaValue F ζ hζ g * lambdaValue F ζ hζ h := by
  obtain ⟨a₁, z₁, hz₁⟩ := (R_eq_product F ζ hζ g.val).mp g.property
  obtain ⟨a₂, z₂, hz₂⟩ := (R_eq_product F ζ hζ h.val).mp h.property
  have hc : z₁.val * KPGlobalTorusFunctionData.s F ζ hζ a₂ =
      KPGlobalTorusFunctionData.s F ζ hζ a₂ * z₁.val :=
    (Subgroup.mem_center_iff.mp z₁.property _).symm
  have hcomm : (KPGlobalTorusFunctionData.s F ζ hζ a₁ * z₁.val) *
      (KPGlobalTorusFunctionData.s F ζ hζ a₂ * z₂.val) =
      KPGlobalTorusFunctionData.s F ζ hζ (a₁ * a₂) * (z₁ * z₂).val := by
    rw [map_mul, Subgroup.coe_mul]
    calc (KPGlobalTorusFunctionData.s F ζ hζ a₁ * z₁.val) *
          (KPGlobalTorusFunctionData.s F ζ hζ a₂ * z₂.val)
        = KPGlobalTorusFunctionData.s F ζ hζ a₁ * ((z₁.val *
            KPGlobalTorusFunctionData.s F ζ hζ a₂) * z₂.val) := by group
      _ = KPGlobalTorusFunctionData.s F ζ hζ a₁ *
            ((KPGlobalTorusFunctionData.s F ζ hζ a₂ * z₁.val) * z₂.val) := by rw [hc]
      _ = (KPGlobalTorusFunctionData.s F ζ hζ a₁ *
            KPGlobalTorusFunctionData.s F ζ hζ a₂) * (z₁.val * z₂.val) := by group
  have hgh : KPGlobalTorusFunctionData.s F ζ hζ (a₁ * a₂) * (z₁ * z₂).val =
      (g * h).val := by
    change KPGlobalTorusFunctionData.s F ζ hζ (a₁ * a₂) * (z₁.val * z₂.val) = g.val * h.val
    rw [← hz₁, ← hz₂]
    exact hcomm.symm
  rw [lambdaValue_formula F ζ hζ g a₁ z₁ hz₁,
    lambdaValue_formula F ζ hζ h a₂ z₂ hz₂,
    lambdaValue_formula F ζ hζ (g * h) (a₁ * a₂) (z₁ * z₂) hgh, map_mul]

theorem lambdaValue_continuous : Continuous (lambdaValue F ζ hζ) := by
  exact KPGlobalCenterRationalCharacterExtension.rational_extension_continuous F ζ hζ
    (omegaA F ζ hζ) (lambdaValue F ζ hζ) (lambdaValue_formula F ζ hζ)

def lambdaR : R F ζ hζ →ₜ* ℂˣ :=
  { toFun := lambdaValue F ζ hζ
    map_one' := lambdaValue_one F ζ hζ
    map_mul' := lambdaValue_mul F ζ hζ
    continuous_toFun := lambdaValue_continuous F ζ hζ }

theorem lambdaR_formula (g : R F ζ hζ) (a : Fˣ) (z : Z F ζ hζ)
    (h : KPGlobalTorusFunctionData.s F ζ hζ a * z.val = g.val) :
    lambdaR F ζ hζ g = omegaA F ζ hζ z := by
  exact lambdaValue_formula F ζ hζ g a z h

theorem lambdaR_rational (a : Fˣ) (g : R F ζ hζ)
    (hg : g.val = KPGlobalTorusFunctionData.s F ζ hζ a) : lambdaR F ζ hζ g = 1 := by
  rw [lambdaR_formula F ζ hζ g a 1 (by simpa using hg.symm), map_one]

theorem lambdaR_genuine (ε : rootsOfUnity 3 F) (g : R F ζ hζ)
    (hg : g.val = (centralRoot F ζ hζ ε).val) :
    lambdaR F ζ hζ g = KPGlobalTorusFunctionData.iota F ζ hζ ε := by
  rw [lambdaR_formula F ζ hζ g 1 (centralRoot F ζ hζ ε) (by simpa using hg.symm)]
  exact omegaA_genuine F ζ hζ ε

def nu : E F ζ hζ →* (ℝ≥0)ˣ :=
  sixthPower.comp (KPGlobalTorusFunctionData.delta F ζ hζ)

theorem nu_formula (g : E F ζ hζ) :
    ((nu F ζ hζ g : ℝ≥0) : ℝ) =
      (((KPGlobalTorusFunctionData.ideleAbs F (KPGlobalTorusFunctionData.p F ζ hζ g)
        : ℝ≥0) : ℝ)) ^ (1 / 6 : ℝ) := by
  exact NNReal.coe_rpow _ _

theorem nu_positive (g : E F ζ hζ) : 0 < ((nu F ζ hζ g : ℝ≥0) : ℝ) := by
  exact_mod_cast pos_iff_ne_zero.mpr (Units.ne_zero (nu F ζ hζ g))

theorem nu_continuous : Continuous (nu F ζ hζ) := by
  have h6 : Continuous sixthPower := by
    exact (NNReal.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 6)).units_map _
  exact h6.comp ((ideleAbs_continuous F).comp (p_continuous F ζ hζ))

theorem nu_centralRoot (ε : rootsOfUnity 3 F) :
    nu F ζ hζ (centralRoot F ζ hζ ε).val = 1 := by
  have hker : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
      (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
    rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
    exact ⟨ε, rfl⟩
  have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ
      (centralRoot F ζ hζ ε).val.val = 1 := by
    rw [centralRoot_formula]
    exact MonoidHom.mem_ker.mp hker
  have hp' : KPGlobalTorusFunctionData.p F ζ hζ (centralRoot F ζ hζ ε).val = 1 := by
    unfold KPGlobalTorusFunctionData.p
    have ht : ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
        (fun t ht => ht)) (centralRoot F ζ hζ ε).val =
          (1 : KPGlobalTorusFunctionData.ordinaryTorus F) := Subtype.ext hp
    change KPGlobalTorusFunctionData.torusRatio F _ = 1
    rw [ht, map_one]
  change sixthPower (KPGlobalTorusFunctionData.ideleAbs F
    (KPGlobalTorusFunctionData.p F ζ hζ (centralRoot F ζ hζ ε).val)) = 1
  rw [hp', map_one, map_one]

 theorem p_rational (a : Fˣ) : KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) = IdeleGroup.unitEmbedding (𝓞 F) F a := by
  let A := KPAdelicCoverRestrictedProduct.rationalBase F (KubotaRankTwo.d F a 1)
  have hp : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a).val = QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A := by
    change QuotientGroup.mk' _ (KPAdelicCoverRestrictedProduct.projection F ζ hζ (KPAdelicCoverRestrictedProduct.rationalSection F ζ hζ _)) = _
    rw [KPAdelicCoverRestrictedProduct.projection_rationalSection]
    rfl
  have h10 : A 1 0 = 0 := by simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  have h01 : A 0 1 = 0 := by simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  have h := KPGlobalTorusFunctionData.ratio_formula F
    ⟨_, (KPGlobalTorusFunctionData.s F ζ hζ a).property⟩ A hp.symm h10 h01
  apply Units.ext
  change (KPGlobalTorusFunctionData.torusRatio F
    ⟨KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a).val,
      (KPGlobalTorusFunctionData.s F ζ hζ a).property⟩ : KPGlobalTorusFunctionData.Adeles F) = _
  rw [h]
  have he1 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).1.unit = IdeleGroup.unitEmbedding (𝓞 F) F a := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPAdelicCoverRestrictedProduct.rationalBase, NumberField.IdeleGroup.unitEmbedding]
  have he2 : (KPGlobalTorusFunctionData.diagonal_entries_units F A h10 h01).2.unit = 1 := by
    apply Units.ext
    rw [IsUnit.unit_spec]
    simp [A, KPAdelicCoverRestrictedProduct.rationalBase]
  simp [he1, he2]
private theorem nu_rational (a : Fˣ) : nu F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a) = 1 := by
  have he : (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
      (IdeleGroup.unitEmbedding (𝓞 F) F a) = IdeleGroup.principalIdele F a := by
    apply (IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact (IdeleGroup.equivAdeleRingUnits_principalIdele F a).symm
  change sixthPower ((IdeleGroup.absoluteNorm
    ((IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F).symm
      (KPGlobalTorusFunctionData.p F ζ hζ (KPGlobalTorusFunctionData.s F ζ hζ a))))⁻¹) = 1
  rw [p_rational, he, IdeleGroup.absoluteNorm_principalIdele, inv_one, map_one]

theorem omegaA_norm (z : Z F ζ hζ) :
    ‖(omegaA F ζ hζ z : ℂ)‖ = ((nu F ζ hζ z.val : ℝ≥0) : ℝ) := by
  obtain ⟨x, hx⟩ := center_has_raw_lift F ζ hζ z
  rw [omegaA_raw_formula F ζ hζ z x hx]
  exact KPGlobalCenterRationalCharacterExtension.raw_product_modulus F ζ hζ x z hx

theorem lambdaR_norm (g : R F ζ hζ) :
    ‖(lambdaR F ζ hζ g : ℂ)‖ = ((nu F ζ hζ g.val : ℝ≥0) : ℝ) := by
  obtain ⟨a, z, hz⟩ := (R_eq_product F ζ hζ g.val).mp g.property
  rw [lambdaR_formula F ζ hζ g a z hz, omegaA_norm F ζ hζ z, ← hz,
    map_mul, nu_rational F ζ hζ a, one_mul]

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacter

end
