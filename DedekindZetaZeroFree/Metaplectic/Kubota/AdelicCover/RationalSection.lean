module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.PGLCentralExtension

@[expose] public section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] localTopology

def rationalBase : KubotaRankTwo.GL2 F →* AdelicGL2 F :=
  Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F))

def rationalCoordinates (g : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPLocalCover.sectionMap F ζ hζ v
    (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F v)) g)

private theorem integers_eq (q : HeightOneSpectrum (𝓞 F)) :
    KPLocalCube.LocalIntegers F q = (q.adicCompletionIntegers F).toSubring := by
  letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  ext a
  rw [Valuation.mem_integer_iff]
  rw [← Valuation.vle_one_iff]
  exact Valuation.vle_one_iff (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))

private theorem rational_integral (a : F) :
    ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      algebraMap F (q.adicCompletion F) a ∈ KPTameCompact.O F q := by
  have h := (algebraMap F (FiniteAdeleRing (𝓞 F) F) a).property
  filter_upwards [h] with q hq
  change _ ∈ KPLocalCube.LocalIntegers F q
  rw [integers_eq]
  exact hq

set_option backward.isDefEq.respectTransparency false in
 def integralMatrix (q : HeightOneSpectrum (𝓞 F)) (g : KubotaRankTwo.GL2 F)
    (hg : ∀ i j, algebraMap F (q.adicCompletion F) (g i j) ∈ KPTameCompact.O F q)
    (hi : ∀ i j, algebraMap F (q.adicCompletion F) (g⁻¹ i j) ∈ KPTameCompact.O F q) :
    KPTameCompact.K0 F q where
  val := fun i j => ⟨algebraMap F (q.adicCompletion F) (g i j), hg i j⟩
  inv := fun i j => ⟨algebraMap F (q.adicCompletion F) (g⁻¹ i j), hi i j⟩
  val_inv := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    apply Subtype.ext
    have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F =>
      algebraMap F (q.adicCompletion F) (m i j)) g.val_inv
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using he
  inv_val := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    apply Subtype.ext
    have he := congrArg (fun m : Matrix (Fin 2) (Fin 2) F =>
      algebraMap F (q.adicCompletion F) (m i j)) g.inv_val
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using he

private theorem integralMatrix_inclusion (q : HeightOneSpectrum (𝓞 F))
    (g : KubotaRankTwo.GL2 F) (hg hi) :
    KPTameCompact.inclusion F q (integralMatrix F q g hg hi) =
      Matrix.GeneralLinearGroup.map (algebraMap F (q.adicCompletion F)) g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rfl

private theorem rational_compact_finite (g : KubotaRankTwo.GL2 F) :
    ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      rationalCoordinates F ζ hζ g (Sum.inr q) ∈ finiteCompact F ζ hζ q := by
  have hg : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j : Fin 2, algebraMap F (q.adicCompletion F) (g i j) ∈ KPTameCompact.O F q :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => rational_integral F (g i j)))
  have hi : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j : Fin 2, algebraMap F (q.adicCompletion F) (g⁻¹ i j) ∈ KPTameCompact.O F q :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => rational_integral F (g⁻¹ i j)))
  have hb : ∀ᶠ q : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ¬ Bad F q := by
    simpa only [Filter.eventually_cofinite, not_not] using bad_finite F
  filter_upwards [hg, hi, hb, rational_integral F (g 1 0)⁻¹] with q hg hi hb hc
  unfold finiteCompact
  rw [dif_neg hb]
  let m := integralMatrix F q g hg hi
  have hm := integralMatrix_inclusion F q g hg hi
  have hk : KPTameCompact.kappa F q ζ hζ m = 1 := by
    by_cases hz : g 1 0 = 0
    · apply KPTameCompact.kappa_zero
      change algebraMap F (q.adicCompletion F) (g 1 0) = 0
      rw [hz, map_zero]
    · apply KPTameCompact.kappa_norm_one
      let u : (KPTameCompact.O F q)ˣ :=
        ⟨⟨algebraMap F (q.adicCompletion F) (g 1 0), hg 1 0⟩,
          ⟨algebraMap F (q.adicCompletion F) (g 1 0)⁻¹, hc⟩,
          by apply Subtype.ext; simp [← map_mul, hz],
          by apply Subtype.ext; simp [← map_mul, hz]⟩
      letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
      letI : (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
        Valuation.Compatible.ofValuation _
      have hv := (Valuation.integer.integers (ValuativeRel.valuation (q.adicCompletion F))).valuation_unit u
      change ValuativeRel.valuation (q.adicCompletion F) (KPTameCompact.c F q m) = 1 at hv
      have hν : Valued.v (KPTameCompact.c F q m) = 1 := by
        apply le_antisymm
        · rw [← Valuation.vle_one_iff, Valuation.vle_one_iff (ValuativeRel.valuation _)]
          exact hv.le
        · rw [← Valuation.one_vle_iff, Valuation.one_vle_iff (ValuativeRel.valuation _)]
          exact hv.ge
      have he : ‖KPTameCompact.c F q m‖ = ‖(1 : q.adicCompletion F)‖ := by
        apply le_antisymm
        · rw [Valued.toNormedField.norm_le_iff]
          simp only [hν, map_one, le_refl]
        · rw [Valued.toNormedField.norm_le_iff]
          simp only [hν, map_one, le_refl]
      simpa using he
  refine ⟨m, ?_⟩
  change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
  rw [hk, hm]

theorem rationalCoordinates_restricted (g : KubotaRankTwo.GL2 F) :
    ∀ᶠ v in Filter.cofinite,
      rationalCoordinates F ζ hζ g v ∈ (compact F ζ hζ v : Set _) := by
  have h := rational_compact_finite F ζ hζ g
  rw [Filter.eventually_cofinite] at h ⊢
  apply (h.image (Sum.inr : HeightOneSpectrum (𝓞 F) → KPHilbert.Place F)).subset
  intro v hv
  cases v with
  | inl w => exact (hv (Subgroup.mem_top _)).elim
  | inr q => exact ⟨q, hv, rfl⟩

def rationalTuple (g : KubotaRankTwo.GL2 F) : RestrictedCover F ζ hζ :=
  ⟨rationalCoordinates F ζ hζ g, rationalCoordinates_restricted F ζ hζ g⟩

def rationalSection (g : KubotaRankTwo.GL2 F) : CubicGL2Adelic F ζ hζ :=
  amalgamation F ζ hζ (rationalTuple F ζ hζ g)

@[simp] theorem rationalTuple_eval (g : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :
    rationalTuple F ζ hζ g v = rationalCoordinates F ζ hζ g v := rfl

theorem projection_rationalSection (g : KubotaRankTwo.GL2 F) :
    projection F ζ hζ (rationalSection F ζ hζ g) = rationalBase F g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Prod.ext
  · funext w
    rfl
  · apply Subtype.ext
    funext q
    rfl

private theorem map_X (g : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :
    KubotaRankTwo.X _ (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F v)) g) =
      KPHilbert.diagonal F v (KubotaRankTwo.X F g) := by
  apply Units.ext
  simp only [KubotaRankTwo.X, Units.val_mk0, KPHilbert.diagonal, Units.coe_map]
  unfold KubotaRankTwo.x
  simp only [Matrix.GeneralLinearGroup.map_apply]
  rw [map_eq_zero_iff _ (RingHom.injective _)]
  split_ifs <;> rfl

 def multiplier (g h : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :=
  KPLocalCover.sigmaTwo F ζ hζ v
    (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F v)) g)
    (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F v)) h)

private theorem multiplier_formula (g h : KubotaRankTwo.GL2 F) (v : KPHilbert.Place F) :
    multiplier F ζ hζ g h v =
      KPHilbert.B3 F ζ hζ v
        (KPHilbert.diagonal F v (KubotaRankTwo.X F (g * h) / KubotaRankTwo.X F g))
        (KPHilbert.diagonal F v (KubotaRankTwo.X F (g * h) /
          (KubotaRankTwo.X F h * KubotaRankTwo.det F g))) *
      KPHilbert.B3 F ζ hζ v
        (KPHilbert.diagonal F v (KubotaRankTwo.det F g))
        (KPHilbert.diagonal F v (KubotaRankTwo.det F h)) ^ 2 := by
  unfold multiplier KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
  simp only [← map_mul, map_X, Matrix.GeneralLinearGroup.map_det]
  simp only [KPHilbert.diagonal, map_div, map_mul]
  rfl

private theorem multiplier_reciprocity (g h : KubotaRankTwo.GL2 F) :
    Function.HasFiniteMulSupport (multiplier F ζ hζ g h) ∧
      (∏ᶠ v, multiplier F ζ hζ g h v) = 1 := by
  obtain ⟨hf, hp⟩ := KPHilbert.B3_productFormula F ζ hζ
    (KubotaRankTwo.X F (g * h) / KubotaRankTwo.X F g)
    (KubotaRankTwo.X F (g * h) / (KubotaRankTwo.X F h * KubotaRankTwo.det F g))
  obtain ⟨hf', hp'⟩ := KPHilbert.B3_productFormula F ζ hζ
    (KubotaRankTwo.det F g) (KubotaRankTwo.det F h)
  simp only [funext (multiplier_formula F ζ hζ g h)]
  constructor
  · exact hf.mul (hf'.pow 2)
  · have hf2 : Function.HasFiniteMulSupport (fun v =>
        KPHilbert.B3 F ζ hζ v (KPHilbert.diagonal F v (KubotaRankTwo.det F g))
          (KPHilbert.diagonal F v (KubotaRankTwo.det F h)) ^ 2) := hf'.pow 2
    rw [finprod_mul_distrib hf hf2, ← finprod_pow hf' 2, hp, hp', one_pow, one_mul]

theorem rationalSection_mul (g h : KubotaRankTwo.GL2 F) :
    rationalSection F ζ hζ (g * h) = rationalSection F ζ hζ g * rationalSection F ζ hζ h := by
  obtain ⟨hf, hp⟩ := multiplier_reciprocity F ζ hζ g h
  let e : CentralTuples F := ⟨multiplier F ζ hζ g h, by
    simpa only [Filter.eventually_cofinite, Subgroup.mem_bot, SetLike.mem_coe, Function.HasFiniteMulSupport, Function.mulSupport] using hf⟩
  have he : centralTupleMap F ζ hζ e ∈ M F ζ hζ := by
    apply Subgroup.mem_map.mpr
    refine ⟨e, ?_, rfl⟩
    exact hp
  have hd : rationalTuple F ζ hζ g * rationalTuple F ζ hζ h =
      centralTupleMap F ζ hζ e * rationalTuple F ζ hζ (g * h) := by
    apply Subtype.ext
    funext v
    change KPLocalCover.sectionMap F ζ hζ v _ * KPLocalCover.sectionMap F ζ hζ v _ =
      KPLocalCover.centralInjection F ζ hζ v (multiplier F ζ hζ g h v) *
        KPLocalCover.sectionMap F ζ hζ v _
    rw [KPLocalCover.sectionMap_mul, ← map_mul]
    rfl
  change amalgamation F ζ hζ _ = amalgamation F ζ hζ _ * amalgamation F ζ hζ _
  rw [← map_mul, hd, map_mul]
  have he1 : amalgamation F ζ hζ (centralTupleMap F ζ hζ e) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr he
  rw [he1, one_mul]

theorem rationalSection_one : rationalSection F ζ hζ 1 = 1 := by
  apply congrArg (amalgamation F ζ hζ)
  apply Subtype.ext
  funext v
  change KPLocalCover.sectionMap F ζ hζ v (Matrix.GeneralLinearGroup.map (algebraMap F (KPHilbert.Completion F v)) 1) = 1
  rw [map_one]
  rfl

theorem rationalSection_scalar (z : Fˣ) :
    rationalSection F ζ hζ (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      scalarHom F ζ hζ (Units.map (algebraMap F (Adeles F)) z) := by
  apply congrArg (amalgamation F ζ hζ)
  apply Subtype.ext
  funext v
  unfold rationalTuple rationalCoordinates scalarTuple scalarTupleValue scalarCoordinates
  change KPLocalCover.sectionMap F ζ hζ v _ =
    KPLocalCover.sectionMap F ζ hζ v _
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> cases v <;>
    simp [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.scalar,
      Matrix.scalar, adeleEval, Matrix.diagonal] <;> rfl

theorem rationalCoordinates_N (x : F) (v : KPHilbert.Place F) :
    rationalCoordinates F ζ hζ (KubotaRankTwo.n F x) v =
      KPStandardLocalRootLifts.N F ζ hζ v (algebraMap F (KPHilbert.Completion F v) x) := by
  unfold rationalCoordinates KPStandardLocalRootLifts.N
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, KubotaRankTwo.n]

theorem rationalCoordinates_A (y : Fˣ) (v : KPHilbert.Place F) :
    rationalCoordinates F ζ hζ (KubotaRankTwo.d F y 1) v =
      KPStandardLocalRootLifts.A F ζ hζ v (Units.map (algebraMap F (KPHilbert.Completion F v)) y) := by
  unfold rationalCoordinates KPStandardLocalRootLifts.A
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, KubotaRankTwo.d]

theorem rationalCoordinates_W (v : KPHilbert.Place F) :
    rationalCoordinates F ζ hζ (KPStandardLocalRootLifts.weylSwap F) v =
      KPStandardLocalRootLifts.W F ζ hζ v := by
  unfold rationalCoordinates KPStandardLocalRootLifts.W
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map_apply, KPStandardLocalRootLifts.weylSwap]

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw

section

open scoped NumberField Classical BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

attribute [local instance] localTopology

def rationalHom : KubotaRankTwo.GL2 F →* CubicGL2Adelic F ζ hζ where
  toFun := rationalSection F ζ hζ
  map_one' := rationalSection_one F ζ hζ
  map_mul' := rationalSection_mul F ζ hζ

theorem rationalHom_injective : Function.Injective (rationalHom F ζ hζ) := by
  intro g h e
  have he := congrArg (projection F ζ hζ) e
  change projection F ζ hζ (rationalSection F ζ hζ g) =
    projection F ζ hζ (rationalSection F ζ hζ h) at he
  rw [projection_rationalSection, projection_rationalSection] at he
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
  exact congrArg (fun m : AdelicGL2 F => m i j) he

end
end DedekindZetaZeroFree.KPAdelicCoverCertificatesRaw

end
