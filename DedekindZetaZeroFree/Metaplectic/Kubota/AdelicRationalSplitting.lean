module

public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology
public import DedekindZetaZeroFree.Metaplectic.Kubota.BruhatLiftsAndScalarQuotients
public import DedekindZetaZeroFree.Metaplectic.Torus.EffectiveDiagonalHilbertMultipliers

@[expose] public section

open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.KPRationalAdelicSplitting

noncomputable section
set_option autoImplicit false

open KPAdelicCoverRestrictedProduct

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def rationalScalars : Subgroup (KubotaRankTwo.GL2 F) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : Fˣ →* KubotaRankTwo.GL2 F).range

theorem rationalScalars_central :
    rationalScalars F ≤ Subgroup.center (KubotaRankTwo.GL2 F) := by
  rintro g ⟨z, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro h
  exact (Matrix.GeneralLinearGroup.scalar_commute z h).symm

instance rationalScalars_normal : (rationalScalars F).Normal :=
  Subgroup.normal_of_le_center (rationalScalars_central F)

abbrev RationalPGL2 := KubotaRankTwo.GL2 F ⧸ rationalScalars F

theorem rationalScalars_le_ker : rationalScalars F ≤
    ((scalarQuotient F ζ hζ).comp (rationalHom F ζ hζ)).ker := by
  rintro g ⟨z, rfl⟩
  change scalarQuotient F ζ hζ (rationalSection F ζ hζ _) = 1
  rw [rationalSection_scalar]
  exact (QuotientGroup.eq_one_iff _).mpr ⟨_, rfl⟩

def rationalPGLHom : RationalPGL2 F →* CubicPGL2Adelic F ζ hζ :=
  QuotientGroup.lift (rationalScalars F)
    ((scalarQuotient F ζ hζ).comp (rationalHom F ζ hζ))
    (rationalScalars_le_ker F ζ hζ)

def NCoordinates (x : Adeles F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v x)

def ACoordinates (y : Ideles F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPStandardLocalRootLifts.A F ζ hζ v (Units.map (adeleEval F v) y)

def WCoordinates (v : KPHilbert.Place F) : KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPStandardLocalRootLifts.W F ζ hζ v

theorem integral_iff (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (x : q.adicCompletion F) : x ∈ KPTameCompact.O F q ↔ x ∈ q.adicCompletionIntegers F := by
  letI : ValuativeRel (q.adicCompletion F) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
  change (ValuativeRel.valuation (q.adicCompletion F)) x ≤ 1 ↔ Valued.v x ≤ 1
  rw [← Valuation.vle_one_iff]
  letI : Valued.v.Compatible := Valuation.Compatible.ofValuation (Valued.v : Valuation (q.adicCompletion F) (WithZero (Multiplicative ℤ)))
  exact Valuation.vle_one_iff Valued.v

private theorem finite_eventually {P : KPHilbert.Place F → Prop}
    (h : ∀ᶠ q in Filter.cofinite, P (Sum.inr q)) : ∀ᶠ v in Filter.cofinite, P v := by
  simp only [Filter.eventually_cofinite] at h ⊢
  apply Set.finite_preimage_inl_and_inr.mp
  exact ⟨Set.toFinite _, h⟩

private theorem good_N (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hq : ¬ Bad F q) (t : KPTameCompact.O F q) :
    KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) t ∈ compact F ζ hζ (Sum.inr q) := by
  simp only [compact, finiteCompact, dif_neg hq]
  refine ⟨KPStandardLocalRootLifts.integralN F q t, ?_⟩
  change KPLocalCover.CubicGL2Raw.mk _ _ = _
  exact (KPStandardLocalRootLifts.N_eq_compact F ζ hζ q (fun h3 => hq (Or.inr h3)) t).symm

theorem good_A (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hq : ¬ Bad F q) (y : (KPTameCompact.O F q)ˣ) :
    KPStandardLocalRootLifts.A F ζ hζ (Sum.inr q)
      (Units.map (KPTameCompact.O F q).subtype y) ∈ compact F ζ hζ (Sum.inr q) := by
  simp only [compact, finiteCompact, dif_neg hq]
  refine ⟨KPStandardLocalRootLifts.integralA F q y, ?_⟩
  change KPLocalCover.CubicGL2Raw.mk _ _ = _
  exact (KPStandardLocalRootLifts.A_eq_compact F ζ hζ q (fun h3 => hq (Or.inr h3)) y).symm

theorem NCoordinates_restricted (x : Adeles F) :
    ∀ᶠ v in Filter.cofinite, NCoordinates F ζ hζ x v ∈ (compact F ζ hζ v : Set _) := by
  apply finite_eventually F
  have hg : ∀ᶠ q in Filter.cofinite, ¬ Bad F q := by
    simpa [Filter.mem_cofinite] using bad_finite F
  filter_upwards [x.2.2, hg] with q hx hq
  exact good_N F ζ hζ q hq ⟨x.2 q, (integral_iff F q _).mpr hx⟩

theorem ACoordinates_restricted (y : Ideles F) :
    ∀ᶠ v in Filter.cofinite, ACoordinates F ζ hζ y v ∈ (compact F ζ hζ v : Set _) := by
  apply finite_eventually F
  have hg : ∀ᶠ q in Filter.cofinite, ¬ Bad F q := by
    simpa [Filter.mem_cofinite] using bad_finite F
  filter_upwards [(y : Adeles F).2.2, (↑y⁻¹ : Adeles F).2.2, hg] with q hy hi hq
  let u : (KPTameCompact.O F q)ˣ :=
    { val := ⟨(y : Adeles F).2 q, (integral_iff F q _).mpr hy⟩
      inv := ⟨(↑y⁻¹ : Adeles F).2 q, (integral_iff F q _).mpr hi⟩
      val_inv := by apply Subtype.ext; exact congrArg (fun z : Adeles F => z.2 q) y.val_inv
      inv_val := by apply Subtype.ext; exact congrArg (fun z : Adeles F => z.2 q) y.inv_val }
  have he : Units.map (KPTameCompact.O F q).subtype u = Units.map (adeleEval F (Sum.inr q)).toMonoidHom y := by
    apply Units.ext
    rfl
  have hh := good_A F ζ hζ q hq u
  rw [he] at hh
  exact hh

theorem WCoordinates_restricted :
    ∀ᶠ v in Filter.cofinite, WCoordinates F ζ hζ v ∈ (compact F ζ hζ v : Set _) := by
  simpa only [WCoordinates, rationalCoordinates_W] using
    rationalCoordinates_restricted F ζ hζ (KPStandardLocalRootLifts.weylSwap F)

def NTuple (x : Adeles F) : RestrictedCover F ζ hζ :=
  ⟨NCoordinates F ζ hζ x, NCoordinates_restricted F ζ hζ x⟩

def ATuple (y : Ideles F) : RestrictedCover F ζ hζ :=
  ⟨ACoordinates F ζ hζ y, ACoordinates_restricted F ζ hζ y⟩

def WTuple : RestrictedCover F ζ hζ :=
  ⟨WCoordinates F ζ hζ, WCoordinates_restricted F ζ hζ⟩

def N (x : Adeles F) : CubicGL2Adelic F ζ hζ :=
  amalgamation F ζ hζ (NTuple F ζ hζ x)

def A (y : Ideles F) : CubicGL2Adelic F ζ hζ :=
  amalgamation F ζ hζ (ATuple F ζ hζ y)

def W : CubicGL2Adelic F ζ hζ :=
  amalgamation F ζ hζ (WTuple F ζ hζ)

def localAdele (v : KPHilbert.Place F) (x : KPHilbert.Completion F v) : Adeles F :=
  match v with
  | Sum.inl w => (Pi.single w x, 0)
  | Sum.inr q => (0, RestrictedProduct.single
      (fun q : IsDedekindDomain.HeightOneSpectrum (𝓞 F) => q.adicCompletionIntegers F) q x)

def localIdele (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) : Ideles F :=
  match v with
  | Sum.inl w => Units.map (NumberField.AdeleRing.ofCompletion (𝓞 F) F w) y
  | Sum.inr q => Units.map (NumberField.AdeleRing.ofAdicCompletion (𝓞 F) F q) y

theorem eval_localAdele (v w : KPHilbert.Place F) (x : KPHilbert.Completion F v) :
    adeleEval F w (localAdele F v x) = Pi.single v x w := by
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      change Pi.single v x w = Pi.single (Sum.inl v) x (Sum.inl w)
      by_cases h : w = v
      · subst w; simp
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (Sum.inl_injective.ne h)]
    | inr w => change 0 = _; simp
  | inr v =>
    cases w with
    | inl w => change 0 = _; simp
    | inr w =>
      change Pi.single v x w = Pi.single (Sum.inr v) x (Sum.inr w)
      by_cases h : w = v
      · subst w; simp
      · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (Sum.inr_injective.ne h)]

theorem eval_localIdele (v w : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) :
    Units.map (adeleEval F w).toMonoidHom (localIdele F v y) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) v y w := by
  apply Units.ext
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      change Pi.mulSingle v (↑y : KPHilbert.Completion F (Sum.inl v)) w =
        ↑(Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inl v) y (Sum.inl w))
      by_cases h : w = v
      · subst w; simp
      · simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (Sum.inl_injective.ne h)]
    | inr w => change (1 : KPHilbert.Completion F (Sum.inr w)) = _; simp
  | inr v =>
    cases w with
    | inl w => change (1 : KPHilbert.Completion F (Sum.inl w)) = _; simp
    | inr w =>
      change Pi.mulSingle v (↑y : KPHilbert.Completion F (Sum.inr v)) w =
        ↑(Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) (Sum.inr v) y (Sum.inr w))
      by_cases h : w = v
      · subst w; simp
      · simp [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne (Sum.inr_injective.ne h)]

theorem N_local (v : KPHilbert.Place F) (x : KPHilbert.Completion F v) :
    N F ζ hζ (localAdele F v x) =
      localInjection F ζ hζ v (KPStandardLocalRootLifts.N F ζ hζ v x) := by
  unfold N localInjection
  simp only [MonoidHom.comp_apply]
  congr 1
  apply RestrictedProduct.ext
  intro w
  change KPStandardLocalRootLifts.N F ζ hζ w (adeleEval F w (localAdele F v x)) =
    Pi.mulSingle v (KPStandardLocalRootLifts.N F ζ hζ v x) w
  rw [eval_localAdele]
  by_cases h : w = v
  · subst w; simp
  · simp [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]

theorem A_local (v : KPHilbert.Place F) (y : (KPHilbert.Completion F v)ˣ) :
    A F ζ hζ (localIdele F v y) =
      localInjection F ζ hζ v (KPStandardLocalRootLifts.A F ζ hζ v y) := by
  unfold A localInjection
  simp only [MonoidHom.comp_apply]
  congr 1
  apply RestrictedProduct.ext
  intro w
  change KPStandardLocalRootLifts.A F ζ hζ w (Units.map (adeleEval F w) (localIdele F v y)) =
    Pi.mulSingle v (KPStandardLocalRootLifts.A F ζ hζ v y) w
  have he : Units.map (adeleEval F w) (localIdele F v y) =
      Pi.mulSingle (M := fun v => (KPHilbert.Completion F v)ˣ) v y w := by
    apply Units.ext
    exact congrArg Units.val (eval_localIdele F v w y)
  rw [he]
  by_cases h : w = v
  · subst w; simp
  · simp [Pi.mulSingle_eq_of_ne h]

@[simp] theorem WTuple_eval (v : KPHilbert.Place F) :
    WTuple F ζ hζ v = KPStandardLocalRootLifts.W F ζ hζ v := rfl

private theorem eval_algebraMap (v : KPHilbert.Place F) (x : F) :
    adeleEval F v (algebraMap F (Adeles F) x) = algebraMap F (KPHilbert.Completion F v) x := by
  cases v <;> rfl

theorem eval_rationalUnit (v : KPHilbert.Place F) (y : Fˣ) :
    Units.map (adeleEval F v).toMonoidHom (Units.map (algebraMap F (Adeles F)).toMonoidHom y) =
      Units.map (algebraMap F (KPHilbert.Completion F v)).toMonoidHom y := by
  apply Units.ext
  exact eval_algebraMap F v y

theorem N_rational (x : F) :
    N F ζ hζ (algebraMap F (Adeles F) x) =
      rationalSection F ζ hζ (KubotaRankTwo.n F x) := by
  change amalgamation F ζ hζ _ = amalgamation F ζ hζ _
  congr 1
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.N F ζ hζ v _ = rationalCoordinates F ζ hζ _ v
  rw [eval_algebraMap, rationalCoordinates_N]

theorem A_rational (y : Fˣ) :
    A F ζ hζ (Units.map (algebraMap F (Adeles F)) y) =
      rationalSection F ζ hζ (KubotaRankTwo.d F y 1) := by
  change amalgamation F ζ hζ _ = amalgamation F ζ hζ _
  congr 1
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.A F ζ hζ v _ = rationalCoordinates F ζ hζ _ v
  rw [rationalCoordinates_A]
  congr 1
  apply Units.ext
  exact eval_algebraMap F v y

theorem W_rational :
    W F ζ hζ = rationalSection F ζ hζ (KPStandardLocalRootLifts.weylSwap F) := by
  change amalgamation F ζ hζ _ = amalgamation F ζ hζ _
  congr 1
  apply RestrictedProduct.ext
  intro v
  exact (rationalCoordinates_W F ζ hζ v).symm

theorem projection_N (x : Adeles F) (v : KPHilbert.Place F) :
    matrixEval F v (projection F ζ hζ (N F ζ hζ x)) =
      KubotaRankTwo.n (KPHilbert.Completion F v) (adeleEval F v x) := by
  rw [N, projection_amalgamation, restrictedProjection_eval]
  rfl

theorem projection_A (y : Ideles F) (v : KPHilbert.Place F) :
    matrixEval F v (projection F ζ hζ (A F ζ hζ y)) =
      KubotaRankTwo.d (KPHilbert.Completion F v) (Units.map (adeleEval F v) y) 1 := by
  rw [A, projection_amalgamation, restrictedProjection_eval]
  rfl

@[simp] theorem N_zero : N F ζ hζ 0 = 1 := by
  change amalgamation F ζ hζ (NTuple F ζ hζ 0) = 1
  have h : NTuple F ζ hζ 0 = 1 := by
    apply RestrictedProduct.ext
    intro v
    change KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v 0) = 1
    simp
  rw [h, map_one]

theorem N_add (x t : Adeles F) :
    N F ζ hζ (x + t) = N F ζ hζ x * N F ζ hζ t := by
  change amalgamation F ζ hζ _ = amalgamation F ζ hζ _ * amalgamation F ζ hζ _
  rw [← map_mul]
  congr 1
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v (x + t)) =
    KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v x) *
      KPStandardLocalRootLifts.N F ζ hζ v (adeleEval F v t)
  rw [map_add, KPStandardLocalRootLifts.N_add]

theorem W_sq : W F ζ hζ ^ 2 = 1 := by
  change (amalgamation F ζ hζ (WTuple F ζ hζ)) ^ 2 = 1
  rw [← map_pow]
  have h : WTuple F ζ hζ ^ 2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact KPStandardLocalRootLifts.W_sq F ζ hζ v
  rw [h, map_one]

theorem upper_diagonal (x : Adeles F) (y : Ideles F) :
    N F ζ hζ x * A F ζ hζ y =
      A F ζ hζ y * N F ζ hζ (x * (↑y⁻¹ : Adeles F)) := by
  unfold N A
  rw [← map_mul, ← map_mul]
  congr 1
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.N F ζ hζ v _ * KPStandardLocalRootLifts.A F ζ hζ v _ =
    KPStandardLocalRootLifts.A F ζ hζ v _ * KPStandardLocalRootLifts.N F ζ hζ v _
  rw [KPCorrectedBruhatLifts.upper_diagonal]
  congr 2
  simp [div_eq_mul_inv]

theorem weyl_diagonal (y : Ideles F) :
    W F ζ hζ * A F ζ hζ y =
      scalarHom F ζ hζ y * A F ζ hζ y⁻¹ * W F ζ hζ := by
  unfold W A scalarHom
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  apply RestrictedProduct.ext
  intro v
  change KPStandardLocalRootLifts.W F ζ hζ v * KPStandardLocalRootLifts.A F ζ hζ v _ =
    KPScalarSplitCentral.scalarHom F ζ hζ v _ * KPStandardLocalRootLifts.A F ζ hζ v _ *
      KPStandardLocalRootLifts.W F ζ hζ v
  rw [KPCorrectedBruhatLifts.weyl_diagonal]
  simp

def pglN (x : Adeles F) : CubicPGL2Adelic F ζ hζ :=
  scalarQuotient F ζ hζ (N F ζ hζ x)

def pglA (y : Ideles F) : CubicPGL2Adelic F ζ hζ :=
  scalarQuotient F ζ hζ (A F ζ hζ y)

def pglW : CubicPGL2Adelic F ζ hζ := scalarQuotient F ζ hζ (W F ζ hζ)

theorem quotient_upper_diagonal (x : Adeles F) (y : Ideles F) :
    pglN F ζ hζ x * pglA F ζ hζ y =
      pglA F ζ hζ y * pglN F ζ hζ (x * (↑y⁻¹ : Adeles F)) := by
  simpa only [map_mul, pglN, pglA] using
    congrArg (scalarQuotient F ζ hζ) (upper_diagonal F ζ hζ x y)

theorem quotient_weyl_diagonal (y : Ideles F) :
    pglW F ζ hζ * pglA F ζ hζ y = pglA F ζ hζ y⁻¹ * pglW F ζ hζ := by
  have hs (y : Ideles F) : scalarQuotient F ζ hζ (scalarHom F ζ hζ y) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨y, rfl⟩
  simpa only [map_mul, pglW, pglA, hs, one_mul] using
    congrArg (scalarQuotient F ζ hζ) (weyl_diagonal F ζ hζ y)

end
end DedekindZetaZeroFree.KPRationalAdelicSplitting

section

open scoped NumberField Classical BigOperators

namespace DedekindZetaZeroFree.KPRationalAdelicSplitting

noncomputable section
set_option autoImplicit false

open KPAdelicCoverRestrictedProduct

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem rational_splitting :
    Function.Injective (rationalHom F ζ hζ) ∧
      (projection F ζ hζ).comp (rationalHom F ζ hζ) = rationalBase F := by
  refine ⟨rationalHom_injective F ζ hζ, ?_⟩
  apply MonoidHom.ext
  intro g
  exact projection_rationalSection F ζ hζ g

def rationalPGLQuotient : KubotaRankTwo.GL2 F →* RationalPGL2 F :=
  QuotientGroup.mk' (rationalScalars F)

@[simp] theorem rationalPGLHom_mk (g : KubotaRankTwo.GL2 F) :
    rationalPGLHom F ζ hζ (rationalPGLQuotient F g) =
      scalarQuotient F ζ hζ (rationalSection F ζ hζ g) := rfl

theorem rationalScalars_le_base_ker : rationalScalars F ≤
    ((QuotientGroup.mk' (scalarSubgroup F)).comp (rationalBase F)).ker := by
  rintro g ⟨z, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  refine ⟨Units.map (algebraMap F (Adeles F)) z, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  by_cases h : i = j <;> simp [rationalBase, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal, h]

def rationalPGLBase : RationalPGL2 F →* AdelicPGL2 F :=
  QuotientGroup.lift (rationalScalars F)
    ((QuotientGroup.mk' (scalarSubgroup F)).comp (rationalBase F))
    (rationalScalars_le_base_ker F)

private theorem rationalBase_scalar (g : KubotaRankTwo.GL2 F)
    (hg : rationalBase F g ∈ scalarSubgroup F) : g ∈ rationalScalars F := by
  obtain ⟨y, hy⟩ := hg
  have hinj := NumberField.AdeleRing.algebraMap_injective (𝓞 F) F
  have hentry (i j : Fin 2) : algebraMap F (Adeles F) (g i j) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) y) i j := by
    exact congrArg (fun m : AdelicGL2 F => m i j) hy.symm
  have he : algebraMap F (Adeles F) (g 0 0) = (y : Adeles F) := by
    simpa using hentry 0 0
  have hn : g 0 0 ≠ 0 := by
    intro h
    have hey : (y : Adeles F) = 0 := by simpa [h] using he.symm
    exact y.ne_zero hey
  refine ⟨Units.mk0 (g 0 0) hn, ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply hinj
  by_cases hij : i = j
  · subst j
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal, he] using
      (hentry i i).symm
  · simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal, hij] using
      (hentry i j).symm

private theorem rationalPGLBase_injective : Function.Injective (rationalPGLBase F) := by
  apply (rationalPGLBase F).ker_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro x hx
  change x = 1
  induction x using QuotientGroup.induction_on with
  | H g =>
    apply (QuotientGroup.eq_one_iff _).mpr
    apply rationalBase_scalar F g
    exact (QuotientGroup.eq_one_iff _).mp hx

theorem rationalPGL_splitting :
    Function.Injective (rationalPGLHom F ζ hζ) ∧
      (pglProjection F ζ hζ).comp (rationalPGLHom F ζ hζ) = rationalPGLBase F := by
  have he : (pglProjection F ζ hζ).comp (rationalPGLHom F ζ hζ) = rationalPGLBase F := by
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H g =>
      change QuotientGroup.mk (projection F ζ hζ (rationalSection F ζ hζ g)) =
        QuotientGroup.mk (rationalBase F g)
      rw [projection_rationalSection]
  refine ⟨?_, he⟩
  intro x y h
  apply rationalPGLBase_injective F
  rw [← he]
  exact congrArg (pglProjection F ζ hζ) h

def LowerNCoordinates (x : Adeles F) (v : KPHilbert.Place F) :
    KPLocalCover.CubicGL2Raw F ζ hζ v :=
  KPStandardLocalRootLifts.LowerN F ζ hζ v (adeleEval F v x)

private theorem good_LowerN (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hq : ¬ Bad F q) (t : KPTameCompact.O F q) :
    KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inr q) t ∈ compact F ζ hζ (Sum.inr q) := by
  simp only [compact, finiteCompact, dif_neg hq]
  refine ⟨KPStandardLocalRootLifts.integralLowerN F q t, ?_⟩
  change KPLocalCover.CubicGL2Raw.mk _ _ = _
  exact (KPStandardLocalRootLifts.LowerN_eq_compact F ζ hζ q (fun h3 => hq (Or.inr h3)) t).symm

theorem LowerNCoordinates_restricted (x : Adeles F) :
    ∀ᶠ v in Filter.cofinite, LowerNCoordinates F ζ hζ x v ∈ (compact F ζ hζ v : Set _) := by
  apply finite_eventually F
  have hg : ∀ᶠ q in Filter.cofinite, ¬ Bad F q := by
    simpa [Filter.mem_cofinite] using bad_finite F
  filter_upwards [x.2.2, hg] with q hx hq
  exact good_LowerN F ζ hζ q hq ⟨x.2 q, (integral_iff F q _).mpr hx⟩

def LowerNTuple (x : Adeles F) : RestrictedCover F ζ hζ :=
  ⟨LowerNCoordinates F ζ hζ x, LowerNCoordinates_restricted F ζ hζ x⟩

def LowerN (x : Adeles F) : CubicGL2Adelic F ζ hζ :=
  amalgamation F ζ hζ (LowerNTuple F ζ hζ x)

theorem LowerN_local (v : KPHilbert.Place F) (x : KPHilbert.Completion F v) :
    LowerN F ζ hζ (localAdele F v x) =
      localInjection F ζ hζ v (KPStandardLocalRootLifts.LowerN F ζ hζ v x) := by
  unfold LowerN localInjection
  simp only [MonoidHom.comp_apply]
  congr 1
  apply RestrictedProduct.ext
  intro w
  change KPStandardLocalRootLifts.LowerN F ζ hζ w (adeleEval F w (localAdele F v x)) =
    Pi.mulSingle v (KPStandardLocalRootLifts.LowerN F ζ hζ v x) w
  rw [eval_localAdele]
  by_cases h : w = v
  · subst w; simp
  · simp [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h]

@[simp] theorem LowerN_zero : LowerN F ζ hζ 0 = 1 := by
  change amalgamation F ζ hζ (LowerNTuple F ζ hζ 0) = 1
  have h : LowerNTuple F ζ hζ 0 = 1 := by
    apply RestrictedProduct.ext
    intro v
    change KPStandardLocalRootLifts.LowerN F ζ hζ v (adeleEval F v 0) = 1
    simp
  rw [h, map_one]

def pglLowerN (x : Adeles F) : CubicPGL2Adelic F ζ hζ :=
  scalarQuotient F ζ hζ (LowerN F ζ hζ x)

end
end DedekindZetaZeroFree.KPRationalAdelicSplitting

end
