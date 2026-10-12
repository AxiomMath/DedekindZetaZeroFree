module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenberg.PolarizationsAndInducedDescent

@[expose] public section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalTorusFunctionData
attribute [local instance] modelTopology

def periodization (C : ModelData F ζ hζ) :
    ProductSmooth F ζ hζ C →L[ℂ] RationalSmooth F ζ hζ := by
  let s := (rational_representatives_exist F ζ hζ C).choose
  exact ⟨smoothPeriodization F ζ hζ C s, smoothPeriodization_continuous F ζ hζ C s⟩

 theorem periodization_formula (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductSmooth F ζ hζ C) (g : E F ζ hζ) :
    (periodization F ζ hζ C f).val.val g =
      ∑' a, periodizationTerm F ζ hζ C s f g a := by
  change (smoothPeriodization F ζ hζ C (rational_representatives_exist F ζ hζ C).choose f).val.val g = _
  rw [smoothPeriodization_formula]
  exact tsum_congr (periodizationTerm_independent F ζ hζ C _ s f g)

def unitaryPeriodization (C : ModelData F ζ hζ) :
    ProductUnitary F ζ hζ C →L[ℂ] RationalUnitary F ζ hζ :=
  (untwistRational F ζ hζ).toContinuousLinearMap.comp
    ((periodization F ζ hζ C).comp (untwistProduct F ζ hζ C).symm.toContinuousLinearMap)

 theorem unitaryPeriodization_formula (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C)
    (f : ProductUnitary F ζ hζ C) (g : E F ζ hζ) :
    (unitaryPeriodization F ζ hζ C f).val.val g =
      ∑' a, (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
        f.val.val ((s.lift a).val * g) := by
  change (untwistRational F ζ hζ (periodization F ζ hζ C ((untwistProduct F ζ hζ C).symm f))).val.val g = _
  rw [untwistRational_formula, periodization_formula F ζ hζ C s, ← tsum_mul_left]
  apply tsum_congr
  intro a
  rw [periodizationTerm, retwistProduct_formula, rational_unit_inverse, nu_complex_mul]
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  field_simp
  <;> ring

 theorem unitaryPeriodization_intertwines (C : ModelData F ζ hζ)
    (a : E F ζ hζ) (f : ProductUnitary F ζ hζ C) :
    unitaryPeriodization F ζ hζ C
        (rightAction F ζ hζ (KPGlobalTorusFiniteStages.productModel F ζ hζ C) a f) =
      rightAction F ζ hζ (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) a
        (unitaryPeriodization F ζ hζ C f) := by
  obtain ⟨s, hs⟩ := rational_representatives_exist F ζ hζ C
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [unitaryPeriodization_formula F ζ hζ C s, rightAction_formula,
    unitaryPeriodization_formula F ζ hζ C s]
  apply tsum_congr
  intro x
  simp only [rightAction_formula, mul_assoc]

end
end DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse

section

open scoped NumberField Classical NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open KPGlobalTorusFunctionData
attribute [local instance] modelTopology

def averaging (C : ModelData F ζ hζ) :
    RationalSmooth F ζ hζ →L[ℂ] ProductSmooth F ζ hζ C := by
  let s := Classical.choice (averaging_representatives_exist F ζ hζ C)
  exact ⟨smoothAveraging F ζ hζ C s, smoothAveraging_continuous F ζ hζ C s⟩

 theorem averaging_formula (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C) (h : RationalSmooth F ζ hζ) (g : E F ζ hζ) :
    (averaging F ζ hζ C h).val.val g =
      ∫ x, averagingIntegrand F ζ hζ C s h g x ∂probabilityHaar F ζ hζ C := by
  rw [show (averaging F ζ hζ C h).val.val g = _ from
    smoothAveraging_formula F ζ hζ C _ h g]
  apply integral_congr_ae
  filter_upwards [] with x
  exact averagingIntegrand_independent F ζ hζ C _ s h g x

private def characterSection {G : Type*} [Group G] (S : Subgroup G)
    (χ : S →* ℂˣ) : FinitePolarization.inducedSpace S χ :=
  ⟨fun g => if hg : g ∈ S then (χ ⟨g, hg⟩ : ℂ) else 0, by
    intro s g
    by_cases hg : g ∈ S
    · have hsg : (s : G) * g ∈ S := S.mul_mem s.property hg
      simp only [dif_pos hg, dif_pos hsg]
      exact map_mul χ s ⟨g, hg⟩ |> congrArg (fun z : ℂˣ => (z : ℂ))
    · have hsg : (s : G) * g ∉ S := by
        intro h
        have := S.mul_mem (S.inv_mem s.property) h
        exact hg (by simpa using this)
      simp only [dif_neg hg, dif_neg hsg, mul_zero]⟩

private theorem characterSection_one {G : Type*} [Group G] (S : Subgroup G)
    (χ : S →* ℂˣ) : (characterSection S χ).val 1 = 1 := by
  change (if h : (1 : G) ∈ S then (χ ⟨1, h⟩ : ℂ) else 0) = 1
  rw [dif_pos S.one_mem]
  exact congrArg (fun z : ℂˣ => (z : ℂ)) (map_one χ)

private theorem recover_character {G H : Type*} [Group G] [Group H]
    (S : Subgroup H) (χ : S →* ℂˣ) (φ : G →* H)
    (V : Submodule ℂ (G → ℂ))
    (e : V ≃ₗ[ℂ] FinitePolarization.inducedSpace S χ)
    (he : ∀ f x, (e f).val (φ x) = f.val x)
    (a : G) (ha : φ a ∈ S) (c : ℂ)
    (hc : ∀ f : V, ∀ x : G, f.val (a * x) = c * f.val x) :
    (χ ⟨φ a, ha⟩ : ℂ) = c := by
  let f := e.symm (characterSection S χ)
  have hf : (e f).val 1 = 1 := by
    rw [e.apply_symm_apply]
    exact characterSection_one S χ
  have h1 : f.val 1 = 1 := by
    rw [← he f 1, map_one, hf]
  have hcov := (e f).property ⟨φ a, ha⟩ 1
  calc
    (χ ⟨φ a, ha⟩ : ℂ) = (e f).val (φ a) := by
      simpa only [mul_one, hf] using hcov.symm
    _ = f.val a := he f a
    _ = c * f.val 1 := by simpa only [mul_one] using hc f 1
    _ = c := by rw [h1, mul_one]

private theorem restricted_character {H : Type*} [Group H]
    (C : ModelData F ζ hζ) (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S : Subgroup H) (χ : S →* ℂˣ)
    (φ : KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L →* H)
    (e : KPGlobalTorusFiniteStages.RestrictedSections F ζ hζ C L Q ≃ₗ[ℂ]
      FinitePolarization.inducedSpace S χ)
    (he : ∀ f x, (e f).val (φ x) = f.val x)
    (a : KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L)
    (ha : φ a ∈ S) (hQ : a.val ∈ Q.H) :
    χ ⟨φ a, ha⟩ = Q.character ⟨a.val, hQ⟩ := by
  apply Units.ext
  exact recover_character S χ φ _ e he a ha
    (Q.character ⟨a.val, hQ⟩ : ℂ)
    (fun f x => f.property.1 ⟨a, hQ⟩ x)

private theorem restricted_weighted_term {H : Type*} [Group H]
    (C : ModelData F ζ hζ) (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (Q Q' : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (S N : Subgroup H) (χ : S →* ℂˣ) (ρ : N →* ℂˣ)
    (φ : KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L →* H)
    (e : KPGlobalTorusFiniteStages.RestrictedSections F ζ hζ C L Q ≃ₗ[ℂ]
      FinitePolarization.inducedSpace S χ)
    (e' : KPGlobalTorusFiniteStages.RestrictedSections F ζ hζ C L Q' ≃ₗ[ℂ]
      FinitePolarization.inducedSpace N ρ)
    (he : ∀ f x, (e f).val (φ x) = f.val x)
    (he' : ∀ f x, (e' f).val (φ x) = f.val x)
    (a x : KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L)
    (ha : φ a ∈ S) (hQ : a.val ∈ Q.H)
    (f : KPGlobalTorusFiniteStages.RestrictedSections F ζ hζ C L Q') :
    (((χ ⟨φ a, ha⟩)⁻¹ : ℂˣ) : ℂ) * (e' f).val (φ a * φ x) =
      (((Q.character ⟨a.val, hQ⟩)⁻¹ : ℂˣ) : ℂ) * f.val (a * x) := by
  rw [restricted_character F ζ hζ C L Q S χ φ e he a ha hQ,
    ← map_mul, he']

 theorem periodization_intertwines (C : ModelData F ζ hζ)
    (a : E F ζ hζ) (f : ProductSmooth F ζ hζ C) :
    periodization F ζ hζ C (rightAction F ζ hζ (productModel F ζ hζ C) a f) =
      rightAction F ζ hζ (rationalModel F ζ hζ) a (periodization F ζ hζ C f) := by
  obtain ⟨s, hs⟩ := rational_representatives_exist F ζ hζ C
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [periodization_formula F ζ hζ C s, rightAction_formula,
    periodization_formula F ζ hζ C s]
  apply tsum_congr
  intro x
  simp only [periodizationTerm, rightAction_formula, mul_assoc]

 theorem averaging_intertwines (C : ModelData F ζ hζ)
    (a : E F ζ hζ) (h : RationalSmooth F ζ hζ) :
    averaging F ζ hζ C (rightAction F ζ hζ (rationalModel F ζ hζ) a h) =
      rightAction F ζ hζ (productModel F ζ hζ C) a (averaging F ζ hζ C h) := by
  obtain ⟨s⟩ := averaging_representatives_exist F ζ hζ C
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [averaging_formula F ζ hζ C s, rightAction_formula,
    averaging_formula F ζ hζ C s]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [averagingIntegrand, rightAction_formula, mul_assoc]

def unitaryAveraging (C : ModelData F ζ hζ) :
    RationalUnitary F ζ hζ →L[ℂ] ProductUnitary F ζ hζ C :=
  (untwistProduct F ζ hζ C).toContinuousLinearMap.comp
    ((averaging F ζ hζ C).comp (untwistRational F ζ hζ).symm.toContinuousLinearMap)

 theorem unitaryAveraging_formula (C : ModelData F ζ hζ)
    (s : AveragingRepresentatives F ζ hζ C)
    (h : RationalUnitary F ζ hζ) (g : E F ζ hζ) :
    (unitaryAveraging F ζ hζ C h).val.val g =
      ∫ x, (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment (s.lift x))⁻¹ : ℂˣ) : ℂ) *
        h.val.val ((s.lift x).val * g) ∂probabilityHaar F ζ hζ C := by
  change (untwistProduct F ζ hζ C (averaging F ζ hζ C ((untwistRational F ζ hζ).symm h))).val.val g = _
  rw [untwistProduct_formula, averaging_formula F ζ hζ C s, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [averagingIntegrand, retwistRational_formula, product_unit_inverse, nu_complex_mul]
  have hn : ((KPGlobalCenterRationalCharacter.nu F ζ hζ g : ℝ≥0) : ℂ) ≠ 0 := by
    exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ g)
  field_simp
  <;> ring

 theorem periodization_transport (C : ModelData F ζ hζ) (f : ProductSmooth F ζ hζ C) :
    untwistRational F ζ hζ (periodization F ζ hζ C f) =
      unitaryPeriodization F ζ hζ C (untwistProduct F ζ hζ C f) := by
  simp [unitaryPeriodization]

 theorem averaging_transport (C : ModelData F ζ hζ) (h : RationalSmooth F ζ hζ) :
    untwistProduct F ζ hζ C (averaging F ζ hζ C h) =
      unitaryAveraging F ζ hζ C (untwistRational F ζ hζ h) := by
  simp [unitaryAveraging]

private def pairingHom (d : KPGlobalCubicIdelePairing.D F) :
    KPGlobalCubicIdelePairing.D F →* rootsOfUnity 3 F where
  toFun := KPGlobalCubicIdelePairing.beta3 F ζ hζ d
  map_one' := by
    have h := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 d 1 1
    simpa only [one_mul, mul_eq_left] using h.symm
  map_mul' := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.1 d
private def fullPairingHom : KPGlobalCubicIdelePairing.D F →*
    (KPGlobalCubicIdelePairing.D F →* rootsOfUnity 3 F) where
  toFun := pairingHom F ζ hζ
  map_one' := by
    apply MonoidHom.ext
    intro y
    change KPGlobalCubicIdelePairing.beta3 F ζ hζ 1 y = 1
    have h := (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 1 1 y
    simpa only [one_mul, mul_eq_left] using h.symm
  map_mul' := by
    intro x y
    apply MonoidHom.ext
    intro z
    exact (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).1 x y z
private theorem maximal_mem {G : Type*} [CommGroup G]
    (b : G →* (G →* rootsOfUnity 3 F)) (halt : ∀ x, b x x = 1)
    (L : Subgroup G)
    (hL : KPGlobalProductPolarizationCharacter.IsMaximalIsotropic F (fun x y => b x y) L)
    (x : G) (hx : ∀ l ∈ L, b x l = 1) : x ∈ L := by
  have hswap (u v : G) : b v u = (b u v)⁻¹ := by
    have h := halt (v * u)
    simp only [map_mul, MonoidHom.mul_apply, halt, one_mul, mul_one] at h
    exact eq_inv_of_mul_eq_one_right h
  have hxl (l : G) (hl : l ∈ L) (n : ℤ) : b (x ^ n) l = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, hx l hl, one_zpow]
  have hlx (l : G) (hl : l ∈ L) (n : ℤ) : b l (x ^ n) = 1 := by
    rw [hswap, hxl l hl n, inv_one]
  have hxx (n p : ℤ) : b (x ^ n) (x ^ p) = 1 := by
    simp only [map_zpow, MonoidHom.zpow_apply, halt, one_zpow]
  have hiso : ∀ u ∈ L ⊔ Subgroup.zpowers x, ∀ v ∈ L ⊔ Subgroup.zpowers x,
      b u v = 1 := by
    intro u hu v hv
    obtain ⟨l, hl, u', hu', rfl⟩ := Subgroup.mem_sup.mp hu
    obtain ⟨m, hm, v', hv', rfl⟩ := Subgroup.mem_sup.mp hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    obtain ⟨p, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv'
    simp only [map_mul, MonoidHom.mul_apply, hL.1 l hl m hm,
      hlx l hl p, hxl m hm n, hxx n p, mul_one, one_mul]
  have heq := hL.2 _ le_sup_left hiso
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
private theorem principal_isotropic (a : A F) (j : A F) :
    KPGlobalCubicIdelePairing.beta3 F ζ hζ a.val j.val = 1 := by
  have ha : a.val ∈ KPGlobalPrincipalCubicLagrangian.annihilator F ζ hζ (A F) := by
    rw [KPGlobalPrincipalCubicLagrangian.principal_self_annihilating]; exact a.property
  exact ha j.val j.property
private def compactCharacter (C : ModelData F ζ hζ) (a : A F) :
    CompactIndex F ζ hζ C →* rootsOfUnity 3 F :=
  QuotientGroup.lift _ ((pairingHom F ζ hζ a.val).comp (M F ζ hζ C).subtype) (by
    intro j hj
    exact principal_isotropic F ζ hζ a ⟨j.val, hj.1⟩)
private theorem compactCharacter_formula (C : ModelData F ζ hζ) (a : A F)
    (b : B F ζ hζ C) :
    compactCharacter F ζ hζ C a (averagingClass F ζ hζ C b) =
      KPGlobalCubicIdelePairing.beta3 F ζ hζ a.val (pD F ζ hζ b.val) := rfl
private theorem compactCharacter_continuous (C : ModelData F ζ hζ) (a : A F) :
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    Continuous (compactCharacter F ζ hζ C a) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  apply (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
  exact (KPGlobalCubicIdelePairing.beta3_continuous F ζ hζ).comp
    (continuous_const.prodMk continuous_subtype_val)
private theorem compactCharacter_integral (C : ModelData F ζ hζ) (a : A F)
    (ha : a.val ∉ M F ζ hζ C) :
    (∫ x, (KPGlobalTorusFunctionData.iota F ζ hζ
      (compactCharacter F ζ hζ C a x ^ 4) : ℂ) ∂probabilityHaar F ζ hζ C) = 0 := by
  let v (x : CompactIndex F ζ hζ C) : ℂ :=
    (KPGlobalTorusFunctionData.iota F ζ hζ (compactCharacter F ζ hζ C a x ^ 4) : ℂ)
  have he : ∃ m : M F ζ hζ C, compactCharacter F ζ hζ C a (QuotientGroup.mk m) ≠ 1 := by
    by_contra hn
    push_neg at hn
    apply ha
    exact maximal_mem F (fullPairingHom F ζ hζ)
      (KPGlobalCubicIdelePairing.beta3_bilinear F ζ hζ).2.2
      (M F ζ hζ C) (KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ C)
      a.val (fun m hm => hn ⟨m, hm⟩)
  obtain ⟨m, hm⟩ := he
  let y : CompactIndex F ζ hζ C := QuotientGroup.mk m
  have hy : v y ≠ 1 := by
    intro h
    have hh : KPGlobalTorusFunctionData.iota F ζ hζ (compactCharacter F ζ hζ C a y ^ 4) = 1 :=
      Units.ext h
    apply hm
    have hp : (compactCharacter F ζ hζ C a y) ^ 3 = 1 := by
      apply Subtype.ext
      exact (compactCharacter F ζ hζ C a y).property
    have hp4 : (compactCharacter F ζ hζ C a y) ^ 4 = compactCharacter F ζ hζ C a y := by
      rw [pow_succ, hp, one_mul]
    rw [hp4] at hh
    apply Subtype.ext
    exact congrArg (fun z : rootsOfUnity 6 F => z.val) ((KPLocalCover.coefficientEmbedding_injective F ζ hζ)
      (hh.trans (map_one _).symm))
  have hv (x) : v (y * x) = v y * v x := by
    simp only [v, map_mul, mul_pow, Units.val_mul]
  have hi := integral_mul_left_eq_self (μ := probabilityHaar F ζ hζ C) v y
  simp_rw [hv] at hi
  rw [integral_const_mul] at hi
  by_contra hn
  apply hy
  exact mul_right_cancel₀ hn (hi.trans (one_mul _).symm)
private theorem diagonal_formula (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.torusRatio F t) = t.val := by
  let A := Classical.choose t.property
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val ∧
      A 1 0 = 0 ∧ A 0 1 = 0 := Classical.choose_spec t.property
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).1.unit
  let w := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).2.unit
  have hu : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := IsUnit.unit_spec _
  have hw : (w : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := IsUnit.unit_spec _
  have heq : A = KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hu, hA.2.1, hA.2.2]
    exact hw.symm
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹)) = t.val
  rw [← hA.1, heq]
  have hs : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  rw [(QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).map_mul, hs, mul_one]
private def torusPullbackBridge : KPGlobalTorusFunctionData.E F ζ hζ →* KPGlobalCubicIdelePairing.E F ζ hζ where
  toFun e := ⟨(e.val, KPGlobalTorusFunctionData.p F ζ hζ e),
    (diagonal_formula F ⟨_, e.property⟩).symm⟩
  map_one' := by apply Subtype.ext; exact Prod.ext rfl (map_one _)
  map_mul' x y := by apply Subtype.ext; exact Prod.ext rfl (map_mul _ _ _)

private theorem torusPullbackBridge_injective :
    Function.Injective (torusPullbackBridge F ζ hζ) := by
  intro x y h
  exact Subtype.ext (congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1) h)

private theorem torusPullbackBridge_projection (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    KPGlobalCubicIdelePairing.torusProjection F ζ hζ (torusPullbackBridge F ζ hζ e) =
      KPGlobalTorusFunctionData.p F ζ hζ e := rfl

private theorem commute_iff_beta (x y : KPGlobalTorusFunctionData.E F ζ hζ) :
    Commute x y ↔ KPGlobalCubicIdelePairing.beta3 F ζ hζ
      (KPGlobalProductPolarizationCharacter.pD F ζ hζ x) (KPGlobalProductPolarizationCharacter.pD F ζ hζ y) = 1 := by
  have h := KPGlobalCubicIdelePairing.commutator_annihilators F ζ hζ
    (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y)
  constructor
  · intro hc
    exact h.mp (hc.map (torusPullbackBridge F ζ hζ))
  · intro hb
    apply torusPullbackBridge_injective F ζ hζ
    simpa only [map_mul] using (h.mpr hb).eq

private theorem central_difference (x y : KPGlobalTorusFunctionData.E F ζ hζ)
    (h : KPGlobalProductPolarizationCharacter.pD F ζ hζ x =
      KPGlobalProductPolarizationCharacter.pD F ζ hζ y) :
    x * y⁻¹ ∈ KPGlobalTorusFunctionData.Z F ζ hζ := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply ((commute_iff_beta F ζ hζ (x * y⁻¹) g).mpr ?_).symm.eq
  rw [map_mul, map_inv, h, mul_inv_cancel]
  exact (KPGlobalCubicIdelePairing.beta3_radical_zero F ζ hζ 1).mpr rfl _

private theorem commutator_root (x y : KPGlobalTorusFunctionData.E F ζ hζ) :
    x * y * x⁻¹ * y⁻¹ =
      (KPGlobalCenterRationalCharacter.centralRoot F ζ hζ
        (KPGlobalCubicIdelePairing.beta3 F ζ hζ
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ x)
          (KPGlobalProductPolarizationCharacter.pD F ζ hζ y) ^ 4)).val := by
  apply Subtype.ext
  have h := congrArg (fun t : KPGlobalCubicIdelePairing.E F ζ hζ => t.val.1)
    (KPGlobalCubicIdelePairing.actual_torus_commutator F ζ hζ
      (torusPullbackBridge F ζ hζ x) (torusPullbackBridge F ζ hζ y))
  rw [KPGlobalCenterRationalCharacter.centralRoot_formula]
  exact h

private theorem swap_formula (C : ModelData F ζ hζ) (f : ProductUnitary F ζ hζ C)
    (r : R F ζ hζ) (b : B F ζ hζ C) (g : E F ζ hζ) :
    (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b)⁻¹ : ℂˣ) : ℂ) *
      f.val.val (r.val * (b.val * g)) =
      (KPGlobalTorusFunctionData.iota F ζ hζ
        (KPGlobalCubicIdelePairing.beta3 F ζ hζ (pD F ζ hζ r.val) (pD F ζ hζ b.val) ^ 4) : ℂ) *
        f.val.val (r.val * g) := by
  let ε := KPGlobalCubicIdelePairing.beta3 F ζ hζ (pD F ζ hζ r.val) (pD F ζ hζ b.val) ^ 4
  let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
  let bz : B F ζ hζ C := ⟨z.val,
    KPGlobalProductPolarizationCharacter.center_le_B F ζ hζ C z.property⟩
  have he : r.val * b.val = z.val * (b.val * r.val) := by
    rw [← commutator_root F ζ hζ r.val b.val]
    group
  have hz : KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment bz =
      KPGlobalTorusFunctionData.iota F ζ hζ ε := by
    change KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ C C.adjustment bz /
      KPGlobalCenterRationalCharacter.positiveComplex (KPGlobalCenterRationalCharacter.nu F ζ hζ z.val) = _
    rw [KPGlobalProductPolarizationCharacter.lambdaB_extends_center F ζ hζ C C.adjustment bz z rfl,
      KPGlobalCenterRationalCharacter.nu_centralRoot, map_one, div_one,
      KPGlobalCenterRationalCharacter.omegaA_genuine]
  rw [← mul_assoc r.val, he, mul_assoc z.val, mul_assoc b.val,
    f.val.property bz, f.val.property b]
  change _ * ((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment bz : ℂ) *
    ((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b : ℂ) * _)) = _
  rw [hz]
  simp only [Units.val_inv_eq_inv_val]
  have hn : (KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b : ℂ) ≠ 0 := Units.ne_zero _
  field_simp
  exact mul_comm _ _

private theorem phase_integrable (C : ModelData F ζ hζ) (a : A F) :
    Integrable (fun x => (KPGlobalTorusFunctionData.iota F ζ hζ
      (compactCharacter F ζ hζ C a x ^ 4) : ℂ)) (probabilityHaar F ζ hζ C) := by
  have hc : Continuous (fun x => (KPGlobalTorusFunctionData.iota F ζ hζ
      (compactCharacter F ζ hζ C a x ^ 4) : ℂ)) := by
    letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
    letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
    exact (continuous_of_discreteTopology (f := fun z : rootsOfUnity 3 F =>
      (KPGlobalTorusFunctionData.iota F ζ hζ (z ^ 4) : ℂ))).comp
        (compactCharacter_continuous F ζ hζ C a)
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hc.continuousOn.integrableOn_compact (μ := probabilityHaar F ζ hζ C) isCompact_univ

private theorem unitary_QP_direct (C : ModelData F ζ hζ) (f : ProductUnitary F ζ hζ C) :
    unitaryAveraging F ζ hζ C (unitaryPeriodization F ζ hζ C f) = f := by
  obtain ⟨s, hs⟩ := rational_representatives_exist F ζ hζ C
  let t := Classical.choice (averaging_representatives_exist F ζ hζ C)
  apply Subtype.ext
  apply Subtype.ext
  funext g
  let c (a : PeriodizationIndex F ζ hζ C) : ℂ :=
    (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
      f.val.val ((s.lift a).val * g)
  let v (a : PeriodizationIndex F ζ hζ C) (x : CompactIndex F ζ hζ C) : ℂ :=
    (KPGlobalTorusFunctionData.iota F ζ hζ
      (compactCharacter F ζ hζ C (rationalClass F ζ hζ (s.lift a)) x ^ 4) : ℂ)
  have hc : (Function.support c).Finite := by
    obtain ⟨U, hU, S, hS⟩ := periodization_locally_finite F ζ hζ C s
      ((untwistProduct F ζ hζ C).symm f) g
    apply S.finite_toSet.subset
    intro a ha
    by_contra hn
    have hz := hS g (mem_of_mem_nhds hU) a hn
    rw [periodizationTerm, retwistProduct_formula] at hz
    apply ha
    dsimp [c]
    have hnLam : (((KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    have hnNu : ((KPGlobalCenterRationalCharacter.nu F ζ hζ ((s.lift a).val * g) : ℝ≥0) : ℂ) ≠ 0 := by
      exact_mod_cast Units.ne_zero (KPGlobalCenterRationalCharacter.nu F ζ hζ ((s.lift a).val * g))
    have hz' := (mul_eq_zero.mp hz).resolve_left hnLam
    rw [(mul_eq_zero.mp hz').resolve_left hnNu, mul_zero]
  let S := hc.toFinset ∪ {1}
  have hout (a) (ha : a ∉ S) : c a = 0 := by
    apply Function.notMem_support.mp
    intro h
    exact ha (Finset.mem_union_left _ (hc.mem_toFinset.mpr h))
  have hterm (x) (a) :
      (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment (t.lift x))⁻¹ : ℂˣ) : ℂ) *
        ((((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
          f.val.val ((s.lift a).val * ((t.lift x).val * g))) = c a * v a x := by
    dsimp [c, v]
    have he := swap_formula F ζ hζ C f (s.lift a) (t.lift x) g
    conv_rhs => rw [← t.projects x, compactCharacter_formula]
    change _ = _
    dsimp only [rationalClass]
    linear_combination (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) * he
  rw [unitaryAveraging_formula F ζ hζ C t]
  have hsum (x) :
      (((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment (t.lift x))⁻¹ : ℂˣ) : ℂ) *
        (unitaryPeriodization F ζ hζ C f).val.val ((t.lift x).val * g) =
      ∑ a ∈ S, c a * v a x := by
    rw [unitaryPeriodization_formula F ζ hζ C s, ← tsum_mul_left]
    simp_rw [hterm x]
    exact tsum_eq_sum (fun a ha => by rw [hout a ha, zero_mul])
  simp_rw [hsum]
  rw [integral_finset_sum S (fun a ha => (phase_integrable F ζ hζ C _).const_mul (c a))]
  simp_rw [integral_const_mul]
  have hi (a) (ha : a ≠ (1 : PeriodizationIndex F ζ hζ C)) :
      (∫ x, v a x ∂probabilityHaar F ζ hζ C) = 0 := by
    apply compactCharacter_integral F ζ hζ C
    intro hm
    apply ha
    rw [← s.projects a]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨(rationalClass F ζ hζ (s.lift a)).property, hm⟩
  rw [Finset.sum_eq_single 1 (fun a ha hne => by rw [hi a hne, mul_zero]) (by simp [S])]
  have h1 : (s.lift 1).val ∈ B F ζ hζ C := by
    have he := s.projects 1
    have hj := (QuotientGroup.eq_one_iff _).mp he
    exact hj.2
  let b : B F ζ hζ C := ⟨(s.lift 1).val, h1⟩
  have hv1 (x) : v 1 x = 1 := by
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
    change (KPGlobalTorusFunctionData.iota F ζ hζ
      (KPGlobalCubicIdelePairing.beta3 F ζ hζ (pD F ζ hζ (s.lift 1).val) m.val ^ 4) : ℂ) = 1
    rw [(KPGlobalProductPolarizationCharacter.M_maximal_isotropic F ζ hζ C).1
      _ h1 _ m.property, one_pow, map_one, Units.val_one]
  change c 1 * (∫ x, v 1 x ∂probabilityHaar F ζ hζ C) = _
  simp_rw [hv1]
  rw [integral_const]
  rw [Measure.real, probabilityHaar_mass, ENNReal.toReal_one, one_smul, mul_one]
  dsimp [c]
  rw [f.val.property b]
  have he := KPGlobalTorusFiniteStages.characters_agree F ζ hζ C C.adjustment C.agrees (s.lift 1) b rfl
  change _ * ((KPGlobalTorusFiniteStages.productUnitCharacter F ζ hζ C C.adjustment b : ℂ) * _) = _
  rw [← he]
  simp

private def finiteComparison {H V : Type*} [Group H] [CommGroup V] [Fintype V]
    (D : FinitePolarization.HeisenbergData H V) (T : FinitePolarization.PolarizationData D) :
    FinitePolarization.inducedSpace (T.N.comap D.π) T.χN ≃ₗ[ℂ]
      FinitePolarization.inducedSpace (T.L.comap D.π) T.χL := by
  let r := Classical.choice (FinitePolarization.liftSection_nonempty D.π D.quotient_surjective T.L T.intersection)
  let s := Classical.choice (FinitePolarization.liftSection_nonempty D.π D.quotient_surjective T.N T.intersection)
  exact {
    toFun := FinitePolarization.P D T r
    invFun := FinitePolarization.Q D T s
    left_inv := FinitePolarization.Q_P D T r s
    right_inv := FinitePolarization.P_Q D T r s
    map_add' := by
      intro f g
      apply Subtype.ext
      funext x
      simp [FinitePolarization.P, FinitePolarization.countingAverage, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro c f
      apply Subtype.ext
      funext x
      simp [FinitePolarization.P, FinitePolarization.countingAverage, Finset.mul_sum, mul_left_comm]
  }

private theorem stage_finrank_eq (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C) :
    Module.finrank ℂ (KPGlobalTorusFiniteStages.Stage F ζ hζ C L (KPGlobalTorusFiniteStages.productModel F ζ hζ C)) =
    Module.finrank ℂ (KPGlobalTorusFiniteStages.Stage F ζ hζ C L (KPGlobalTorusFiniteStages.rationalModel F ζ hζ)) := by
  letI : Fintype (KPGlobalTorusFiniteStages.symplecticQuotient F ζ hζ C L) :=
    @Fintype.ofFinite _ (KPGlobalTorusFiniteStages.quotient_finite F ζ hζ C L)
  obtain ⟨T, hC, hπ, hω, hp⟩ := TorusFiniteHeisenberg.actual_finite_heisenberg F ζ hζ C L
  obtain ⟨P, hL, hN, eR, eB, heR, heB⟩ :=
    TorusFinitePolarizations.actual_polarizations_descent F ζ hζ C L T hC hπ hω hp
  let rR := LinearEquiv.ofBijective (KPGlobalTorusFiniteStages.restriction F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ))
    (KPGlobalTorusFiniteStages.restriction_bijective F ζ hζ C L _ (Or.inl rfl))
  let rB := LinearEquiv.ofBijective (KPGlobalTorusFiniteStages.restriction F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C))
    (KPGlobalTorusFiniteStages.restriction_bijective F ζ hζ C L _ (Or.inr rfl))
  exact ((rB.trans eB).trans ((finiteComparison T P).trans (rR.trans eR).symm)).finrank_eq

private theorem unitaryPeriodization_stage (C : ModelData F ζ hζ)
    (L : KPGlobalTorusFiniteStages.Level F ζ hζ C)
    (s : PeriodizationRepresentatives F ζ hζ C) (f : ProductUnitary F ζ hζ C)
    (hf : f.val ∈ KPGlobalTorusFiniteStages.Stage F ζ hζ C L
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C)) :
    (unitaryPeriodization F ζ hζ C f).val ∈ KPGlobalTorusFiniteStages.Stage F ζ hζ C L
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) := by
  constructor
  · intro g hg
    rw [unitaryPeriodization_formula F ζ hζ C s]
    suffices hh : ∀ a, (((KPGlobalTorusFiniteStages.rationalUnitCharacter F ζ hζ (s.lift a))⁻¹ : ℂˣ) : ℂ) *
        f.val.val ((s.lift a).val * g) = 0 by simp only [hh, tsum_zero]
    intro a
    have hn : (s.lift a).val * g ∉ KPGlobalTorusFiniteStages.saturatedDomain F ζ hζ C L
        (KPGlobalTorusFiniteStages.productModel F ζ hζ C) := by
      rintro ⟨b, x, he⟩
      have hb : b.val ∈ KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L :=
        KPGlobalTorusFiniteStages.product_inside_annihilator F ζ hζ C L b.property
      apply hg
      refine ⟨(s.lift a)⁻¹, ⟨b.val * x.val,
        (KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L).mul_mem hb x.property⟩, ?_⟩
      have hh := congrArg (fun t : E F ζ hζ => (s.lift a).val⁻¹ * t) he
      change g = (s.lift a).val⁻¹ * (b.val * x.val)
      simpa only [inv_mul_cancel_left] using hh
    rw [hf.1 _ hn, mul_zero]
  · intro k x
    rw [unitaryPeriodization_formula F ζ hζ C s, unitaryPeriodization_formula F ζ hζ C s, ← tsum_mul_left]
    apply tsum_congr
    intro a
    have hall := KPGlobalTorusTensorFibers.scalar_phase_global_covariance
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).H
      (KPGlobalTorusFiniteStages.stageDomain F ζ hζ C L)
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C).character.toMonoidHom
      f.val hf.1 k.val (KPGlobalTorusFiniteStages.phase_inside_domain F ζ hζ C L k.property)
      (KPGlobalTorusFiniteStages.phaseCharacter F ζ hζ C L k : ℂ)
      (fun y => hf.2 k y) ((s.lift a).val * x.val)
    rw [← mul_assoc, hall]
    ring

private theorem unitaryPeriodization_surjective (C : ModelData F ζ hζ) :
    Function.Surjective (unitaryPeriodization F ζ hζ C) := by
  intro h
  obtain ⟨L, hh⟩ := KPGlobalTorusFiniteStages.smooth_vector_in_stage F ζ hζ C
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl) h
  let SB := KPGlobalTorusFiniteStages.Stage F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C)
  let SR := KPGlobalTorusFiniteStages.Stage F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ)
  letI := KPGlobalTorusFiniteStages.stage_module_finite F ζ hζ C L
    (KPGlobalTorusFiniteStages.productModel F ζ hζ C) (Or.inr rfl)
  letI := KPGlobalTorusFiniteStages.stage_module_finite F ζ hζ C L
    (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) (Or.inl rfl)
  have hB : SB ≤ ProductUnitary F ζ hζ C := by
    obtain ⟨U, hU⟩ := KPGlobalTorusFiniteStages.stage_in_smooth_level F ζ hζ C L
      (KPGlobalTorusFiniteStages.productModel F ζ hζ C) (Or.inr rfl)
    intro f hf
    exact Submodule.mem_iSup_of_mem U (hU hf)
  let iB : SB →ₗ[ℂ] ProductUnitary F ζ hζ C := Submodule.inclusion hB
  let p0 : SB →ₗ[ℂ] KPGlobalTorusFunctionData.TorusFunctions F ζ hζ
      (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) :=
    (RationalUnitary F ζ hζ).subtype.comp ((unitaryPeriodization F ζ hζ C).toLinearMap.comp iB)
  let s := (rational_representatives_exist F ζ hζ C).choose
  let p : SB →ₗ[ℂ] SR := p0.codRestrict SR (fun f =>
    unitaryPeriodization_stage F ζ hζ C L s (iB f) f.property)
  have hinj : Function.Injective p := by
    intro f g he
    have hv : (p f).val = (p g).val := congrArg Subtype.val he
    have he' : unitaryPeriodization F ζ hζ C (iB f) =
        unitaryPeriodization F ζ hζ C (iB g) := Subtype.ext hv
    have hi : iB f = iB g :=
      (Function.LeftInverse.injective (unitary_QP_direct F ζ hζ C)) he'
    exact Submodule.inclusion_injective hB hi
  have hdim : Module.finrank ℂ SB = Module.finrank ℂ SR := stage_finrank_eq F ζ hζ C L
  have hsur : Function.Surjective p := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (K := ℂ) (V := SB) (V₂ := SR) hdim (f := p)).mp hinj
  obtain ⟨f, hf⟩ := hsur ⟨h.val, hh⟩
  have hv : (p f).val = h.val := congrArg Subtype.val hf
  exact ⟨iB f, Subtype.ext hv⟩

private theorem unitary_PQ (C : ModelData F ζ hζ) (h : RationalUnitary F ζ hζ) :
    unitaryPeriodization F ζ hζ C (unitaryAveraging F ζ hζ C h) = h := by
  obtain ⟨f, rfl⟩ := unitaryPeriodization_surjective F ζ hζ C h
  rw [unitary_QP_direct]

 theorem periodization_averaging (C : ModelData F ζ hζ) (h : RationalSmooth F ζ hζ) :
    periodization F ζ hζ C (averaging F ζ hζ C h) = h := by
  apply (untwistRational F ζ hζ).injective
  rw [periodization_transport, averaging_transport]
  exact unitary_PQ F ζ hζ C (untwistRational F ζ hζ h)

 theorem unitaryPeriodization_unitaryAveraging (C : ModelData F ζ hζ) (h : RationalUnitary F ζ hζ) :
    unitaryPeriodization F ζ hζ C (unitaryAveraging F ζ hζ C h) = h := by
  simp only [unitaryPeriodization, unitaryAveraging, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [periodization_averaging]
  exact (untwistRational F ζ hζ).apply_symm_apply h

 theorem averaging_periodization (C : ModelData F ζ hζ) (f : ProductSmooth F ζ hζ C) :
    averaging F ζ hζ C (periodization F ζ hζ C f) = f := by
  apply (untwistProduct F ζ hζ C).injective
  have hp := periodization_transport F ζ hζ C f
  have hq := averaging_transport F ζ hζ C (periodization F ζ hζ C f)
  rw [hq, hp]
  exact unitary_QP_direct F ζ hζ C (untwistProduct F ζ hζ C f)

 theorem unitaryAveraging_unitaryPeriodization (C : ModelData F ζ hζ) (f : ProductUnitary F ζ hζ C) :
    unitaryAveraging F ζ hζ C (unitaryPeriodization F ζ hζ C f) = f := by
  simp only [unitaryPeriodization, unitaryAveraging, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  rw [averaging_periodization]
  exact (untwistProduct F ζ hζ C).apply_symm_apply f

 theorem unitaryAveraging_intertwines (C : ModelData F ζ hζ)
    (a : E F ζ hζ) (h : RationalUnitary F ζ hζ) :
    unitaryAveraging F ζ hζ C
        (rightAction F ζ hζ (KPGlobalTorusFiniteStages.rationalModel F ζ hζ) a h) =
      rightAction F ζ hζ (KPGlobalTorusFiniteStages.productModel F ζ hζ C) a
        (unitaryAveraging F ζ hζ C h) := by
  obtain ⟨s⟩ := averaging_representatives_exist F ζ hζ C
  apply Subtype.ext
  apply Subtype.ext
  funext g
  rw [unitaryAveraging_formula F ζ hζ C s, rightAction_formula,
    unitaryAveraging_formula F ζ hζ C s]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [rightAction_formula, mul_assoc]

 theorem periodization_rational_formula (C : ModelData F ζ hζ)
    (s : PeriodizationRepresentatives F ζ hζ C)
    (hs : ∀ a, ∃ y : Fˣ, s.lift a = rationalLift F ζ hζ y)
    (f : ProductSmooth F ζ hζ C) (g : E F ζ hζ) :
    (periodization F ζ hζ C f).val.val g = ∑' a, f.val.val ((s.lift a).val * g) := by
  rw [periodization_formula F ζ hζ C s]
  apply tsum_congr
  intro a
  obtain ⟨y, hy⟩ := hs a
  simp [periodizationTerm, hy, (rational_representative_character F ζ hζ y).1]

end
end DedekindZetaZeroFree.KPGlobalTorusPeriodizationInverse

end
