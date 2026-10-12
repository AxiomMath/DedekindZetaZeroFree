module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Tame.TransposeKernelTestCoefficients

@[expose] public section

section
noncomputable section
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.KPTameConductorOneBruhat.StandardIntegral
open scoped NumberField Classical Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

theorem conductor_matrix_constraints {K : Type*} [Field K]
    (b a p₁ p₂ : Kˣ) (k : GL (Fin 2) K) (z v x : K)
    (hk11 : k 1 1 ≠ 0)
    (h : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w K * KubotaRankTwo.n K v * KubotaRankTwo.d K a 1 *
        KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.n K x) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d K b 1 * KubotaRankTwo.n K z *
          KubotaRankTwo.d K p₁ p₂ * k * KPStandardLocalRootLifts.weylSwap K)) :
    ∃ c : Kˣ, v ≠ 0 ∧
      v * (c : K) = (p₂ : K) * k 1 1 ∧
      (v * x + (a : K)) * (c : K) = (p₂ : K) * k 1 0 ∧
      a * c ^ 2 = b * p₁ * p₂ * Matrix.GeneralLinearGroup.det k := by
  obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h10 := congrArg (fun g : GL (Fin 2) K => g 1 0) hc
  have h11 := congrArg (fun g : GL (Fin 2) K => g 1 1) hc
  simp [Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.w,
    KubotaRankTwo.n, KubotaRankTwo.d, KPStandardLocalRootLifts.weylSwap,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
    Matrix.vecMul, dotProduct] at h10 h11
  have hv : v ≠ 0 := by
    intro hv
    rw [hv, zero_mul] at h10
    exact mul_ne_zero p₂.ne_zero hk11 h10.symm
  refine ⟨c, hv, h10, h11, ?_⟩
  have hd := congrArg Matrix.GeneralLinearGroup.det hc
  have detd (r s : Kˣ) : Matrix.GeneralLinearGroup.det (KubotaRankTwo.d K r s) = r * s := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detn (t : K) : Matrix.GeneralLinearGroup.det (KubotaRankTwo.n K t) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  have detw : Matrix.GeneralLinearGroup.det (KubotaRankTwo.w K) = 1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, KubotaRankTwo.w]
  have dets : Matrix.GeneralLinearGroup.det (KPStandardLocalRootLifts.weylSwap K) = -1 := by
    apply Units.ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, KPStandardLocalRootLifts.weylSwap]
  simp only [map_mul, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
    detw, detn, detd, dets, one_mul, mul_one] at hd
  have he : -(a * c ^ 2) = -(b * p₁ * p₂ * Matrix.GeneralLinearGroup.det k) := by
    simpa [mul_assoc] using hd
  exact neg_injective he

private theorem conductor_matrix_valuation_label {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (b a p₁ p₂ : Kˣ) (k : GL (Fin 2) K) (z v x : K)
    (hk11 : valuation K (k 1 1) = 1) (hk10 : valuation K (k 1 0) ≤ 1)
    (hdet : valuation K (Matrix.GeneralLinearGroup.det k : K) = 1)
    (hx : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K x) =
      WithZero.exp (1 : ℤ))
    (hb : (KPCubicExpansion.valuationExponent K b : ZMod 3) = 0)
    (h : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w K * KubotaRankTwo.n K v * KubotaRankTwo.d K a 1 *
        KPStandardLocalRootLifts.weylSwap K * KubotaRankTwo.n K x) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d K b 1 * KubotaRankTwo.n K z *
          KubotaRankTwo.d K p₁ p₂ * k * KPStandardLocalRootLifts.weylSwap K)) :
    ((KPCubicExpansion.valuationExponent K p₁ - KPCubicExpansion.valuationExponent K p₂ +
      KPCubicExpansion.valuationExponent K a + 2 : ℤ) : ZMod 3) = 0 := by
  have hk0 : k 1 1 ≠ 0 := by
    intro hh
    simp [hh] at hk11
  obtain ⟨c, hv, h10, h11, hd⟩ := conductor_matrix_constraints b a p₁ p₂ k z v x hk0 h
  let V : Kˣ := Units.mk0 v hv
  let R : K := k 1 0 / k 1 1
  have hr : valuation K R ≤ 1 := by
    simpa [R, map_div₀, hk11] using hk10
  have hxlt : 1 < valuation K x := by
    apply (map_lt_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)).mp
    rw [map_one, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have he : (a : K) / v = R - x := by
    apply (div_eq_iff hv).mpr
    apply mul_right_cancel₀ c.ne_zero
    calc
      (a : K) * (c : K) = (p₂ : K) * k 1 0 - v * x * (c : K) := by linear_combination h11
      _ = (R - x) * v * (c : K) := by
        rw [sub_mul, sub_mul, mul_assoc R v (c : K), h10]
        dsimp [R]
        field_simp
  have hev : valuation K (a / V : Kˣ) = valuation K x := by
    rw [Units.val_div_eq_div_val]
    change valuation K ((a : K) / v) = _
    rw [he, (valuation K).map_sub_eq_of_lt_right (hr.trans_lt hxlt)]
  have hVa : KPCubicExpansion.valuationExponent K (a / V) = -1 := by
    simp only [KPCubicExpansion.valuationExponent, hev, hx, WithZero.log_exp]
  have hVi : KPCubicExpansion.valuationExponent K V = KPCubicExpansion.valuationExponent K a + 1 := by
    have hh := hVa
    rw [div_eq_mul_inv, KPCubicExpansion.valuationExponent_mul,
      ← zpow_neg_one, KPCubicExpansion.valuationExponent_zpow] at hh
    omega
  have hVc : KPCubicExpansion.valuationExponent K V + KPCubicExpansion.valuationExponent K c =
      KPCubicExpansion.valuationExponent K p₂ := by
    let U : Kˣ := Units.mk0 (k 1 1) hk0
    have hU : KPCubicExpansion.valuationExponent K U = 0 := by
      simp [KPCubicExpansion.valuationExponent, U, hk11]
    have hh : V * c = p₂ * U := Units.ext h10
    have hh' := congrArg (KPCubicExpansion.valuationExponent K) hh
    simpa only [KPCubicExpansion.valuationExponent_mul, hU, add_zero] using hh'
  have hD : KPCubicExpansion.valuationExponent K (Matrix.GeneralLinearGroup.det k) = 0 := by
    unfold KPCubicExpansion.valuationExponent
    rw [hdet, map_one, WithZero.log_one, neg_zero]
  have hd' := congrArg (KPCubicExpansion.valuationExponent K) hd
  simp only [KPCubicExpansion.valuationExponent_mul, ← zpow_natCast c 2,
    KPCubicExpansion.valuationExponent_zpow, hD, add_zero] at hd'
  have hi : KPCubicExpansion.valuationExponent K p₁ - KPCubicExpansion.valuationExponent K p₂ +
      KPCubicExpansion.valuationExponent K a + 2 = -KPCubicExpansion.valuationExponent K b := by
    omega
  rw [hi, Int.cast_neg, hb]
  exact neg_zero
local instance (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) :
    ValuativeRel (KPLocalCube.LocalField F q) := ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (KPLocalCube.LocalField F q) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q

theorem conductor_congruence_matrix_label
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π b : (KPLocalCube.LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (KPLocalCube.LocalField F q)
      (valuation (KPLocalCube.LocalField F q) (π : KPLocalCube.LocalField F q)) =
        WithZero.exp (-1 : ℤ))
    (m : ℕ) (hm : 0 < m) (k : KPLocalCube.Gamma F q m)
    (i : ℕ) (r s : ℤ) (z v x : KPLocalCube.LocalField F q)
    (hx : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (KPLocalCube.LocalField F q)
      (valuation (KPLocalCube.LocalField F q) x) = WithZero.exp (1 : ℤ))
    (hb : (KPCubicExpansion.valuationExponent (KPLocalCube.LocalField F q) b : ZMod 3) = 0)
    (h : Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.w (KPLocalCube.LocalField F q) * KubotaRankTwo.n (KPLocalCube.LocalField F q) v *
        KubotaRankTwo.d (KPLocalCube.LocalField F q) (π ^ i) 1 *
          KPStandardLocalRootLifts.weylSwap (KPLocalCube.LocalField F q) *
            KubotaRankTwo.n (KPLocalCube.LocalField F q) x) =
      Matrix.ProjGenLinGroup.mk
        (KubotaRankTwo.d (KPLocalCube.LocalField F q) b 1 *
          KubotaRankTwo.n (KPLocalCube.LocalField F q) z *
          KubotaRankTwo.d (KPLocalCube.LocalField F q) (π ^ r) (π ^ s) * k.val *
            KPStandardLocalRootLifts.weylSwap (KPLocalCube.LocalField F q))) :
    ((r - s + i + 2 : ℤ) : ZMod 3) = 0 := by
  have hdet : valuation (KPLocalCube.LocalField F q)
      (Matrix.GeneralLinearGroup.det k.val : KPLocalCube.LocalField F q) = 1 := by
    obtain ⟨k₀, hk₀, he₀⟩ := k.property
    have hd := (Valuation.integer.integers (valuation (KPLocalCube.LocalField F q))).valuation_unit
      (Matrix.GeneralLinearGroup.det k₀)
    rw [← he₀]
    change valuation (KPLocalCube.LocalField F q)
      ((Matrix.GeneralLinearGroup.det ((Matrix.GeneralLinearGroup.map
        (KPLocalCube.LocalIntegers F q).subtype) k₀) : (KPLocalCube.LocalField F q)ˣ) :
          KPLocalCube.LocalField F q) = 1
    rw [Matrix.GeneralLinearGroup.map_det]
    exact hd
  have hk11 : valuation (KPLocalCube.LocalField F q) (k.val 1 1) = 1 := by
    obtain ⟨k₀, hk₀, he₀⟩ := k.property
    have hent := (KPLocalCube.mem_integerCongruence_iff F q m k₀).mp hk₀
    have hdiag : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by simpa using hent 1 1
    have hu : IsUnit (k₀ 1 1) := by
      apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
      have hmem := Ideal.pow_le_self (Nat.ne_of_gt hm) hdiag
      change 1 - k₀ 1 1 ∈ KPLocalCube.maximalIdeal F q
      simpa only [neg_sub] using (KPLocalCube.maximalIdeal F q).neg_mem hmem
    have hv := (Valuation.integer.integers (valuation (KPLocalCube.LocalField F q))).isUnit_iff_valuation_eq_one.mp hu
    rw [← he₀]
    exact hv
  have hk10 : valuation (KPLocalCube.LocalField F q) (k.val 1 0) ≤ 1 := by
    obtain ⟨k₀, hk₀, he₀⟩ := k.property
    rw [← he₀]
    exact (k₀ 1 0).property
  have hl := conductor_matrix_valuation_label b (π ^ i) (π ^ r) (π ^ s) k.val
    z v x hk11 hk10 hdet hx hb h
  have hp : KPCubicExpansion.valuationExponent (KPLocalCube.LocalField F q) π = 1 := by
    simp [KPCubicExpansion.valuationExponent, hπ, WithZero.log_exp]
  simpa only [KPCubicExpansion.valuationExponent_zpow, ← zpow_natCast π i, hp, mul_one] using hl

open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetBruhatTests.Raw

 def conductorModVal (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative (ZMod 3) where
  toFun y := Multiplicative.ofAdd (KPCubicExpansion.valuationExponent K y : ZMod 3)
  map_one' := by simp [KPCubicExpansion.valuationExponent]
  map_mul' y z := by
    change (KPCubicExpansion.valuationExponent K (y*z) : ZMod 3) =
      (KPCubicExpansion.valuationExponent K y : ZMod 3) + (KPCubicExpansion.valuationExponent K z : ZMod 3)
    rw [KPCubicExpansion.valuationExponent_mul, Int.cast_add]

private theorem conductor_borel_label
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P) (b : BL F ζ hζ q S P) :
    (KPCubicExpansion.valuationExponent (LocalField F q)
      (S.borel.coordinate (retractL F ζ hζ q S P b)) : ZMod 3) = 0 := by
  let K := LocalField F q
  have hc : CubicCharacters.cubes Kˣ ≤ (conductorModVal K).ker := by
    rintro y ⟨z, rfl⟩
    change (KPCubicExpansion.valuationExponent K (z ^ 3) : ZMod 3) = 0
    rw [← zpow_natCast z 3, KPCubicExpansion.valuationExponent_zpow, Int.cast_mul]
    change (3 : ZMod 3) * _ = 0
    rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  let φ := QuotientGroup.lift (CubicCharacters.cubes Kˣ) (conductorModVal K) hc
  have hL : KPTameValuationCoordinates.unitCubeClasses K ≤ φ.ker := by
    apply Subgroup.map_le_iff_le_comap.mpr
    apply sup_le
    · rintro y ⟨u, rfl⟩
      change (KPCubicExpansion.valuationExponent K (KPRamifiedBeta.unitsInclusion K u) : ZMod 3) = 0
      rw [show KPRamifiedBeta.unitsInclusion K u = Units.map (valuation K).integer.subtype.toMonoidHom u from rfl,
        KPCubicExpansion.valuationExponent_unit]
      rfl
    · intro y hy
      change φ (QuotientGroup.mk' (CubicCharacters.cubes Kˣ) y) = 1
      exact hc hy
  have hmem : QuotientGroup.mk' (CubicCharacters.cubes Kˣ)
      (S.borel.coordinate (retractL F ζ hζ q S P b)) ∈ KPTameValuationCoordinates.unitCubeClasses K := by
    change QuotientGroup.mk (S.borel.coordinate (retractL F ζ hζ q S P b)) ∈ _
    rw [← S.cube_class, ← hP]
    exact ⟨S.heisenberg.π (retractL F ζ hζ q S P b),
      (retractL F ζ hζ q S P b).property, rfl⟩
  exact hL hmem

private theorem conductor_one_valuation
    (F : Type) [Field F] [NumberField F] (q : HeightOneSpectrum (𝓞 F))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (x : LocalField F q)
    (hx : x ∈ expandingBall F q π 1 ∧ x ∉ (valuation (LocalField F q)).integer) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) x) = WithZero.exp (1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  have hxl : 1 < valuation (LocalField F q) x := lt_of_not_ge hx.2
  have hx0 : valuation (LocalField F q) x ≠ 0 := ne_of_gt (zero_lt_one.trans hxl)
  have hn : e (valuation (LocalField F q) x) ≠ 0 := by simpa [e] using hx0
  obtain ⟨o, ho⟩ := hx.1
  have hxu : e (valuation (LocalField F q) x) ≤ WithZero.exp (1 : ℤ) := by
    rw [ho]
    simp only [pow_one, Units.val_inv_eq_inv_val, map_mul, map_inv₀]
    have hep : e (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ) := hπ
    rw [hep]
    rw [← WithZero.exp_neg]
    have ho : e (valuation (LocalField F q) o) ≤ 1 := by
      have hh := e.toOrderIso.monotone (show valuation (LocalField F q) (o : LocalField F q) ≤ 1 from o.property)
      change e (valuation (LocalField F q) o) ≤ e 1 at hh
      simpa only [map_one] using hh
    simpa using mul_le_mul_left ho (WithZero.exp (1 : ℤ))
  have hlogu : WithZero.log (e (valuation (LocalField F q) x)) ≤ 1 :=
    (WithZero.log_le_iff_le_exp hn).mpr hxu
  have hlogl : 0 < WithZero.log (e (valuation (LocalField F q) x)) := by
    apply (WithZero.lt_log_iff_exp_lt hn).mpr
    simpa only [WithZero.exp_zero, map_one] using e.strictMono hxl
  have hl : WithZero.log (e (valuation (LocalField F q) x)) = 1 := by omega
  rw [← WithZero.exp_log hn, hl]

theorem conductor_actual_factorization_label
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (m : ℕ) (hm : 0 < m) (i : Fin 3) (r s : ℤ)
    (b : BL F ζ hζ q S P) (k : KPLocalCube.Gamma F q m) (v x : LocalField F q)
    (hx : x ∈ expandingBall F q π 1 ∧ x ∉ (valuation (LocalField F q)).integer)
    (hg : S.borel.liftedW * KPPGLLocalCover.N F ζ hζ (Sum.inr q) v *
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ i.val) *
        KPPGLLocalCover.W F ζ hζ (Sum.inr q) * KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) =
      b.val * KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) (KubotaRankTwo.d (LocalField F q) (π ^ r) (π ^ s))) *
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val) * KPPGLLocalCover.W F ζ hζ (Sum.inr q)) :
    ((r - s + (i.val : ℤ) + 2 : ℤ) : ZMod 3) = 0 := by
  obtain ⟨t, ht⟩ := S.borel.borel_decomposition (inBorel F ζ hζ q S P b)
  have pb : S.borel.projection b.val = Matrix.ProjGenLinGroup.mk
      (KubotaRankTwo.d (LocalField F q) (S.borel.coordinate (retractL F ζ hζ q S P b)) 1 *
        KubotaRankTwo.n (LocalField F q) t.toAdd) := by
    have he : (inBorel F ζ hζ q S P b).val =
        (S.borel.torus (S.borel.retract (inBorel F ζ hζ q S P b)) : ActualCover F ζ hζ q) *
          (S.borel.upperRoot t : ActualCover F ζ hζ q) := congrArg Subtype.val ht
    change S.borel.projection ((inBorel F ζ hζ q S P b).val) = _
    rw [he, map_mul, S.borel.torus_projection, S.borel.upperRoot_projection, map_mul]
    rfl
  have pw : S.borel.projection (KPPGLLocalCover.W F ζ hζ (Sum.inr q)) =
      Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap (LocalField F q)) :=
    (S.openCell P).projection_eq _
  have pn (z : LocalField F q) : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) z) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) z) := (S.openCell P).projection_eq _
  have pe : S.borel.projection (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (π ^ i.val)) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (LocalField F q) (π ^ i.val) 1) :=
    (S.openCell P).projection_eq _
  have pk (g : GL (Fin 2) (LocalField F q)) : S.borel.projection
      (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) g)) =
      Matrix.ProjGenLinGroup.mk g := (S.openCell P).projection_eq _
  have pkw : S.borel.projection S.borel.liftedW = Matrix.ProjGenLinGroup.mk (KubotaRankTwo.w (LocalField F q)) := by
    rw [(S.openCell P).weyl_eq, KPRankOneOpenCellKernel.signedWeyl,
      (S.openCell P).projection_eq, KPRankOneOpenCellKernel.signedWeyl_matrix]
  have hp := congrArg S.borel.projection hg
  simp only [map_mul, pb, pw, pn, pe, pk, pkw] at hp
  apply conductor_congruence_matrix_label F q π (S.borel.coordinate (retractL F ζ hζ q S P b))
    hπ m hm k i.val r s t.toAdd v x (conductor_one_valuation F q π hπ x hx)
      (conductor_borel_label F ζ hζ q S P hP b)
  simpa only [map_mul, mul_assoc] using hp

end DedekindZetaZeroFree.KPTameConductorOneBruhat.StandardIntegral

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPTameConductorOneBruhat.StandardIntegral

open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneOppositeZero KPRankOneForwardTestVector
open KPTameJacquetTestDuality KPTameValuationCoordinates KPTameTransposeKernelUnfoldingRaw

private theorem deform_coordinate {K : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
    {T : LocalHeisenbergData H D}
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (s : ℂ) (f : sectionSpace A P ε 0) (g : G) :
    (((compactTrivialization A P I ε s)
      ((compactTrivialization A P I ε 0).symm f)).val g).val 1 =
    normPower K (A.coordinate (A.retract (I.borelPart g))) s * (f.val g).val 1 := by
  have hf := congrArg (fun v : sectionSpace A P ε 0 => (v.val g).val 1)
    ((compactTrivialization A P I ε 0).apply_symm_apply f)
  change (inducingAction A P ε s (I.borelPart g)
    (f.val (I.compactPart g))).val 1 = _
  change (inducingAction A P ε 0 (I.borelPart g)
    (f.val (I.compactPart g))).val 1 = (f.val g).val 1 at hf
  rw [← hf]
  simp [inducingAction, inducingScalar, normPower]
  ring

theorem offlabel_standard_zero
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (hP : IsTamePolarization F ζ hζ q S P)
    (coordinates : ∀ ε : Sign,
      sectionSpace S.borel P ε 0 ≃ₗ[ℂ] scalarSections F ζ hζ q S P hP ε)
    (hcoordinates : ∀ ε f g, (coordinates ε f).val g = (f.val g).val 1)
    (μ : Measure (LocalField F q))
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (i : Fin 3) (f' : DiagonalValuations)
    (hl : ((f'.1 - f'.2 + (i.val : ℤ) + 2 : ℤ) : ZMod 3) ≠ 0)
    (m : ℕ) (hm : 0 < m) (f : scalarSections F ζ hζ q S P hP .minus)
    (hf : IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π f') m f)
    (s : ℂ) (x : LocalField F q) (hx : x ∈ conductorOneShell F q π) :
    standardIntegralCoordinate (LocalField F q) S.borel P S.iwasawa μ .minus s
      ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
        ((coordinates .minus).symm f))
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) 1 = 0 := by
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro v
  change (((compactTrivialization S.borel P S.iwasawa .minus (sourceParameter .minus s))
    ((compactTrivialization S.borel P S.iwasawa .minus 0).symm
      ((coordinates .minus).symm f))).val
    (S.borel.liftedW * (S.borel.upperRoot (Multiplicative.ofAdd v) : ActualCover F ζ hζ q) *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1 = 0
  rw [deform_coordinate, ← hcoordinates, LinearEquiv.apply_symm_apply]
  suffices hz : f.val (S.borel.liftedW *
      (S.borel.upperRoot (Multiplicative.ofAdd v) : ActualCover F ζ hζ q) *
      (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
        KPPGLLocalCover.N F ζ hζ (Sum.inr q) x)) = 0 by rw [hz, mul_zero]
  by_contra hn
  have hsup := hf.2.1 (show _ ∈ Function.support f.val from hn)
  obtain ⟨b, k, hk, hg⟩ := hsup
  obtain ⟨k₀, rfl⟩ := hk
  apply hl
  apply conductor_actual_factorization_label F ζ hζ q S P hP π hπ m hm i f'.1 f'.2 b k₀ v x hx
  simpa only [(S.openCell P).upper_eq, KPRankOneOpenCellKernel.nLift,
    eta, diagonalLift] using hg

end DedekindZetaZeroFree.KPTameConductorOneBruhat.StandardIntegral

end

end
