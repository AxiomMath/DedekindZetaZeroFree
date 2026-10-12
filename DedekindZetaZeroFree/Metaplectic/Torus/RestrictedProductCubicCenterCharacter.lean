module

public import DedekindZetaZeroFree.Metaplectic.Torus.CenterCubeIdeles
public import DedekindZetaZeroFree.Metaplectic.Torus.LocalDiagonalRatioCoordinates

@[expose] public section

open scoped NumberField Classical BigOperators NNReal Matrix Topology
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
noncomputable section
set_option autoImplicit false
variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem localAbs_mul (v : KPHilbert.Place F) (u u' : (KPHilbert.Completion F v)ˣ) :
    localAbs F v (u * u') = localAbs F v u * localAbs F v u' := by
  cases v with
  | inl w => simp [localAbs, Units.val_mul, norm_mul, mul_pow]
  | inr q => simp [localAbs, Units.val_mul, norm_mul]

theorem localAbs_inv (v : KPHilbert.Place F) (u : (KPHilbert.Completion F v)ˣ) :
    localAbs F v u⁻¹ = (localAbs F v u)⁻¹ := by
  cases v with
  | inl w => simp [localAbs]
  | inr q => simp [localAbs]

theorem isUnit_diag_entries (v : KPHilbert.Place F)
    (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (h10 : (g.g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 0 = 0)
    (h01 : (g.g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 1 = 0) :
    IsUnit (g.g 0 0) ∧ IsUnit (g.g 1 1) := by
  have hdet : IsUnit ((g.g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 0 0 *
      (g.g : Matrix (Fin 2) (Fin 2) (KPHilbert.Completion F v)) 1 1) := by
    have h := (KubotaRankTwo.det (KPHilbert.Completion F v) g.g).isUnit
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h01] at h
    simpa using h
  exact ⟨isUnit_of_mul_isUnit_left hdet, isUnit_of_mul_isUnit_right hdet⟩

theorem localValue_diag (v : KPHilbert.Place F) (g : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (h10 : g.g 1 0 = 0) (h01 : g.g 0 1 = 0) :
    localValue F ζ hζ v g = KPGlobalTorusFunctionData.iota F ζ hζ g.epsilon *
      positiveComplex (sixthPower (Units.mk0 (localAbs F v
        ((isUnit_diag_entries F ζ hζ v g h10 h01).1.unit *
         ((isUnit_diag_entries F ζ hζ v g h10 h01).2.unit)⁻¹))
        (ne_of_gt (localAbs_pos F v _)))) := by
  rw [localValue, dif_pos (isUnit_diag_entries F ζ hζ v g h10 h01)]

theorem localValue_mul_diagonal (v : KPHilbert.Place F)
    (g h : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg10 : g.g 1 0 = 0) (hg01 : g.g 0 1 = 0)
    (hh10 : h.g 1 0 = 0) (hh01 : h.g 0 1 = 0) :
    localValue F ζ hζ v (g * h) =
      KPGlobalTorusFunctionData.iota F ζ hζ (KPLocalCover.sigmaTwo F ζ hζ v g.g h.g) *
        localValue F ζ hζ v g * localValue F ζ hζ v h := by
  have hdiag := fun (u : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hu10 : u.g 1 0 = 0) (hu01 : u.g 0 1 = 0) =>
    isUnit_diag_entries F ζ hζ v u hu10 hu01
  have hm10 : (g * h).g 1 0 = 0 := by
    simp only [KPLocalCover.mul_g, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hg10, hg01, hh10, hh01, mul_zero, zero_mul, add_zero, zero_add]
  have hm01 : (g * h).g 0 1 = 0 := by
    simp only [KPLocalCover.mul_g, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hg10, hg01, hh10, hh01, mul_zero, zero_mul, add_zero, zero_add]
  have hu00 : (hdiag (g * h) hm10 hm01).1.unit = (hdiag g hg10 hg01).1.unit *
      (hdiag h hh10 hh01).1.unit := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    simp only [KPLocalCover.mul_g, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hg10, hg01, hh10, hh01, mul_zero, zero_mul, add_zero, zero_add]
  have hu11 : (hdiag (g * h) hm10 hm01).2.unit = (hdiag g hg10 hg01).2.unit *
      (hdiag h hh10 hh01).2.unit := by
    apply Units.ext
    simp only [IsUnit.unit_spec, Units.val_mul]
    simp only [KPLocalCover.mul_g, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hg10, hg01, hh10, hh01, mul_zero, zero_mul, add_zero, zero_add]
  have hratio_eq : (hdiag (g * h) hm10 hm01).1.unit *
        ((hdiag (g * h) hm10 hm01).2.unit)⁻¹ =
      ((hdiag g hg10 hg01).1.unit * ((hdiag g hg10 hg01).2.unit)⁻¹) *
        ((hdiag h hh10 hh01).1.unit * ((hdiag h hh10 hh01).2.unit)⁻¹) := by
    rw [hu00, hu11, mul_inv_rev]
    ac_rfl
  have hratio : Units.mk0 (localAbs F v
        ((hdiag (g * h) hm10 hm01).1.unit * ((hdiag (g * h) hm10 hm01).2.unit)⁻¹))
        (ne_of_gt (localAbs_pos F v _)) =
      Units.mk0 (localAbs F v
        ((hdiag g hg10 hg01).1.unit * ((hdiag g hg10 hg01).2.unit)⁻¹))
        (ne_of_gt (localAbs_pos F v _)) *
      Units.mk0 (localAbs F v
        ((hdiag h hh10 hh01).1.unit * ((hdiag h hh10 hh01).2.unit)⁻¹))
        (ne_of_gt (localAbs_pos F v _)) := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    rw [hratio_eq, localAbs_mul]
  rw [localValue_diag F ζ hζ v (g * h) hm10 hm01,
    localValue_diag F ζ hζ v g hg10 hg01, localValue_diag F ζ hζ v h hh10 hh01,
    hratio, KPLocalCover.mul_epsilon]
  simp only [map_mul]
  ac_rfl

theorem rawCenter_local_diagonal (x : rawCenter F ζ hζ) (v : KPHilbert.Place F) :
    (x.val v).g 1 0 = 0 ∧ (x.val v).g 0 1 = 0 := by
  obtain ⟨t, ht, he⟩ := x.property
  have ht' := t.property
  change KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ t.val ∈
    KPGlobalTorusFunctionData.ordinaryTorus F at ht'
  change t.val = KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) at he
  rw [he] at ht'
  change QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
    (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val) ∈
    KPGlobalTorusFunctionData.ordinaryTorus F at ht'
  obtain ⟨B, hB, h10, h01⟩ := ht'
  rw [QuotientGroup.mk'_eq_mk'] at hB
  obtain ⟨z, hz, he⟩ := hB
  obtain ⟨u, rfl⟩ := hz
  have hd : (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val) 1 0 = 0 ∧
      (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val) 0 1 = 0 := by
    rw [← he]
    simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
  have hev := KPAdelicCoverRestrictedProduct.restrictedProjection_eval F ζ hζ x.val v
  have h10v := congrArg (fun A : Matrix (Fin 2) (Fin 2)
      (KPHilbert.Completion F v) => A 1 0) (congrArg Units.val hev)
  have h01v := congrArg (fun A : Matrix (Fin 2) (Fin 2)
      (KPHilbert.Completion F v) => A 0 1) (congrArg Units.val hev)
  change KPAdelicCoverRestrictedProduct.adeleEval F v
    ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val) 1 0) =
    (x.val v).g 1 0 at h10v
  change KPAdelicCoverRestrictedProduct.adeleEval F v
    ((KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ x.val) 0 1) =
    (x.val v).g 0 1 at h01v
  constructor
  · exact h10v.symm.trans (by rw [hd.1, map_zero])
  · exact h01v.symm.trans (by rw [hd.2, map_zero])

private theorem sigmaTwo_diag_cubes (v : KPHilbert.Place F)
    (g h : KPLocalCover.CubicGL2Raw F ζ hζ v)
    (hg10 : g.g 1 0 = 0) (hg01 : g.g 0 1 = 0)
    (hh10 : h.g 1 0 = 0) (hh01 : h.g 0 1 = 0)
    (a b : (KPHilbert.Completion F v)ˣ)
    (ha : a ^ 3 = (isUnit_diag_entries F ζ hζ v g hg10 hg01).1.unit *
      ((isUnit_diag_entries F ζ hζ v g hg10 hg01).2.unit)⁻¹)
    (hb : b ^ 3 = (isUnit_diag_entries F ζ hζ v h hh10 hh01).1.unit *
      ((isUnit_diag_entries F ζ hζ v h hh10 hh01).2.unit)⁻¹) :
    KPLocalCover.sigmaTwo F ζ hζ v g.g h.g = 1 := by
  let K := KPHilbert.Completion F v
  let B := KPHilbert.B3 F ζ hζ v
  let u := (isUnit_diag_entries F ζ hζ v g hg10 hg01).2.unit
  let w := (isUnit_diag_entries F ζ hζ v h hh10 hh01).2.unit
  have hga : (isUnit_diag_entries F ζ hζ v g hg10 hg01).1.unit = a ^ 3 * u := by
    rw [ha]; simp [u]
  have hhb : (isUnit_diag_entries F ζ hζ v h hh10 hh01).1.unit = b ^ 3 * w := by
    rw [hb]; simp [w]
  have hXg : KubotaRankTwo.X K g.g = u := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, hg10, u]
  have hXh : KubotaRankTwo.X K h.g = w := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, hh10, w]
  have hXgh : KubotaRankTwo.X K (g.g * h.g) = u * w := by
    apply Units.ext
    simp [KubotaRankTwo.X, KubotaRankTwo.x, Matrix.mul_apply, Fin.sum_univ_two,
      hg10, hh10, u, w]
  have hdg : KubotaRankTwo.det K g.g = a ^ 3 * u ^ 2 := by
    apply Units.ext
    have hh := congrArg Units.val hga
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_pow_eq_pow_val] at hh
    simp [KubotaRankTwo.det, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two, hg10, hh, u, pow_two, K, mul_assoc]
  have hdh : KubotaRankTwo.det K h.g = b ^ 3 * w ^ 2 := by
    apply Units.ext
    have hh := congrArg Units.val hhb
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_pow_eq_pow_val] at hh
    simp [KubotaRankTwo.det, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_two, hh10, hh, w, pow_two, K, mul_assoc]
  obtain ⟨hL, hR, hsk, _, hc, _⟩ := KPHilbert.B3_laws F ζ hζ v
  change ∀ a b c, B (a * b) c = B a c * B b c at hL
  change ∀ a b c, B a (b * c) = B a b * B a c at hR
  change ∀ a b, B a b = (B b a)⁻¹ at hsk
  change ∀ a b, B (a ^ 3) b = 1 ∧ B a (b ^ 3) = 1 at hc
  have hInv := KubotaDefectSymbolAlgebra.inv_right K (rootsOfUnity 3 F) B hR
  have hquot : u * w / (w * (a ^ 3 * u ^ 2)) = (a ^ 3)⁻¹ * u⁻¹ := by
    apply Units.ext
    simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val]
    field_simp
    <;> ring
  change B (KubotaRankTwo.X K (g.g * h.g) / KubotaRankTwo.X K g.g)
    (KubotaRankTwo.X K (g.g * h.g) /
      (KubotaRankTwo.X K h.g * KubotaRankTwo.det K g.g)) *
    B (KubotaRankTwo.det K g.g) (KubotaRankTwo.det K h.g) ^ 2 = 1
  rw [hXg, hXh, hXgh, hdg, hdh]
  rw [show u * w / u = w from by simp [mul_comm], hquot]
  change B w ((a ^ 3)⁻¹ * u⁻¹) * B (a ^ 3 * u ^ 2) (b ^ 3 * w ^ 2) ^ 2 = 1
  rw [hR, hInv, (hc w a).2, inv_one, one_mul, hInv, hL,
    (hc a (b ^ 3 * w ^ 2)).1, one_mul, hR, (hc (u ^ 2) b).2, one_mul]
  simp only [pow_two, hL, hR]
  rw [hsk w u]
  simp only [inv_inv]
  have h9 : B u w ^ 9 = 1 := by
    apply Subtype.ext
    change (B u w : Fˣ) ^ 9 = 1
    rw [show (9 : ℕ) = 3 * 3 from rfl, pow_mul, (B u w).property, one_pow]
  convert h9 using 1 <;> simp [pow_succ, pow_two, mul_assoc]

theorem rawCenter_cocycle_twist (x y : rawCenter F ζ hζ) :
    (∏ᶠ v, KPGlobalTorusFunctionData.iota F ζ hζ
      (KPLocalCover.sigmaTwo F ζ hζ v (x.val v).g (y.val v).g)) = 1 := by
  have hc (x : rawCenter F ζ hζ) (v : KPHilbert.Place F) :
      ∃ a : (KPHilbert.Completion F v)ˣ,
        a ^ 3 = (isUnit_diag_entries F ζ hζ v (x.val v)
          (rawCenter_local_diagonal F ζ hζ x v).1
          (rawCenter_local_diagonal F ζ hζ x v).2).1.unit *
          ((isUnit_diag_entries F ζ hζ v (x.val v)
            (rawCenter_local_diagonal F ζ hζ x v).1
            (rawCenter_local_diagonal F ζ hζ x v).2).2.unit)⁻¹ := by
    obtain ⟨t, ht, he⟩ := x.property
    change t.val = KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) at he
    rw [CubeDiagonalProduct.covered_torus_center_eq_cubes F ζ hζ] at ht
    obtain ⟨a, ha⟩ := ht
    change a ^ 3 = KPGlobalTorusFunctionData.p F ζ hζ t at ha
    obtain ⟨h, hr⟩ := KPGlobalCenterRationalCharacterModulus.raw_torus_local_ratio
      F ζ hζ x.val t he.symm v
    refine ⟨KPGlobalCubicIdelePairing.ideleEval F v a, ?_⟩
    rw [← map_pow, ha, ← hr]
  calc
    _ = ∏ᶠ v : KPHilbert.Place F, (1 : ℂˣ) := by
      apply finprod_congr
      intro v
      obtain ⟨a, ha⟩ := hc x v
      obtain ⟨b, hb⟩ := hc y v
      rw [sigmaTwo_diag_cubes F ζ hζ v (x.val v) (y.val v)
        (rawCenter_local_diagonal F ζ hζ x v).1
        (rawCenter_local_diagonal F ζ hζ x v).2
        (rawCenter_local_diagonal F ζ hζ y v).1
        (rawCenter_local_diagonal F ζ hζ y v).2 a b ha hb, map_one]
    _ = 1 := finprod_one

private theorem integral_diagonal_value (q : HeightOneSpectrum (𝓞 F))
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (h10 : g.g 1 0 = 0) (h01 : g.g 0 1 = 0)
    (he : g.epsilon = 1) (k : KPTameCompact.K0 F q)
    (hk : g.g = KPTameCompact.inclusion F q k) :
    localValue F ζ hζ (Sum.inr q) g = 1 := by
  obtain ⟨hdet, hentries⟩ := KPTameCompact.det_norm_and_entries F q k
  have hmul : ‖g.g 0 0‖ * ‖g.g 1 1‖ = 1 := by
    have hd : KPTameCompact.Δ F q k = g.g 0 0 * g.g 1 1 := by
      change (Matrix.GeneralLinearGroup.det (KPTameCompact.inclusion F q k) :
        q.adicCompletion F) = _
      rw [← hk, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10]
      simp
    rw [hd, norm_mul] at hdet
    exact hdet
  have hle0 : ‖g.g 0 0‖ ≤ 1 := by rw [hk]; exact hentries 0 0
  have hle1 : ‖g.g 1 1‖ ≤ 1 := by rw [hk]; exact hentries 1 1
  have hn0 : ‖g.g 0 0‖ = 1 := by nlinarith [norm_nonneg (g.g 0 0), norm_nonneg (g.g 1 1)]
  have hn1 : ‖g.g 1 1‖ = 1 := by nlinarith [norm_nonneg (g.g 0 0), norm_nonneg (g.g 1 1)]
  have hr : Units.mk0 (localAbs F (Sum.inr q)
      ((isUnit_diag_entries F ζ hζ (Sum.inr q) g h10 h01).1.unit *
        ((isUnit_diag_entries F ζ hζ (Sum.inr q) g h10 h01).2.unit)⁻¹))
      (ne_of_gt (localAbs_pos F (Sum.inr q) _)) = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    simp [localAbs, norm_mul, norm_inv, hn0, hn1]
  rw [localValue_diag F ζ hζ (Sum.inr q) g h10 h01, he, hr]
  simp

private theorem compact_diagonal_value (q : HeightOneSpectrum (𝓞 F))
    (g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (hg : g ∈ KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q)
    (h10 : g.g 1 0 = 0) (h01 : g.g 0 1 = 0) :
    localValue F ζ hζ (Sum.inr q) g = 1 := by
  unfold KPAdelicCoverRestrictedProduct.finiteCompact at hg
  split_ifs at hg with hbad
  · obtain ⟨k, rfl⟩ := hg
    obtain ⟨i, hi, he⟩ := k.property
    apply integral_diagonal_value F ζ hζ q _ h10 h01 rfl i
    exact he.symm
  · obtain ⟨k, rfl⟩ := hg
    have hz : KPTameCompact.c F q k = 0 := h10
    exact integral_diagonal_value F ζ hζ q _ h10 h01
      (KPTameCompact.kappa_zero F q ζ hζ k hz) k rfl

private theorem raw_value_finiteSupport (x : rawCenter F ζ hζ) :
    Function.HasFiniteMulSupport (fun v => localValue F ζ hζ v (x.val v)) := by
  have hf := Filter.mem_cofinite.mp x.val.property
  apply ((Set.finite_univ : (Set.univ : Set (InfinitePlace F)).Finite).image
    (Sum.inl : InfinitePlace F → KPHilbert.Place F)).union hf |>.subset
  intro v hv
  cases v with
  | inl w => exact Or.inl ⟨w, trivial, rfl⟩
  | inr q =>
    apply Or.inr
    intro hg
    exact hv (compact_diagonal_value F ζ hζ q (x.val (Sum.inr q)) hg
      (rawCenter_local_diagonal F ζ hζ x (Sum.inr q)).1
      (rawCenter_local_diagonal F ζ hζ x (Sum.inr q)).2)

private theorem raw_product_mul (x y : rawCenter F ζ hζ) :
    rawProduct F ζ hζ (x * y) = rawProduct F ζ hζ x * rawProduct F ζ hζ y := by
  let f := fun v => localValue F ζ hζ v (x.val v)
  let g := fun v => localValue F ζ hζ v (y.val v)
  let c := fun v => KPGlobalTorusFunctionData.iota F ζ hζ
    (KPLocalCover.sigmaTwo F ζ hζ v (x.val v).g (y.val v).g)
  have hloc : ∀ v, localValue F ζ hζ v ((x * y).val v) = c v * (f v * g v) := by
    intro v
    have hh := localValue_mul_diagonal F ζ hζ v (x.val v) (y.val v)
      (rawCenter_local_diagonal F ζ hζ x v).1 (rawCenter_local_diagonal F ζ hζ x v).2
      (rawCenter_local_diagonal F ζ hζ y v).1 (rawCenter_local_diagonal F ζ hζ y v).2
    change localValue F ζ hζ v (x.val v * y.val v) = _
    simpa only [mul_assoc] using hh
  have hf : Function.HasFiniteMulSupport f := raw_value_finiteSupport F ζ hζ x
  have hg : Function.HasFiniteMulSupport g := raw_value_finiteSupport F ζ hζ y
  have hc : Function.HasFiniteMulSupport c := by
    have hm := raw_value_finiteSupport F ζ hζ (x * y)
    have hh : c = (fun v => localValue F ζ hζ v ((x * y).val v)) * (f * g)⁻¹ := by
      funext v
      change c v = localValue F ζ hζ v ((x * y).val v) * (f v * g v)⁻¹
      rw [hloc]
      exact (mul_inv_cancel_right (c v) (f v * g v)).symm
    rw [hh]
    exact hm.mul (hf.mul hg).inv
  change (∏ᶠ v, localValue F ζ hζ v ((x * y).val v)) = (∏ᶠ v, f v) * ∏ᶠ v, g v
  simp_rw [hloc]
  change (∏ᶠ v, c v * (f * g) v) = _
  rw [finprod_mul_distrib hc (hf.mul hg)]
  change (∏ᶠ v, c v) * (∏ᶠ v, f v * g v) = _
  rw [finprod_mul_distrib hf hg]
  rw [show (∏ᶠ v, c v) = 1 from rawCenter_cocycle_twist F ζ hζ x y, one_mul]

private theorem complex_raw_value_continuous (w : InfinitePlace F) :
    Continuous (fun x : rawCenter F ζ hζ => localValue F ζ hζ (Sum.inl w) (x.val (Sum.inl w))) := by
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  letI : DiscreteTopology (rootsOfUnity 3 F) := ⟨rfl⟩
  letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : TopologicalSpace w.Completion := inferInstance
  have hev : Continuous (fun x : rawCenter F ζ hζ => x.val (Sum.inl w)) :=
    (RestrictedProduct.continuous_eval (Sum.inl w)).comp continuous_subtype_val
  obtain ⟨e, he, hc, _⟩ := KPLocalChartTopology.complex_product_cover F ζ hζ w
  have hc' := hc.comp hev
  have hmatrix : Continuous (fun x : rawCenter F ζ hζ => (x.val (Sum.inl w)).g) := by
    convert continuous_fst.comp hc' using 1
    funext x
    simp only [Function.comp_apply, he]
  have heps : Continuous (fun x : rawCenter F ζ hζ => (x.val (Sum.inl w)).epsilon) := by
    convert continuous_snd.comp hc' using 1
    funext x
    simp only [Function.comp_apply, he]
  let d := fun x : rawCenter F ζ hζ => isUnit_diag_entries F ζ hζ (Sum.inl w)
    (x.val (Sum.inl w)) (rawCenter_local_diagonal F ζ hζ x (Sum.inl w)).1
      (rawCenter_local_diagonal F ζ hζ x (Sum.inl w)).2
  let r := fun x : rawCenter F ζ hζ => (d x).1.unit * ((d x).2.unit)⁻¹
  have hent (i j : Fin 2) : Continuous (fun x : rawCenter F ζ hζ =>
      (x.val (Sum.inl w)).g i j) :=
    (continuous_apply_apply i j).comp ((show Continuous (fun A :
      Matrix.GeneralLinearGroup (Fin 2) w.Completion =>
      (A : Matrix (Fin 2) (Fin 2) w.Completion)) from Units.continuous_val).comp hmatrix)
  have hrat : Continuous r := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun x => (r x : w.Completion))
      have hh : ∀ x, (r x : w.Completion) =
          (x.val (Sum.inl w)).g 0 0 / (x.val (Sum.inl w)).g 1 1 := by
        intro x
        simp [r, d, div_eq_mul_inv]
      simp_rw [hh]
      exact (hent 0 0).div (hent 1 1) (fun x => (d x).2.ne_zero)
    · change Continuous (fun x => ((r x)⁻¹ : (w.Completion)ˣ).val)
      have hh : ∀ x, ((r x)⁻¹ : (w.Completion)ˣ).val =
          (x.val (Sum.inl w)).g 1 1 / (x.val (Sum.inl w)).g 0 0 := by
        intro x
        simp [r, d, div_eq_mul_inv]
      simp_rw [hh]
      exact (hent 1 1).div (hent 0 0) (fun x => (d x).1.ne_zero)
  let a := fun x : rawCenter F ζ hζ => Units.mk0 (localAbs F (Sum.inl w) (r x))
    (ne_of_gt (localAbs_pos F (Sum.inl w) (r x)))
  have ha : Continuous a := by
    apply Units.continuous_iff.mpr
    constructor
    · change Continuous (fun x => localAbs F (Sum.inl w) (r x))
      exact (Units.continuous_val.comp hrat).nnnorm.pow 2
    · change Continuous (fun x => ((a x)⁻¹ : (ℝ≥0)ˣ).val)
      have hh : ∀ x, ((a x)⁻¹ : (ℝ≥0)ˣ).val = localAbs F (Sum.inl w) ((r x)⁻¹) := by
        intro x
        change (localAbs F (Sum.inl w) (r x))⁻¹ = _
        exact (localAbs_inv F (Sum.inl w) (r x)).symm
      simp_rw [hh]
      exact (Units.continuous_val.comp hrat.inv).nnnorm.pow 2
  have hpos : Continuous positiveComplex := by
    apply Units.continuous_map
    exact Complex.continuous_ofReal.comp NNReal.continuous_coe
  have hsix : Continuous sixthPower := by
    apply Units.continuous_map
    exact NNReal.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 6)
  have hi : Continuous (KPGlobalTorusFunctionData.iota F ζ hζ) := continuous_of_discreteTopology
  convert (hi.comp heps).mul (hpos.comp (hsix.comp ha)) using 1
  funext x
  exact (localValue_diag F ζ hζ (Sum.inl w) (x.val (Sum.inl w))
    (rawCenter_local_diagonal F ζ hζ x (Sum.inl w)).1
    (rawCenter_local_diagonal F ζ hζ x (Sum.inl w)).2)

theorem raw_character_laws :
    (∀ x : rawCenter F ζ hζ,
      Function.HasFiniteMulSupport (fun v => localValue F ζ hζ v (x.val v))) ∧
    (∀ x y : rawCenter F ζ hζ,
      rawProduct F ζ hζ (x * y) = rawProduct F ζ hζ x * rawProduct F ζ hζ y) ∧
    Continuous (rawProduct F ζ hζ) := by
  refine ⟨raw_value_finiteSupport F ζ hζ, raw_product_mul F ζ hζ, ?_⟩
  letI := KPAdelicCoverRestrictedProduct.localTopology F ζ hζ
  letI : ∀ v : KPHilbert.Place F, IsTopologicalGroup
      (KPLocalCover.CubicGL2Raw F ζ hζ v) := fun v => by
    cases v with
    | inl w => exact (KPLocalChartTopology.complex_topological_cover F ζ hζ w).2.2.1
    | inr q => exact (KPLocalChartTopology.finite_topological_group F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2
  letI : Fact (∀ v : KPHilbert.Place F, IsOpen
      (KPAdelicCoverRestrictedProduct.compact F ζ hζ v :
        Set (KPLocalCover.CubicGL2Raw F ζ hζ v))) :=
    ⟨KPAdelicCoverRestrictedProduct.compact_open F ζ hζ⟩
  letI : IsTopologicalGroup (Raw F ζ hζ) :=
    RestrictedProduct.isTopologicalGroup
      (R := fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (B := KPAdelicCoverRestrictedProduct.compact F ζ hζ)
  have h1 : rawProduct F ζ hζ 1 = 1 := by
    unfold rawProduct
    have hh : ∀ v, localValue F ζ hζ v ((1 : rawCenter F ζ hζ).val v) = 1 := by
      intro v
      change localValue F ζ hζ v (1 : KPLocalCover.CubicGL2Raw F ζ hζ v) = 1
      have hdiag : (1 : KPLocalCover.CubicGL2Raw F ζ hζ v).g 1 0 = 0 ∧
          (1 : KPLocalCover.CubicGL2Raw F ζ hζ v).g 0 1 = 0 := by simp
      rw [localValue_diag F ζ hζ v 1 hdiag.1 hdiag.2]
      have hh : (isUnit_diag_entries F ζ hζ v 1 hdiag.1 hdiag.2).1.unit = 1 ∧
          (isUnit_diag_entries F ζ hζ v 1 hdiag.1 hdiag.2).2.unit = 1 := by
        constructor <;> apply Units.ext <;> simp
      rw [hh.1, hh.2]
      cases v <;> simp [localAbs]
    simp_rw [hh]
    exact finprod_one
  let χ : rawCenter F ζ hζ →* ℂˣ :=
    { toFun := rawProduct F ζ hζ
      map_one' := h1
      map_mul' := raw_product_mul F ζ hζ }
  apply continuous_of_continuousAt_one χ
  let S : Finset (KPHilbert.Place F) := Finset.univ.image Sum.inl
  let f := fun x : rawCenter F ζ hζ =>
    ∏ w : InfinitePlace F, localValue F ζ hζ (Sum.inl w) (x.val (Sum.inl w))
  have hf : Continuous f := continuous_finset_prod _
    (fun w _ => complex_raw_value_continuous F ζ hζ w)
  have ho : IsOpen {x : Raw F ζ hζ | ∀ v, x v ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ v} :=
    RestrictedProduct.isOpen_forall_mem (KPAdelicCoverRestrictedProduct.compact_open F ζ hζ)
  have hevent : ∀ᶠ x : rawCenter F ζ hζ in 𝓝 1,
      ∀ v, x.val v ∈ KPAdelicCoverRestrictedProduct.compact F ζ hζ v :=
    (ho.preimage continuous_subtype_val).mem_nhds (by intro v; exact Subgroup.one_mem _)
  have heq : rawProduct F ζ hζ =ᶠ[𝓝 (1 : rawCenter F ζ hζ)] f := by
    filter_upwards [hevent] with x hx
    unfold rawProduct
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · change (∏ v ∈ Finset.univ.image Sum.inl, localValue F ζ hζ v (x.val v)) = _
      rw [Finset.prod_image (fun _ _ _ _ h => Sum.inl_injective h)]
    · intro v hv
      cases v with
      | inl w => exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
      | inr q =>
        exact False.elim (hv (compact_diagonal_value F ζ hζ q (x.val (Sum.inr q))
          (hx (Sum.inr q)) (rawCenter_local_diagonal F ζ hζ x (Sum.inr q)).1
          (rawCenter_local_diagonal F ζ hζ x (Sum.inr q)).2))
  exact hf.continuousAt.congr heq.symm

end
end DedekindZetaZeroFree.KPGlobalCenterRationalCharacterExtension
