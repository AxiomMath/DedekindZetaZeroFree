module

public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.CubeClassesAndCenterCoordinates

@[expose] public section

open scoped NumberField commutatorElement
open NumberField IsDedekindDomain ValuativeRel

namespace DedekindZetaZeroFree.ActualFiniteTorus

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

def normUnit (y : (K F q)ˣ) : ℂˣ :=
  Units.mk0 (KPLocalPrincipalSeries.normPower (K F q) y (1 / 6))
    (Complex.exp_ne_zero _)

def rawCenterValue (c : C F ζ hζ q) : ℂˣ :=
  ordinaryIota F ζ hζ (sheet F ζ hζ q c) *
    normUnit F q (coordinate F ζ hζ q c)

def commutatorCenter (x y : H F ζ hζ q) : C F ζ hζ q :=
  ⟨⁅x, y⁆, by
    rw [(actual_cube_quotient_pairing F ζ hζ q).2.2.2.2.2.1]
    exact (actual_center_cube_normal_form F ζ hζ q).2.2.1 _⟩

private theorem center_word (e : rootsOfUnity 3 F) (y : (K F q)ˣ) :
    ((centerInjection F ζ hζ q e * cubeLift F ζ hζ q y : C F ζ hζ q) : Cover F ζ hζ q) =
      normalWord F ζ hζ q e (y ^ 3) := by
  simp [centerInjection, cubeLift, central, torusLift, normalWord]
private theorem center_coords (e : rootsOfUnity 3 F) (y : (K F q)ˣ) :
    coordinate F ζ hζ q (centerInjection F ζ hζ q e * cubeLift F ζ hζ q y) = y ^ 3 ∧
    sheet F ζ hζ q (centerInjection F ζ hζ q e * cubeLift F ζ hζ q y) = e := by
  exact (actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 e (y ^ 3) _ (center_word F ζ hζ q e y)
private theorem value_word (e : rootsOfUnity 3 F) (y : (K F q)ˣ) :
    rawCenterValue F ζ hζ q (centerInjection F ζ hζ q e * cubeLift F ζ hζ q y) =
      ordinaryIota F ζ hζ e * normUnit F q (y ^ 3) := by
  rcases center_coords F ζ hζ q e y with ⟨hc, hs⟩
  simp only [rawCenterValue, Subgroup.coe_mul, hc, hs]
private theorem center_decomp (c : C F ζ hζ q) :
    ∃ (e : rootsOfUnity 3 F) (y : (K F q)ˣ),
      c = centerInjection F ζ hζ q e * cubeLift F ζ hζ q y := by
  obtain ⟨⟨e, v⟩, hv, _⟩ := (actual_center_cube_normal_form F ζ hζ q).2.2.2.2.1 c
  obtain ⟨y, hy⟩ := v.property
  refine ⟨e, y, ?_⟩
  apply Subtype.ext
  change y ^ 3 = (v : (K F q)ˣ) at hy
  change (c : H F ζ hζ q) = central F ζ hζ q e * torusLift F ζ hζ q (y ^ 3)
  rw [hy]
  exact hv
private theorem normUnit_one : normUnit F q 1 = 1 := by
  apply Units.ext
  simp [normUnit, KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs_one]
private theorem normUnit_mul (x y : (K F q)ˣ) :
    normUnit F q (x * y) = normUnit F q x * normUnit F q y := by
  apply Units.ext
  simp [normUnit, KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs_mul,
    Real.log_mul (ne_of_gt (KPLocalPrincipalSeries.localAbs_pos (K F q) x))
      (ne_of_gt (KPLocalPrincipalSeries.localAbs_pos (K F q) y)), mul_add, Complex.exp_add]
private theorem value_one : rawCenterValue F ζ hζ q 1 = 1 := by
  have h := value_word F ζ hζ q 1 1
  simpa [normUnit_one] using h
private theorem value_mul (c d : C F ζ hζ q) :
    rawCenterValue F ζ hζ q (c * d) = rawCenterValue F ζ hζ q c * rawCenterValue F ζ hζ q d := by
  obtain ⟨e, x, rfl⟩ := center_decomp F ζ hζ q c
  obtain ⟨f, y, rfl⟩ := center_decomp F ζ hζ q d
  rw [show (centerInjection F ζ hζ q e * cubeLift F ζ hζ q x) *
      (centerInjection F ζ hζ q f * cubeLift F ζ hζ q y) =
      centerInjection F ζ hζ q (e * f) * cubeLift F ζ hζ q (x * y) by
        simp only [map_mul]; ac_rfl]
  rw [value_word, value_word, value_word, map_mul, mul_pow, normUnit_mul]
  ac_rfl
private theorem sheet_locallyConstant : IsLocallyConstant (sheet F ζ hζ q) := by
  letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
    @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
      (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))
  let p := KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
  let r : H F ζ hζ q → Cover F ζ hζ q := fun h =>
    (h : Cover F ζ hζ q) * (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (coordinate F ζ hζ q h))⁻¹
  have hr (h : H F ζ hζ q) : r h =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (sheet F ζ hζ q h) := by
    dsimp [r]
    rw [(actual_torus_normal_form F ζ hζ q).2.2.1 h]
    simp [normalWord]
  have hrmem (h : H F ζ hζ q) : r h ∈ p.ker := by
    rw [hr]
    change KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) _ ∈
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).ker
    rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
    exact ⟨_, rfl⟩
  let r' : H F ζ hζ q → p.ker := fun h => ⟨r h, hrmem h⟩
  have hc : Continuous r' := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.mul
      (((KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
        (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.comp
        (actual_torus_normal_form F ζ hζ q).2.2.2.1).inv)
  letI : T2Space (Cover F ζ hζ q) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).1
  haveI : Finite p.ker := by
    apply Finite.of_surjective
      (fun e : rootsOfUnity 3 F => (⟨KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e,
        by rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]; exact ⟨e, rfl⟩⟩ : p.ker))
    intro x
    have hx := x.property
    have hx : x.val ∈ (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).range := by
      simpa only [KPPGLLocalCover.range_centralInjection_eq_ker_projection] using hx
    obtain ⟨e, he⟩ := hx
    exact ⟨e, Subtype.ext he⟩
  haveI : DiscreteTopology p.ker := inferInstance
  have hl := (IsLocallyConstant.iff_continuous r').mpr hc
  rw [IsLocallyConstant.iff_eventually_eq]
  intro h
  filter_upwards [hl.eventually_eq h] with x hx
  apply KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q)
  simpa only [r', hr] using congrArg Subtype.val hx
private theorem normUnit_locallyConstant : IsLocallyConstant (normUnit F q) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro y
  have hv := (ValuativeRel.valuation (K F q)).locally_const
    ((Valuation.ne_zero_iff _).mpr y.ne_zero)
  have hu := (Units.continuous_val (M := K F q)).continuousAt.preimage_mem_nhds hv
  filter_upwards [hu] with x hx
  change ValuativeRel.valuation (K F q) (x : K F q) =
    ValuativeRel.valuation (K F q) (y : K F q) at hx
  simp only [normUnit, KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs, hx]
private theorem value_locallyConstant : IsLocallyConstant (rawCenterValue F ζ hζ q) := by
  exact ((sheet_locallyConstant F ζ hζ q).comp_continuous continuous_subtype_val).comp₂
    ((normUnit_locallyConstant F q).comp_continuous
      ((actual_torus_normal_form F ζ hζ q).2.2.2.1.comp continuous_subtype_val))
    (fun e n => ordinaryIota F ζ hζ e * n)
private theorem value_cube (y : (K F q)ˣ) :
    rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y) = normUnit F q (y ^ 3) := by
  simpa using value_word F ζ hζ q 1 y
private theorem nonfaithful :
    ∃ c : C F ζ hζ q, c ≠ 1 ∧ rawCenterValue F ζ hζ q c = 1 := by
  refine ⟨cubeLift F ζ hζ q (-1), ?_, ?_⟩
  · intro he
    have hc := (center_coords F ζ hζ q 1 (-1)).1
    simp only [map_one, one_mul, he] at hc
    norm_num at hc
  · rw [value_cube]
    apply Units.ext
    simp [normUnit, KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs]
private theorem exists_nonunitary_cube :
    ∃ y : (K F q)ˣ, ‖(rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y) : ℂ)‖ < 1 := by
  let iso := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (K F q)
  obtain ⟨π, hπ⟩ := ValuativeRel.valuation_surjective (iso.symm (WithZero.exp (-1 : ℤ)))
  have hn : π ≠ 0 := by
    intro hz
    have hz' := hπ
    rw [hz, map_zero] at hz'
    have h := congrArg iso hz'
    simp only [map_zero, iso.apply_symm_apply] at h
    exact WithZero.exp_ne_zero h.symm
  let y : (K F q)ˣ := Units.mk0 π hn
  have hy : iso (ValuativeRel.valuation (K F q) (y : K F q)) = WithZero.exp (-1 : ℤ) := by
    change iso (ValuativeRel.valuation (K F q) π) = _
    rw [hπ, iso.apply_symm_apply]
  have hq : 1 < (KPLocalPrincipalSeries.residueCardinality (K F q) : ℝ) := by
    change 1 < (Nat.card 𝓀[K F q] : ℝ)
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K F q]))
  have habs : KPLocalPrincipalSeries.localAbs (K F q) y =
      (KPLocalPrincipalSeries.residueCardinality (K F q) : ℝ)⁻¹ := by
    change _ ^ ((WithZero.log (iso (ValuativeRel.valuation (K F q) (y : K F q))) : ℤ) : ℝ) = _
    rw [hy, WithZero.log_exp]
    rw [show ((-1 : ℤ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
  have hp : KPLocalPrincipalSeries.localAbs (K F q) (y ^ 3) < 1 := by
    rw [KPLocalPrincipalSeriesNormWeights.absolute_pow _
      (KPLocalPrincipalSeries.localAbs_one (K F q))
      (KPLocalPrincipalSeries.localAbs_mul (K F q)), habs]
    exact pow_lt_one₀ (by positivity) (inv_lt_one_of_one_lt₀ hq) (by decide)
  refine ⟨y, ?_⟩
  rw [value_cube]
  change ‖Complex.exp ((1 / 6 : ℂ) *
    (Real.log (KPLocalPrincipalSeries.localAbs (K F q) (y ^ 3)) : ℂ))‖ < 1
  rw [Complex.norm_exp]
  apply Real.exp_lt_one_iff.mpr
  have hlog := Real.log_neg (KPLocalPrincipalSeries.localAbs_pos (K F q) (y ^ 3)) hp
  simpa using (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 1 / 6) hlog)
private theorem not_inversion_invariant :
    ∃ y : (K F q)ˣ, rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y) ≠
      rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y⁻¹) := by
  obtain ⟨y, hy⟩ := exists_nonunitary_cube F ζ hζ q
  refine ⟨y, ?_⟩
  intro he
  have hm := value_mul F ζ hζ q (cubeLift F ζ hζ q y) (cubeLift F ζ hζ q y⁻¹)
  rw [← map_mul, mul_inv_cancel, map_one, value_one, ← he] at hm
  have hnorm := congrArg (fun z : ℂˣ => ‖(z : ℂ)‖) hm
  simp only [Units.val_one, norm_one, Units.val_mul, norm_mul] at hnorm
  have hn := norm_nonneg (rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y) : ℂ)
  nlinarith

theorem prescribed_center_character :
    rawCenterValue F ζ hζ q 1 = 1 ∧
    (∀ c d : C F ζ hζ q, rawCenterValue F ζ hζ q (c * d) =
      rawCenterValue F ζ hζ q c * rawCenterValue F ζ hζ q d) ∧
    Continuous (rawCenterValue F ζ hζ q) ∧
    IsOpen {c : C F ζ hζ q | rawCenterValue F ζ hζ q c = 1} ∧
    (∀ (e : rootsOfUnity 3 F) (y : (K F q)ˣ),
      (rawCenterValue F ζ hζ q (centerInjection F ζ hζ q e * cubeLift F ζ hζ q y) : ℂ) =
        (ordinaryIota F ζ hζ e : ℂ) *
          KPLocalPrincipalSeries.normPower (K F q) (y ^ 3) (1 / 6)) ∧
    (∃ c : C F ζ hζ q, ‖(rawCenterValue F ζ hζ q c : ℂ)‖ ≠ 1) ∧
    (∃ c : C F ζ hζ q, c ≠ 1 ∧ rawCenterValue F ζ hζ q c = 1) ∧
    (∃ y : (K F q)ˣ, rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y) ≠
      rawCenterValue F ζ hζ q (cubeLift F ζ hζ q y⁻¹)) := by
  refine ⟨value_one F ζ hζ q, value_mul F ζ hζ q,
    (value_locallyConstant F ζ hζ q).continuous,
    (value_locallyConstant F ζ hζ q).isOpen_fiber 1, ?_, ?_,
    nonfaithful F ζ hζ q, not_inversion_invariant F ζ hζ q⟩
  · intro e y
    exact congrArg Units.val (value_word F ζ hζ q e y)
  · obtain ⟨y, hy⟩ := exists_nonunitary_cube F ζ hζ q
    exact ⟨cubeLift F ζ hζ q y, ne_of_lt hy⟩

def prescribedCenterCharacter : C F ζ hζ q →ₜ* ℂˣ where
  toFun := rawCenterValue F ζ hζ q
  map_one' := (prescribed_center_character F ζ hζ q).1
  map_mul' := (prescribed_center_character F ζ hζ q).2.1
  continuous_toFun := (prescribed_center_character F ζ hζ q).2.2.1

def actualHeisenberg :
    letI := finiteCubeClasses F ζ hζ q
    KPLocalStoneVonNeumann.LocalHeisenbergData (H F ζ hζ q) (D F q) := by
  letI := finiteCubeClasses F ζ hζ q
  refine {
    C := C F ζ hζ q
    central := le_rfl
    center_open := (actual_center_cube_normal_form F ζ hζ q).2.1
    π := π F ζ hζ q
    quotient_surjective := (actual_cube_quotient_pairing F ζ hζ q).2.1
    quotient_kernel := (actual_center_cube_normal_form F ζ hζ q).1
    ω := prescribedCenterCharacter F ζ hζ q
    character_kernel_open := (prescribed_center_character F ζ hζ q).2.2.2.1
    pairing := pairing F ζ hζ q
    alternating := (actual_cube_quotient_pairing F ζ hζ q).2.2.1
    perfect := (actual_cube_quotient_pairing F ζ hζ q).2.2.2.1
    commutator_mem := fun x y => (commutatorCenter F ζ hζ q x y).property
    commutator_pairing := ?_
    detects_commutation := (actual_cube_quotient_pairing F ζ hζ q).2.2.2.2.2.2.1 }
  intro x y
  let e := KPHilbert.B3 F ζ hζ (Sum.inr q)
    (coordinate F ζ hζ q x) (coordinate F ζ hζ q y)
  have he : (commutatorCenter F ζ hζ q x y) = centerInjection F ζ hζ q e := by
    apply Subtype.ext
    exact (actual_cube_quotient_pairing F ζ hζ q).2.2.2.2.2.1 x y
  change rawCenterValue F ζ hζ q (commutatorCenter F ζ hζ q x y) = _
  rw [he]
  rw [(actual_cube_quotient_pairing F ζ hζ q).2.2.2.2.2.2.2 x y]
  apply Units.ext
  have hv := (prescribed_center_character F ζ hζ q).2.2.2.2.1 e 1
  simpa [KPLocalPrincipalSeries.normPower, KPLocalPrincipalSeries.localAbs_one] using hv

theorem actual_heisenberg_and_polarization :
    letI := finiteCubeClasses F ζ hζ q
    (actualHeisenberg F ζ hζ q).C = C F ζ hζ q ∧
    (actualHeisenberg F ζ hζ q).π = π F ζ hζ q ∧
    (actualHeisenberg F ζ hζ q).ω = prescribedCenterCharacter F ζ hζ q ∧
    (∀ (e : rootsOfUnity 3 F) (y : (K F q)ˣ),
      ((actualHeisenberg F ζ hζ q).ω
        (centerInjection F ζ hζ q e * cubeLift F ζ hζ q y) : ℂ) =
      (ordinaryIota F ζ hζ e : ℂ) *
        KPLocalPrincipalSeries.normPower (K F q) (y ^ 3) (1 / 6)) ∧
    Nonempty (KPLocalStoneVonNeumann.Polarization (actualHeisenberg F ζ hζ q)) := by
  letI := finiteCubeClasses F ζ hζ q
  refine ⟨rfl, rfl, rfl, (prescribed_center_character F ζ hζ q).2.2.2.2.1, ?_⟩
  let T := actualHeisenberg F ζ hζ q
  obtain ⟨L, hL, _, ωL, hωL⟩ :=
    KPLocalPolarization.exists_continuous_maximal_polarization T.π
      T.quotient_surjective T.C T.quotient_kernel T.center_open T.pairing
      T.detects_commutation T.ω
  exact ⟨{ L := L, maximal := hL, ωL := ωL, extends_center := hωL }⟩

end
end DedekindZetaZeroFree.ActualFiniteTorus
