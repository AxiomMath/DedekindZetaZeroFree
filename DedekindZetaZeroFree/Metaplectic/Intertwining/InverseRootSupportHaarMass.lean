module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalInverseRootSupport

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries

variable (F : Type) [Field F] [NumberField F]
  (q : HeightOneSpectrum (𝓞 F))

theorem rootLevelSet_eq_congruence_ideal
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (m : ℕ) (hm : 0 < m) :
    KPTameJacquetTestDuality.rootLevelSet F ζ hζ q m =
      (KPLocalCube.LocalIntegers F q).subtype ''
        ((KPLocalCube.maximalIdeal F q ^ m : Ideal (KPLocalCube.LocalIntegers F q)) : Set (KPLocalCube.LocalIntegers F q)) := by
  apply Set.Subset.antisymm
  · rintro x ⟨k, hk⟩
    have hp := congrArg S.borel.projection hk
    have hp' : Matrix.ProjGenLinGroup.mk k.val =
        Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) x) := by
      change S.borel.projection
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          (KPLocalCover.sectionMap F ζ hζ (Sum.inr q) k.val)) =
        S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) at hp
      have pn : S.borel.projection (KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) =
          Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n (LocalField F q) x) :=
        (S.openCell P).projection_eq _
      rw [(S.openCell P).projection_eq, pn] at hp
      exact hp
    obtain ⟨c, hc⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp'
    have h01 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 0 1) hc
    have h11 := congrArg (fun g : GL (Fin 2) (LocalField F q) => g 1 1) hc
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.diagonal_apply,
      KubotaRankTwo.n, Matrix.mul_apply, Fin.sum_univ_two] at h01 h11
    obtain ⟨k₀, hk₀, he₀⟩ := k.property
    have hent := (KPLocalCube.mem_integerCongruence_iff F q m k₀).mp hk₀
    have h11ideal : k₀ 1 1 - 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by simpa using hent 1 1
    have h01ideal : k₀ 0 1 ∈ KPLocalCube.maximalIdeal F q ^ m := by simpa using hent 0 1
    have hu : IsUnit (k₀ 1 1) := by
      apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
      have hmem := Ideal.pow_le_self (Nat.ne_of_gt hm) h11ideal
      change 1 - k₀ 1 1 ∈ KPLocalCube.maximalIdeal F q
      simpa only [neg_sub] using (KPLocalCube.maximalIdeal F q).neg_mem hmem
    obtain ⟨u, hu⟩ := hu
    let y : KPLocalCube.LocalIntegers F q := k₀ 0 1 * (↑u⁻¹)
    refine ⟨y, (KPLocalCube.maximalIdeal F q ^ m).mul_mem_right _ h01ideal, ?_⟩
    have hk01 : (k₀ 0 1 : LocalField F q) = k.val 0 1 := by rw [← he₀]; rfl
    have hk11 : (k₀ 1 1 : LocalField F q) = k.val 1 1 := by rw [← he₀]; rfl
    have hui : ((↑u⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) =
        ((u : KPLocalCube.LocalIntegers F q) : LocalField F q)⁻¹ :=
      Units.val_inv_eq_inv_val (Units.map (KPLocalCube.LocalIntegers F q).subtype.toMonoidHom u)
    change (k₀ 0 1 : LocalField F q) * ((↑u⁻¹ : KPLocalCube.LocalIntegers F q) : LocalField F q) = x
    rw [hui, hu, hk01, hk11]
    have hinv : (k.val 1 1)⁻¹ = (c : LocalField F q) := by
      exact inv_eq_of_mul_eq_one_right h11
    rw [hinv, h01]
  · rintro _ ⟨y, hy, rfl⟩
    let n₀ : KPLocalCube.IntegerGL2 F q :=
      ⟨!![1,y;0,1], !![1,-y;0,1], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply], by
        ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]⟩
    have hn₀ : n₀ ∈ KPLocalCube.integerCongruence F q m := by
      rw [KPLocalCube.mem_integerCongruence_iff]
      intro i j
      fin_cases i <;> fin_cases j <;> simp [n₀]
      exact hy
    have hn : KubotaRankTwo.n (LocalField F q) y ∈ KPLocalCube.Gamma F q m := by
      refine ⟨n₀, hn₀, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [n₀, KPLocalCube.integerInclusion, Matrix.GeneralLinearGroup.map_apply,
          KubotaRankTwo.n]
    exact ⟨⟨_, hn⟩, rfl⟩

theorem fullDiagonal_residual_ideal_image
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (KPTameCompact.O F q)ˣ) (I : Ideal (KPLocalCube.LocalIntegers F q)) :
    (fun t : LocalField F q =>
      (KPTameCompact.unitInclusion F q u : LocalField F q) * t /
        ((KPTameCompact.unitInclusion F q u : LocalField F q) + π * t)) ''
      ((KPLocalCube.LocalIntegers F q).subtype '' (I : Set (KPLocalCube.LocalIntegers F q))) =
      (KPLocalCube.LocalIntegers F q).subtype '' (I : Set (KPLocalCube.LocalIntegers F q)) := by
  let U := KPTameCompact.unitInclusion F q u
  apply Set.Subset.antisymm
  · rintro y ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨w, hw⟩ := fullDiagonal_shifted_unit F q π hπ u t
    refine ⟨(u * w⁻¹ : (KPTameCompact.O F q)ˣ) * t, I.mul_mem_left _ ht, ?_⟩
    change ((u * w⁻¹ : (KPTameCompact.O F q)ˣ) : LocalField F q) * t = _
    have hw' : (KPTameCompact.unitInclusion F q w : LocalField F q) = (U : LocalField F q) + π * t := hw
    have hc : ((u * w⁻¹ : (KPTameCompact.O F q)ˣ) : LocalField F q) =
        (U : LocalField F q) * (KPTameCompact.unitInclusion F q w : LocalField F q)⁻¹ := by
      change (KPTameCompact.unitInclusion F q (u * w⁻¹) : LocalField F q) = _
      simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, U]
    rw [hc, hw']
    dsimp
    ring
  · rintro y ⟨y, hy, rfl⟩
    obtain ⟨w, hw⟩ := fullDiagonal_shifted_unit F q π hπ u (-y)
    have hw' : (KPTameCompact.unitInclusion F q w : LocalField F q) = (U : LocalField F q) - π * y := by
      simpa only [Subring.coe_neg, mul_neg, ← sub_eq_add_neg] using hw
    let t : KPLocalCube.LocalIntegers F q := (u * w⁻¹ : (KPTameCompact.O F q)ˣ) * y
    have ht : t ∈ I := I.mul_mem_left _ hy
    refine ⟨t, ⟨t, ht, rfl⟩, ?_⟩
    have ht' : (t : LocalField F q) = (U : LocalField F q) * y /
        (KPTameCompact.unitInclusion F q w : LocalField F q) := by
      change ((u * w⁻¹ : (KPTameCompact.O F q)ˣ) : LocalField F q) * y = _
      have hc : ((u * w⁻¹ : (KPTameCompact.O F q)ˣ) : LocalField F q) =
          (U : LocalField F q) * (KPTameCompact.unitInclusion F q w : LocalField F q)⁻¹ := by
        change (KPTameCompact.unitInclusion F q (u * w⁻¹) : LocalField F q) = _
        simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, U]
      rw [hc]
      ring
    change (U : LocalField F q) * t / ((U : LocalField F q) + π * t) = y
    rw [ht']
    have hU := U.ne_zero
    have hW := (KPTameCompact.unitInclusion F q w).ne_zero
    have hden : (U : LocalField F q) + π * ((U : LocalField F q) * y /
        (KPTameCompact.unitInclusion F q w : LocalField F q)) =
        (U : LocalField F q)^2 / (KPTameCompact.unitInclusion F q w : LocalField F q) := by
      apply (eq_div_iff hW).mpr
      field_simp
      rw [hw']
      ring
    rw [hden]
    field_simp

theorem fullDiagonal_inverse_root_ideal_image
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (KPTameCompact.O F q)ˣ) (i : Fin 3)
    (I : Ideal (KPLocalCube.LocalIntegers F q)) :
    (fun t : LocalField F q =>
      (π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) /
        ((KPTameCompact.unitInclusion F q u : LocalField F q) + π * t)) ''
      ((KPLocalCube.LocalIntegers F q).subtype '' (I : Set (KPLocalCube.LocalIntegers F q))) =
    (fun t : LocalField F q =>
      ((π ^ ((i.val : ℤ) + 1) / KPTameCompact.unitInclusion F q u : (LocalField F q)ˣ) : LocalField F q) -
      ((π ^ ((i.val : ℤ) + 2) / (KPTameCompact.unitInclusion F q u)^2 : (LocalField F q)ˣ) : LocalField F q) * t) ''
      ((KPLocalCube.LocalIntegers F q).subtype '' (I : Set (KPLocalCube.LocalIntegers F q))) := by
  let A := (KPLocalCube.LocalIntegers F q).subtype '' (I : Set (KPLocalCube.LocalIntegers F q))
  let U := KPTameCompact.unitInclusion F q u
  let T := fun t : LocalField F q => (U : LocalField F q) * t / ((U : LocalField F q) + π * t)
  let L := fun t : LocalField F q =>
    ((π ^ ((i.val : ℤ) + 1) / U : (LocalField F q)ˣ) : LocalField F q) -
      ((π ^ ((i.val : ℤ) + 2) / U^2 : (LocalField F q)ˣ) : LocalField F q) * t
  have hT : T '' A = A := fullDiagonal_residual_ideal_image F q π hπ u I
  change _ '' A = L '' A
  conv_rhs => rw [← hT, Set.image_image]
  apply Set.image_congr
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨w, hw⟩ := fullDiagonal_shifted_unit F q π hπ u t
  have hd : (U : LocalField F q) + π * t ≠ 0 := by
    rw [← hw]
    exact (KPTameCompact.unitInclusion F q w).ne_zero
  change (π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) / ((U : LocalField F q) + π * t) =
    ((π ^ ((i.val : ℤ) + 1) / U : (LocalField F q)ˣ) : LocalField F q) -
      ((π ^ ((i.val : ℤ) + 2) / U^2 : (LocalField F q)ˣ) : LocalField F q) *
        ((U : LocalField F q) * t / ((U : LocalField F q) + π * t))
  rw [show (i.val : ℤ) + 2 = ((i.val : ℤ) + 1) + 1 by omega,
    zpow_add, zpow_one]
  simp only [Units.val_mul, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  simp only [zpow_add, zpow_one, zpow_ofNat, Units.val_mul, Units.val_pow_eq_pow_val]
  field_simp
  <;> ring

theorem affine_dilation_haar_mass
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (a : LocalField F q) (c : (LocalField F q)ˣ) (A : Set (LocalField F q)) :
    μ ((fun t : LocalField F q => a - (c : LocalField F q) * t) '' A) =
      ENNReal.ofReal (IntrinsicHaarScaling.abs (LocalField F q) (c : LocalField F q)) * μ A := by
  let E := MeasurableEquiv.mulLeft₀ (-(c : LocalField F q)) (neg_ne_zero.mpr c.ne_zero)
  have hm := IntrinsicHaarScaling.map_mul (LocalField F q) μ
    (-(c : LocalField F q)) (neg_ne_zero.mpr c.ne_zero)
  have he : (fun t : LocalField F q => a - (c : LocalField F q) * t) '' A =
      (fun t => a + t) '' (E '' A) := by
    rw [Set.image_image]
    congr 1
    funext t
    simp [E, sub_eq_add_neg]
  rw [he]
  have htrans : μ ((fun t => a + t) '' (E '' A)) = μ (E '' A) := by
    have hp := measure_preimage_add μ (-a) (E '' A)
    have hs : (fun t => a + t) '' (E '' A) = (fun t => -a + t) ⁻¹' (E '' A) := by
      ext t
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hx
        exact ⟨-a + t, hx, by simp⟩
    rw [hs, hp]
  rw [htrans]
  have hh := congrArg (fun ν : Measure (LocalField F q) => ν (E '' A)) hm
  change (Measure.map E μ) (E '' A) = _ at hh
  rw [E.measurableEmbedding.map_apply, E.injective.preimage_image,
    Measure.smul_apply, smul_eq_mul] at hh
  have habs : IntrinsicHaarScaling.abs (LocalField F q) (-(c : LocalField F q)) =
      IntrinsicHaarScaling.abs (LocalField F q) (c : LocalField F q) := by
    simp [IntrinsicHaarScaling.abs, c.ne_zero]
  rw [habs] at hh
  have hpos : 0 < IntrinsicHaarScaling.abs (LocalField F q) (c : LocalField F q) := by
    simp only [IntrinsicHaarScaling.abs, if_neg c.ne_zero]
    exact zpow_pos (by exact_mod_cast Nat.card_pos) _
  have hn : ENNReal.ofReal (IntrinsicHaarScaling.abs (LocalField F q) (c : LocalField F q)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpos).ne'
  rw [hh, ← mul_assoc, ENNReal.mul_inv_cancel hn ENNReal.ofReal_ne_top, one_mul]

theorem fullDiagonal_inverse_root_haar_mass
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (KPTameCompact.O F q)ˣ) (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    μ ((fun t : LocalField F q =>
      (π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) /
        ((KPTameCompact.unitInclusion F q u : LocalField F q) + π * t)) ''
      KPTameJacquetTestDuality.rootLevelSet F ζ hζ q m) =
    ENNReal.ofReal ((residueCardinality (LocalField F q) : ℝ) ^ (-(i.val : ℤ) - 2)) *
      μ (KPTameJacquetTestDuality.rootLevelSet F ζ hζ q m) := by
  rw [rootLevelSet_eq_congruence_ideal F q ζ hζ S P m hm,
    fullDiagonal_inverse_root_ideal_image F q π hπ u i,
    affine_dilation_haar_mass]
  congr 2
  have habs : IntrinsicHaarScaling.abs (LocalField F q)
      ((π ^ ((i.val : ℤ) + 2) / (KPTameCompact.unitInclusion F q u)^2 : (LocalField F q)ˣ) : LocalField F q) =
      localAbs (LocalField F q)
        (π ^ ((i.val : ℤ) + 2) / (KPTameCompact.unitInclusion F q u)^2) := by
    simp only [IntrinsicHaarScaling.abs, if_neg (Units.ne_zero _)]
    unfold localAbs
    rw [Real.rpow_intCast]
    rfl
  rw [habs]
  simpa only [pow_two] using fullDiagonal_inner_increment_abs F q π hπ u u i

theorem fullDiagonal_inverse_root_real_mass
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : KPLocalStoneVonNeumann.Polarization S.heisenberg)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (u : (KPTameCompact.O F q)ˣ) (i : Fin 3) (m : ℕ) (hm : 0 < m) :
    (μ ((fun t : LocalField F q =>
      (π ^ ((i.val : ℤ) + 1) : (LocalField F q)ˣ) /
        ((KPTameCompact.unitInclusion F q u : LocalField F q) + π * t)) ''
      KPTameJacquetTestDuality.rootLevelSet F ζ hζ q m)).toReal =
    (residueCardinality (LocalField F q) : ℝ) ^ (-(i.val : ℤ) - 2) *
      KPTameJacquetTestDuality.rootMass F ζ hζ q μ m := by
  rw [fullDiagonal_inverse_root_haar_mass F q ζ hζ S P μ π hπ u i m hm,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  · rfl
  · exact le_of_lt (zpow_pos (by exact_mod_cast Nat.card_pos) _)

end DedekindZetaZeroFree.KPTameTransposeUnitNumeratorSteps

end
