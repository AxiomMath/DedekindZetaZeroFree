module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicRootRescaling
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.UniformLevelTailCutoff
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.CubicTailPhaseInvariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalFields.ValuationShellMeasure

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneShellRepair
open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneShellContinuation KPRankOneRootParameter
variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

def actualStandardIntegrand (P : Polarization S.heisenberg) (ε : Sign) (s : ℂ)
    (φ : compactPicture S.borel P S.iwasawa (sourceSign ε))
    (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q)
    (x : LocalField F q) : ℂ :=
  ((compactTrivialization S.borel P S.iwasawa (sourceSign ε) (sourceParameter ε s) φ).val
    (kernelW (LocalField F q) S.borel ε *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) * k)).val h

def actualShellRatio (ε : Sign) (s : ℂ) : ℂ :=
  if ε = .plus then t (LocalField F q) s else
    (residueCardinality (LocalField F q) : ℂ) * (r (LocalField F q) s)⁻¹ ^ 6

private theorem uniformizer_multiplier (ε : Sign) (s : ℂ)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    (residueCardinality (LocalField F q) : ℂ) ^ 3 *
      (deltaHalf S.borel (rootCubeLift S.borel π) *
        rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) π) =
      actualShellRatio F q ε s := by
  have hq : 0 < (residueCardinality (LocalField F q) : ℝ) := by
    exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField (valuation (LocalField F q)).integer))
  have ha : localAbs (LocalField F q) π = (residueCardinality (LocalField F q) : ℝ)⁻¹ := by
    simp only [localAbs, hπ, WithZero.log_exp]
    norm_cast
    simp
  have hap : localAbs (LocalField F q) (π ^ 6) = localAbs (LocalField F q) π ^ 6 := by
    simp only [pow_succ, pow_zero, localAbs_mul, localAbs_one]
  have hd : deltaHalf S.borel (rootCubeLift S.borel π) =
      (residueCardinality (LocalField F q) : ℂ)⁻¹ ^ 3 := by
    rw [deltaHalf, rootCubeLift_coordinate, normPower, hap, ha, Real.log_pow, Real.log_inv]
    have hx : (1 / 2 : ℂ) * ↑((6 : ℝ) * -Real.log (residueCardinality (LocalField F q) : ℝ)) =
        (3 : ℕ) * (-↑(Real.log (residueCardinality (LocalField F q) : ℝ)) : ℂ) := by
      push_cast
      ring
    norm_num only [Nat.cast_ofNat] at ⊢
    rw [hx, Complex.exp_nat_mul, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hq]
    simp
  have hq0 : (residueCardinality (LocalField F q) : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  rw [hd, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hq0, one_pow, one_mul]
  cases ε with
  | plus => exact rootCharacter_uniformizer S.borel s π hπ
  | minus =>
    change rootCharacter S.borel .minus (-s) π = _
    rw [rootCharacter_weyl_inversion, rootCharacter_uniformizer S.borel s π hπ]
    simp [actualShellRatio, t, mul_inv_rev, inv_pow, mul_comm]

private theorem tail_pointwise_rescale (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) (π : (LocalField F q)ˣ) :
    ∀ᶠ v : LocalField F q in nhds 0, ∀ (s : ℂ)
      (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q) (hv : v ≠ 0),
      actualStandardIntegrand F ζ hζ q S P ε s φ.val k h
        (-((((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * v)⁻¹)) =
      (deltaHalf S.borel (rootCubeLift S.borel π) *
        rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) π) *
      actualStandardIntegrand F ζ hζ q S P ε s φ.val k h (-(v⁻¹)) := by
  have hc := actual_level_tail_uniform F ζ hζ q S P J hJ ε
  have hm : Filter.Tendsto (fun v : LocalField F q => ((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * v)
      (nhds 0) (nhds 0) := by
    have hh : Continuous (fun v : LocalField F q =>
        ((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * v) :=
      continuous_const.mul continuous_id
    simpa using (hh.continuousAt (x := (0 : LocalField F q))).tendsto
  filter_upwards [hc, hm.eventually hc] with v hv0 hv1
  intro s φ k h hv
  have hnv : (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * v) ≠ 0 :=
    mul_ne_zero (π ^ 3).ne_zero hv
  have h0 := congrArg (fun V : InducedModule P => V.val h) (hv0 s φ k hv)
  have h1 := congrArg (fun V : InducedModule P => V.val h) (hv1 s φ k hnv)
  have hu : Units.mk0 (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * v) hnv =
      π ^ 3 * Units.mk0 v hv := by
    apply Units.ext
    rfl
  change actualStandardIntegrand F ζ hζ q S P ε s φ.val k h (-(v⁻¹)) = _ at h0
  change actualStandardIntegrand F ζ hζ q S P ε s φ.val k h
    (-((((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * v)⁻¹)) = _ at h1
  rw [hu, actual_tail_phase_cube, actualRootAction_cube_rescale] at h1
  rw [h1, h0]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem shell_inverse_cutoff (U : Set (LocalField F q)) (hU : U ∈ nhds 0) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ x ∈ actualShell F q (m : ℤ), -(x⁻¹) ∈ U := by
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff'.mp hU
  simp only [sub_zero] at hγ
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
  let b := WithZero.log (e (γ : ValueGroupWithZero (LocalField F q)))
  refine ⟨b.natAbs + 2, ?_⟩
  intro m hm x hx
  have hQ : (1 : ℝ) < residueCardinality (LocalField F q) := by
    simpa only [residueCardinality, KPCubicUnitIndices.residueCard, CubicUnitCharacters.residueCard] using
      (show (1 : ℝ) < KPCubicUnitIndices.residueCard (LocalField F q) from by
        exact_mod_cast (KPCubicUnitIndices.two_le_residueCard (LocalField F q)))
  have hx0 : x ≠ 0 := by
    intro h; subst x
    have := hx.1
    simp only [KPCubicHaar.abs_zero] at this
    exact (not_lt_of_ge (zpow_pos (lt_trans zero_lt_one hQ) _).le) this
  have hex : e (valuation (LocalField F q) x) ≠ 0 := by simpa [e] using hx0
  have heγ : e (γ : ValueGroupWithZero (LocalField F q)) ≠ 0 := by simpa [e] using γ.ne_zero
  have hlog : (m : ℤ) - 1 < WithZero.log (e (valuation (LocalField F q) x)) := by
    have hh := hx.1
    simp only [actualShell, Set.mem_setOf_eq] at hx
    simp only [KPCubicHaar.abs, if_neg hx0] at hh
    exact (zpow_lt_zpow_iff_right₀ hQ).mp hh
  apply hγ
  change valuation (LocalField F q) (-(x⁻¹)) < γ
  rw [← e.toOrderIso.lt_iff_lt]
  change e (valuation (LocalField F q) (-(x⁻¹))) < e (γ : ValueGroupWithZero (LocalField F q))
  rw [Valuation.map_neg, map_inv₀, map_inv₀, ← WithZero.exp_log hex, ← WithZero.exp_log heγ,
    ← WithZero.exp_neg, WithZero.exp_lt_exp]
  dsimp only [b] at hm
  have hb : -((WithZero.log (e (↑γ : ValueGroupWithZero (LocalField F q)))).natAbs : ℤ) ≤ WithZero.log (e (↑γ : ValueGroupWithZero (LocalField F q))) := by rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
  omega

theorem actual_shell_dilation {L : Type*} [RCLike L]
      (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
      (π : (LocalField F q)ˣ)
      (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
        (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
      (m : ℤ) (f : LocalField F q → L) :
      (∫ x in actualShell F q (m + 3), f x ∂μ) =
        (residueCardinality (LocalField F q) : ℝ) ^ 3 •
          (∫ x in actualShell F q m, f (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q)⁻¹ * x) ∂μ) := by
    let Q : ℝ := residueCardinality (LocalField F q)
    let c : LocalField F q := ((π ^ 3 : (LocalField F q)ˣ) : LocalField F q)
    have hc0 : c ≠ 0 := (π ^ 3).ne_zero
    have hQ : 0 < Q := by
      dsimp only [Q]
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (KPCubicUnitIndices.two_le_residueCard (LocalField F q)))
    have ha : KPCubicHaar.abs (LocalField F q) c = Q ^ (-3 : ℤ) := by
      dsimp only [c]
      rw [Units.val_pow_eq_pow_val, KPCubicHaar.abs_pow]
      simp only [KPCubicHaar.abs, if_neg π.ne_zero, hπ, WithZero.log_exp]
      change (Q ^ (-1 : ℤ)) ^ 3 = Q ^ (-3 : ℤ)
      rw [← zpow_natCast, ← zpow_mul]
      norm_num
    have hs : (fun x : LocalField F q => c * x) ⁻¹' actualShell F q m =
        actualShell F q (m + 3) := by
      ext x
      simp only [Set.mem_preimage, actualShell, Set.mem_setOf_eq, KPCubicHaar.abs_mul, ha]
      have h1 : Q ^ (m - 1) = Q ^ (-3 : ℤ) * Q ^ (m + 3 - 1) := by
        rw [← zpow_add₀ hQ.ne']; congr 1; omega
      have h2 : Q ^ m = Q ^ (-3 : ℤ) * Q ^ (m + 3) := by
        rw [← zpow_add₀ hQ.ne']; congr 1; omega
      change Q ^ (m - 1) < Q ^ (-3 : ℤ) * _ ∧ Q ^ (-3 : ℤ) * _ ≤ Q ^ m ↔ _
      rw [h1, h2, mul_lt_mul_iff_right₀ (zpow_pos hQ _), mul_le_mul_iff_right₀ (zpow_pos hQ _)]
    have H := (Homeomorph.mulLeft₀ c hc0).isClosedEmbedding.setIntegral_map
      (μ := μ) (f := fun x => f (c⁻¹ * x)) (actualShell F q m)
    change (∫ x in actualShell F q m, f (c⁻¹ * x) ∂Measure.map (fun x => c * x) μ) =
      (∫ x in (fun x => c * x) ⁻¹' actualShell F q m, f (c⁻¹ * (c * x)) ∂μ) at H
    rw [NonarchimedeanHaarScaling.map_mul (LocalField F q) μ c hc0, ha,
      Measure.restrict_smul, integral_smul_measure, hs] at H
    have he : (ENNReal.ofReal (Q ^ (-3 : ℤ)))⁻¹.toReal = Q ^ 3 := by
      rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (zpow_pos hQ _).le, zpow_neg,
        inv_inv]
      norm_num
    simp only [inv_mul_cancel_left₀ hc0] at H
    rw [he] at H
    exact H.symm

theorem actual_tail_shell_pointwise (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (ε : Sign) (π : (LocalField F q)ˣ) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ x ∈ actualShell F q (m : ℤ), ∀ (s : ℂ)
      (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
      actualStandardIntegrand F ζ hζ q S P ε s φ.val k h
          (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q)⁻¹ * x) =
        (deltaHalf S.borel (rootCubeLift S.borel π) *
          rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) π) *
        actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x := by
  have hc := tail_pointwise_rescale F ζ hζ q S P J hJ ε π
  obtain ⟨M, hM⟩ := shell_inverse_cutoff F q _ hc
  refine ⟨M, ?_⟩
  intro m hm x hx s φ k h
  have hx0 : x ≠ 0 := by
    intro H; subst x
    have hQ : (0 : ℝ) < residueCardinality (LocalField F q) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (KPCubicUnitIndices.two_le_residueCard (LocalField F q)))
    have hh := hx.1
    simp only [KPCubicHaar.abs_zero] at hh
    exact (not_lt_of_ge (zpow_pos hQ _).le) hh
  have H := hM m hm x hx s φ k h (neg_ne_zero.mpr (inv_ne_zero hx0))
  have he : -((((π ^ 3 : (LocalField F q)ˣ) : LocalField F q) * -(x⁻¹))⁻¹) =
      (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q)⁻¹ * x) := by
    simp [mul_inv_rev, mul_comm]
  simpa only [he, inv_neg, inv_inv, neg_neg] using H

theorem actual_tail_shell_step (P : Polarization S.heisenberg)
    (J : CompactOpenLevel (ActualCover F ζ hζ q))
    (hJ : (J.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) ≤ S.iwasawa.compact.toOpenSubgroup)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ))
    (ε : Sign) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ (s : ℂ)
      (φ : compactLevel S.borel P S.iwasawa (sourceSign ε) J)
      (k : S.iwasawa.compact.toOpenSubgroup) (h : actualTorus F ζ hζ q),
      (∫ x in actualShell F q ((m : ℤ) + 3),
        actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) =
      actualShellRatio F q ε s *
        (∫ x in actualShell F q (m : ℤ),
          actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x ∂μ) := by
  obtain ⟨M, hM⟩ := actual_tail_shell_pointwise F ζ hζ q S P J hJ ε π
  refine ⟨M, ?_⟩
  intro m hm s φ k h
  rw [actual_shell_dilation F q μ π hπ]
  have habs : Measurable (KPCubicHaar.abs (LocalField F q)) := by
    unfold KPCubicHaar.abs
    simpa only [KPCubicUnitIndices.residueCard, CubicUnitCharacters.residueCard] using
      KPRamifiedBetaConductorSeries.normalizedAbs_measurable (LocalField F q)
  have hset : MeasurableSet (actualShell F q (m : ℤ)) :=
    (measurableSet_lt measurable_const habs).inter (measurableSet_le habs measurable_const)
  have he := setIntegral_congr_fun (f := fun x =>
      actualStandardIntegrand F ζ hζ q S P ε s φ.val k h
        (((π ^ 3 : (LocalField F q)ˣ) : LocalField F q)⁻¹ * x))
      (g := fun x => (deltaHalf S.borel (rootCubeLift S.borel π) *
        rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) π) *
        actualStandardIntegrand F ζ hζ q S P ε s φ.val k h x)
      (μ := μ) hset
      (fun x hx => hM m hm x hx s φ k h)
  rw [he, integral_const_mul]
  simp only [Complex.real_smul, Complex.ofReal_pow]
  rw [← mul_assoc]
  congr 1
  exact uniformizer_multiplier F ζ hζ q S ε s π hπ

theorem actual_uniformizer_multiplier (ε : Sign) (s : ℂ)
    (π : (LocalField F q)ˣ)
    (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
    (residueCardinality (LocalField F q) : ℂ) ^ 3 *
      (deltaHalf S.borel (rootCubeLift S.borel π) *
        rootCharacter S.borel (sourceSign ε) (sourceParameter ε s) π) =
      actualShellRatio F q ε s :=
  uniformizer_multiplier F ζ hζ q S ε s π hπ

end DedekindZetaZeroFree.KPRankOneShellRepair

end
