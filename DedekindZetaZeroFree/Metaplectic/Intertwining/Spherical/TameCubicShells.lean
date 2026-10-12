module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.CubicUnitShells
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RootIndependenceAndExactness
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.MeromorphicContinuation

@[expose] public section

section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneTameSphericalFactor
open LocalFieldTheory.IsNonarchimedeanLocalField
open KPExceptionalRaw.FiniteSource.GoodSphericalVector

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (q : HeightOneSpectrum (𝓞 F)) (S : KPExceptionalRaw.RawFiniteInducingData F ζ hζ q)

private theorem tame_invmask (P : Polarization S.heisenberg) (V : InducedModule P)
    (hu : ∀ u : (KPTameCompact.O F q)ˣ,
      tau P ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u)) V = V)
    (u : (KPTameCompact.O F q)ˣ) (v : (LocalField F q)ˣ) :
    tau P (((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u * v))⁻¹) V =
      (ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q)
        (KPTameCompact.unitInclusion F q u ^ 2) (v ^ 2) ^ 2) : ℂ) •
        tau P (((S.openCell P).rootTorus v)⁻¹) V := by
  let a := (S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u)
  let b := (S.openCell P).rootTorus v
  let r := (S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u * v)
  let z := (S.openCell P).centralTorus (KPHilbert.B3 F ζ hζ (Sum.inr q)
    (KPTameCompact.unitInclusion F q u ^ 2) (v ^ 2) ^ 2)
  have he : a * b = z * r := actual_rootTorus_mul F ζ hζ q S P _ _
  have hr : r⁻¹ = b⁻¹ * a⁻¹ * z := by
    apply inv_eq_of_mul_eq_one_left
    rw [mul_assoc, ← he]
    simp [mul_assoc]
  have ha : tau P a⁻¹ V = V := by
    have hh := congrArg (tau P a⁻¹) (hu u)
    rw [← Module.End.mul_apply, ← map_mul] at hh
    simpa [a] using hh.symm
  change tau P r⁻¹ V = _
  rw [hr, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
    actual_centralTorus_action F ζ hζ q S, map_smul, ha, map_smul]
  rfl
private theorem tame_phase (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (π : (LocalField F q)ˣ) (hπ : valuationMap (LocalField F q) (Additive.ofMul π) = -1)
    (u : (KPTameCompact.O F q)ˣ) (v : (LocalField F q)ˣ) :
    KPHilbert.B3 F ζ hζ (Sum.inr q)
      (KPTameCompact.unitInclusion F q u ^ 2) (v ^ 2) ^ 2 =
        KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u) ^
          (8 * valuationMap (LocalField F q) (Additive.ofMul v)) := by
  have hp : valuationMap (LocalField F q) (Additive.ofMul π⁻¹) = 1 := by
    rw [valuationMap_ofMul_inv, hπ]; norm_num
  obtain ⟨w, hw⟩ := exists_integerUnit_mul_uniformizer_zpow (LocalField F q) π⁻¹ hp v
  have hwB := KPTameCompact.B3_units F q ζ hζ ht u w
  have ha := (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1 π
    (KPTameCompact.unitInclusion F q u)
  simp only [KPHilbert.B3_canonical] at hwB ha ⊢
  simp only [map_pow, MonoidHom.pow_apply]
  conv_lhs => rw [← hw]
  simp only [map_mul, MonoidHom.mul_apply, map_zpow, MonoidHom.zpow_apply,
    map_inv, MonoidHom.inv_apply]
  change KPHilbert.finiteThreePairing F ζ hζ q
    (ClassFieldTheory.powerClass (LocalField F q) 3 (KPTameCompact.unitInclusion F q u))
    (ClassFieldTheory.powerClass (LocalField F q) 3 ((integerUnitsToFieldUnits (LocalField F q)) w)) = 1 at hwB
  rw [hwB, one_mul, ← ha]
  simp only [inv_zpow, inv_inv, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

private theorem tame_valunit (u : (KPTameCompact.O F q)ˣ) :
    valuation (LocalField F q) (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 := by
  exact (Valuation.Integers.isUnit_iff_valuation_eq_one
    (Valuation.integer.integers (valuation (LocalField F q)))).mp u.isUnit

theorem tame_noncubic_shell_unit_eigenvalue
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    (S : KPExceptionalRaw.RawFiniteInducingData F ζ hζ q)
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (V : InducedModule P) (H : LocalField F q → ℂ)
    (t : actualTorus F ζ hζ q)
    (hBruhat : ∀ v : (LocalField F q)ˣ,
      ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q →
      H (v : LocalField F q) =
        normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) *
          ((tau P) (((S.openCell P).rootTorus v)⁻¹) V).val t)
    (hUnit : ∀ u : (KPTameCompact.O F q)ˣ,
      tau P ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u)) V = V)
    (n : ℕ) (hn : ¬ 3 ∣ n + 1) :
    ∃ (u : (LocalField F q)ˣ) (c : ℂ),
      valuation (LocalField F q) (u : LocalField F q) = 1 ∧ c ≠ 1 ∧
      ∀ x ∈ negativeValuationShell (LocalField F q) n,
        H ((u : LocalField F q) * x) = c * H x := by
  obtain ⟨πa, hπa⟩ := valuationMap_surjective (LocalField F q) (-1)
  let π := Additive.toMul πa
  have hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ) := by
    have hv : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (π : LocalField F q))) = -1 := by
      change Multiplicative.toAdd (WithZero.unzero _) = -1 at hπa
      rw [WithZero.toAdd_unzero_eq_log] at hπa
      exact hπa
    rw [← hv, WithZero.exp_log]
    simp
  have he : ((8 * ((n + 1 : ℕ) : ℤ) : ℤ) : ZMod 3) ≠ 0 := by
    intro he
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp he
    have hn' : (3 : ℤ) ∣ ((n + 1 : ℕ) : ℤ) := by omega
    exact hn (by exact_mod_cast hn')
  obtain ⟨u, hu⟩ := KPTameTransposeLowShellSupport.exists_tame_cubic_unit_detecting_exponent
    F ζ hζ q ht π hπ (8 * ((n + 1 : ℕ) : ℤ)) he
  let c : ℂ := (ordinaryIota F ζ hζ
    (KPHilbert.B3 F ζ hζ (Sum.inr q) π (KPTameCompact.unitInclusion F q u)) : ℂ) ^
      (8 * ((n + 1 : ℕ) : ℤ))
  refine ⟨KPTameCompact.unitInclusion F q u, c, tame_valunit F q u, hu, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hh
    simp [negativeValuationShell, hh] at hx
  let v : (LocalField F q)ˣ := Units.mk0 x hx0
  have hv : valuationMap (LocalField F q) (Additive.ofMul v) = ((n + 1 : ℕ) : ℤ) := by
    change Multiplicative.toAdd (WithZero.unzero _) = _
    rw [WithZero.toAdd_unzero_eq_log]
    change WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) x)) = _
    rw [hx, WithZero.log_exp]
  have hvint : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q := by
    change valuation (LocalField F q) (↑v⁻¹) ≤ 1
    apply (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q))).mp
    simp only [map_one, Units.val_inv_eq_inv_val, map_inv₀]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) x))⁻¹ ≤ 1
    rw [hx]
    rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have huvint : (((KPTameCompact.unitInclusion F q u * v)⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q := by
    change valuation (LocalField F q) (↑(KPTameCompact.unitInclusion F q u * v)⁻¹) ≤ 1
    simp only [Units.val_inv_eq_inv_val, Units.val_mul, map_inv₀, map_mul, tame_valunit F q u, one_mul]
    simpa only [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀] using hvint
  have hnrm : normPower (LocalField F q) ((KPTameCompact.unitInclusion F q u * v)⁻¹ ^ 2) (1 / 2) =
      normPower (LocalField F q) (v⁻¹ ^ 2) (1 / 2) := by
    unfold normPower localAbs
    congr 4
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mul,
      map_pow, map_inv₀, map_mul, tame_valunit F q u, one_mul]
  change H (↑(KPTameCompact.unitInclusion F q u * v)) = c * H (↑v)
  rw [hBruhat _ huvint, hBruhat _ hvint, hnrm, tame_invmask F ζ hζ q S P V hUnit,
    tame_phase F ζ hζ q ht π hπa u v, hv, map_zpow, Units.val_zpow_eq_zpow_val]
  change _ * (c • tau P (((S.openCell P).rootTorus v)⁻¹) V).val t = _
  change _ * (c * _) = _
  ring

theorem tame_actual_compact_spherical_negative_shell_coordinate
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (q : HeightOneSpectrum (𝓞 F))
    (S : KPExceptionalRaw.RawFiniteInducingData F ζ hζ q)
    (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (P : Polarization S.heisenberg)
    (f : sectionSpace S.borel P .plus 0)
    (hfixed : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P
        (((KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)).comp
          (KPGoodCompactSplitting.kStar F ζ hζ q ht)) k) f = f)
    (n : ℕ) (t : actualTorus F ζ hζ q) :
    (∫ x : LocalField F q in negativeValuationShell (LocalField F q) n,
      (f.val (S.borel.liftedW⁻¹ *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val t ∂μ) =
      if 3 ∣ n + 1 then
        (1 - (residueCardinality (LocalField F q) : ℂ)⁻¹) *
          ((residueCardinality (LocalField F q) : ℂ)⁻¹) ^ ((n + 1) / 3) *
          (f.val 1).val t
      else 0 := by
  classical
  let H : LocalField F q → ℂ := fun x =>
    (f.val (S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val t
  by_cases hn : 3 ∣ n + 1
  · rw [if_pos hn]
    exact NegativeShell.integral_cubic_shell_of_sphere_values
      (LocalField F q) μ hμ H ((f.val 1).val t)
      (fun a v ha hv => actual_compact_spherical_cubic_sphere_coordinate
        F ζ hζ q S ht P f hfixed a v ha hv t) n hn
  · rw [if_neg hn]
    have hBruhat := fun (v : (LocalField F q)ˣ)
        (hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ KPTameCompact.O F q) =>
      actual_compact_spherical_bruhat_coordinate_phase_free
        F ζ hζ q S ht P f hfixed v hv t
    have hUnit : ∀ u : (KPTameCompact.O F q)ˣ,
        tau P ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u))
          (f.val 1) = f.val 1 := by
      intro u
      exact actual_compact_spherical_identity_unit_fixed F ζ hζ q S ht P f
        hfixed (u ^ 2) ((S.openCell P).rootTorus (KPTameCompact.unitInclusion F q u))
        (by rw [← S.torus_full, (S.openCell P).torus_eq,
          KPRankOneOpenCellKernel.hLift, map_pow])
    obtain ⟨u, c, hu, hc, hEigen⟩ :=
      tame_noncubic_shell_unit_eigenvalue
        F ζ hζ q S ht P (f.val 1) H t hBruhat hUnit n hn
    exact NegativeShell.integral_shell_eq_zero_of_unit_eigenfunction
      (LocalField F q) μ H n u hu c hc hEigen

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end

end

section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPRankOneTameSphericalFactor

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
  (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
  (hμ : μ ((valuation (LocalField F q)).integer : Set (LocalField F q)) = 1)

include hμ in

theorem tame_spherical_zero_shells_of_actual_compact
    (ht : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
    (hcompact : (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q)) =
      (actualGoodCompactSplit F ζ hζ q ht).range)
    (φ : compactPicture S.borel P S.iwasawa .plus)
    (hφ : IsSphericalVector (LocalField F q) S.borel P S.iwasawa .plus φ) :
    ∀ n : ℕ, (∫ x in
      KPExceptionalRaw.FiniteSource.GoodSphericalVector.negativeValuationShell
        (LocalField F q) n,
      ((compactTrivialization S.borel P S.iwasawa .plus 0 φ).val
        (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q))).val 1 ∂μ) =
      if 3 ∣ n + 1 then
        (haarMass (LocalField F q) μ : ℂ) *
        (1 - (residueCardinality (LocalField F q) : ℂ)⁻¹) *
        ((residueCardinality (LocalField F q) : ℂ)⁻¹) ^ ((n + 1) / 3) else 0 := by
  intro n
  have hf : ∀ k : KPTameCompact.K0 F q,
      IPlus S.borel P (actualGoodCompactSplit F ζ hζ q ht k)
        (compactTrivialization S.borel P S.iwasawa .plus 0 φ) =
          compactTrivialization S.borel P S.iwasawa .plus 0 φ := by
    intro k
    have hk : actualGoodCompactSplit F ζ hζ q ht k ∈ S.iwasawa.compact.toOpenSubgroup := by
      change _ ∈ (S.iwasawa.compact.toOpenSubgroup : Subgroup (ActualCover F ζ hζ q))
      rw [hcompact]
      exact ⟨k, rfl⟩
    exact hφ.2 0 ⟨_, hk⟩
  have hs := tame_actual_compact_spherical_negative_shell_coordinate
    F ζ hζ q (rawInducingAlias F ζ hζ q S) μ hμ ht P
    (compactTrivialization S.borel P S.iwasawa .plus 0 φ) hf n 1
  have hmass : haarMass (LocalField F q) μ = 1 := by
    simp [haarMass, hμ]
  simp only [rawInducingAlias, hφ.1 0, mul_one] at hs
  simp only [hmass, Complex.ofReal_one, one_mul]
  convert hs using 1

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end

end
