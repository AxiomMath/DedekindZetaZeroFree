module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.FiniteExceptionalRepresentationData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.Spherical.CubicShellDeformation

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace DedekindZetaZeroFree.KPLocalTameIntertwiningBlock
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

private theorem localAbs_injective (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (a b : Kˣ) (hab : localAbs K a = localAbs K b) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (a : K)) =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (b : K)) := by
  have hq : 1 < (residueCardinality K : ℝ) := by
    exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
  have he : WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (a : K))) =
      WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (b : K))) := by
    exact_mod_cast (Real.rpow_right_inj (lt_trans zero_lt_one hq) (ne_of_gt hq)).mp hab
  have ha : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (a : K)) ≠ 0 := by simp
  have hb : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (b : K)) ≠ 0 := by simp
  rw [← WithZero.exp_log ha, ← WithZero.exp_log hb, he]

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
  (S : CanonicalFiniteInducingData F ζ hζ q)

private theorem borel_coordinate_of_compact_factor
    (g : ActualCover F ζ hζ q) (b : S.borel.B)
    (k : S.iwasawa.compact.toOpenSubgroup)
    (hg : g = (b : ActualCover F ζ hζ q) * k) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (S.borel.coordinate (S.borel.retract (S.iwasawa.borelPart g)) : LocalField F q)) =
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (S.borel.coordinate (S.borel.retract b) : LocalField F q)) := by
  let c := (S.iwasawa.borelPart g)⁻¹ * b
  have hc : (c : ActualCover F ζ hζ q) =
      (S.iwasawa.compactPart g : ActualCover F ζ hζ q) * (k : ActualCover F ζ hζ q)⁻¹ := by
    have he := S.iwasawa.decomposition g
    have hh := hg.symm.trans he
    dsimp [c]
    exact eq_mul_inv_iff_mul_eq.mpr (by
      simpa only [mul_assoc, inv_mul_cancel_left] using
        congrArg (fun z : ActualCover F ζ hζ q => (S.iwasawa.borelPart g : ActualCover F ζ hζ q)⁻¹ * z) hh)
  have hmem : (c : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup := by
    rw [hc]
    exact S.iwasawa.compact.toOpenSubgroup.mul_mem (S.iwasawa.compactPart g).property
      (S.iwasawa.compact.toOpenSubgroup.inv_mem k.property)
  have hn := S.iwasawa.intersection_norm c hmem
  apply localAbs_injective
  have he : S.iwasawa.borelPart g * c = b := by dsimp [c]; group
  have hh := congrArg (fun d : S.borel.B => localAbs (LocalField F q) (S.borel.coordinate (S.borel.retract d))) he
  simpa only [map_mul, localAbs_mul, hn, mul_one] using hh

theorem signed_bruhat_iwasawa_coordinate
    (hw : S.borel.liftedW ∈ S.iwasawa.compact.toOpenSubgroup)
    (hn : ∀ x : (valuation (LocalField F q)).integer,
      (S.borel.upperRoot (Multiplicative.ofAdd (x : LocalField F q)) : ActualCover F ζ hζ q) ∈
        S.iwasawa.compact.toOpenSubgroup)
    (v : (LocalField F q)ˣ)
    (hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ (valuation (LocalField F q)).integer) :
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (S.borel.coordinate (S.borel.retract
        (S.iwasawa.borelPart (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) : ActualCover F ζ hζ q)))) : LocalField F q)) =
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) ((v⁻¹ ^ 2 : (LocalField F q)ˣ) : LocalField F q)) := by
  let B := S.openCell S.polarization
  let u : S.borel.B := S.borel.upperRoot (Multiplicative.ofAdd
    (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)))
  let b : S.borel.B := u * (S.borel.torus (B.rootTorus v))⁻¹ *
    (S.borel.torus (B.centralTorus (KPRankOneOpenCellKernel.kappa F ζ hζ q v 0)))⁻¹
  have hu : (u : ActualCover F ζ hζ q) ∈ S.iwasawa.compact.toOpenSubgroup :=
    hn ⟨_, (valuation (LocalField F q)).integer.neg_mem hv⟩
  let k : S.iwasawa.compact.toOpenSubgroup := ⟨S.borel.liftedW⁻¹ * u * S.borel.liftedW⁻¹,
    S.iwasawa.compact.toOpenSubgroup.mul_mem
      (S.iwasawa.compact.toOpenSubgroup.mul_mem (S.iwasawa.compact.toOpenSubgroup.inv_mem hw) hu)
      (S.iwasawa.compact.toOpenSubgroup.inv_mem hw)⟩
  have hb := KPRankOneOpenCellKernel.lifted_bruhat_identity F ζ hζ q v 0
  have hn0 : KPRankOneOpenCellKernel.nLift F ζ hζ q 0 = 1 := by
    simp only [KPRankOneOpenCellKernel.nLift, KPPGLLocalCover.N,
      KPStandardLocalRootLifts.N_zero, map_one]
  simp only [hn0, zero_add, mul_one] at hb
  rw [← B.weyl_eq, ← B.upper_eq, ← B.upper_eq, ← B.upper_eq, ← B.torus_eq, ← B.central_eq] at hb
  have he : S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd (v : LocalField F q)) : ActualCover F ζ hζ q) =
      (b : ActualCover F ζ hζ q) * k := by
    change _ = (b : ActualCover F ζ hζ q) *
      (S.borel.liftedW⁻¹ * (S.borel.upperRoot (Multiplicative.ofAdd
        (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) : ActualCover F ζ hζ q) * S.borel.liftedW⁻¹)
    rw [hb]
    have hi : (u : ActualCover F ζ hζ q) =
        (S.borel.upperRoot (Multiplicative.ofAdd
          ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q)) : ActualCover F ζ hζ q)⁻¹ := by
      change (S.borel.upperRoot (Multiplicative.ofAdd (-((v⁻¹ : (LocalField F q)ˣ) : LocalField F q))) : ActualCover F ζ hζ q) = _
      rw [← Subgroup.coe_inv, ← map_inv]
      rfl
    dsimp [b, k]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hi]
    group
  rw [borel_coordinate_of_compact_factor F ζ hζ q S _ b k he]
  dsimp [b, u]
  simp only [map_mul, map_inv, S.borel.retract_upperRoot, S.borel.retract_torus,
    map_one, B.coordinate_eq, B.central_coordinate, inv_one, one_mul, mul_one, inv_pow]
  congr 2

theorem negative_shell_iwasawa_coordinate
    (hw : S.borel.liftedW ∈ S.iwasawa.compact.toOpenSubgroup)
    (hn : ∀ x : (valuation (LocalField F q)).integer,
      (S.borel.upperRoot (Multiplicative.ofAdd (x : LocalField F q)) : ActualCover F ζ hζ q) ∈
        S.iwasawa.compact.toOpenSubgroup) :
    ∀ n : ℕ, ∀ x ∈
      KPExceptionalRaw.FiniteSource.GoodSphericalVector.negativeValuationShell
        (LocalField F q) n,
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
        (valuation (LocalField F q) (S.borel.coordinate (S.borel.retract
          (S.iwasawa.borelPart (S.borel.liftedW⁻¹ *
            (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q)))) : LocalField F q)) =
          WithZero.exp (-2 * (n + 1 : ℕ) : ℤ) := by
  intro n x hx
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) x) = WithZero.exp (n + 1 : ℤ) at hx
  have hx0 : x ≠ 0 := by
    intro h
    simp [h] at hx
  let v : (LocalField F q)ˣ := Units.mk0 x hx0
  have hv : ((v⁻¹ : (LocalField F q)ˣ) : LocalField F q) ∈ (valuation (LocalField F q)).integer := by
    change valuation (LocalField F q) (x⁻¹) ≤ 1
    apply (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)).toOrderIso.le_iff_le.mp
    change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
      (valuation (LocalField F q) (x⁻¹)) ≤
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q) 1
    rw [map_inv₀, map_inv₀, hx, map_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    omega
  have he := signed_bruhat_iwasawa_coordinate F ζ hζ q S hw hn v hv
  dsimp [v] at he
  rw [he]
  change IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
    (valuation (LocalField F q) (x⁻¹ ^ 2)) = _
  rw [map_pow, map_pow, map_inv₀, map_inv₀, hx, ← WithZero.exp_neg, ← WithZero.exp_nsmul]
  congr 1

end DedekindZetaZeroFree.KPLocalTameIntertwiningBlock

end
