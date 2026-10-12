module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.ReverseRegulatorShellData
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBeta.RamifiedConductorFormula

@[expose] public section

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

def smallBlock (N n : ℕ) : Set (LocalField F q)ˣ :=
  {v | -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
    valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}

def constantKernel (B : Binding F ζ hζ q A P) (V : CenterModule T)
    (r : ℂˣ) (lam : ℂ) (h : H₀) (v : (LocalField F q)ˣ) : ℂ :=
  (B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (reverseRoot F ζ hζ q T A P B r v V).val h *
    normPower (LocalField F q) v lam

theorem eta_norm (B : Binding F ζ hζ q A P) (e : rootsOfUnity 3 F) :
    ‖(B.eta e : ℂ)‖ = 1 := by
  have hp : (B.eta e : ℂ) ^ 3 = 1 := by
    have he : e ^ 3 = 1 := Subtype.ext ((mem_rootsOfUnity 3 _).mp e.property)
    have hh := congrArg (fun u : ℂˣ => (u : ℂ)) (congrArg B.eta he)
    simpa using hh
  have hh := congrArg norm hp
  simp only [norm_pow, norm_one] at hh
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide)).mp hh

theorem centerTorus_plus_central_scalar (c : T.C) (V : CenterModule T) :
    centerTorus F ζ hζ q T A .plus (c : H₀) V = (T.ω c : ℂ) • V := by
  apply Subtype.ext
  funext x
  change V.val (x * (c : H₀)) = (T.ω c : ℂ) * V.val x
  rw [Subgroup.mem_center_iff.mp (T.central c.property) x]
  exact V.property c x

theorem centerTorus_minus_cube_scalar (y : (LocalField F q)ˣ) (V : CenterModule T) :
    centerTorus F ζ hζ q T A .minus (A.cubeLift y : H₀) V =
      normPower (LocalField F q) (y ^ 3) (-(1 / 6)) • V := by
  change centerTorus F ζ hζ q T A .plus (A.weyl (A.cubeLift y : H₀)) V = _
  rw [← A.weylCenter_coe, A.weyl_cube, centerTorus_plus_central_scalar, A.exceptional_cube]
  congr 1
  unfold normPower
  have hi (u : (LocalField F q)ˣ) :
      localAbs (LocalField F q) u⁻¹ = (localAbs (LocalField F q) u)⁻¹ := by
    have hh := localAbs_mul (LocalField F q) u u⁻¹
    rw [mul_inv_cancel, localAbs_one] at hh
    exact eq_inv_of_mul_eq_one_right hh.symm
  rw [inv_pow, hi, Real.log_inv]
  simp

private theorem projection_kernel (B : Binding F ζ hζ q A P)
    (g : Cover F ζ hζ q) (hg : A.projection g = 1) :
    ∃ e, KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e = g := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
  induction g using QuotientGroup.induction_on with | _ g =>
    change A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) = 1 at hg
    rw [B.projection_eq] at hg
    obtain ⟨u, hu⟩ := (show ∃ u, Matrix.GeneralLinearGroup.scalar (Fin 2) u = g.g from by
      simpa only [Matrix.GeneralLinearGroup.center_eq_range_scalar, MonoidHom.mem_range] using
        Matrix.ProjGenLinGroup.mk_eq_one.mp hg)
    have hp : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
        (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) = 1 := by
      rw [KPPGLLocalCover.projection_coverQuotient]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨u, hu⟩
    change (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) ∈
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).range
    rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
    exact hp

private theorem coordinate_kernel (B : Binding F ζ hζ q A P)
    (a : H₀) (ha : A.coordinate a = 1) : ∃ e, B.centralTorus e = a := by
  obtain ⟨e, he⟩ := projection_kernel F ζ hζ q T A P B (A.torus a)
    (by
      rw [A.torus_projection, ha]
      have hd : KubotaRankTwo.d (LocalField F q) 1 1 = 1 := by
        apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.coe_d]
      rw [hd, map_one])
  refine ⟨e, A.torus_injective (Subtype.ext ?_)⟩
  exact (B.central_eq e).trans he

private theorem root_decomposition (B : Binding F ζ hζ q A P)
    (v r y : (LocalField F q)ˣ) (hv : v = r * y ^ 3) :
    ∃ e, B.rootTorus v = B.centralTorus e * B.rootTorus r * (A.cubeLift (y ^ 2) : H₀) := by
  let a := B.rootTorus v * (B.rootTorus r * (A.cubeLift (y ^ 2) : H₀))⁻¹
  have ha : A.coordinate a = 1 := by
    simp only [a, map_mul, map_inv, B.coordinate_eq, A.cube_coordinate]
    rw [hv]
    simp only [mul_pow, ← pow_mul]
    ring_nf
    simp
  obtain ⟨e, he⟩ := coordinate_kernel F ζ hζ q T A P B a ha
  refine ⟨e, ?_⟩
  rw [he, mul_assoc]
  simp [a, mul_assoc]

private theorem localAbs_pow (v : (LocalField F q)ˣ) (n : ℕ) :
    localAbs (LocalField F q) (v ^ n) = localAbs (LocalField F q) v ^ n := by
  induction n with
  | zero => simp [localAbs_one]
  | succ n ih => rw [pow_succ, localAbs_mul, ih, pow_succ]

private theorem norm_normPower (v : (LocalField F q)ˣ) (w : ℂ) :
    ‖normPower (LocalField F q) v w‖ = (localAbs (LocalField F q) v).rpow w.re := by
  rw [normPower, Complex.norm_exp, Real.rpow_eq_pow, Real.rpow_def_of_pos (localAbs_pos _ _)]
  simp [Complex.mul_re, mul_comm]

private theorem center_root_norm (B : Binding F ζ hζ q A P)
    (v u y : (LocalField F q)ˣ) (hv : v = u * y ^ 3)
    (V : CenterModule T) (h : H₀) :
    ∃ e : rootsOfUnity 3 F,
      ‖(centerTorus F ζ hζ q T A .minus (B.rootTorus v) V).val h‖ =
        (localAbs (LocalField F q) v).rpow (-(1 / 3)) *
        ((localAbs (LocalField F q) u).rpow (1 / 3) *
          ‖(centerTorus F ζ hζ q T A .minus (B.centralTorus e * B.rootTorus u) V).val h‖) := by
  obtain ⟨e, he⟩ := root_decomposition F ζ hζ q T A P B v u y hv
  refine ⟨e, ?_⟩
  rw [he, map_mul, Module.End.mul_apply, centerTorus_minus_cube_scalar, map_smul]
  change ‖normPower (LocalField F q) ((y ^ 2) ^ 3) (-(1 / 6)) *
    (centerTorus F ζ hζ q T A .minus (B.centralTorus e * B.rootTorus u) V).val h‖ = _
  rw [norm_mul, norm_normPower]
  have hp := localAbs_pos (LocalField F q) y
  have hu := localAbs_pos (LocalField F q) u
  have hx : localAbs (LocalField F q) v = localAbs (LocalField F q) u * localAbs (LocalField F q) y ^ 3 := by
    rw [hv, localAbs_mul, localAbs_pow]
  rw [localAbs_pow, localAbs_pow, hx]
  norm_num
  simp only [Real.rpow_eq_pow, Real.rpow_def_of_pos (mul_pos hu (pow_pos hp _)),
    Real.rpow_def_of_pos (pow_pos (pow_pos hp 2) 3), Real.rpow_def_of_pos hu,
    Real.log_mul (ne_of_gt hu) (ne_of_gt (pow_pos hp 3)), Real.log_pow]
  rw [← mul_assoc (Real.exp _) (Real.exp _) _, ← Real.exp_add]
  congr 1
  congr 1 <;> ring

set_option maxHeartbeats 800000 in
private theorem center_root_bound (B : Binding F ζ hζ q A P)
    (V : CenterModule T) (h : H₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : (LocalField F q)ˣ,
      ‖(centerTorus F ζ hζ q T A .minus (B.rootTorus v) V).val h‖ ≤
        C * (localAbs (LocalField F q) v).rpow (-(1 / 3)) := by
  classical
  let K := LocalField F q
  let X := Kˣ ⧸ CubicCharacters.cubes Kˣ
  letI : Finite X := ClassFieldTheory.powerClassGroup_finite K 3 (by norm_num)
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  let proj : Kˣ →* X := QuotientGroup.mk' _
  let u : X → Kˣ := Function.surjInv (QuotientGroup.mk'_surjective (CubicCharacters.cubes Kˣ))
  have hu (d : X) : proj (u d) = d := Function.surjInv_eq _ d
  let b : X × rootsOfUnity 3 F → ℝ := fun de =>
    (localAbs K (u de.1)).rpow (1 / 3) *
      ‖(centerTorus F ζ hζ q T A .minus (B.centralTorus de.2 * B.rootTorus (u de.1)) V).val h‖
  let C : ℝ := ∑ de, b de
  have hb (de : X × rootsOfUnity 3 F) : 0 ≤ b de :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt (localAbs_pos K (u de.1))) _) (norm_nonneg _)
  refine ⟨C, Finset.sum_nonneg (fun de _ => hb de), ?_⟩
  intro v
  have heq : (v : X) = (u (proj v) : X) := (hu (proj v)).symm
  obtain ⟨y, hy⟩ := (QuotientGroup.eq_iff_div_mem.mp heq : v / u (proj v) ∈ CubicCharacters.cubes Kˣ)
  have hv : v = u (proj v) * y ^ 3 := by
    change y ^ 3 = v / u (proj v) at hy
    rw [hy, mul_comm, div_mul_cancel]
  obtain ⟨e, he⟩ := center_root_norm F ζ hζ q T A P B v (u (proj v)) y hv V h
  rw [he]
  have hle : b (proj v, e) ≤ C :=
    Finset.single_le_sum (fun de _ => hb de) (Finset.mem_univ (proj v, e))
  calc
    _ ≤ (localAbs K v).rpow (-(1 / 3)) * C :=
      mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg (le_of_lt (localAbs_pos K v)) _)
    _ = C * (localAbs K v).rpow (-(1 / 3)) := mul_comm _ _

private theorem kernel_power_bound (B : Binding F ζ hζ q A P)
    (V : CenterModule T) (r : ℂˣ) (lam : ℂ) (h : H₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : (LocalField F q)ˣ,
      ‖constantKernel F ζ hζ q T A P B V r lam h v‖ ≤
        C * (localAbs (LocalField F q) v).rpow
          (lam.re - 2 * (additiveParameter F q r).re - 1 / 3) := by
  obtain ⟨C, hC, hb⟩ := center_root_bound F ζ hζ q T A P B V h
  refine ⟨C, hC, ?_⟩
  intro v
  change ‖(B.eta (kappa F ζ hζ q v 0) : ℂ) *
    (normPower (LocalField F q) (v ^ 2) (-additiveParameter F q r) *
      (centerTorus F ζ hζ q T A .minus (B.rootTorus v) V).val h) *
    normPower (LocalField F q) v lam‖ ≤ _
  rw [norm_mul, norm_mul, eta_norm, one_mul, norm_mul, norm_normPower,
    norm_normPower, localAbs_pow, Complex.neg_re]
  calc
    _ ≤ ((localAbs (LocalField F q) v ^ 2).rpow (-(additiveParameter F q r).re) *
      (C * (localAbs (LocalField F q) v).rpow (-(1 / 3)))) *
        (localAbs (LocalField F q) v).rpow lam.re := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hb v)
          (Real.rpow_nonneg (sq_nonneg _) _))
        (Real.rpow_nonneg (le_of_lt (localAbs_pos _ v)) _)
    _ = _ := by
      have hp := localAbs_pos (LocalField F q) v
      simp only [Real.rpow_eq_pow, Real.rpow_def_of_pos hp,
        Real.rpow_def_of_pos (pow_pos hp 2), Real.log_pow]
      rw [mul_left_comm _ C, mul_assoc C, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

private theorem ratio_exp (r : ℂˣ) (lam : ℂ) :
    ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ =
      Real.exp (-3 * (Real.log (residueCardinality (LocalField F q) : ℝ) *
        (lam.re - 2 * (additiveParameter F q r).re - 1 / 3))) := by
  let a : ℝ := residueCardinality (LocalField F q)
  have ha : 1 < a := by
    dsimp [a]
    exact_mod_cast (Finite.one_lt_card : 1 < residueCardinality (LocalField F q))
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hlog : Real.log a ≠ 0 := ne_of_gt (Real.log_pos ha)
  have hr : 0 < ‖(r : ℂ)‖ := norm_pos_iff.mpr r.ne_zero
  have hz : (additiveParameter F q r).re = -Real.log ‖(r : ℂ)‖ / Real.log a := by
    simp only [additiveParameter, Complex.div_ofReal_re, Complex.neg_re, Complex.log_re]
    rfl
  have hn : ‖(residueCardinality (LocalField F q) : ℂ)‖ = a := by
    rw [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  have hQ : ‖Q F q lam‖ = Real.exp (-lam.re * Real.log a) := by
    simp only [Q, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero]
    rfl
  rw [norm_mul, norm_inv, norm_pow, t, norm_mul, norm_inv, norm_pow, hn, hQ]
  rw [← Real.exp_nat_mul, ← Real.exp_log ha0, ← Real.exp_log hr,
    ← Real.exp_nat_mul, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_neg, ← Real.exp_add, hz]
  simp only [Real.log_exp]
  congr 1
  dsimp [a] at hlog ⊢
  field_simp
  <;> ring

theorem constantKernel_geometric_bound (B : Binding F ζ hζ q A P)
    (V : CenterModule T) (N : ℕ) (r : ℂˣ) (lam : ℂ) (h : H₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ v ∈ smallBlock F q N n,
      ‖constantKernel F ζ hζ q T A P B V r lam h v‖ ≤
        C * ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n := by
  obtain ⟨C, hC, hb⟩ := kernel_power_bound F ζ hζ q T A P B V r lam h
  let a : ℝ := residueCardinality (LocalField F q)
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (lt_trans Nat.zero_lt_one
      (Finite.one_lt_card : 1 < residueCardinality (LocalField F q)))
  let k : ℝ := lam.re - 2 * (additiveParameter F q r).re - 1 / 3
  let b : ℝ := Real.log a * k
  refine ⟨C * Real.exp (((N : ℝ) + 3) * |b|),
    mul_nonneg hC (Real.exp_pos _).le, ?_⟩
  intro n v hv
  have hv' : -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
      valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ) := hv
  have hlo : -((N : ℝ) + 3) ≤ (valuationIndex F q v : ℝ) + 3 * n := by
    have hh := (Int.cast_le (R := ℝ)).mpr hv'.1
    push_cast at hh
    linarith
  have hhi : (valuationIndex F q v : ℝ) + 3 * n ≤ (N : ℝ) + 3 := by
    have hh := (Int.cast_lt (R := ℝ)).mpr hv'.2
    push_cast at hh
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hbd : ((valuationIndex F q v : ℝ) + 3 * n) * b ≤ ((N : ℝ) + 3) * |b| := by
    calc
      _ ≤ |((valuationIndex F q v : ℝ) + 3 * n) * b| := le_abs_self _
      _ = |(valuationIndex F q v : ℝ) + 3 * n| * |b| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (abs_le.mpr ⟨hlo, hhi⟩) (abs_nonneg _)
  have heq : (localAbs (LocalField F q) v).rpow k =
      Real.exp ((((valuationIndex F q v : ℝ) + 3 * n) * b)) *
        ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n := by
    rw [ratio_exp F q r lam, ← Real.exp_nat_mul, ← Real.exp_add]
    change (a ^ (valuationIndex F q v : ℝ)).rpow k = _
    simp only [Real.rpow_eq_pow, Real.rpow_def_of_pos (Real.rpow_pos_of_pos ha _),
      Real.log_rpow ha]
    congr 1
    dsimp [b, k, a]
    ring
  calc
    _ ≤ C * (localAbs (LocalField F q) v).rpow k := hb v
    _ = C * (Real.exp (((valuationIndex F q v : ℝ) + 3 * n) * b) *
      ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n) := by rw [heq]
    _ ≤ C * (Real.exp (((N : ℝ) + 3) * |b|) *
      ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbd) (pow_nonneg (norm_nonneg _) _)) hC
    _ = _ := (mul_assoc _ _ _).symm

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

end

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

open scoped NumberField Valued ValuativeRel Topology
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private lemma root_cont (B : Binding F ζ hζ q A P) : Continuous B.rootTorus := by
 have hc := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ q _
   (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2
 have ht : Continuous (fun v => A.torus (B.rootTorus v)) := by
   apply Continuous.subtype_mk
   change Continuous (fun v => (A.torus (B.rootTorus v) : Cover F ζ hζ q))
   simp_rw [B.torus_eq]
   exact hc.comp (continuous_id.pow 2)
 have he : B.rootTorus = fun v => A.retract (A.torus (B.rootTorus v)) := by
   funext v; exact (A.retract_torus _).symm
 rw [he]
 exact A.retract_continuous.comp ht
private lemma kappa_lc : IsLocallyConstant (fun v : (LocalField F q)ˣ => kappa F ζ hζ q v 0) := by
 let m := KPAdelicCoverRestrictedProduct.depth F ζ hζ q
 have hm := KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q
 letI := KPLocalChartTopology.translatedTopology F ζ hζ q m
 letI := (KPLocalChartTopology.finite_topological_group F ζ hζ q m hm).2.2
 have hn := KPStandardLocalRootLifts.finite_N_continuous F ζ hζ q m hm
 have ha := KPStandardLocalRootLifts.finite_A_continuous F ζ hζ q m hm
 have hs := (KPScalarSplitCentral.finite_continuous_closed F ζ hζ q m hm).1
 have hl : Continuous (fun v : (LocalField F q)ˣ => bruhatLeft F ζ hζ q v 0) :=
   (((continuous_const.mul (hn.comp (Units.continuous_val.comp continuous_inv).neg)).mul continuous_const).mul continuous_const)
 have hr : Continuous (fun v : (LocalField F q)ˣ => bruhatRight F ζ hζ q v 0) :=
   (hs.comp continuous_inv).mul
     (((ha.comp (continuous_id.pow 2)).mul (hn.comp (Units.continuous_val.comp continuous_inv))).mul continuous_const |>.mul
       (hn.comp (continuous_const.add Units.continuous_val)))
 have hq : Continuous (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)) := QuotientGroup.continuous_mk
 have he (v : (LocalField F q)ˣ) :
     KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
       (bruhatLeft F ζ hζ q v 0 * (bruhatRight F ζ hζ q v 0)⁻¹) =
     KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v 0) := by
   rw [raw_bruhat_identity, mul_inv_cancel_right]
   rfl
 have hc : Continuous (fun v : (LocalField F q)ˣ =>
     KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v 0)) := by
   simp_rw [← he]
   exact hq.comp (hl.mul hr.inv)
 letI : Group (KPPGLLocalCover.LocalPGL2 F (Sum.inr q)) :=
   @QuotientGroup.Quotient.group _ _ (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))
    (KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q))
 letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
 letI := (KPPGLLocalCover.finite_discrete_kernel F ζ hζ q m hm).1
 have hsub : Continuous (fun v : (LocalField F q)ˣ =>
   (⟨KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (kappa F ζ hζ q v 0),
     by rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection]; exact ⟨_, rfl⟩⟩ :
     (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).ker)) := hc.subtype_mk _
 have hh := (IsLocallyConstant.iff_continuous _).mpr hsub
 rw [IsLocallyConstant.iff_eventually_eq] at hh ⊢
 intro v
 filter_upwards [hh v] with w hw
 exact KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q) (congrArg Subtype.val hw)

private lemma center_lc (f : CenterModule T) : IsLocallyConstant f.val := by
 let J : Subgroup H₀ := T.ω.toMonoidHom.ker.map T.C.subtype
 have hJ : IsOpen (J : Set H₀) := by
   exact T.center_open.isOpenMap_subtype_val _ T.character_kernel_open
 rw [IsLocallyConstant.iff_eventually_eq]
 intro h
 have hc : Continuous (fun y : H₀ => y * h⁻¹) := continuous_id.mul continuous_const
 have hn : ∀ᶠ y in nhds h, y * h⁻¹ ∈ J :=
   hc.continuousAt.preimage_mem_nhds (by simpa using hJ.mem_nhds J.one_mem)
 filter_upwards [hn] with y hy
 obtain ⟨c, hc, he⟩ := hy
 have hw : T.ω c = 1 := hc
 have hf := f.property c h
 change (c : H₀) = y * h⁻¹ at he
 have hey : (c : H₀) * h = y := by rw [he]; group
 simpa [hey, hw] using hf

private lemma normPower_lc (s : ℂ) :
    IsLocallyConstant (fun v : (LocalField F q)ˣ => normPower (LocalField F q) v s) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro v
  have hc := (valuation (LocalField F q)).locally_const
    (x := (v : LocalField F q)) (by simp)
  have hn := Units.continuous_val.continuousAt.preimage_mem_nhds hc
  filter_upwards [hn] with w hw
  change valuation (LocalField F q) (w : LocalField F q) =
    valuation (LocalField F q) (v : LocalField F q) at hw
  simp only [normPower, localAbs, hw]

theorem constantKernel_stronglyMeasurable (B : Binding F ζ hζ q A P)
    (V : CenterModule T) (r : ℂˣ) (lam : ℂ) (h : H₀) :
    StronglyMeasurable (constantKernel F ζ hζ q T A P B V r lam h) := by
  letI : BorelSpace (LocalField F q)ˣ := ⟨by
    change MeasurableSpace.comap Units.val ‹MeasurableSpace (LocalField F q)› =
      borel (LocalField F q)ˣ
    rw [(Units.isEmbedding_val₀ (G₀ := LocalField F q)).eq_induced, borel_comap]
    congr 1
    exact BorelSpace.measurable_eq⟩
  have hr := root_cont F ζ hζ q T A P B
  have hv := (center_lc T V).comp_continuous
    (continuous_const.mul (A.weyl.continuous.comp hr) :
      Continuous (fun v : (LocalField F q)ˣ => h * A.weyl (B.rootTorus v)))
  have hk := (kappa_lc F ζ hζ q).comp (fun e => (B.eta e : ℂ))
  have hz := (normPower_lc F q (-additiveParameter F q r)).comp_continuous
    (continuous_id.pow 2)
  have hl := normPower_lc F q lam
  have hc := ((hk.continuous.mul (hz.continuous.mul hv.continuous)).mul hl.continuous)
  change StronglyMeasurable (fun v : (LocalField F q)ˣ =>
    (B.eta (kappa F ζ hζ q v 0) : ℂ) *
      (normPower (LocalField F q) (v ^ 2) (-additiveParameter F q r) *
        V.val (h * A.weyl (B.rootTorus v))) * normPower (LocalField F q) v lam)
  exact hc.stronglyMeasurable

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

end

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPRankOneOpenCellKernel KPRankOneReverseRegulatorShellsRaw

set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

private theorem smallBlock_units_borel (K : Type*) [Field K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] [MeasurableSpace K] [BorelSpace K] : BorelSpace Kˣ := by
  constructor
  change MeasurableSpace.comap Units.val ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K),
    (Units.isEmbedding_val₀ (G₀ := K)).isInducing.eq_induced, borel_comap]

theorem smallBlock_measurableSet (N n : ℕ) :
    MeasurableSet (smallBlock F q N n) := by
  letI : BorelSpace (LocalField F q)ˣ := smallBlock_units_borel (LocalField F q)
  have hc : IsLocallyConstant (valuationIndex F q) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro v
    have hv : valuation (LocalField F q) (v : LocalField F q) ≠ 0 :=
      (valuation (LocalField F q)).ne_zero_iff.mpr v.ne_zero
    have he := (valuation (LocalField F q)).locally_const hv
    filter_upwards [Units.continuous_val.continuousAt.preimage_mem_nhds he] with w hw
    exact congrArg (fun a => WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt
      (LocalField F q) a)) hw
  have hset : smallBlock F q N n = {v : (LocalField F q)ˣ |
      -((N + 3 * n + 3 : ℕ) : ℤ) ≤ valuationIndex F q v ∧
      valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)} := rfl
  rw [hset]
  exact (isClosed_le continuous_const hc.continuous).measurableSet.inter
    (isOpen_lt hc.continuous continuous_const).measurableSet

end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

end

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPRankOneOpenCellKernel KPRankOneReverseRegulatorShellsRaw

set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

theorem smallBlock_uniform_mass (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N n : ℕ,
      multiplicativeMeasure F q μ (smallBlock F q N n) ≤ ENNReal.ofReal M := by
  classical
  let qK : ℝ := (CubicUnitCharacters.residueCard (LocalField F q) : ℝ)
  let A : LocalField F q → ℝ := KPCubicHaar.abs (LocalField F q)
  let ν : Measure (LocalField F q) := μ.withDensity (fun x => ENNReal.ofReal ((A x)⁻¹))
  let O : Set (LocalField F q) := ((valuation (LocalField F q)).integer : Set (LocalField F q))
  have hAv : ∀ v : (LocalField F q)ˣ, A (v : LocalField F q) = qK ^ (valuationIndex F q v) := by
    intro v
    simp only [A, qK, KPCubicHaar.abs, valuationIndex, if_neg v.ne_zero]
    rfl
  have hshell : ∀ k : ℤ, ν {x : LocalField F q | A x = qK ^ k} ≤ μ O := by
    intro k
    have := KPRamifiedBetaConductorSeries.multiplicative_shell_mass_le (LocalField F q) μ k
    simpa only [A, ν, qK, O, KPCubicHaar.abs, KPCubicUnitIndices.residueCard,
      CubicUnitCharacters.residueCard] using this
  have hmeasA : Measurable A := KPRamifiedBetaConductorSeries.normalizedAbs_measurable (LocalField F q)
  have hcomap : multiplicativeMeasure F q μ =
      Measure.comap (Units.val : (LocalField F q)ˣ → LocalField F q) ν := rfl
  have hO : μ O ≠ ⊤ :=
    (IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1).measure_lt_top.ne
  refine ⟨3 * (μ O).toReal, by positivity, ?_⟩
  intro N n
  let S : ℤ → Set (LocalField F q) := fun k => {x | A x = qK ^ k}
  let k1 : ℤ := -((N + 3 * n + 3 : ℕ) : ℤ)
  let k2 : ℤ := -((N + 3 * n + 2 : ℕ) : ℤ)
  let k3 : ℤ := -((N + 3 * n + 1 : ℕ) : ℤ)
  let T : Set (LocalField F q) := S k1 ∪ S k2 ∪ S k3
  have hmeasS : ∀ k : ℤ, MeasurableSet (S k) := fun k => hmeasA (measurableSet_singleton _)
  have hmeasT : MeasurableSet T := ((hmeasS k1).union (hmeasS k2)).union (hmeasS k3)
  have hmem : ∀ v : (LocalField F q)ˣ, v ∈ smallBlock F q N n → (v : LocalField F q) ∈ T := by
    intro v hv
    rw [smallBlock] at hv
    obtain ⟨h1, h2⟩ := hv
    have hS : ∀ k : ℤ, valuationIndex F q v = k → (v : LocalField F q) ∈ S k := by
      intro k hk
      simp only [S, A]
      rw [← hk]
      exact hAv v
    have hcases : valuationIndex F q v = k1 ∨ valuationIndex F q v = k2 ∨
        valuationIndex F q v = k3 := by
      simp only [k1, k2, k3] at *
      omega
    rcases hcases with h | h | h
    · exact Or.inl (Or.inl (hS k1 h))
    · exact Or.inl (Or.inr (hS k2 h))
    · exact Or.inr (hS k3 h)
  have hsub : smallBlock F q N n ⊆ Units.val ⁻¹' T := fun v hv => hmem v hv
  have hpre : MeasurableSet (Units.val ⁻¹' T) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨T, hmeasT, rfl⟩
  have h2 : multiplicativeMeasure F q μ (Units.val ⁻¹' T) ≤ ν T := by
    rw [hcomap]
    refine le_trans (Measure.comap_apply_le (f := (Units.val : (LocalField F q)ˣ → LocalField F q))
      (μ := ν) hpre.nullMeasurableSet) ?_
    exact measure_mono (Set.image_preimage_subset _ _)
  have hT : ν T ≤ 3 * μ O := by
    have h12 : ν (S k1 ∪ S k2) ≤ μ O + μ O :=
      (measure_union_le (S k1) (S k2)).trans (add_le_add (hshell k1) (hshell k2))
    have h123 : ν T ≤ (μ O + μ O) + μ O := by
      simp only [T]
      exact (measure_union_le (S k1 ∪ S k2) (S k3)).trans (add_le_add h12 (hshell k3))
    refine h123.trans (le_of_eq ?_)
    ring
  have hfin : (3 : ENNReal) * μ O = ENNReal.ofReal (3 * (μ O).toReal) := by
    have h3 : (3 : ENNReal) = ENNReal.ofReal 3 := by norm_num
    rw [h3]
    conv_lhs => rw [← ENNReal.ofReal_toReal hO]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
  calc multiplicativeMeasure F q μ (smallBlock F q N n)
      ≤ multiplicativeMeasure F q μ (Units.val ⁻¹' T) := measure_mono hsub
    _ ≤ ν T := h2
    _ ≤ 3 * μ O := hT
    _ = ENNReal.ofReal (3 * (μ O).toReal) := hfin

end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail.AbsoluteBlock

end

section
namespace DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail

open scoped NumberField Valued ValuativeRel
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalStoneVonNeumann KPLocalPrincipalSeries KPRankOneShellContinuation
open KPRankOneOpenCellKernel KPRankOneCenterInducedDiagonalComparison
open KPRankOneReverseRegulatorShellsRaw

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
variable [ValuativeRel (LocalField F q)] [IsNonarchimedeanLocalField (LocalField F q)]
variable {H₀ D : Type} [Group H₀] [TopologicalSpace H₀] [IsTopologicalGroup H₀]
  [CommGroup D] [Finite D] [DecidableEq D]
variable (T : LocalHeisenbergData H₀ D)
variable (A : LocalBorelData (K := LocalField F q) (G := Cover F ζ hζ q) T)
variable (P : Polarization T)
variable [MeasurableSpace (LocalField F q)] [BorelSpace (LocalField F q)]

theorem reverseIntegrand_on_small_block (I : IwasawaData A) (μ : Measure (LocalField F q))
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) (hprofile : ∀ (r : ℂˣ), IsRegular F q r →
      ∀ v ∈ smallRegion F q N,
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q (v : LocalField F q)) =
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q 0))
    (r : ℂˣ) (hr : IsRegular F q r) (lam : ℂ) (h : H₀) (n : ℕ)
    (v : (LocalField F q)ˣ)
    (hv : v ∈ {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
      valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}) :
    reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v =
      (B.eta (kappa F ζ hζ q v 0) : ℂ) *
        (reverseRoot F ζ hζ q T A P B r v
          ((forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
            (openCoordinate F ζ hζ q 0))).val h * normPower (LocalField F q) v lam := by
  have hs : v ∈ smallRegion F q N := by
    change valuationIndex F q v < -(N : ℤ)
    have hu := hv.2
    push_cast at hu
    omega
  unfold reverseIntegrand
  rw [hprofile r hr v hs]

theorem absolute_block_majorant (I : IwasawaData A) (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
    (J : CenterStandardFamily F ζ hζ q T A I μ) (B : Binding F ζ hζ q A P)
    (rep : D → H₀) (hrep : ∀ d, T.π (rep d) = d) (d : D)
    (φ : LocalField F q → ℂ) (hφ : IsLocallyConstant φ) (hcφ : HasCompactSupport φ)
    (N : ℕ) (hprofile : ∀ (r : ℂˣ), IsRegular F q r →
      ∀ v ∈ smallRegion F q N,
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q (v : LocalField F q)) =
        (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
          (openCoordinate F ζ hζ q 0))
    (r : ℂˣ) (hr : IsRegular F q r) (lam : ℂ)
    (hlam : ConvergenceRegion F q r lam) (h : H₀) :
    ∃ M : ℝ,
      (∀ n : ℕ, IntegrableOn
        (reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h)
        {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
          valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)}
        (multiplicativeMeasure F q μ)) ∧
      (∀ n : ℕ, (∫ v in {v : (LocalField F q)ˣ | -((N + 3 * n + 3 : ℕ) : ℤ) ≤
          valuationIndex F q v ∧ valuationIndex F q v < -((N + 3 * n : ℕ) : ℤ)},
        ‖reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h v‖ ∂multiplicativeMeasure F q μ) ≤
        M * ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖ ^ n) := by
  let V : CenterModule T :=
    (forwardSection F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r).val
      (openCoordinate F ζ hζ q 0)
  let f := reverseIntegrand F ζ hζ q T A P I μ J B rep hrep d φ hφ hcφ r lam h
  let k := AbsoluteBlock.constantKernel F ζ hζ q T A P B V r lam h
  let ν := multiplicativeMeasure F q μ
  let ρ := ‖(t F q (r : ℂ))⁻¹ * Q F q lam ^ 3‖
  change ∃ M : ℝ,
    (∀ n : ℕ, IntegrableOn f (AbsoluteBlock.smallBlock F q N n) ν) ∧
    (∀ n : ℕ, (∫ v in AbsoluteBlock.smallBlock F q N n, ‖f v‖ ∂ν) ≤ M * ρ ^ n)
  obtain ⟨C, hC, hbound⟩ :=
    AbsoluteBlock.constantKernel_geometric_bound F ζ hζ q T A P B V N r lam h
  obtain ⟨M, hM, hmass⟩ := AbsoluteBlock.smallBlock_uniform_mass F q μ
  have heq (n : ℕ) : Set.EqOn k f (AbsoluteBlock.smallBlock F q N n) := by
    intro v hv
    exact (reverseIntegrand_on_small_block F ζ hζ q T A P I μ J B rep hrep d
      φ hφ hcφ N hprofile r hr lam h n v hv).symm
  have hfinite (n : ℕ) : ν (AbsoluteBlock.smallBlock F q N n) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass N n)
  have hmassReal (n : ℕ) : (ν (AbsoluteBlock.smallBlock F q N n)).toReal ≤ M := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass N n)).trans_eq
      (ENNReal.toReal_ofReal hM)
  have hboundf (n : ℕ) (v : (LocalField F q)ˣ)
      (hv : v ∈ AbsoluteBlock.smallBlock F q N n) : ‖f v‖ ≤ C * ρ ^ n := by
    rw [← heq n hv]
    exact hbound n v hv
  have hint (n : ℕ) : IntegrableOn f (AbsoluteBlock.smallBlock F q N n) ν := by
    have hk : IntegrableOn k (AbsoluteBlock.smallBlock F q N n) ν :=
      IntegrableOn.of_bound (lt_top_iff_ne_top.mpr (hfinite n))
        (AbsoluteBlock.constantKernel_stronglyMeasurable F ζ hζ q T A P B V r lam h).aestronglyMeasurable
        (C * ρ ^ n)
        (ae_restrict_of_forall_mem (AbsoluteBlock.smallBlock_measurableSet F q N n)
          (hbound n))
    exact hk.congr_fun (heq n) (AbsoluteBlock.smallBlock_measurableSet F q N n)
  refine ⟨M * C, hint, fun n => ?_⟩
  calc
    (∫ v in AbsoluteBlock.smallBlock F q N n, ‖f v‖ ∂ν) ≤
        ∫ _v in AbsoluteBlock.smallBlock F q N n, C * ρ ^ n ∂ν :=
      setIntegral_mono_on (hint n).norm (integrableOn_const (hfinite n))
        (AbsoluteBlock.smallBlock_measurableSet F q N n) (hboundf n)
    _ = (ν (AbsoluteBlock.smallBlock F q N n)).toReal * (C * ρ ^ n) := by
      simp [integral_const, Measure.real_def, smul_eq_mul]
    _ ≤ M * (C * ρ ^ n) := mul_le_mul_of_nonneg_right (hmassReal n)
      (mul_nonneg hC (pow_nonneg (norm_nonneg _) n))
    _ = (M * C) * ρ ^ n := (mul_assoc M C (ρ ^ n)).symm

end
end DedekindZetaZeroFree.KPRankOneReverseLaurentShellExpansion.SmallTail

end
