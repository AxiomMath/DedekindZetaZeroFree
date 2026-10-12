module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.DiagonalBorelCoordinatesAndCoefficientNorms
public import DedekindZetaZeroFree.Metaplectic.Intertwining.RootSupportAndAugmentationTransport

@[expose] public section

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
open scoped Classical
open MeasureTheory ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
 [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

theorem exterior_abs_measurable : Measurable (KPCubicHaar.abs K) := by
 unfold KPCubicHaar.abs
 simpa only [KPCubicUnitIndices.residueCard, CubicUnitCharacters.residueCard] using
   KPRamifiedBetaConductorSeries.normalizedAbs_measurable K

private theorem exterior_shells : {u : K | 1 ≤ KPCubicHaar.abs K u} =
 ⋃ n : ℕ, {u : K | KPCubicHaar.abs K u = (Nat.card 𝓀[K] : ℝ)^n} := by
 ext u
 simp only [Set.mem_iUnion, Set.mem_setOf_eq]
 constructor
 · intro hu
   have hu0 : u ≠ 0 := by intro h; subst u; simp [KPCubicHaar.abs] at hu; norm_num at hu
   let z := WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K u))
   have he : KPCubicHaar.abs K u = (Nat.card 𝓀[K] : ℝ)^z := by
     simp [KPCubicHaar.abs, hu0, KPCubicUnitIndices.residueCard, z]
   have hz : 0 ≤ z := by
     by_contra hn
     have hlt : (Nat.card 𝓀[K] : ℝ)^z < 1 := zpow_lt_one_of_neg₀
       (by exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))) (by omega)
     rw [← he] at hlt
     exact (not_lt_of_ge hu) hlt
   refine ⟨z.toNat, ?_⟩
   rw [he, ← zpow_natCast, Int.toNat_of_nonneg hz]
 · rintro ⟨n, hn⟩
   rw [hn]
   exact one_le_pow₀ (by exact_mod_cast (Finite.one_lt_card (α := 𝓀[K])).le)

theorem exterior_abs_rpow_integrable
 (μ : Measure K) [μ.IsAddHaarMeasure] (a : ℝ) (ha : a < -1) :
 IntegrableOn (fun u : K => ((KPCubicHaar.abs K u ^ a : ℝ) : ℂ))
   {u : K | 1 ≤ KPCubicHaar.abs K u} μ := by
 let Q : ℝ := Nat.card 𝓀[K]
 let shell : ℕ → Set K := fun n => {u | KPCubicHaar.abs K u = Q^n}
 let bound : ℕ → ℝ := fun n => (Q^a)^n
 have hQ : 1 < Q := by dsimp [Q]; exact_mod_cast (Finite.one_lt_card (α := 𝓀[K]))
 have hQ0 : 0 < Q := lt_trans zero_lt_one hQ
 have hm (n : ℕ) : MeasurableSet (shell n) := measurableSet_eq_fun (exterior_abs_measurable K) measurable_const
 have hmass (n : ℕ) : μ {u : K | KPCubicHaar.abs K u ≤ Q^n} =
   ENNReal.ofReal (Q^n) * μ ((valuation K).integer : Set K) := by
   simpa only [zpow_natCast] using NonarchimedeanHaarScaling.closedBall_measure K μ (n : ℤ)
 have hO : μ ((valuation K).integer : Set K) ≠ ⊤ :=
   (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
 have hfinite (n : ℕ) : μ (shell n) ≠ ⊤ := by
   apply ne_top_of_le_ne_top (b := μ {u : K | KPCubicHaar.abs K u ≤ Q^n})
   · rw [hmass]
     exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO
   · exact measure_mono (fun _ h => le_of_eq h)
 have hr : Q^(a+1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hQ (by linarith)
 have hs : Summable (fun n : ℕ => μ.real ((valuation K).integer : Set K) * (Q^(a+1))^n) :=
   (summable_geometric_of_lt_one (Real.rpow_nonneg hQ0.le _) hr).mul_left _
 have hsum : Summable (fun n : ℕ => μ.real (shell n) * bound n) := by
   apply Summable.of_nonneg_of_le (fun n => mul_nonneg ENNReal.toReal_nonneg (by positivity)) (fun n => ?_) hs
   have hl : μ.real (shell n) ≤ Q^n * μ.real ((valuation K).integer : Set K) := by
     have hh := measureReal_mono (μ := μ) (s₁ := shell n)
       (s₂ := {u : K | KPCubicHaar.abs K u ≤ Q^n}) (fun _ h => le_of_eq h)
       (by rw [hmass]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hO)
     simpa [measureReal_def, hmass, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hQ0.le n)] using hh
   calc
    μ.real (shell n) * bound n ≤ (Q^n * μ.real ((valuation K).integer : Set K)) * bound n := mul_le_mul_of_nonneg_right hl (by positivity)
    _ = μ.real ((valuation K).integer : Set K) * (Q^(a+1))^n := by
      dsimp [bound]
      rw [Real.rpow_add hQ0, Real.rpow_one, mul_pow]
      ring
 rw [exterior_shells K]
 apply KPRamifiedBetaConductorSeries.integrableOn_shell_union_of_bounds μ _
   (((exterior_abs_measurable K).pow_const a).complex_ofReal.aestronglyMeasurable) shell hm hfinite bound
 · intro n; positivity
 · intro n u hu
   change KPCubicHaar.abs K u = Q^n at hu
   rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by rw [hu]; positivity) a), hu]
   dsimp [bound]
   rw [Real.rpow_pow_comm hQ0.le]
 · exact hsum
end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeLiteral
open KPTameTransposeKernelUnfolding KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)

private theorem np_mul (a b : (LocalField F q)ˣ) (s : ℂ) :
 normPower (LocalField F q) (a*b) s =
 normPower (LocalField F q) a s * normPower (LocalField F q) b s := by
 simp only [normPower, localAbs_mul, Real.log_mul
   (ne_of_gt (localAbs_pos _ _)) (ne_of_gt (localAbs_pos _ _)), Complex.ofReal_add,
   mul_add, Complex.exp_add]

private theorem chiH_mul (a b : HL F ζ hζ q S P) :
 chiH F ζ hζ q S P hP .minus (a*b) =
 chiH F ζ hζ q S P hP .minus a * chiH F ζ hζ q S P hP .minus b := by
 simp only [chiH, map_mul, Units.val_mul, Subgroup.coe_mul, np_mul]
 ring

private theorem cube_weight (y : (LocalField F q)ˣ) (hc :
 (S.borel.cubeLift y : actualTorus F ζ hζ q) ∈ HL F ζ hζ q S P) :
 chiH F ζ hζ q S P hP .minus ⟨S.borel.cubeLift y, hc⟩ =
 normPower (LocalField F q) (y^3) (1/3) := by
 let c : HL F ζ hζ q S P := ⟨S.borel.cubeLift y, hc⟩
 have hw : ((weylHL F ζ hζ q S P hP c).val : actualTorus F ζ hζ q) =
   (S.borel.cubeLift y⁻¹ : actualTorus F ζ hζ q) := by
   change S.borel.weyl (S.borel.cubeLift y) = _
   rw [← S.borel.weylCenter_coe, S.borel.weyl_cube]
 have hp := P.extends_center (weylHL F ζ hζ q S P hP c)
   (show ((weylHL F ζ hζ q S P hP c).val : actualTorus F ζ hζ q) ∈ S.heisenberg.C from hw ▸ (S.borel.cubeLift y⁻¹).property)
 have he : (⟨(weylHL F ζ hζ q S P hP c).val, hw ▸ (S.borel.cubeLift y⁻¹).property⟩ : S.heisenberg.C) = S.borel.cubeLift y⁻¹ := Subtype.ext hw
 rw [he] at hp
 change (P.ωL (weylHL F ζ hζ q S P hP c) : ℂ) * _ = _
 rw [hp, S.borel.exceptional_cube, S.borel.cube_coordinate]
 simp only [normPower]
 have ha : localAbs (LocalField F q) (y ^ 3)⁻¹ = (localAbs (LocalField F q) (y ^ 3))⁻¹ := by
   apply eq_inv_of_mul_eq_one_left
   rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
 rw [inv_pow, ha, Real.log_inv,
   Complex.ofReal_neg, ← Complex.exp_add]
 congr 1
 ring

include hP in
private theorem tame_coordinate_unit_cube (h : HL F ζ hζ q S P) :
 ∃ (u : (KPTameCompact.O F q)ˣ) (y : (LocalField F q)ˣ),
 S.borel.coordinate h.val = KPTameCompact.unitInclusion F q u * y^3 := by
 have hm : QuotientGroup.mk' (CubicCharacters.cubes (LocalField F q)ˣ)
   (S.borel.coordinate h.val) ∈ KPTameValuationCoordinates.unitCubeClasses (LocalField F q) := by
   change QuotientGroup.mk (S.borel.coordinate h.val) ∈ _
   rw [← S.cube_class, ← hP]
   exact ⟨S.heisenberg.π h.val, h.property, rfl⟩
 obtain ⟨z, hz, he⟩ := hm
 obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hz
 obtain ⟨u, rfl⟩ := ha
 obtain ⟨c, rfl⟩ := hb
 have hd := (QuotientGroup.eq_iff_div_mem).mp he
 obtain ⟨r, hr⟩ := hd
 change r^3 = _ at hr
 refine ⟨u, c / r, ?_⟩
 change S.borel.coordinate h.val = KPRamifiedBeta.unitsInclusion (LocalField F q) u * (c/r)^3
 rw [div_pow]
 change r^3 = KPRamifiedBeta.unitsInclusion (LocalField F q) u * c^3 / S.borel.coordinate h.val at hr
 rw [hr]
 apply Units.ext
 simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
 field_simp
 <;> ring

theorem normalized_minus_chiH_norm
 (hnormalized : RawNormalizedExtension F ζ hζ q S P)
 (h : HL F ζ hζ q S P) :
 ‖chiH F ζ hζ q S P hP .minus h‖ =
   (localAbs (LocalField F q) (S.borel.coordinate h.val)) ^ (1/3 : ℝ) := by
 obtain ⟨u, y, hy⟩ := tame_coordinate_unit_cube F ζ hζ q S P hP h
 have hc := KPTameTransposeKernelUnfoldingRaw.HigherShellCubicUnitConjugation.CubicUnitConjugationAtoms.cubeLift_mem_HL F ζ hζ q S P y
 let c : HL F ζ hζ q S P := ⟨S.borel.cubeLift y, hc⟩
 let a := h * c⁻¹
 have ha : S.borel.coordinate a.val = KPTameCompact.unitInclusion F q u := by
   simp only [a, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, c, S.borel.cube_coordinate, hy]
   group
 have hu : valuation (LocalField F q) (S.borel.coordinate a.val : LocalField F q) = 1 := by
   rw [ha]
   exact (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
 have hn := KPTameTransposeUnitNumeratorSteps.normalizedExtension_coordinate_unit_chiH_norm F ζ hζ q S P hP hnormalized .minus a hu
 have hh : h = a*c := by dsimp [a]; group
 rw [hh, chiH_mul, norm_mul, hn, one_mul, cube_weight]
 have he : localAbs (LocalField F q) (S.borel.coordinate (a*c).val) =
   localAbs (LocalField F q) (y^3) := by
   rw [Subgroup.coe_mul, map_mul]
   change localAbs (LocalField F q) (S.borel.coordinate a.val * S.borel.coordinate (S.borel.cubeLift y)) = _
   rw [ha, S.borel.cube_coordinate, localAbs_mul]
   have hv : valuation (LocalField F q) (KPTameCompact.unitInclusion F q u : LocalField F q) = 1 :=
     (Valuation.integer.integers (valuation (LocalField F q))).valuation_unit u
   simp [localAbs, hv]
 rw [he, normPower, Complex.norm_exp]
 simp only [Complex.mul_re, Complex.div_re, Complex.one_re, Complex.ofReal_re,
   Complex.ofReal_im, Complex.one_im, mul_zero, sub_zero, zero_div, mul_one,
   one_pow, add_zero]
 rw [Real.rpow_def_of_pos (localAbs_pos _ _)]
 congr 1
 norm_num [Complex.normSq, Complex.ofReal_re, Complex.ofReal_im]
 ring

private theorem np_norm (a : (LocalField F q)ˣ) (s : ℂ) :
 ‖normPower (LocalField F q) a s‖ = localAbs (LocalField F q) a ^ s.re := by
 rw [normPower, Complex.norm_exp, Real.rpow_def_of_pos (localAbs_pos _ _)]
 simp [Complex.mul_re]
 ring

theorem eventual_deformed_test_kernel_norm_profile
 (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
 (hnormalized : RawNormalizedExtension F ζ hζ q S P)
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
   (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
 ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
 (f : scalarSections F ζ hζ q S P hP .minus),
 IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π ((i.val : ℤ),0)) m f →
 ∀ (u : (LocalField F q)ˣ) (b : BL F ζ hζ q S P),
 (b : ActualCover F ζ hζ q) =
   KPPGLLocalCover.N F ζ hζ (Sum.inr q) (-(u⁻¹ : (LocalField F q)ˣ) : LocalField F q) *
   KPPGLLocalCover.A F ζ hζ (Sum.inr q) (u⁻¹ ^ (2 : ℕ)) →
 ∀ (s : ℂ) (x : LocalField F q),
 ‖((deformedTest F ζ hζ q S P hP f s).val
   (kernelW (LocalField F q) S.borel .minus *
     KPPGLLocalCover.N F ζ hζ (Sum.inr q) (u : LocalField F q) *
     (eta F ζ hζ q π i * KPPGLLocalCover.W F ζ hζ (Sum.inr q) *
       KPPGLLocalCover.N F ζ hζ (Sum.inr q) x))).val 1‖ =
 localAbs (LocalField F q) u ^ (2*s.re - 2/3) *
   ‖diagonalAnchorTwist F ζ hζ q S π i s‖ *
   (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℝ))
     (x + ((π^i.val : (LocalField F q)ˣ) : LocalField F q) / (u : LocalField F q)) := by
 obtain ⟨M, hM⟩ := eventual_deformed_test_kernel_profile F ζ hζ q S P hP htame π hπ
 refine ⟨M, fun m hm i f hf u b hb s x => ?_⟩
 rw [hM m hm i f hf u b hb s x]
 have hc := relative_borel_coordinate F ζ hζ q S P u b hb
 have hn := normalized_minus_chiH_norm F ζ hζ q S P hP hnormalized (retractL F ζ hζ q S P b)
 have ha : localAbs (LocalField F q) (u⁻¹^2) = localAbs (LocalField F q) u ^ (-2 : ℝ) := by
   have hi : localAbs (LocalField F q) u⁻¹ = (localAbs (LocalField F q) u)⁻¹ := by
     apply eq_inv_of_mul_eq_one_left
     rw [← localAbs_mul, inv_mul_cancel, localAbs_one]
   rw [pow_two, localAbs_mul, hi]
   rw [Real.rpow_neg (le_of_lt (localAbs_pos _ _)), Real.rpow_two]
   ring
 have hw : ‖chi F ζ hζ q S P hP .minus b *
   normPower (LocalField F q) (u⁻¹^2) (KPRankOneShellContinuation.sourceParameter .minus s)‖ =
   localAbs (LocalField F q) u ^ (2*s.re - 2/3) := by
   rw [norm_mul, chi, hn, hc, np_norm, ha, ← Real.rpow_mul (le_of_lt (localAbs_pos _ _)),
     ← Real.rpow_mul (le_of_lt (localAbs_pos _ _)), ← Real.rpow_add (localAbs_pos _ _)]
   congr 1
   simp [KPRankOneShellContinuation.sourceParameter]
   ring
 rw [norm_mul, hw, norm_mul]
 simp only [Units.val_pow_eq_pow_val]
 by_cases hx : x + ((π^i.val : (LocalField F q)ˣ) : LocalField F q) / (u : LocalField F q) ∈ rootLevelSet F ζ hζ q m
 · simp only [Units.val_pow_eq_pow_val] at hx
   simp only [Set.indicator_of_mem hx, norm_one, mul_one]
 · simp only [Units.val_pow_eq_pow_val] at hx
   simp only [Set.indicator_of_notMem hx, norm_zero, mul_zero]
end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end

end

section
noncomputable section
namespace DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry
open scoped NumberField Classical
open NumberField IsDedekindDomain MeasureTheory ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries
open KPTameJacquetTestDuality KPTameTransposeLiteral
open KPTameTransposeKernelUnfolding KPRankOneShellContinuation
variable (F : Type) [Field F] [NumberField F]
 (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
 (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
 (hP : IsTamePolarization F ζ hζ q S P)

private theorem abs_unit_eq (u : (LocalField F q)ˣ) :
 KPCubicHaar.abs (LocalField F q) (u : LocalField F q) = localAbs (LocalField F q) u := by
 rw [KPCubicHaar.abs, if_neg (Units.ne_zero u)]
 unfold localAbs KPCubicUnitIndices.residueCard residueCardinality
 exact (Real.rpow_intCast _ _).symm

theorem eventual_diagonalDoubleKernel_product_integrable
 (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
 (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
 (hnormalized : RawNormalizedExtension F ζ hζ q S P)
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
   (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
 ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
 (f : scalarSections F ζ hζ q S P hP .minus),
 IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π ((i.val : ℤ),0)) m f →
 ∀ s : ℂ, convergenceHalfPlane .minus s →
 Integrable (Function.uncurry (diagonalDoubleKernel F ζ hζ q S P hP π i f s))
   ((μ.restrict (lowShell F q)).prod μ) := by
 obtain ⟨M, hM⟩ := eventual_deformed_test_kernel_norm_profile F ζ hζ q S P hP htame hnormalized π hπ
 obtain ⟨D, hD⟩ := KPTameJacquetBruhatTests.TestConstruction.eventually_matrixChartDepth F q
 obtain ⟨E, hE⟩ := KPTameJacquetBruhatTests.BruhatGeometry.eventually_actual_raw_bruhat_geometry F ζ hζ q S P hP htame π hπ .minus
 refine ⟨max M (max D E), fun m hm i f hf s hs => ?_⟩
 have hmM := (le_max_left M (max D E)).trans hm
 have hmD := (le_max_left D E).trans ((le_max_right M (max D E)).trans hm)
 have hmE := (le_max_right D E).trans ((le_max_right M (max D E)).trans hm)
 have hdepth := hD m hmD
 obtain ⟨K, hK, hc, hn, hd, hr, ho, hz, hroot, hchart⟩ := hE m hmE
 let ext : Set (LocalField F q) := {u | 1 ≤ KPCubicHaar.abs (LocalField F q) u}
 let A := ‖diagonalAnchorTwist F ζ hζ q S π i s‖
 let R : LocalField F q → ℝ := fun u => KPCubicHaar.abs (LocalField F q) u ^ (2*s.re - 2/3)
 have hmext : MeasurableSet ext := by
   exact measurableSet_le measurable_const (exterior_abs_measurable (LocalField F q))
 have hint : Integrable (ext.indicator R) μ := by
   apply (integrable_indicator_iff hmext).mpr
   exact (exterior_abs_rpow_integrable (LocalField F q) μ (2*s.re-2/3) (by dsimp [convergenceHalfPlane] at hs; linarith)).re
 have hOfinite : μ (lowShell F q) ≠ ⊤ :=
   (IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1).measure_lt_top.ne
 letI : IsFiniteMeasure (μ.restrict (lowShell F q)) := ⟨by simpa using lt_top_iff_ne_top.mpr hOfinite⟩
 have hprod := (integrable_const A (μ := μ.restrict (lowShell F q))).mul_prod hint
 apply hprod.mono' ((diagonalDoubleKernel_locallyConstant F ζ hζ q S P hP π i f s).continuous.aestronglyMeasurable)
 have hxAE : ∀ᵐ z : LocalField F q × LocalField F q ∂((μ.restrict (lowShell F q)).prod μ), z.1 ∈ lowShell F q := by
   apply (Measure.ae_prod_iff_ae_ae (((valuation (LocalField F q)).isClosed_integer).measurableSet.preimage measurable_fst)).mpr
   filter_upwards [ae_restrict_mem ((valuation (LocalField F q)).isClosed_integer).measurableSet] with x hx
   exact Filter.Eventually.of_forall (fun _ => hx)
 filter_upwards [hxAE] with z hz
 by_cases hne : diagonalDoubleKernel F ζ hζ q S P hP π i f s z.1 z.2 = 0
 · simp only [Function.uncurry, hne, norm_zero]
   exact mul_nonneg (norm_nonneg _) (Set.indicator_nonneg (fun _ _ => Real.rpow_nonneg (by unfold KPCubicHaar.abs; split_ifs <;> positivity) _) _)
 · obtain ⟨u, hu, b, hb⟩ := diagonalDoubleKernel_ne_zero_mem_relativeBorelRootChart
     F ζ hζ q S P hP π hπ i m hdepth f hf s z.1 z.2 hne
   have hcut := diagonalDoubleKernel_ne_zero_radial_cutoff F ζ hζ q S P hP π hπ i m hdepth hroot f hf s z.1 hz u (by simpa [hu] using hne)
   have hdvd := RootResidualGeometry.relative_diagonal_exponent_dvd F ζ hζ q S P hP b u (relative_borel_coordinate F ζ hζ q S P u b hb)
   have hle : KPCubicExpansion.valuationExponent (LocalField F q) u ≤ 0 :=
     (RootResidualGeometry.cubic_cutoffs_eq _ hdvd i).mp hcut
   have hext : z.2 ∈ ext := by
     rw [← hu]
     change 1 ≤ KPCubicHaar.abs (LocalField F q) (u : LocalField F q)
     rw [abs_unit_eq, localAbs]
     apply Real.one_le_rpow (by exact_mod_cast (Finite.one_lt_card (α := 𝓀[LocalField F q])).le)
     dsimp [KPCubicExpansion.valuationExponent] at hle
     exact_mod_cast (neg_nonpos.mp hle)
   have hp := hM m hmM i f hf u b hb s z.1
   change ‖diagonalDoubleKernel F ζ hζ q S P hP π i f s z.1 (u : LocalField F q)‖ = _ at hp
   have hextu : (u : LocalField F q) ∈ ext := hu ▸ hext
   rw [Function.uncurry, ← hu, hp, Set.indicator_of_mem hextu]
   change _ ≤ A * R (u : LocalField F q)
   have hInd : (rootLevelSet F ζ hζ q m).indicator (fun _ => (1 : ℝ))
     (z.1 + ((π^i.val : (LocalField F q)ˣ) : LocalField F q)/(u : LocalField F q)) ≤ 1 := by
     exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
   dsimp [A, R]
   rw [abs_unit_eq]
   calc
    _ ≤ localAbs (LocalField F q) u ^ (2*s.re-2/3) * ‖diagonalAnchorTwist F ζ hζ q S π i s‖ * 1 :=
      mul_le_mul_of_nonneg_left hInd (mul_nonneg (Real.rpow_nonneg (localAbs_pos _ _).le _) (norm_nonneg _))
    _ = _ := by ring

theorem eventual_u_first_transport
 (μ : Measure (LocalField F q)) [μ.IsAddHaarMeasure]
 (htame : ringChar (KPTameCompact.O F q ⧸ KPTameCompact.p F q) ≠ 3)
 (hnormalized : RawNormalizedExtension F ζ hζ q S P)
 (π : (LocalField F q)ˣ)
 (hπ : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt (LocalField F q)
   (valuation (LocalField F q) (π : LocalField F q)) = WithZero.exp (-1 : ℤ)) :
 ∃ M : ℕ, ∀ m ≥ M, ∀ (i : Fin 3)
 (f₀ fᵢ : scalarSections F ζ hζ q S P hP .minus),
 IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π (0,0)) m f₀ →
 IsMinusTest F ζ hζ q S P hP (diagonalLift F ζ hζ q π ((i.val : ℤ),0)) m fᵢ →
 ∀ s : ℂ, convergenceHalfPlane .minus s →
 (∫ x in lowShell F q, ∫ u,
   diagonalDoubleKernel F ζ hζ q S P hP π i fᵢ s x u ∂μ ∂μ) =
 (evaluationUnit (LocalField F q) .minus s : ℂ) ^ (i.val : ℤ) *
   (∫ x in lowShell F q, ∫ u,
     diagonalDoubleKernel F ζ hζ q S P hP π 0 f₀ s x u ∂μ ∂μ) := by
 obtain ⟨M, hM⟩ := eventual_u_first_transport_of_integrable F ζ hζ q S P hP μ htame π hπ
 obtain ⟨D, hD⟩ := eventual_diagonalDoubleKernel_product_integrable F ζ hζ q S P hP μ htame hnormalized π hπ
 refine ⟨max M D, fun m hm i f₀ fᵢ hf₀ hfᵢ s hs => ?_⟩
 apply hM m ((le_max_left M D).trans hm) i f₀ fᵢ hf₀ hfᵢ s
 · exact hD m ((le_max_right M D).trans hm) 0 f₀ (by simpa only [Fin.val_zero, Int.ofNat_zero] using hf₀) s hs
 · exact hD m ((le_max_right M D).trans hm) i fᵢ hfᵢ s hs

end DedekindZetaZeroFree.KPTameTransposeLiteralMassTransport.DiagonalLiftGeometry

end

end
