module

public import DedekindZetaZeroFree.Theta.Whittaker.TensorProduct.FrozenTensor

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport
open MomentSources NumberField MeasureTheory
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

lemma class_eq_one_of_finite_eq_one (z : R.A.G) (hz : ∀ p : R.A.Sf, z.2 p = 1) :
    QuotientGroup.mk' R.A.sixthPowers z = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  choose r hr using (fun w : InfinitePlace F =>
    R.A.infinite_unit_isPower w 6 (Or.inr (Or.inr rfl)) (z.1 w))
  refine ⟨(r, 1), ?_⟩
  apply Prod.ext
  · funext w
    exact hr w
  · funext p
    simpa using (hz p).symm

lemma uniform_class (u : ℝ) :
    QuotientGroup.mk' R.A.sixthPowers
      (R.A.radialSection (Real.exp u) (Real.exp_pos u)) = 1 := by
  exact class_eq_one_of_finite_eq_one R _ (fun p => by simp [SArithmeticData.radialSection])

lemma uniform_branch (v : R.A.UnitQuotient) (u : ℝ) :
    C.packet.branch v (R.A.radialSection (Real.exp u) (Real.exp_pos u)) = 1 := by
  rw [C.packet.branch_exact v _ (fun p => by
    simpa [SArithmeticData.radialSection] using (C.packet.cutoff p).one_mem)]
  apply Finset.prod_eq_one
  intro w _
  have hp : 0 < (Real.exp u) ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ))) :=
    Real.rpow_pos_of_pos (Real.exp_pos u) _
  have he : InfinitePlace.Completion.extensionEmbedding w
      ((R.A.radialSection (Real.exp u) (Real.exp_pos u)).1 w : w.Completion) =
      (((Real.exp u) ^ (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))) : ℝ) := by
    change (InfinitePlace.Completion.extensionEmbedding w)
      ((InfinitePlace.Completion.ringEquivComplexOfIsComplex (R.A.complex_place w)).symm
        (↑(Real.rpow (Real.exp u) (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))) : ℂ)) = _
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply (R.A.complex_place w),
      RingEquiv.apply_symm_apply]
    rfl
  rw [he]
  have hang : DHCubic.angular
      (↑(Real.rpow (Real.exp u) (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))) : ℂ) = 1 := by
    have hang_pos (a : ℝ) (ha : 0 < a) : DHCubic.angular (a : ℂ) = 1 := by
      unfold DHCubic.angular
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
      simp [ha.ne']
    exact hang_pos _ (Real.rpow_pos_of_pos (Real.exp_pos u) _)
  change DHCubic.angular (↑(Real.rpow (Real.exp u)
    (1 / (2 * (InfinitePlace.nrComplexPlaces F : ℝ)))) : ℂ) ^ C.packet.exponents v w = 1
  rw [hang, one_zpow]

def phase (v : R.A.UnitQuotient) (κ : R.A.V) (z : R.A.G) : ℂ :=
  (if κ * (QuotientGroup.mk' R.A.sixthPowers z)⁻¹ ∈ R.probe.correction.B then 1 else 0) *
    (R.σ ((R.probe.correction.H κ (QuotientGroup.mk' R.A.sixthPowers z) : Fˣ) : F) ^ 2)⁻¹ *
      C.packet.branch v z

lemma phase_radial (v : R.A.UnitQuotient) (κ : R.A.V) (z : R.A.G) (u : ℝ) :
    phase R C v κ (z * R.A.radialSection (Real.exp u) (Real.exp_pos u)) =
      phase R C v κ z := by
  unfold phase
  have hc : QuotientGroup.mk' R.A.sixthPowers
      (z * R.A.radialSection (Real.exp u) (Real.exp_pos u)) =
      QuotientGroup.mk' R.A.sixthPowers z := by
    rw [map_mul, uniform_class]
    exact mul_one (QuotientGroup.mk' R.A.sixthPowers z)
  rw [hc, map_mul, uniform_branch, mul_one]

lemma root_norm (h : rootsOfUnity 6 F) : ‖R.σ ((h : Fˣ) : F)‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 6) _ (by norm_num)
  rw [← map_pow, ← Units.val_pow_eq_pow_val]
  have hh : (h : Fˣ) ^ 6 = 1 := (mem_rootsOfUnity _ _).mp h.property
  rw [hh]
  simp

lemma branch_norm (v : R.A.UnitQuotient) (z : R.A.G) : ‖C.packet.branch v z‖ = 1 := by
  rw [C.packet.branch_global, norm_mul, Circle.norm_coe, root_norm, one_mul]

lemma phase_norm_le_one (v : R.A.UnitQuotient) (κ : R.A.V) (z : R.A.G) :
    ‖phase R C v κ z‖ ≤ 1 := by
  unfold phase
  have hh : ‖R.σ ((R.probe.correction.H κ (QuotientGroup.mk' R.A.sixthPowers z) : Fˣ) : F)‖ = 1 := by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective R.A.sixthPowers κ
    rw [← hx, R.probe.correction.H_actual]
    exact root_norm R (R.A.H_S x z)
  rw [norm_mul, norm_mul, norm_inv, norm_pow, hh, branch_norm]
  split_ifs <;> norm_num

theorem radialIntegrand_eq (v : R.A.UnitQuotient) (κ : R.A.V) (y : R.A.G1) :
    (fun u => ThetaExpansion.radialSheetIntegrand R C v κ u y) =
      fun u => phase R C v κ y.val *
        MomentSources.fourier R C.sources.dq (C.realization.theta v)
          (diagonal R (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)) *
            KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12) := by
  funext u
  change phase R C v κ (y.val * R.A.radialSection (Real.exp u) (Real.exp_pos u)) * _ = _
  rw [phase_radial]

theorem radialIntegrand_jet_le (v : R.A.UnitQuotient) (κ : R.A.V) (y : R.A.G1)
    (j : ℕ) (u : ℝ) :
    ‖iteratedDeriv j (fun t => ThetaExpansion.radialSheetIntegrand R C v κ t y) u‖ ≤
      ‖iteratedDeriv j (fun t =>
        MomentSources.fourier R C.sources.dq (C.realization.theta v)
          (diagonal R (y.val * R.A.radialSection (Real.exp t) (Real.exp_pos t)) *
            KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)) u‖ := by
  rw [radialIntegrand_eq, iteratedDeriv_const_mul_field, norm_mul]
  exact (mul_le_mul_of_nonneg_right (phase_norm_le_one R C v κ y.val) (norm_nonneg _)).trans_eq
    (one_mul _)

end DedekindZetaZeroFree.SheetRescaling.WeylTensorTransport

end
