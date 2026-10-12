module

public import DedekindZetaZeroFree.Theta.Unfolding.ParityOrbitSlabMellin
public import DedekindZetaZeroFree.Theta.Unfolding.ParityOrbitSummability

@[expose] public section

noncomputable section

open Classical NumberField MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.SlabAbsoluteSummability

variable {K : Type} [Field K] [NumberField K]

theorem summable_integral_norm (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun α : RayCoset.Cx D =>
      ∫ p, ‖OrbitSlabMellin.integrand D δ α s p‖ ∂(OrbitSlabMellin.μB D)) := by
  apply (RayCoset.chosenOrbitProductEquiv D).summable_iff.mp
  change Summable (fun p : RayCoset.X D × RayCoset.U K D.m =>
    ∫ th, ‖OrbitSlabMellin.integrand D δ
      (p.2 • RayCoset.orbitRepresentative D p.1) s th‖ ∂(OrbitSlabMellin.μB D))
  apply (summable_prod_of_nonneg (fun p => integral_nonneg (fun th => norm_nonneg _))).mpr
  refine ⟨fun x => OrbitSlabMellin.summable_integral_norm D δ
    (RayCoset.orbitRepresentative D x) s (lt_trans zero_lt_one hs), ?_⟩
  have hrow (x : RayCoset.X D) := OrbitSlabMellin.hasSum_integral_norm D δ
    (RayCoset.orbitRepresentative D x) s (lt_trans zero_lt_one hs)
  simp only [RayCoset.orbitMk_orbitRepresentative] at hrow
  apply ((RayCoset.summable_normWeight_rpow D s hs).mul_left
    ((RayCoset.rayUnitTorsionCard K D.m : ℝ) * ‖κδ K δ (s.re : ℂ)‖)).congr
  exact fun x => (hrow x).tsum_eq.symm

private theorem integrable_kernel (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re)
    (α : RayCoset.Cx D) :
    Integrable (OrbitSlabMellin.integrand D δ α s) (OrbitSlabMellin.μB D) := by
  simpa only [one_smul] using OrbitSlabMellin.integrable D δ α s
    (lt_trans zero_lt_one hs) (1 : RayCoset.U K D.m)

private theorem l1_integrable_tsum {A I E : Type*} [MeasurableSpace A]
    {μ : Measure A} [Countable I] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : I → A → E}
    (hF_int : ∀ i, Integrable (F i) μ)
    (hF_sum : Summable fun i ↦ ∫ a, ‖F i a‖ ∂μ) :
    Integrable (fun a ↦ ∑' i, F i a) μ := by
  let G : I → A →₁[μ] E := fun i ↦ (hF_int i).toL1 (F i)
  have hnorm (i : I) : ‖G i‖ = ∫ a, ‖F i a‖ ∂μ := by
    rw [show G i = (hF_int i).toL1 (F i) by rfl,
      Integrable.norm_toL1, integral_norm_eq_lintegral_enorm
        (hF_int i).aestronglyMeasurable]
    simp only [edist_zero_right]
  have hG_norm : Summable fun i ↦ ‖G i‖ := hF_sum.congr fun i ↦ (hnorm i).symm
  have hG_enorm : ∑' i, ‖G i‖ₑ ≠ ⊤ := tsum_enorm_ne_top_iff_summable_norm.mpr hG_norm
  have hcoe : (⇑(∑' i, G i) : A → E) =ᵐ[μ] fun a ↦ ∑' i, F i a := by
    filter_upwards [Lp.coeFn_tsum hG_enorm,
      ae_all_iff.mpr (fun i ↦ (hF_int i).coeFn_toL1)] with a hsum hterm
    exact hsum.trans (tsum_congr fun i ↦ hterm i)
  exact (L1.integrable_coeFn (∑' i, G i)).congr hcoe

theorem integrable_tsum (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    Integrable (fun p => ∑' α : RayCoset.Cx D,
      OrbitSlabMellin.integrand D δ α s p) (OrbitSlabMellin.μB D) := by
  letI := RayCoset.countable_Cx D
  exact l1_integrable_tsum (integrable_kernel D δ s hs) (summable_integral_norm D δ s hs)

theorem hasSum_integral (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun α : RayCoset.Cx D =>
      ∫ p, OrbitSlabMellin.integrand D δ α s p ∂(OrbitSlabMellin.μB D))
      ((RayCoset.rayUnitTorsionCard K D.m : ℂ) * κδ K δ s *
        RayCoset.Zδ D δ s) := by
  have hint : Summable (fun α : RayCoset.Cx D =>
      ∫ p, OrbitSlabMellin.integrand D δ α s p ∂(OrbitSlabMellin.μB D)) :=
    (summable_integral_norm D δ s hs).of_norm_bounded
      (fun α => norm_integral_le_integral_norm _)
  apply (RayCoset.chosenOrbitProductEquiv D).hasSum_iff.mp
  have hp := (RayCoset.chosenOrbitProductEquiv D).summable_iff.mpr hint
  apply hp.hasSum_iff.mpr
  rw [hp.tsum_prod]
  have hrow (x : RayCoset.X D) := OrbitSlabMellin.hasSum_integral D δ
    (RayCoset.orbitRepresentative D x) s (lt_trans zero_lt_one hs)
  simp only [RayCoset.orbitMk_orbitRepresentative] at hrow
  change (∑' x : RayCoset.X D, ∑' u : RayCoset.U K D.m,
    ∫ p, OrbitSlabMellin.integrand D δ (u • RayCoset.orbitRepresentative D x) s p
      ∂(OrbitSlabMellin.μB D)) = _
  simp_rw [(hrow _).tsum_eq, mul_assoc]
  simpa only [RayCoset.signedOrbitWeight, mul_assoc] using
    ((RayCoset.hasSum_signedOrbitWeight D δ s hs).mul_left
      ((RayCoset.rayUnitTorsionCard K D.m : ℂ) * κδ K δ s)).tsum_eq

theorem integral_tsum (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    (∫ p, (∑' α : RayCoset.Cx D, OrbitSlabMellin.integrand D δ α s p)
      ∂(OrbitSlabMellin.μB D)) =
      (RayCoset.rayUnitTorsionCard K D.m : ℂ) * κδ K δ s *
        RayCoset.Zδ D δ s := by
  letI := RayCoset.countable_Cx D
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm
    (integrable_kernel D δ s hs) (summable_integral_norm D δ s hs)).unique
      (hasSum_integral D δ s hs)

end DedekindZetaZeroFree.AbelianQuotient.RayParity.SlabAbsoluteSummability

end
