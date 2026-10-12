module

public import DedekindZetaZeroFree.Theta.Unfolding.ParityRayUnitOrbits
public import DedekindZetaZeroFree.Theta.Unfolding.ParityScaledMellin

@[expose] public section

noncomputable section

open Classical NumberField MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.OrbitSlabMellin

variable {K : Type} [Field K] [NumberField K]

abbrev μrad : Measure ℝ := Theta.positiveRadialHaar

abbrev μB (D : RayCoset.Data K) : Measure (ℝ × RayCoset.logHyperplane K) :=
  μrad.prod ((Theta.normalizedLogHaar K).restrict
    (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot))

abbrev q (th : ℝ × RayCoset.logHyperplane K) : InfinitePlace K → ℝ :=
  fun v => th.1 ^ (1 / (Module.finrank ℚ K : ℝ)) * Real.exp (th.2.val v)

abbrev integrand (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (th : ℝ × RayCoset.logHyperplane K) : ℂ :=
  (th.1 : ℂ) ^ s *
    RayParity.gδ K δ
      (RayParity.Q K (q th) (RayCoset.normalizedEmbedding D α.val))

open scoped Pointwise

namespace RadialPullback

private theorem map_log_positiveHaar : Measure.map Real.log «μ₊» = volume := by
  have himage : Real.log '' Set.Ioi (0 : ℝ) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro s
    exact ⟨Real.exp s, Real.exp_pos s, Real.log_exp s⟩
  have hj := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure ℝ) measurableSet_Ioi.nullMeasurableSet
    (f := Real.log) (f' := fun t => ContinuousLinearMap.toSpanSingleton ℝ (t⁻¹))
    (fun t ht => (Real.hasDerivAt_log (ne_of_gt ht)).hasFDerivAt.hasFDerivWithinAt)
    (fun a ha b hb hab => Real.log_injOn_pos ha hb hab)
  rw [himage, Measure.restrict_univ] at hj
  convert hj using 1
  unfold «μ₊»
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  congr 1
  have hd : (ContinuousLinearMap.toSpanSingleton ℝ (t⁻¹)).det = t⁻¹ := by
    have he : (ContinuousLinearMap.toSpanSingleton ℝ (t⁻¹)).toLinearMap =
        t⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
      ext
      simp [mul_comm]
    rw [ContinuousLinearMap.det, he, LinearMap.det_smul]
    simp
  rw [hd, abs_of_pos (inv_pos.mpr ht)]
theorem map_exp_volume_eq : Measure.map Real.exp volume = «μ₊» := by
  rw [← map_log_positiveHaar, Measure.map_map Real.continuous_exp.measurable Real.measurable_log]
  have he : Real.exp ∘ Real.log =ᵐ[«μ₊»] id := by
    filter_upwards [ae_positiveHaar_pos] with t ht
    exact Real.exp_log ht
  rw [Measure.map_congr he, Measure.map_id]
theorem map_exp_volume_pi_eq :
    Measure.map (fun x : InfinitePlace K → ℝ => fun v => Real.exp (x v)) volume = μ K := by
  letI : SigmaFinite (Measure.map Real.exp volume) := by
    rw [map_exp_volume_eq]
    infer_instance
  change Measure.map _ (Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ))) = _
  rw [Measure.pi_map_pi (fun _ => Real.continuous_exp.measurable.aemeasurable)]
  simp only [map_exp_volume_eq, μ]
theorem q_eq_exp_positiveRadialAngularLogMap
    (th : ℝ × RayCoset.logHyperplane K) (ht : 0 < th.1) :
    q th = fun v => Real.exp (Theta.positiveRadialAngularLogMap K th v) := by
  funext v
  rw [q, Real.rpow_def_of_pos ht]
  change Real.exp (Real.log th.1 * (1 / (Module.finrank ℚ K : ℝ))) *
    Real.exp (th.2.val v) = Real.exp (Real.log th.1 / (Module.finrank ℚ K : ℝ) + th.2.val v)
  rw [mul_one_div, Real.exp_add]

theorem map_q_eq :
    Measure.map (q (K := K)) (Theta.positiveRadialHaar.prod (Theta.normalizedLogHaar K)) = μ K := by
  have ht : ∀ᵐ th ∂(Theta.positiveRadialHaar.prod (Theta.normalizedLogHaar K)), 0 < th.1 := by
    exact Measure.quasiMeasurePreserving_fst.ae ae_positiveHaar_pos
  have he : q (K := K) =ᵐ[Theta.positiveRadialHaar.prod (Theta.normalizedLogHaar K)]
      ((fun x : InfinitePlace K → ℝ => fun v => Real.exp (x v)) ∘
        Theta.positiveRadialAngularLogMap K) := by
    filter_upwards [ht] with th hth
    exact q_eq_exp_positiveRadialAngularLogMap th hth
  rw [Measure.map_congr he, ← Measure.map_map
    (by fun_prop : Measurable (fun x : InfinitePlace K → ℝ => fun v => Real.exp (x v)))
    (by
      unfold Theta.positiveRadialAngularLogMap Theta.radialAngularLogMap
      apply measurable_pi_lambda
      intro v
      exact (Real.measurable_log.comp measurable_fst).div_const _ |>.add
        ((measurable_pi_apply v).comp (measurable_subtype_coe.comp measurable_snd))),
    Theta.map_positiveRadialHaar_prod_normalizedLogHaar K,
    map_exp_volume_pi_eq]

end RadialPullback

namespace ProductUnfolding

 instance radSFinite : SFinite μrad := by
  change SFinite RayParity.«μ₊»
  infer_instance
 instance latticeVAddInvariant (m : Ideal (𝓞 K)) :
    VAddInvariantMeasure (RayCoset.rayUnitLogLattice K m)
      (RayCoset.logHyperplane K) (Theta.normalizedLogHaar K) :=
  ⟨fun γ s _ => measure_preimage_add _ (γ : RayCoset.logHyperplane K) s⟩
 instance latticeMeasurableVAdd (m : Ideal (𝓞 K)) :
    MeasurableConstVAdd (RayCoset.rayUnitLogLattice K m) (RayCoset.logHyperplane K) :=
  ⟨fun γ => by
    change Measurable (fun h : RayCoset.logHyperplane K => (γ : RayCoset.logHyperplane K) + h)
    exact (Homeomorph.addLeft (γ : RayCoset.logHyperplane K)).measurable⟩
private theorem slab_sum_measure (D : RayCoset.Data K) :
    Measure.sum (fun γ : RayCoset.rayUnitLogLattice K D.m =>
      μrad.prod ((Theta.normalizedLogHaar K).restrict
        (γ +ᵥ RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot))) =
      μrad.prod (Theta.normalizedLogHaar K) := by
  letI := RayCoset.countable_rayUnitLogLattice (K := K) D.m
  rw [← Measure.prod_sum_right,
    (RayCoset.isAddFundamentalDomain_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot).sum_restrict]
theorem integrable_unit_slab {E : Type*} [NormedAddCommGroup E]
    (D : RayCoset.Data K) (f : ℝ × RayCoset.logHyperplane K → E)
    (hf : Integrable f (μrad.prod (Theta.normalizedLogHaar K))) (u : RayCoset.U K D.m) :
    Integrable (fun th => f (th.1, th.2 + RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ)))) (μB D) := by
  have hmp := (MeasurePreserving.id μrad).prod
    (measurePreserving_add_right (Theta.normalizedLogHaar K)
      (RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ))))
  have h := hmp.integrable_comp_of_integrable hf
  apply h.mono_measure
  exact Measure.prod_mono le_rfl Measure.restrict_le_self

private theorem slab_translate_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : RayCoset.Data K) (f : ℝ × RayCoset.logHyperplane K → E)
    (γ : RayCoset.rayUnitLogLattice K D.m) :
    (∫ th, f th ∂(μrad.prod ((Theta.normalizedLogHaar K).restrict
      (γ +ᵥ RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)))) =
    ∫ th, f (th.1, th.2 + (γ : RayCoset.logHyperplane K)) ∂μB D := by
  let S := RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot
  have hmp := (MeasurePreserving.id μrad).prod
    (measurePreserving_add_right (Theta.normalizedLogHaar K) (γ : RayCoset.logHyperplane K))
  have hemb : MeasurableEmbedding (Prod.map (id : ℝ → ℝ)
      (fun h : RayCoset.logHyperplane K => h + (γ : RayCoset.logHyperplane K))) :=
    MeasurableEmbedding.id.prodMap (Homeomorph.addRight (γ : RayCoset.logHyperplane K)).measurableEmbedding
  have himage : Prod.map (id : ℝ → ℝ) (fun h : RayCoset.logHyperplane K => h + (γ : RayCoset.logHyperplane K)) ''
      (Set.univ ×ˢ S) = Set.univ ×ˢ (γ +ᵥ S) := by
    rw [Set.prodMap_image_prod]
    simp only [Set.image_id]
    congr 1
    ext h
    simp only [Set.mem_image, Set.mem_vadd_set, Submodule.vadd_def, vadd_eq_add]
    constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, add_comm _ _⟩
  have h := hmp.setIntegral_image_emb hemb f (Set.univ ×ˢ S)
  rw [himage, ← Measure.prod_restrict, ← Measure.prod_restrict,
    Measure.restrict_univ] at h
  exact h
private theorem hasSum_lattice_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : RayCoset.Data K) (f : ℝ × RayCoset.logHyperplane K → E)
    (hf : Integrable f (μrad.prod (Theta.normalizedLogHaar K))) :
    HasSum (fun γ : RayCoset.rayUnitLogLattice K D.m =>
      ∫ th, f (th.1, th.2 + (γ : RayCoset.logHyperplane K)) ∂μB D)
      (∫ th, f th ∂(μrad.prod (Theta.normalizedLogHaar K))) := by
  have h : Integrable f (Measure.sum (fun γ : RayCoset.rayUnitLogLattice K D.m =>
      μrad.prod ((Theta.normalizedLogHaar K).restrict
        (γ +ᵥ RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)))) := by
    rw [slab_sum_measure]; exact hf
  simpa only [slab_translate_integral, slab_sum_measure] using hasSum_integral_measure h

 theorem hasSum_unit_slab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (D : RayCoset.Data K) (f : ℝ × RayCoset.logHyperplane K → E)
    (hf : Integrable f (μrad.prod (Theta.normalizedLogHaar K))) :
    HasSum (fun u : RayCoset.U K D.m =>
      ∫ th, f (th.1, th.2 + RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ))) ∂μB D)
      (RayCoset.rayUnitTorsionCard K D.m •
        ∫ th, f th ∂(μrad.prod (Theta.normalizedLogHaar K))) := by
  letI := Fintype.ofFinite (RayCoset.rayUnitTorsion K D.m)
  let A := fun γ : RayCoset.rayUnitLogLattice K D.m =>
    ∫ th, f (th.1, th.2 + (γ : RayCoset.logHyperplane K)) ∂μB D
  have hnorm : Summable (fun γ : RayCoset.rayUnitLogLattice K D.m =>
      ∫ th, ‖f (th.1, th.2 + (γ : RayCoset.logHyperplane K))‖ ∂μB D) :=
    (hasSum_lattice_slab D (fun th => ‖f th‖) hf.norm).summable
  have ha : Summable (fun γ => ‖A γ‖) := by
    apply hnorm.of_nonneg_of_le (fun γ => norm_nonneg _)
    exact fun γ => norm_integral_le_integral_norm _
  have hp : Summable (fun p : RayCoset.rayUnitLogLattice K D.m × RayCoset.rayUnitTorsion K D.m => A p.1) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
    refine ⟨fun γ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_const, nsmul_eq_mul] using ha.mul_left (Nat.card (RayCoset.rayUnitTorsion K D.m) : ℝ)
  have heq (u : RayCoset.U K D.m) :
      A (RayCoset.rayUnitLogTorsionEquiv K D.m u).1 =
      ∫ th, f (th.1, th.2 + RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ))) ∂μB D := by
    simp only [A, RayCoset.rayUnitLogTorsionEquiv_fst, RayCoset.rayUnitLogMap_coe]
  have hpsum : HasSum (fun p : RayCoset.rayUnitLogLattice K D.m × RayCoset.rayUnitTorsion K D.m => A p.1)
      (RayCoset.rayUnitTorsionCard K D.m • ∫ th, f th ∂(μrad.prod (Theta.normalizedLogHaar K))) := by
    convert hp.hasSum using 1
    rw [hp.tsum_prod]
    simp only [tsum_const]
    have h := (hasSum_lattice_slab D f hf).nsmul (Nat.card (RayCoset.rayUnitTorsion K D.m))
    exact h.tsum_eq.symm
  have hu := (RayCoset.rayUnitLogTorsionEquiv K D.m).hasSum_iff.mpr hpsum
  simpa only [Function.comp_def, heq] using hu

end ProductUnfolding

 theorem integrand_unit_shift (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (u : RayCoset.U K D.m) (th : ℝ × RayCoset.logHyperplane K)
    (ht : 0 < th.1) :
    integrand D δ (u • α) s th =
      integrand D δ α s (th.1, th.2 + RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ))) := by
  have hq : ∀ v, 0 < q th v := fun v => mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)
  have hu (v : InfinitePlace K) : 0 < RayCoset.absEmbedding D.m u v := by
    unfold RayCoset.absEmbedding
    apply InfinitePlace.pos_iff.mpr
    exact Units.ne_zero (Units.map (algebraMap (𝓞 K) K).toMonoidHom (u : (𝓞 K)ˣ))
  have he : (fun v => q th v * RayCoset.absEmbedding D.m u v) =
      q (th.1, th.2 + RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ))) := by
    funext v
    simp only [q, Submodule.coe_add, Pi.add_apply, RayCoset.logAbs_apply]
    rw [Real.exp_add]
    change _ = th.1 ^ (1 / (Module.finrank ℚ K : ℝ)) *
      (Real.exp (th.2.val v) * Real.exp (Real.log (RayCoset.absEmbedding D.m u v)))
    rw [Real.exp_log (hu v), mul_assoc]
  change (th.1 : ℂ) ^ s * _ = (th.1 : ℂ) ^ s * _
  rw [RayCoset.gδ_normalizedEmbedding_smul D δ α u (q th) hq, he]

theorem integrand_unit_shift_ae (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (u : RayCoset.U K D.m) :
    integrand D δ (u • α) s =ᵐ[μB D]
      (fun th => integrand D δ α s
        (th.1, th.2 + RayCoset.logAbs K (Additive.ofMul (u : (𝓞 K)ˣ)))) := by
  have ht : ∀ᵐ th ∂μB D, 0 < th.1 := by
    exact Measure.quasiMeasurePreserving_fst.ae RayParity.ae_positiveHaar_pos
  filter_upwards [ht] with th hth
  exact integrand_unit_shift D δ α s u th hth

 theorem J_q (th : ℝ × RayCoset.logHyperplane K) (ht : 0 < th.1) :
    RayParity.J K (q th) = th.1 := by
  have hs : ∑ v : InfinitePlace K, (v.mult : ℝ) * th.2.val v = 0 := by
    have h : RayCoset.weightedLogSum K th.2.val = 0 := th.2.property
    simpa [RayCoset.weightedLogSum] using h
  have hdeg : (∑ v : InfinitePlace K, (v.mult : ℝ)) = (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast InfinitePlace.sum_mult_eq
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  unfold RayParity.J q
  simp_rw [mul_pow, ← Real.exp_nat_mul]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  rw [hs, Real.exp_zero, mul_one]
  have hp : ∀ n : ℕ, (th.1 ^ (1 / (Module.finrank ℚ K : ℝ))) ^ n =
      th.1 ^ ((1 / (Module.finrank ℚ K : ℝ)) * n) := by
    intro n
    rw [Real.rpow_mul ht.le, Real.rpow_natCast]
  simp_rw [hp]
  rw [← Real.rpow_sum_of_nonneg ht.le]
  rw [← Finset.mul_sum, hdeg, div_mul_cancel₀ _ hn, Real.rpow_one]
  intro v hv
  positivity

theorem integrand_eq_scaledMellin_ae (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D) (s : ℂ) :
    integrand D δ α s =ᵐ[μrad.prod (Theta.normalizedLogHaar K)]
      (fun th => ScaledMellin.integrand D δ α s (q th)) := by
  have ht : ∀ᵐ th ∂μrad.prod (Theta.normalizedLogHaar K), 0 < th.1 :=
    Measure.quasiMeasurePreserving_fst.ae RayParity.ae_positiveHaar_pos
  filter_upwards [ht] with th hth
  have hq : ∀ v, 0 < q th v := fun v =>
    mul_pos (Real.rpow_pos_of_pos hth _) (Real.exp_pos _)
  simp only [ScaledMellin.integrand, if_pos hq, J_q th hth]
  exact mul_comm _ _

theorem hasSum_integral_of_integrable_full (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D) (s : ℂ)
    (hf : Integrable (integrand D δ α s) (μrad.prod (Theta.normalizedLogHaar K))) :
    HasSum (fun u : RayCoset.U K D.m => ∫ th, integrand D δ (u • α) s th ∂μB D)
      ((RayCoset.rayUnitTorsionCard K D.m : ℂ) *
        ∫ th, integrand D δ α s th ∂(μrad.prod (Theta.normalizedLogHaar K))) := by
  have h := ProductUnfolding.hasSum_unit_slab D (integrand D δ α s) hf
  simp only [nsmul_eq_mul] at h
  apply h.congr_fun
  intro u
  exact integral_congr_ae (integrand_unit_shift_ae D δ α s u)

theorem hasSum_integral_norm_of_integrable_full (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D) (s : ℂ)
    (hf : Integrable (integrand D δ α s) (μrad.prod (Theta.normalizedLogHaar K))) :
    HasSum (fun u : RayCoset.U K D.m => ∫ th, ‖integrand D δ (u • α) s th‖ ∂μB D)
      ((RayCoset.rayUnitTorsionCard K D.m : ℝ) *
        ∫ th, ‖integrand D δ α s th‖ ∂(μrad.prod (Theta.normalizedLogHaar K))) := by
  have h := ProductUnfolding.hasSum_unit_slab D (fun th => ‖integrand D δ α s th‖) hf.norm
  simp only [nsmul_eq_mul] at h
  apply h.congr_fun
  intro u
  apply integral_congr_ae
  exact (integrand_unit_shift_ae D δ α s u).fun_comp norm

theorem measurable_q : Measurable (q (K := K)) := by
  apply measurable_pi_lambda
  intro v
  exact (measurable_fst.pow_const _).mul
    (Real.measurable_exp.comp ((measurable_pi_apply v).comp
      (measurable_subtype_coe.comp measurable_snd)))

theorem measurePreserving_q : MeasurePreserving (q (K := K))
    (μrad.prod (Theta.normalizedLogHaar K)) (RayParity.μ K) :=
  ⟨measurable_q, RadialPullback.map_q_eq⟩

theorem integrable_full (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    Integrable (integrand D δ α s) (μrad.prod (Theta.normalizedLogHaar K)) := by
  exact (measurePreserving_q.integrable_comp_of_integrable
    (ScaledMellin.integrable D δ α s hs)).congr
      (integrand_eq_scaledMellin_ae D δ α s).symm

theorem integral_full (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ th, integrand D δ α s th ∂(μrad.prod (Theta.normalizedLogHaar K))) =
      RayParity.κδ K δ s * (RayCoset.signδ D δ (RayCoset.orbitMk D α) : ℂ) *
        (RayCoset.normWeight D (RayCoset.orbitMk D α) : ℂ) ^ (-s) := by
  rw [integral_congr_ae (integrand_eq_scaledMellin_ae D δ α s)]
  have hm := (ScaledMellin.integrable D δ α s hs).aestronglyMeasurable
  rw [← RadialPullback.map_q_eq] at hm
  rw [← integral_map measurable_q.aemeasurable hm, RadialPullback.map_q_eq]
  exact ScaledMellin.integral D δ α s hs

theorem integral_norm_full (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ th, ‖integrand D δ α s th‖ ∂(μrad.prod (Theta.normalizedLogHaar K))) =
      ‖RayParity.κδ K δ (s.re : ℂ)‖ *
        RayCoset.normWeight D (RayCoset.orbitMk D α) ^ (-s.re) := by
  have he : (fun th => ‖integrand D δ α s th‖) =ᵐ[μrad.prod (Theta.normalizedLogHaar K)]
      (fun th => ‖ScaledMellin.integrand D δ α s (q th)‖) :=
    (integrand_eq_scaledMellin_ae D δ α s).fun_comp norm
  rw [integral_congr_ae he]
  have hm := (ScaledMellin.integrable_norm D δ α s hs).aestronglyMeasurable
  rw [← RadialPullback.map_q_eq] at hm
  rw [← integral_map measurable_q.aemeasurable hm, RadialPullback.map_q_eq]
  exact ScaledMellin.integral_norm D δ α s hs

theorem integrable (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) (u : RayCoset.U K D.m) :
    Integrable (integrand D δ (u • α) s) (μB D) := by
  exact (ProductUnfolding.integrable_unit_slab D (integrand D δ α s)
    (integrable_full D δ α s hs) u).congr (integrand_unit_shift_ae D δ α s u).symm

theorem hasSum_integral (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun u : RayCoset.U K D.m =>
      ∫ th, integrand D δ (u • α) s th ∂(μB D))
      ((RayCoset.rayUnitTorsionCard K D.m : ℂ) * RayParity.κδ K δ s *
        (RayCoset.signδ D δ (RayCoset.orbitMk D α) : ℂ) *
        (RayCoset.normWeight D (RayCoset.orbitMk D α) : ℂ) ^ (-s)) := by
  have h := hasSum_integral_of_integrable_full D δ α s (integrable_full D δ α s hs)
  rw [integral_full D δ α s hs] at h
  simpa only [mul_assoc] using h

theorem hasSum_integral_norm (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    HasSum (fun u : RayCoset.U K D.m =>
      ∫ th, ‖integrand D δ (u • α) s th‖ ∂(μB D))
      ((RayCoset.rayUnitTorsionCard K D.m : ℝ) *
        ‖RayParity.κδ K δ (s.re : ℂ)‖ *
        RayCoset.normWeight D (RayCoset.orbitMk D α) ^ (-s.re)) := by
  have h := hasSum_integral_norm_of_integrable_full D δ α s (integrable_full D δ α s hs)
  rw [integral_norm_full D δ α s hs] at h
  simpa only [mul_assoc] using h

theorem summable_integral_norm (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (α : RayCoset.Cx D)
    (s : ℂ) (hs : 0 < s.re) :
    Summable (fun u : RayCoset.U K D.m =>
      ∫ th, ‖integrand D δ (u • α) s th‖ ∂(μB D)) := by
  exact (hasSum_integral_norm D δ α s hs).summable

end DedekindZetaZeroFree.AbelianQuotient.RayParity.OrbitSlabMellin

end
