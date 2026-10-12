module

public import DedekindZetaZeroFree.Theta.Unfolding.ParitySlabAbsoluteSummability
public import DedekindZetaZeroFree.Theta.RayClasses.FunctionalEquationPair

@[expose] public section

noncomputable section

open Classical NumberField MeasureTheory

namespace DedekindZetaZeroFree.AbelianQuotient.RayParity.ThetaMellinIntegral

variable {K : Type} [Field K] [NumberField K]

 instance radSFinite : SFinite OrbitSlabMellin.μrad := by
  change SFinite RayParity.«μ₊»
  infer_instance

 def cosetLatticeEquiv (D : RayCoset.Data K) :
    RayCoset.C D ≃ RayCoset.normalizedLattice D :=
  (RayCoset.normalizedEmbedding_bijOn D).equiv (RayCoset.normalizedEmbedding D) |>.trans
    { toFun := fun x => ⟨x.val - RayCoset.normalizedBasepoint D, x.property⟩
      invFun := fun x => ⟨RayCoset.normalizedBasepoint D + x.val, by
        change RayCoset.normalizedBasepoint D + x.val - RayCoset.normalizedBasepoint D ∈ RayCoset.normalizedLattice D
        simpa using x.property⟩
      left_inv := fun x => by apply Subtype.ext; dsimp; abel
      right_inv := fun x => by apply Subtype.ext; dsimp; abel }

private theorem cosetLatticeEquiv_apply (D : RayCoset.Data K) (α : RayCoset.C D) :
    RayCoset.normalizedBasepoint D + (cosetLatticeEquiv D α).val =
      RayCoset.normalizedEmbedding D α.val := by
  change RayCoset.normalizedBasepoint D +
    (RayCoset.normalizedEmbedding D α.val - RayCoset.normalizedBasepoint D) = _
  abel

 def nonzeroCosetEquiv (D : RayCoset.Data K) :
    RayCoset.Cx D ≃ {α : RayCoset.C D // α.val ≠ 0} where
  toFun α := ⟨⟨α.val, α.property.1⟩, by simpa using α.property.2⟩
  invFun α := ⟨α.val.val, α.val.property, by simpa using α.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem zero_mem_iff (D : RayCoset.Data K) :
    (0 : 𝓞 K) ∈ RayCoset.C D ↔
      (0 : NumberField.mixedEmbedding.euclidean.mixedSpace K) ∈
        RayCoset.normalizedAffineCoset D := by
  constructor
  · intro h
    simpa only [map_zero] using (RayCoset.normalizedEmbedding_bijOn D).1 h
  · intro h
    obtain ⟨α, hα, he⟩ := (RayCoset.normalizedEmbedding_bijOn D).2.2 h
    have hi : Function.Injective (RayCoset.normalizedEmbedding D) := by
      intro x y hxy
      apply RingOfIntegers.coe_injective
      apply NumberField.mixedEmbedding_injective K
      have hh := (smul_right_injective _ (RayCoset.normalizationScale_pos D).ne').eq_iff.mp hxy
      simpa [Theta.traceEmbedding] using congrArg (Theta.traceToMixed K) hh
    have : α = 0 := hi (he.trans (map_zero _).symm)
    simpa [this] using hα

private theorem theta_sum_split (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (t : ℝ) (ht : 0 < t)
    (h : RayCoset.logHyperplane K) :
    (∑' ℓ : RayCoset.normalizedLattice D,
      gδ K δ (Q K (RayTheta.q K t h)
        (RayCoset.normalizedBasepoint D + ℓ.val))) =
      (∑' α : RayCoset.Cx D, gδ K δ
        (Q K (RayTheta.q K t h) (RayCoset.normalizedEmbedding D α.val))) +
      (if δ = ∅ ∧ (0 : 𝓞 K) ∈ RayCoset.C D then 1 else 0) := by
  letI := RayCoset.normalizedLattice_discrete D
  letI := RayCoset.normalizedLattice_isZLattice D
  let f : RayCoset.C D → ℂ := fun α =>
    gδ K δ (Q K (RayTheta.q K t h) (RayCoset.normalizedEmbedding D α.val))
  have heq : (∑' ℓ : RayCoset.normalizedLattice D,
      gδ K δ (Q K (RayTheta.q K t h)
        (RayCoset.normalizedBasepoint D + ℓ.val))) = ∑' α, f α := by
    rw [← (cosetLatticeEquiv D).tsum_eq]
    simp only [cosetLatticeEquiv_apply, f]
  have hf : Summable f := by
    have hl := (ShiftedPoisson.poisson K (RayCoset.normalizedLattice D) δ
      (RayTheta.q K t h)
      (fun v => mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _))
      (RayCoset.normalizedBasepoint D)).2.2.summable
    have hc := (cosetLatticeEquiv D).summable_iff.mpr hl
    simpa only [Function.comp_def, cosetLatticeEquiv_apply, f] using hc
  have hnon : (∑' α : RayCoset.Cx D, gδ K δ
      (Q K (RayTheta.q K t h) (RayCoset.normalizedEmbedding D α.val))) =
      ∑' α : {α : RayCoset.C D // α.val ≠ 0}, f α.val := by
    rw [← (nonzeroCosetEquiv D).tsum_eq]
    rfl
  rw [heq, hnon]
  by_cases hz : (0 : 𝓞 K) ∈ RayCoset.C D
  · let z : RayCoset.C D := ⟨0, hz⟩
    have hn : (∑' α : {α : RayCoset.C D // α.val ≠ 0}, f α.val) =
        ∑' α : {α : RayCoset.C D // α ∉ ({z} : Finset _)}, f α.val := by
      apply tsum_congr_set_coe
      ext α
      simp [z, Subtype.ext_iff]
    rw [hn, ← hf.sum_add_tsum_subtype_compl {z}]
    have hfz : f z = if δ = ∅ then 1 else 0 := by
      change gδ K δ (Q K (RayTheta.q K t h) (RayCoset.normalizedEmbedding D 0)) = _
      rw [map_zero]
      have hQ : Q K (RayTheta.q K t h) 0 = 0 := by simp [Q]
      rw [hQ, AffineFourier.gδ_zero]
    simp only [Finset.sum_singleton, hfz]
    by_cases hd : δ = ∅ <;> simp [hd, hz, add_comm]
  · let e : RayCoset.C D ≃ {α : RayCoset.C D // α.val ≠ 0} :=
      { toFun := fun α => ⟨α, fun hh => hz (hh ▸ α.property)⟩
        invFun := Subtype.val
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← e.tsum_eq]
    simp [hz, e]

theorem ae_weighted_tail_eq (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    ∀ᵐ t : ℝ ∂OrbitSlabMellin.μrad,
      (t : ℂ) ^ s * (RayTheta.fδ D δ t - RayTheta.f0δ D δ) =
        (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹ *
          ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
            (∑' α : RayCoset.Cx D, OrbitSlabMellin.integrand D δ α s (t, h))
            ∂Theta.normalizedLogHaar K := by
  let ν := (Theta.normalizedLogHaar K).restrict
    (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
  letI : IsFiniteMeasure ν :=
    (isFiniteMeasure_restrict).mpr
      (RayCoset.measure_rayUnitHalfOpenDomain_lt_top K D.m D.modulus_ne_bot).ne
  have hi := (SlabAbsoluteSummability.integrable_tsum D δ s hs).prod_right_ae
  filter_upwards [hi, RayParity.ae_positiveHaar_pos] with t hit ht
  let G : RayCoset.logHyperplane K → ℂ := fun h =>
    ∑' α : RayCoset.Cx D, gδ K δ
      (Q K (RayTheta.q K t h) (RayCoset.normalizedEmbedding D α.val))
  let c : ℂ := if δ = ∅ ∧ (0 : 𝓞 K) ∈ RayCoset.C D then 1 else 0
  have hF (h : RayCoset.logHyperplane K) :
      (∑' α : RayCoset.Cx D, OrbitSlabMellin.integrand D δ α s (t,h)) =
      (t : ℂ)^s * G h := by
    simp only [OrbitSlabMellin.integrand, OrbitSlabMellin.q, RayTheta.q, G, one_div]
    rw [tsum_mul_left]
    congr 1
    apply tsum_congr
    intro α
    congr 2
    funext v
    simp [OrbitSlabMellin.q, RayTheta.q, one_div]
  have hp : (t : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast ht.ne'))
  have hG : Integrable G ν := by
    have hii : Integrable (fun h => (t : ℂ)^s * G h) ν := by
      simpa only [hF] using hit
    convert hii.const_mul ((t : ℂ)^s)⁻¹ using 1
    ext h
    simp [← mul_assoc, hp]
  have hsum : (∫ h, (∑' ℓ : RayCoset.normalizedLattice D,
      gδ K δ (Q K (RayTheta.q K t h)
        (RayCoset.normalizedBasepoint D + ℓ.val))) ∂ν) =
        (∫ h, G h ∂ν) + (∫ h, c ∂ν) := by
    simp_rw [theta_sum_split D δ t ht]
    exact integral_add hG (integrable_const c)
  have hc : (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹ * (∫ h, c ∂ν) =
      RayTheta.f0δ D δ := by
    have hv : ν.real Set.univ = RayCoset.rayUnitDomainVolume K D.m D.modulus_ne_bot := by
      simp [ν, Measure.real, RayCoset.rayUnitDomainVolume]
    rw [integral_const, hv]
    simp only [RayTheta.f0δ, ← zero_mem_iff D]
    by_cases hh : δ = ∅ ∧ (0 : 𝓞 K) ∈ RayCoset.C D
    · simp [c, hh, div_eq_mul_inv, mul_comm]
    · simp [c, hh]
  simp_rw [hF]
  rw [integral_const_mul]
  rw [RayTheta.fδ, if_pos ht]
  change (t : ℂ)^s *
    ((RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹ * _ - _) = _
  rw [hsum, ← hc]
  ring

theorem mellinConvergent (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    MellinConvergent (fun t : ℝ => RayTheta.fδ D δ t - RayTheta.f0δ D δ) s := by
  exact (RayTheta.Pδ D δ).hasMellin (s := s) hs |>.1

theorem mellin_eq_integral_tsum (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    mellin (fun t : ℝ => RayTheta.fδ D δ t - RayTheta.f0δ D δ) s =
      (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹ *
        ∫ p, (∑' α : RayCoset.Cx D, OrbitSlabMellin.integrand D δ α s p)
          ∂(OrbitSlabMellin.μB D) := by
  let ν := (Theta.normalizedLogHaar K).restrict
    (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
  letI : IsFiniteMeasure ν :=
    (isFiniteMeasure_restrict).mpr
      (RayCoset.measure_rayUnitHalfOpenDomain_lt_top K D.m D.modulus_ne_bot).ne
  have hconvert : (∫ t : ℝ,
      (t : ℂ) ^ s * (RayTheta.fδ D δ t - RayTheta.f0δ D δ)
        ∂OrbitSlabMellin.μrad) =
      mellin (fun t : ℝ => RayTheta.fδ D δ t - RayTheta.f0δ D δ) s := by
    rw [OrbitSlabMellin.μrad, Theta.positiveRadialHaar]
    rw [integral_withDensity_eq_integral_toReal_smul (by measurability)
      (by filter_upwards with t; exact ENNReal.ofReal_lt_top)]
    unfold mellin
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr ht)),
      RCLike.real_smul_eq_coe_mul, smul_eq_mul]
    rw [Complex.cpow_sub s 1 ht0, Complex.cpow_one, div_eq_mul_inv]
    rw [show RCLike.ofReal t⁻¹ = (↑t)⁻¹ from Complex.ofReal_inv t]
    ring
  rw [← hconvert]
  rw [integral_congr_ae (ae_weighted_tail_eq D δ s hs), integral_const_mul]
  congr 1
  exact (integral_prod _ (SlabAbsoluteSummability.integrable_tsum D δ s hs)).symm

theorem hasMellin (D : RayCoset.Data K)
    (δ : Finset (RayCoset.RealPlaces K)) (s : ℂ) (hs : 1 < s.re) :
    HasMellin (fun t : ℝ => RayTheta.fδ D δ t - RayTheta.f0δ D δ) s
      (κδ K δ s * RayCoset.Zδ D δ s) := by
  refine ⟨mellinConvergent D δ s hs, ?_⟩
  rw [mellin_eq_integral_tsum D δ s hs]
  rw [SlabAbsoluteSummability.integral_tsum D δ s hs]
  have hw : (RayCoset.rayUnitTorsionCard K D.m : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (RayCoset.rayUnitTorsionCard_pos K D.m))
  field_simp

end DedekindZetaZeroFree.AbelianQuotient.RayParity.ThetaMellinIntegral

end
