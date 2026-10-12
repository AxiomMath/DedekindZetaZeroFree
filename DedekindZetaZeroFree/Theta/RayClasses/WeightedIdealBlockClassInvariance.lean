module

public import DedekindZetaZeroFree.Theta.RayClasses.WeightedIdealBlocks
public import DedekindZetaZeroFree.Theta.Periods.RayUnits.LogHaarInvariance
public import DedekindZetaZeroFree.Theta.Profiles.PrincipalIdealCenteredShapeCovariance

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient NumberField NumberField.mixedEmbedding
open MeasureTheory

open NumberField DedekindZetaZeroFree.AbelianQuotient
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

-- Source attribution and Apache 2.0 credit: `hecke_ray_angular_transport`.
 def weightedIntegrand {m : Ideal (𝓞 F)}
 (η : DedekindZetaZeroFree.RayClassCharacter F m)
 (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) (h : RayCoset.logHyperplane F) : ℂ :=
 ∑' x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)},
 η (integralElementIdeal I x) *
 RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
  ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
   (-1 / (Module.finrank ℚ F : ℝ)) • Theta.traceEmbedding F x.val))
private theorem gaussian_shape (c : ℝ) (hc : c ≠ 0)
 (q : InfinitePlace F → ℝ) (hq : ∀ v, q v ≠ 0) (x : F) :
 RayParity.gδ F ∅ (RayParity.Q F q (c • Theta.traceEmbedding F x)) =
 Theta.mixedGaussian F x (fun v => c * q v) := by
 rw [Theta.mixedGaussian_eq_latticeGaussian F x _ (fun v => mul_ne_zero hc (hq v))]
 simp only [RayParity.gδ, Finset.prod_empty, one_mul]
 congr 1
 rw [← RayParity.Q_eq_traceRadialScale]
 apply (Theta.traceToMixed F).injective
 simp only [RayParity.Q, ContinuousLinearEquiv.apply_symm_apply, map_smul]
 ext v <;> simp [mixedSpaceOfRealSpace] <;> ring
private theorem span_unit (e : (𝓞 F)ˣ) :
 FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F (e : 𝓞 F)) = 1 := by
 rw [← FractionalIdeal.spanSingleton_one]
 apply FractionalIdeal.spanSingleton_eq_spanSingleton.mpr
 refine ⟨e⁻¹, ?_⟩
 change algebraMap (𝓞 F) F (↑e⁻¹ : 𝓞 F) * algebraMap (𝓞 F) F (e : 𝓞 F) = 1
 rw [← map_mul, Units.inv_mul, map_one]
 def unitEquiv (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (e : (𝓞 F)ˣ) :
 {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} ≃ {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} where
 toFun x := ⟨algebraMap (𝓞 F) F (e : 𝓞 F) * x.val, by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ x.2⟩
 invFun x := ⟨algebraMap (𝓞 F) F (↑e⁻¹ : 𝓞 F) * x.val, by
  rw [← Algebra.smul_def]; exact Submodule.smul_mem _ _ x.2⟩
 left_inv x := by
  apply Subtype.ext
  change algebraMap (𝓞 F) F (↑e⁻¹ : 𝓞 F) * (algebraMap (𝓞 F) F (e : 𝓞 F) * x.val) = x.val
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
 right_inv x := by
  apply Subtype.ext
  change algebraMap (𝓞 F) F (e : 𝓞 F) * (algebraMap (𝓞 F) F (↑e⁻¹ : 𝓞 F) * x.val) = x.val
  rw [← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
private theorem coefficient_unit (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (e : (𝓞 F)ˣ)
 (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
 integralElementIdeal I (unitEquiv I e x) = integralElementIdeal I x := by
 apply FractionalIdeal.coeIdeal_injective (K := F)
 change (integralElementIdeal I (unitEquiv I e x) : FractionalIdeal (𝓞 F)⁰ F) = (integralElementIdeal I x : FractionalIdeal (𝓞 F)⁰ F)
 rw [integralElementIdeal_coe, integralElementIdeal_coe]
 change FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F (e : 𝓞 F) * x.val) * _ = _
 rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, span_unit, one_mul]
private theorem weighted_periodic {m : Ideal (𝓞 F)}
 (η : DedekindZetaZeroFree.RayClassCharacter F m)
 (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) (hu : 0 < u)
 (γ : RayCoset.rayUnitLogLattice F m) (h : RayCoset.logHyperplane F) :
 weightedIntegrand η I u (h+γ) = weightedIntegrand η I u h := by
 obtain ⟨e, he⟩ := γ.property
 let ε : (𝓞 F)ˣ := e.toMul.val
 have hg : (γ : RayCoset.logHyperplane F) = RayCoset.logAbs F (Additive.ofMul ε) := he.symm
 have hq (h : RayCoset.logHyperplane F) (v : InfinitePlace F) : RayTheta.q F u h v ≠ 0 := by
  exact mul_ne_zero (Real.rpow_pos_of_pos hu _).ne' (Real.exp_pos _).ne'
 have hn : (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^ (-1 / (Module.finrank ℚ F : ℝ)) ≠ 0 := by
  apply (Real.rpow_pos_of_pos _ _).ne'
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _) (Ne.symm (fun hz => Units.ne_zero I (FractionalIdeal.absNorm_eq_zero_iff.mp hz)))
 have hshape : ∀ v, RayTheta.q F u (h+γ) v = v (algebraMap (𝓞 F) F (ε : 𝓞 F)) * RayTheta.q F u h v := by
  intro v
  simp only [RayTheta.q, hg, Submodule.coe_add, Pi.add_apply, RayCoset.logAbs_apply, Real.exp_add]
  change u ^ (Module.finrank ℚ F : ℝ)⁻¹ * (Real.exp (h.val v) * Real.exp (Real.log (v (algebraMap (𝓞 F) F (ε : 𝓞 F))))) = _
  rw [Real.exp_log (NumberField.Units.pos_at_place ε v)]
  ring
 unfold weightedIntegrand
 simp_rw [gaussian_shape _ hn _ (hq _) ]
 symm
 rw [← (unitEquiv I ε).tsum_eq]
 apply tsum_congr
 intro x
 rw [coefficient_unit]
 congr 1
 change Theta.mixedGaussian F (algebraMap (𝓞 F) F (ε : 𝓞 F) * x.val) _ = _
 rw [Theta.mixedGaussian_mul_unit]
 congr 1
 ext v
 rw [hshape]
 ring
private theorem periodic_translation_without_continuity
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : RayCoset.logHyperplane F → ℂ)
    (hperiodic : ∀ (γ : RayCoset.rayUnitLogLattice F m)
      (h : RayCoset.logHyperplane F), f (h + (γ : RayCoset.logHyperplane F)) = f h)
    (v : RayCoset.logHyperplane F) :
    (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
      f (h + v) ∂Theta.normalizedLogHaar F) =
      ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        f h ∂Theta.normalizedLogHaar F := by
  classical
  letI := RayCoset.isZLattice_rayUnitLogLattice F m hm
  let L := RayCoset.rayUnitLogLattice F m
  let D := RayCoset.rayUnitHalfOpenDomain F m hm
  let μ := Theta.normalizedLogHaar F
  have hD : IsAddFundamentalDomain L D μ :=
    RayCoset.isAddFundamentalDomain_rayUnitHalfOpenDomain F m hm
  letI : VAddInvariantMeasure L (RayCoset.logHyperplane F) μ := ⟨fun g s hs =>
    (measurePreserving_add_left μ (g : RayCoset.logHyperplane F)).measure_preimage
      hs.nullMeasurableSet⟩
  have hp : ∀ (g : L) h, f (g +ᵥ h) = f h := by
    intro g h
    change f ((g : RayCoset.logHyperplane F) + h) = f h
    rw [add_comm]
    exact hperiodic g h
  let e : RayCoset.logHyperplane F ≃ᵐ RayCoset.logHyperplane F :=
    MeasurableEquiv.addRight v
  have he : MeasurePreserving e μ μ :=
    ⟨e.measurable, by simpa [e] using map_add_right_eq_self μ v⟩
  have hT : IsAddFundamentalDomain L (e '' D) μ := by
    apply hD.image_of_equiv e.toEquiv ?_ (Equiv.refl L) ?_
    · exact (measurePreserving_add_right μ (-v)).quasiMeasurePreserving
    · intro g h
      change ((g : RayCoset.logHyperplane F) + h) + v =
        (g : RayCoset.logHyperplane F) + (h + v)
      exact add_assoc _ _ _
  calc
    _ = ∫ h in e '' D, f h ∂μ :=
      (he.setIntegral_image_emb e.measurableEmbedding f D).symm
    _ = ∫ h in D, f h ∂μ := hT.setIntegral_eq hD hp

private theorem periodic_negation_without_continuity
    (F : Type) [Field F] [NumberField F]
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (f : RayCoset.logHyperplane F → ℂ)
    (hperiodic : ∀ (γ : RayCoset.rayUnitLogLattice F m)
      (h : RayCoset.logHyperplane F), f (h + (γ : RayCoset.logHyperplane F)) = f h) :
    (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
      f (-h) ∂Theta.normalizedLogHaar F) =
      ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
        f h ∂Theta.normalizedLogHaar F := by
  classical
  letI := RayCoset.isZLattice_rayUnitLogLattice F m hm
  let L := RayCoset.rayUnitLogLattice F m
  let D := RayCoset.rayUnitHalfOpenDomain F m hm
  let μ := Theta.normalizedLogHaar F
  have hD : IsAddFundamentalDomain L D μ :=
    RayCoset.isAddFundamentalDomain_rayUnitHalfOpenDomain F m hm
  letI : VAddInvariantMeasure L (RayCoset.logHyperplane F) μ := ⟨fun g s hs =>
    (measurePreserving_add_left μ (g : RayCoset.logHyperplane F)).measure_preimage
      hs.nullMeasurableSet⟩
  have hp : ∀ (g : L) h, f (g +ᵥ h) = f h := by
    intro g h
    change f ((g : RayCoset.logHyperplane F) + h) = f h
    rw [add_comm]
    exact hperiodic g h
  let e : RayCoset.logHyperplane F ≃ᵐ RayCoset.logHyperplane F :=
    MeasurableEquiv.neg (RayCoset.logHyperplane F)
  have he : MeasurePreserving e μ μ := Measure.measurePreserving_neg μ
  have hT : IsAddFundamentalDomain L (e '' D) μ := by
    apply hD.image_of_equiv e.toEquiv ?_ (Equiv.neg L) ?_
    · exact (Measure.measurePreserving_neg μ).quasiMeasurePreserving
    · intro g h
      change -(-(g : RayCoset.logHyperplane F) + h) =
        (g : RayCoset.logHyperplane F) + -h
      simp [add_comm]
  calc
    _ = ∫ h in e '' D, f h ∂μ :=
      (he.setIntegral_image_emb e.measurableEmbedding f D).symm
    _ = ∫ h in D, f h ∂μ := hT.setIntegral_eq hD hp

private theorem weightedNeg_eq (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) (hu : 0 < u) :
    weightedIdealBlockNeg hF hm hmt η I u = weightedIdealBlock hF hm hmt η I u := by
  unfold weightedIdealBlockNeg weightedIdealBlock
  rw [if_pos hu, if_pos hu]
  change _ * (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
    weightedIntegrand η I u (-h) ∂Theta.normalizedLogHaar F) =
      _ * (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
    weightedIntegrand η I u h ∂Theta.normalizedLogHaar F)
  rw [periodic_negation_without_continuity F m hm (weightedIntegrand η I u)
    (weighted_periodic η I u hu)]

theorem weightedIdealBlockNeg_eq_weightedIdealBlock
    (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (u : ℝ) (hu : 0 < u) :
    weightedIdealBlockNeg hF hm hmt η I u = weightedIdealBlock hF hm hmt η I u := by
  exact weightedNeg_eq hF hm hmt η I u hu

private theorem gaussian_scale (q : InfinitePlace F → ℝ) (hq : ∀ v, q v ≠ 0)
    (c : ℝ) (hc : c ≠ 0) (x : F) :
    RayParity.gδ F ∅ (RayParity.Q F q (c • Theta.traceEmbedding F x)) =
      Theta.mixedGaussian F x (fun v => c * q v) := by
  simp only [RayParity.gδ, Finset.prod_empty, one_mul]
  rw [Theta.mixedGaussian_eq_latticeGaussian F x (fun v => c * q v)
    (fun v => mul_ne_zero hc (hq v))]
  rw [← RayParity.Q_eq_traceRadialScale]
  congr 1
  apply (Theta.traceToMixed F).injective
  simp only [RayParity.Q, ContinuousLinearEquiv.apply_symm_apply, map_smul]
  ext v <;> simp [mixedSpaceOfRealSpace, mul_assoc, mul_left_comm, smul_eq_mul]

 def idealMulEquiv (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F)) :
    {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} ≃
      {x : F // x ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} := by
  have h := FractionalIdeal.eq_spanSingleton_mul.mp hJ
  let f : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)} →
      {x : F // x ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} := fun x => ⟨a * x, h.2 x x.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    exact mul_left_cancel₀ (Units.ne_zero a) (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨x, hx, he⟩ := h.1 y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext he⟩

private theorem idealMulEquiv_val (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F))
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    (idealMulEquiv I J a hJ x).val = a * x := rfl

private theorem idealMulEquiv_coeff (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F))
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    integralElementIdeal J (idealMulEquiv I J a hJ x) = integralElementIdeal I x := by
  apply FractionalIdeal.coeIdeal_injective (K := F)
  change (integralElementIdeal J (idealMulEquiv I J a hJ x) : FractionalIdeal (𝓞 F)⁰ F) =
    (integralElementIdeal I x : FractionalIdeal (𝓞 F)⁰ F)
  rw [integralElementIdeal_coe, integralElementIdeal_coe, idealMulEquiv_val,
    ← FractionalIdeal.spanSingleton_mul_spanSingleton]
  have hJu : J = (toPrincipalIdeal (𝓞 F) F a) * I := by
    apply Units.ext
    simpa using hJ
  rw [hJu]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val]
  have h : FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) =
    (toPrincipalIdeal (𝓞 F) F a : FractionalIdeal (𝓞 F)⁰ F) := (coe_toPrincipalIdeal a).symm
  rw [h, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  have hinv : ↑(((toPrincipalIdeal (𝓞 F) F) a * I)⁻¹) =
      (↑((toPrincipalIdeal (𝓞 F) F) a)⁻¹ : FractionalIdeal (𝓞 F)⁰ F) * ↑I⁻¹ := by
    simp [mul_comm]
  rw [hinv]
  calc
    _ = FractionalIdeal.spanSingleton (𝓞 F)⁰ (x : F) *
      (↑((toPrincipalIdeal (𝓞 F) F) a) * ↑((toPrincipalIdeal (𝓞 F) F) a)⁻¹) * ↑I⁻¹ := by ring
    _ = _ := by simp [← Units.val_mul]

private theorem norm_pos (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
    0 < (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) := by
  exact_mod_cast lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
    (Ne.symm (fun h => Units.ne_zero I (FractionalIdeal.absNorm_eq_zero_iff.mp h)))

 def normShape (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (t : ℝ) (h : RayCoset.logHyperplane F) (v : InfinitePlace F) : ℝ :=
  (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
    (-1 / (Module.finrank ℚ F : ℝ)) * RayTheta.q F t h v

private theorem exists_normShape_shift
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ d : RayCoset.logHyperplane F, ∀ t h v,
      normShape I t (h + d) v = normShape J t h v * v (a : F) := by
  classical
  let N : ℝ := (|(Algebra.norm ℚ) (a : F)| : ℚ)
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast abs_pos.mpr (Algebra.norm_ne_zero_iff.mpr (Units.ne_zero a))
  have ha : ∀ v : InfinitePlace F, 0 < v (a : F) :=
    fun v => InfinitePlace.pos_iff.mpr (Units.ne_zero a)
  have hlog : ∑ v : InfinitePlace F, (v.mult : ℝ) * Real.log (v (a : F)) =
      Real.log N := by
    have h := congrArg Real.log (InfinitePlace.prod_eq_abs_norm (a : F))
    simpa only [Real.log_prod (fun v _ => pow_ne_zero _ (ha v).ne'), Real.log_pow, N] using h
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  let d : RayCoset.logHyperplane F := ⟨fun v => Real.log (v (a : F)) -
    Real.log N / (Module.finrank ℚ F : ℝ), by
      change RayCoset.weightedLogSum F _ = 0
      simp only [RayCoset.weightedLogSum, LinearMap.sum_apply, LinearMap.smul_apply,
        LinearMap.proj_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hlog]
      have hmult : ∑ v : InfinitePlace F, (v.mult : ℝ) = Module.finrank ℚ F := by
        exact_mod_cast (InfinitePlace.sum_mult_eq : ∑ v : InfinitePlace F, v.mult = Module.finrank ℚ F)
      rw [hmult]
      field_simp
      ring⟩
  refine ⟨d, ?_⟩
  intro t h v
  have habs : (FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 F)⁰ F) : ℝ) =
      N * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) := by
    rw [hJ, map_mul, FractionalIdeal.absNorm_span_singleton]
    simp [N]
  have he : Real.exp ((d : InfinitePlace F → ℝ) v) =
      v (a : F) * N ^ (-1 / (Module.finrank ℚ F : ℝ)) := by
    dsimp [d]
    rw [Real.exp_sub, Real.exp_log (ha v), Real.rpow_def_of_pos hN]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  unfold normShape RayTheta.q
  rw [habs, Real.mul_rpow hN.le (norm_pos I).le]
  change _ * (_ * Real.exp ((h : InfinitePlace F → ℝ) v + (d : InfinitePlace F → ℝ) v)) = _
  rw [Real.exp_add, he]
  ring

private theorem weighted_series_covariance
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (a : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F))
    (η : Ideal (𝓞 F) → ℂ) :
    ∃ d : RayCoset.logHyperplane F, ∀ t h,
      (∑' x : {x : F // x ∈ (J : FractionalIdeal (𝓞 F)⁰ F)},
        η (integralElementIdeal J x) * Theta.mixedGaussian F x.val (normShape J t h)) =
      ∑' x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)},
        η (integralElementIdeal I x) * Theta.mixedGaussian F x.val (normShape I t (h + d)) := by
  obtain ⟨d, hd⟩ := exists_normShape_shift I J a hJ
  refine ⟨d, ?_⟩
  intro t h
  rw [← (idealMulEquiv I J a hJ).tsum_eq]
  apply tsum_congr
  intro x
  rw [idealMulEquiv_coeff, idealMulEquiv_val]
  congr 1
  unfold Theta.mixedGaussian
  congr 3
  apply Finset.sum_congr rfl
  intro v _
  rw [map_mul, hd]
  ring

private theorem gaussian_normShape (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    {t : ℝ} (ht : 0 < t) (h : RayCoset.logHyperplane F) (x : F) :
    RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F t h)
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
        (-1 / (Module.finrank ℚ F : ℝ)) • Theta.traceEmbedding F x)) =
      Theta.mixedGaussian F x (normShape I t h) := by
  apply gaussian_scale
  · intro v
    exact (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)).ne'
  · exact (Real.rpow_pos_of_pos (norm_pos I) _).ne'

private theorem exists_principal_of_class_eq
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hc : ClassGroup.mk F I = ClassGroup.mk F J) :
    ∃ a : Fˣ, (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * (I : FractionalIdeal (𝓞 F)⁰ F) := by
  have h : (ClassGroup.equiv F) (ClassGroup.mk F I) =
      (ClassGroup.equiv F) (ClassGroup.mk F J) := congrArg (ClassGroup.equiv F) hc
  simp only [ClassGroup.equiv_mk, QuotientGroup.mk'_eq_mk', MonoidHom.mem_range] at h
  obtain ⟨_, ⟨a, rfl⟩, ha⟩ := h
  refine ⟨a, ?_⟩
  have he := congrArg (fun u : (FractionalIdeal (𝓞 F)⁰ F)ˣ => (u : FractionalIdeal (𝓞 F)⁰ F)) ha
  simpa [mul_comm] using he.symm

theorem weightedIdealBlock_class_invariant
    (hF : NumberField.IsTotallyComplex F)
    {m : Ideal (𝓞 F)} (hm : m ≠ ⊥) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (hclass : ClassGroup.mk F I = ClassGroup.mk F J)
    (u : ℝ) (hu : 0 < u) :
    weightedIdealBlock hF hm hmt η I u =
      weightedIdealBlock hF hm hmt η J u := by
  obtain ⟨a, ha⟩ := exists_principal_of_class_eq I J hclass
  obtain ⟨d, hd⟩ := weighted_series_covariance I J a ha η
  have hpoint : ∀ h : RayCoset.logHyperplane F,
      weightedIntegrand η J u h = weightedIntegrand η I u (h + d) := by
    intro h
    unfold weightedIntegrand
    simp_rw [gaussian_normShape _ hu]
    exact hd u h
  unfold weightedIdealBlock
  rw [if_pos hu, if_pos hu]
  change _ * (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
    weightedIntegrand η I u h ∂Theta.normalizedLogHaar F) =
      _ * (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
    weightedIntegrand η J u h ∂Theta.normalizedLogHaar F)
  have hint : (∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
      weightedIntegrand η J u h ∂Theta.normalizedLogHaar F) =
    ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
      weightedIntegrand η I u (h+d) ∂Theta.normalizedLogHaar F :=
    integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [hint]
  rw [periodic_translation_without_continuity F m hm (weightedIntegrand η I u)
    (weighted_periodic η I u hu) d]

end DedekindZetaZeroFree.Hecke.Theta

end
