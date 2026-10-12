module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.ResidualFlatRange.Source
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance sourceStageBorel (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance sourceStageBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩
local instance sourceStageTopGroup : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1

def alpha (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K) (g : G F ζ hζ) : ℂ :=
  (Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) g : NNReal) : ℝ)) : ℂ)

def source (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ)
    (h : C(K, ℂ)) : Functions F ζ hζ :=
  fun g => Complex.exp (-s * alpha F ζ hζ K hK g) *
    ∫ k : K, h k * f.val s (g * k.val * a) ∂μ

def kernelTranslate (K : Subgroup (G F ζ hζ)) (b : K) : C(K, ℂ) →ₗ[ℂ] C(K, ℂ) where
  toFun h := ⟨fun k => h (b⁻¹ * k), h.continuous.comp (continuous_const.mul continuous_id)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def kernelRepresentation (K : Subgroup (G F ζ hζ)) : Representation ℂ K C(K, ℂ) where
  toFun := kernelTranslate F ζ hζ K
  map_one' := by ext h k; simp [kernelTranslate]
  map_mul' b c := by
    ext h k
    change h ((b * c)⁻¹ * k) = h (c⁻¹ * (b⁻¹ * k))
    rw [mul_inv_rev, mul_assoc]

lemma alpha_right_compact (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (g : G F ζ hζ) (b : K) : alpha F ζ hζ K hK (g * b.val) = alpha F ζ hζ K hK g := by
  unfold alpha
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_right_compact F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) g b]

lemma source_intertwines (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ)
    (h : C(K, ℂ)) (b : K) :
    source F ζ hζ K hK μ f a s (kernelTranslate F ζ hζ K b h) =
      rightAction F ζ hζ b.val (source F ζ hζ K hK μ f a s h) := by
  ext g
  change Complex.exp (-s * alpha F ζ hζ K hK g) * (∫ k : K, h (b⁻¹ * k) * f.val s (g * k.val * a) ∂μ) =
    Complex.exp (-s * alpha F ζ hζ K hK (g * b.val)) * (∫ k : K, h k * f.val s ((g * b.val) * k.val * a) ∂μ)
  rw [alpha_right_compact]
  congr 1
  rw [← integral_mul_left_eq_self (fun k : K => h (b⁻¹ * k) * f.val s (g * k.val * a)) b]
  apply integral_congr_ae
  filter_upwards with k
  simp only [inv_mul_cancel_left, Subgroup.coe_mul, mul_assoc]

lemma source_integrable (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ)
    (h : C(K, ℂ)) (g : G F ζ hζ) :
    Integrable (fun k : K => h k * f.val s (g * k.val * a)) μ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  exact (h.continuous.mul ((f.property.1 s).1.1.comp
    ((continuous_const.mul continuous_subtype_val).mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

def sourceMap (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ) :
    C(K, ℂ) →ₗ[ℂ] Functions F ζ hζ where
  toFun := source F ζ hζ K hK μ f a s
  map_add' h l := by
    ext g
    simp only [source, ContinuousMap.add_apply, add_mul, Pi.add_apply]
    rw [integral_add (source_integrable F ζ hζ K hK μ f a s h g)
      (source_integrable F ζ hζ K hK μ f a s l g), mul_add]
  map_smul' c h := by
    ext g
    simp only [source, ContinuousMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]
    rw [integral_const_mul]
    simp only [RingHom.id_apply]
    ring

lemma source_continuous (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ)
    (h : C(K, ℂ)) : Continuous (source F ζ hζ K hK μ f a s h) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  have hc : Continuous (fun p : G F ζ hζ × K => h p.2 * f.val s (p.1 * p.2.val * a)) :=
    (h.continuous.comp continuous_snd).mul ((f.property.1 s).1.1.comp
      ((continuous_fst.mul (continuous_subtype_val.comp continuous_snd)).mul continuous_const))
  have hi : Continuous (fun g : G F ζ hζ => ∫ k : K, h k * f.val s (g * k.val * a) ∂μ) := by
    rw [← continuousOn_univ]
    exact continuousOn_integral_of_compact_support (μ := μ) isCompact_univ
      hc.continuousOn (fun _ _ _ hk => (hk (Set.mem_univ _)).elim)
  apply Continuous.mul _ hi
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (KPLiteralChamber.JointProfile.literal_log_modulus_continuous F ζ hζ K hK))).cexp

lemma alpha_borel (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (t : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    alpha F ζ hζ K hK ((t.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) : ℂ) +
        alpha F ζ hζ K hK g := by
  unfold alpha
  rw [KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) t x g,
    Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
      (NNReal.coe_ne_zero.mpr (Units.ne_zero _)), Complex.ofReal_add]

lemma source_covariance (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ) (h : C(K, ℂ))
    (r : R F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    source F ζ hζ K hK μ f a s h ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2) *
        (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
        source F ζ hζ K hK μ f a s h g := by
  let d : ℂ := (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) : ℂ)
  simp only [source, alpha_borel]
  have hi : (∫ k : K, h k * f.val s
      (((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) * k.val * a) ∂μ) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2 + s) *
          (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
            ∫ k : K, h k * f.val s (g * k.val * a) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k
    have hg : ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) * k.val * a =
        (r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * (g * k.val * a) := by group
    rw [hg, (f.property.1 s).2 r x]
    ring
  rw [hi]
  simp only [KPGlobalExceptionalParameter.realLogPower]
  have he : Complex.exp (-s * (d + alpha F ζ hζ K hK g)) * Complex.exp ((1 / 2 + s) * d) =
      Complex.exp ((1 / 2) * d) * Complex.exp (-s * alpha F ζ hζ K hK g) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  change Complex.exp (-s * (d + alpha F ζ hζ K hK g)) *
    (Complex.exp ((1 / 2 + s) * d) * _ * _) = Complex.exp ((1 / 2) * d) * _ * (Complex.exp (-s * alpha F ζ hζ K hK g) * _)
  calc
    _ = (Complex.exp (-s * (d + alpha F ζ hζ K hK g)) * Complex.exp ((1 / 2 + s) * d)) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) * (∫ k : K, h k * f.val s (g * k.val * a) ∂μ) := by ring
    _ = _ := by rw [he]; ring

def KernelFinite (K : Subgroup (G F ζ hζ)) (h : C(K, ℂ)) : Prop :=
  ∃ W : Submodule ℂ C(K, ℂ), Module.Finite ℂ W ∧ h ∈ W ∧
    ∀ b : K, ∀ l ∈ W, kernelTranslate F ζ hζ K b l ∈ W

lemma kernelFinite_matrixCoeff (K : Subgroup (G F ζ hζ))
    (n : ℕ) (π : ContRepresentation ℂ K (EuclideanSpace ℂ (Fin n)))
    (hπ : Continuous π) (v w : EuclideanSpace ℂ (Fin n)) :
    KernelFinite F ζ hζ K (TauCeti.ContRepresentation.matrixCoeff π hπ v w) := by
  let L := TauCeti.ContRepresentation.matrixCoeffₛₗ π hπ v
  refine ⟨L.range, Module.Finite.range L, ⟨w, rfl⟩, ?_⟩
  intro b l hl
  obtain ⟨w', rfl⟩ := hl
  refine ⟨(π b⁻¹).adjoint w', ?_⟩
  ext k
  change TauCeti.ContRepresentation.matrixCoeff π hπ v ((π b⁻¹).adjoint w') k =
    TauCeti.ContRepresentation.matrixCoeff π hπ v w' (b⁻¹ * k)
  simp only [TauCeti.ContRepresentation.matrixCoeff_apply, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  rw [← mul_apply_eq_comp, ← map_mul]

private lemma kernelFinite_add (K : Subgroup (G F ζ hζ)) (h l : C(K, ℂ))
    (hh : KernelFinite F ζ hζ K h) (hl : KernelFinite F ζ hζ K l) :
    KernelFinite F ζ hζ K (h + l) := by
  obtain ⟨W, hW, hhW, hWi⟩ := hh
  obtain ⟨V, hV, hlV, hVi⟩ := hl
  let := hW
  let := hV
  refine ⟨W ⊔ V, inferInstance, Submodule.add_mem_sup hhW hlV, ?_⟩
  intro b w hw
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
  rw [map_add]
  exact Submodule.add_mem_sup (hWi b x hx) (hVi b y hy)

private lemma kernelFinite_smul (K : Subgroup (G F ζ hζ)) (h : C(K, ℂ))
    (hh : KernelFinite F ζ hζ K h) (c : ℂ) :
    KernelFinite F ζ hζ K (c • h) := by
  obtain ⟨W, hW, hhW, hWi⟩ := hh
  exact ⟨W, hW, W.smul_mem c hhW, hWi⟩

lemma representative_kernelFinite (K : Subgroup (G F ζ hζ)) (h : C(K, ℂ))
    (hh : h ∈ TauCeti.representativeSubmodule ℂ K) : KernelFinite F ζ hζ K h := by
  rw [TauCeti.representativeSubmodule_eq_span] at hh
  induction hh using Submodule.span_induction with
  | mem h hh =>
      obtain ⟨n, π, hπ, v, w, rfl⟩ := TauCeti.isRepresentative_iff.mp hh
      exact kernelFinite_matrixCoeff F ζ hζ K n π hπ v w
  | zero =>
      refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
      intro b l hl
      rw [Submodule.mem_bot] at hl ⊢
      rw [hl, map_zero]
  | add h l _ _ ih₁ ih₂ => exact kernelFinite_add F ζ hζ K h l ih₁ ih₂
  | smul c h _ ih => exact kernelFinite_smul F ζ hζ K h ih c

lemma normalized_source_entire (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (h : C(K, ℂ)) (g : G F ζ hζ) :
    Differentiable ℂ (fun s => source F ζ hζ K hK μ f a s h g) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.1
  let o : C(K, G F ζ hζ) :=
    ⟨fun k => g * k.val * a, (continuous_const.mul continuous_subtype_val).mul continuous_const⟩
  let L : C(K, ℂ) :=
    ⟨fun k => alpha F ζ hζ K hK (o k) - alpha F ζ hζ K hK g,
      (Complex.continuous_ofReal.comp
        ((KPLiteralChamber.JointProfile.literal_log_modulus_continuous F ζ hζ K hK).comp
          o.continuous)).sub continuous_const⟩
  let b : C(K, ℂ) := ⟨fun k => h k * f.val 0 (o k),
    h.continuous.mul ((f.property.1 0).1.1.comp o.continuous)⟩
  let j : ℂ → C(K, ℂ) := fun s => NormedSpace.exp (s • L) * b
  have hj : Differentiable ℂ j :=
    (differentiable_exp_smul_const ℂ L).mul (differentiable_const b)
  let A : C(K, ℂ) →L[ℂ] ℂ :=
    (L1.integralCLM' ℂ).comp (ContinuousMap.toLp 1 μ ℂ)
  have hA (v : C(K, ℂ)) : A v = ∫ k, v k ∂μ := by
    change L1.integralCLM' ℂ (ContinuousMap.toLp 1 μ ℂ v) = _
    rw [← L1.integral_eq', L1.integral_eq_integral]
    exact integral_congr_ae (ContinuousMap.coeFn_toLp μ v)
  have he (s : ℂ) : A (j s) = source F ζ hζ K hK μ f a s h g := by
    rw [hA]
    unfold source
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with k
    rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f s]
    simp only [j, ContinuousMap.mul_apply, NormedSpace.exp_continuousMap_eq,
      ContinuousMap.coe_mk, Function.comp_apply, ContinuousMap.smul_apply,
      smul_eq_mul, L, b, o]
    simp only [← Complex.exp_eq_exp_ℂ]
    have he : Complex.exp (s * (alpha F ζ hζ K hK (g * k.val * a) - alpha F ζ hζ K hK g)) =
        Complex.exp (-s * alpha F ζ hζ K hK g) *
          Complex.exp (s * alpha F ζ hζ K hK (g * k.val * a)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [he]
    dsimp only [alpha]
    ring
  have heq : (fun s => A (j s)) = (fun s => source F ζ hζ K hK μ f a s h g) := funext he
  rw [← heq]
  exact A.differentiable.comp hj

lemma normalized_source_kfinite (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ)
    (h : C(K, ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    KFinite F ζ hζ K (source F ζ hζ K hK μ f a s h) := by
  obtain ⟨W, hW, hhW, hWi⟩ := representative_kernelFinite F ζ hζ K h hh
  let := hW
  let L := (sourceMap F ζ hζ K hK μ f a s).comp W.subtype
  refine ⟨L.range, Module.Finite.range L, ⟨⟨h, hhW⟩, rfl⟩, ?_⟩
  intro b u hu
  obtain ⟨l, rfl⟩ := hu
  refine ⟨⟨kernelTranslate F ζ hζ K b l.val, hWi b l.val l.property⟩, ?_⟩
  exact source_intertwines F ζ hζ K hK μ f a s l.val b

def kernelOn (K : Subgroup (G F ζ hζ)) (W : Submodule ℂ C(K, ℂ))
    (hi : ∀ b : K, ∀ h ∈ W, kernelTranslate F ζ hζ K b h ∈ W) :
    Representation ℂ K W where
  toFun b :=
    { toFun h := ⟨kernelTranslate F ζ hζ K b h.val, hi b h.val h.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext h k; simp [kernelTranslate]
  map_mul' b c := by
    ext h k
    change h.val ((b * c)⁻¹ * k) = h.val (c⁻¹ * (b⁻¹ * k))
    rw [mul_inv_rev, mul_assoc]

end DedekindZetaZeroFree.ResidualFlatRange.Source

end
