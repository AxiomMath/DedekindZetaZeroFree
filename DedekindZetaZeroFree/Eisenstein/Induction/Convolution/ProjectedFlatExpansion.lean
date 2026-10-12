module

public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.SourceSmoothness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField MeasureTheory
namespace DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion
open KPLiteralRaw
open KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming target_subgroup_eq → target_subgroup_eq
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming sourceH → sourceH
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming sourceChi → sourceChi
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming sourceChi_hN → sourceChi_hN
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming source_covariant → source_covariant
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.NormalizedFiniteSource renaming normalized_entire_finite_expansion → normalized_entire_finite_expansion
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.SourceSpatialRegularity renaming covariant_source_smooth → covariant_source_smooth
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming normalized_multiplier → normalized_multiplier
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming cToBorel → cToBorel
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance : IsTopologicalGroup (G F ζ hζ) :=
  (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
local instance (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

 theorem kfinite_add
    (K : Subgroup (G F ζ hζ)) (f v : Functions F ζ hζ)
    (hf : KFinite F ζ hζ K f) (hv : KFinite F ζ hζ K v) :
    KFinite F ζ hζ K (f + v) := by
  obtain ⟨S, hS, hfS, hSinv⟩ := hf
  obtain ⟨T, hT, hvT, hTinv⟩ := hv
  let := hS
  let := hT
  refine ⟨S ⊔ T, inferInstance, Submodule.add_mem_sup hfS hvT, ?_⟩
  intro k w hw
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hw
  exact Submodule.add_mem_sup (hSinv k s hs) (hTinv k t ht)

 theorem kfinite_smul
    (K : Subgroup (G F ζ hζ)) (f : Functions F ζ hζ)
    (hf : KFinite F ζ hζ K f) (c : ℂ) :
    KFinite F ζ hζ K (c • f) := by
  obtain ⟨S, hS, hfS, hSinv⟩ := hf
  exact ⟨S, hS, S.smul_mem c hfS, hSinv⟩

 def reweight (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (s : ℂ) : Functions F ζ hζ →ₗ[ℂ] Functions F ζ hζ where
  toFun v g := Complex.exp (s * alpha F ζ hζ K hK g) * v g
  map_add' := by intros; ext g; simp [mul_add]
  map_smul' := by intros; ext g; simp [mul_left_comm]

 def parameterChi (s : ℂ) : KPSpatialSmoothing.actualC F ζ hζ →* ℂ where
  toFun c := (KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
    (sourceH F ζ hζ c).val : ℂ) * sourceChi F ζ hζ c
  map_one' := by simp
  map_mul' := by intros; simp only [map_mul, Subgroup.coe_mul, Units.val_mul]; ring

private theorem sourceH_hN (r : (KPSpatialSmoothing.P0 F ζ hζ).H)
    (x : KPAdeles F) (c : KPSpatialSmoothing.actualC F ζ hζ)
    (he : c.val = r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) :
    sourceH F ζ hζ c = (MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ)) r := by
  have hh : KPSpatialSmoothing.actualHCoordinate F ζ hζ c = r := by
    have hb : cToBorel F ζ hζ c =
      ActualBorelRetraction.torusInBorel F ζ hζ r.val *
      ActualBorelRetraction.rootInBorel F ζ hζ (Multiplicative.ofAdd x) := Subtype.ext he
    apply Subtype.ext
    change ActualBorelRetraction.retraction F ζ hζ _ = r.val
    rw [hb, map_mul, ActualBorelRetraction.retraction_torus,
      ActualBorelRetraction.retraction_root, mul_one]
  change (MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ))
    (KPSpatialSmoothing.actualHCoordinate F ζ hζ c) = _
  rw [hh]

private theorem reweight_covariant
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (v : Functions F ζ hζ)
    (hv : ∀ c : KPSpatialSmoothing.actualC F ζ hζ, ∀ g,
      v (c.val * g) = sourceChi F ζ hζ c * v g)
    (s : ℂ) (c : KPSpatialSmoothing.actualC F ζ hζ) (g : G F ζ hζ) :
    reweight F ζ hζ K hK s v (c.val * g) =
      parameterChi F ζ hζ s c * reweight F ζ hζ K hK s v g := by
  obtain ⟨r, x, he⟩ := (KPSpatialSmoothing.mem_actualC_iff F ζ hζ c.val).mp c.property
  change Complex.exp (s * alpha F ζ hζ K hK (c.val * g)) * v (c.val * g) = _
  rw [hv]
  have hew : Complex.exp (s * alpha F ζ hζ K hK (c.val * g)) =
      (KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (sourceH F ζ hζ c).val : ℂ) * Complex.exp (s * alpha F ζ hζ K hK g) := by
    rw [sourceH_hN F ζ hζ r x c he, he]
    rw [alpha_borel, mul_add, Complex.exp_add]
    rfl
  rw [hew]
  change _ = (↑(KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
    (sourceH F ζ hζ c).val) * sourceChi F ζ hζ c) *
      (Complex.exp (s * alpha F ζ hζ K hK g) * v g)
  ring

private theorem reweight_continuous
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (s : ℂ) (v : Functions F ζ hζ) (hv : Continuous v) :
    Continuous (reweight F ζ hζ K hK s v) := by
  have ha : Continuous (alpha F ζ hζ K hK) :=
    Complex.continuous_ofReal.comp
      (KPLiteralChamber.JointProfile.literal_log_modulus_continuous F ζ hζ K hK)
  exact ((continuous_const.mul ha).cexp).mul hv

private theorem reweight_kfinite
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (s : ℂ) (v : Functions F ζ hζ) (hv : KFinite F ζ hζ K v) :
    KFinite F ζ hζ K (reweight F ζ hζ K hK s v) := by
  obtain ⟨S, hS, hvS, hSinv⟩ := hv
  let := hS
  let L := (reweight F ζ hζ K hK s).comp S.subtype
  refine ⟨L.range, Module.Finite.range L, ⟨⟨v, hvS⟩, rfl⟩, ?_⟩
  intro k u hu
  obtain ⟨w, rfl⟩ := hu
  refine ⟨⟨rightAction F ζ hζ k.val w.val, hSinv k w.val w.property⟩, ?_⟩
  ext g
  change Complex.exp (s * alpha F ζ hζ K hK g) * w.val (g * k.val) =
    Complex.exp (s * alpha F ζ hζ K hK (g * k.val)) * w.val (g * k.val)
  rw [alpha_right_compact]

private theorem normalized_source_span_properties
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (h : C(K, ℂ))
    (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ v ∈ Submodule.span ℂ
        (Set.range (fun s : ℂ => source F ζ hζ K hK μ f a s h)),
        Continuous v ∧
        (∀ c : KPSpatialSmoothing.actualC F ζ hζ, ∀ g,
          v (c.val * g) = sourceChi F ζ hζ c * v g) ∧
        (∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
          v (g * u) = v g) ∧ KFinite F ζ hζ K v := by
  obtain ⟨J, hJ⟩ := CommonLevel.source_uniform_level F ζ hζ K hK f a
  refine ⟨J, ?_⟩
  intro v hv
  apply Submodule.span_induction (p := fun v _ => Continuous v ∧
      (∀ c : KPSpatialSmoothing.actualC F ζ hζ, ∀ g,
        v (c.val * g) = sourceChi F ζ hζ c * v g) ∧
      (∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
        v (g * u) = v g) ∧ KFinite F ζ hζ K v) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨s, rfl⟩
    exact ⟨source_continuous F ζ hζ K hK μ f a s h,
      source_covariant F ζ hζ K hK μ f a s h,
      hJ μ s h, normalized_source_kfinite F ζ hζ K hK μ f a s h hh⟩
  · refine ⟨continuous_const, ?_, ?_, ?_⟩
    · intro c g; simp
    · intro g u hu; simp
    · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k w hw => by
        rw [Submodule.mem_bot] at hw ⊢
        rw [hw, map_zero]⟩
  · intro u v hu hv hu' hv'
    rcases hu' with ⟨huc, hucov, huJ, hufin⟩
    rcases hv' with ⟨hvc, hvcov, hvJ, hvfin⟩
    refine ⟨huc.add hvc, ?_, ?_, kfinite_add F ζ hζ K u v hufin hvfin⟩
    · intro c g; simp only [Pi.add_apply, hucov, hvcov, mul_add]
    · intro g j hj; simp only [Pi.add_apply, huJ g j hj, hvJ g j hj]
  · intro z v hv hv'
    rcases hv' with ⟨hvc, hvcov, hvJ, hvfin⟩
    refine ⟨continuous_const.mul hvc, ?_, ?_, kfinite_smul F ζ hζ K v hvfin z⟩
    · intro c g; simp only [Pi.smul_apply, smul_eq_mul, hvcov]; ring
    · intro g j hj; simp only [Pi.smul_apply, hvJ g j hj]

private theorem reweight_uniform_level
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (v : Functions F ζ hζ)
    (hv : ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
      v (g * u) = v g) :
    ∃ J' : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ s g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J'),
        reweight F ζ hζ K hK s v (g * j.val) =
          reweight F ζ hζ K hK s v g := by
  let D := KPLiteralChamber.literalIwasawa F ζ hζ K hK
  obtain ⟨U, hU⟩ :=
    KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level D
  let J' : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨J.toOpenSubgroup ⊓ U.toOpenSubgroup,
      J.isCompact.inter_right U.toOpenSubgroup.isClosed⟩
  refine ⟨J', ?_⟩
  intro s g j
  have hJ : j.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J :=
    Subgroup.map_mono (by dsimp [J']; exact inf_le_left) j.property
  have hU' : j.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.map_mono (by dsimp [J']; exact inf_le_right) j.property
  change Complex.exp (s * alpha F ζ hζ K hK (g * j.val)) * v (g * j.val) =
    Complex.exp (s * alpha F ζ hζ K hK g) * v g
  rw [hv g j.val hJ]
  unfold alpha
  rw [hU g ⟨j.val, hU'⟩]

private theorem reweight_mem_flat
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (v : Functions F ζ hζ) (hv : Continuous v)
    (hc : ∀ c : KPSpatialSmoothing.actualC F ζ hζ, ∀ g,
      v (c.val * g) = sourceChi F ζ hζ c * v g)
    (hf : KFinite F ζ hζ K v)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hJ : ∀ g u, u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J →
      v (g * u) = v g) :
    (∀ s, Induced F ζ hζ s (reweight F ζ hζ K hK s v)) ∧
    (∀ s (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K),
      reweight F ζ hζ K hK s v (t.val * k.val) =
        KPGlobalExceptionalParameter.realLogPower
          (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) s *
          reweight F ζ hζ K hK 0 v (t.val * k.val)) ∧
    KFinite F ζ hζ K (reweight F ζ hζ K hK 0 v) := by
  obtain ⟨J', hJ'⟩ := reweight_uniform_level F ζ hζ K hK J v hJ
  refine ⟨?_, ?_, reweight_kfinite F ζ hζ K hK 0 v hf⟩
  · intro s
    refine ⟨covariant_source_smooth F ζ hζ
      (KPLiteralChamber.literalIwasawa F ζ hζ K hK) (parameterChi F ζ hζ s)
      (reweight F ζ hζ K hK s v) (reweight_continuous F ζ hζ K hK s v hv)
      (reweight_covariant F ζ hζ K hK v hc s)
      (reweight_kfinite F ζ hζ K hK s v hf) J' (hJ' s), ?_⟩
    intro r x g
    let e := MulEquiv.subgroupCongr (target_subgroup_eq F ζ hζ)
    let u : (KPSpatialSmoothing.P0 F ζ hζ).H := e.symm r
    have hu : u.val.val = r.val.val := rfl
    let c : KPSpatialSmoothing.actualC F ζ hζ :=
      ⟨r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x,
        (KPSpatialSmoothing.mem_actualC_iff F ζ hζ _).mpr ⟨u, x, rfl⟩⟩
    have hχ : parameterChi F ζ hζ s c =
        KPGlobalExceptionalParameter.realLogPower
          (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2 + s) *
        (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) := by
      change (KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ s
        (sourceH F ζ hζ c).val : ℂ) * sourceChi F ζ hζ c = _
      rw [sourceH_hN F ζ hζ u x c rfl, sourceChi_hN F ζ hζ u x c rfl,
        normalized_multiplier F ζ hζ s r.val]
      change KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s r.val *
          (KPGlobalTorusFunctionData.deltaHalf F ζ hζ r.val *
            (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ)) = _
      ring
    have h := reweight_covariant F ζ hζ K hK v hc s c g
    rw [hχ] at h
    exact h
  · intro s t k
    change Complex.exp (s * alpha F ζ hζ K hK (t.val * k.val)) * v (t.val * k.val) = _
    have hn : KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ
        (KPLiteralChamber.literalIwasawa F ζ hζ K hK) (t.val * k.val) =
          KPGlobalTorusFunctionData.delta F ζ hζ t := by
      have h := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
        (KPLiteralChamber.literalIwasawa F ζ hζ K hK) t 0 k
      have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
        (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
      simpa only [hN, mul_one] using h
    simp only [reweight, LinearMap.coe_mk, AddHom.coe_mk, alpha, hn,
      zero_mul, Complex.exp_zero, one_mul, KPGlobalExceptionalParameter.realLogPower]

 theorem projected_family_finite_flat_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ) (h : C(K, ℂ))
    (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (n : ℕ) (b : Fin n → Flat F ζ hζ K) (c : Fin n → ℂ → ℂ),
      (∀ j, AnalyticOnNhd ℂ (c j) Set.univ) ∧
      ∀ s g, (∫ k : K, h k * f.val s (g * k.val * a) ∂μ) =
        ∑ j, c j s * (b j).val s g := by
  obtain ⟨J, hJ⟩ := normalized_source_span_properties F ζ hζ K hK μ f a h hh
  obtain ⟨n, v, c, hv, hc, he⟩ :=
    normalized_entire_finite_expansion F ζ hζ K hK μ f a h hh
  let b : Fin n → Flat F ζ hζ K := fun j =>
    ⟨fun s => reweight F ζ hζ K hK s (v j),
      reweight_mem_flat F ζ hζ K hK (v j) (hJ _ (hv j)).1
        (hJ _ (hv j)).2.1 (hJ _ (hv j)).2.2.2 J (hJ _ (hv j)).2.2.1⟩
  refine ⟨n, b, c, hc, ?_⟩
  intro s g
  have hEq := congrArg (fun v : Functions F ζ hζ => reweight F ζ hζ K hK s v g) (he s)
  have hn : reweight F ζ hζ K hK s (source F ζ hζ K hK μ f a s h) g =
      ∫ k : K, h k * f.val s (g * k.val * a) ∂μ := by
    change Complex.exp (s * alpha F ζ hζ K hK g) *
      (Complex.exp (-s * alpha F ζ hζ K hK g) * _) = _
    rw [← mul_assoc, ← Complex.exp_add]
    simp

  simpa only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b,
    LinearMap.sum_apply, hn] using hEq

end DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion

end
