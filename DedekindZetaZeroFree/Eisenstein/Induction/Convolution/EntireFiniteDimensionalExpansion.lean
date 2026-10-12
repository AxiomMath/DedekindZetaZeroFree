module

public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationFiniteLevelCovers
public import DedekindZetaZeroFree.RepresentationTheory.Induction.FiniteDimensionalIntertwiners
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.UniformFiniteLevel

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage.ParameterStage
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local instance stageBorel (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance stageBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

 lemma targetH_eq_R : (KPSpatialSmoothing.P0 F ζ hζ).H = R F ζ hζ := by
  change (KPMsRationalCompactCrossPairing.targetPolarization F ζ hζ 0).H = _
  rw [KPMsRationalCompactCrossPairing.targetPolarization,
    KPMsRationalCompactCrossPairing.actual_weyl_fibre]
  rfl

def sourceH : (KPSpatialSmoothing.P0 F ζ hζ).H →* R F ζ hζ :=
  Subgroup.inclusion (le_of_eq (targetH_eq_R F ζ hζ))

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming cToBorel → cToBorel

lemma sourceH_coordinate_hN (r : (KPSpatialSmoothing.P0 F ζ hζ).H) (x : KPAdeles F)
    (c : KPSpatialSmoothing.actualC F ζ hζ)
    (hc : c.val = r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) :
    KPSpatialSmoothing.actualHCoordinate F ζ hζ c = r := by
  have he : cToBorel F ζ hζ c = ActualBorelRetraction.torusInBorel F ζ hζ r.val *
      ActualBorelRetraction.rootInBorel F ζ hζ (Multiplicative.ofAdd x) := Subtype.ext hc
  apply Subtype.ext
  change ActualBorelRetraction.retraction F ζ hζ (cToBorel F ζ hζ c) = r.val
  rw [he, map_mul, ActualBorelRetraction.retraction_torus,
    ActualBorelRetraction.retraction_root, mul_one]

def sourceCharacter : KPSpatialSmoothing.actualC F ζ hζ →* ℂ :=
  (Units.coeHom ℂ).comp
    ((((KPGlobalTorusBorelTwistCompatibility.normCharacter F ζ hζ (1 / 2)).toMonoidHom.comp
      (R F ζ hζ).subtype * (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).toMonoidHom).comp
      ((sourceH F ζ hζ).comp (KPSpatialSmoothing.actualHCoordinate F ζ hζ))))

lemma sourceCharacter_hN (r : (KPSpatialSmoothing.P0 F ζ hζ).H) (x : KPAdeles F)
    (c : KPSpatialSmoothing.actualC F ζ hζ)
    (hc : c.val = r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) :
    sourceCharacter F ζ hζ c =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2) *
          (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (sourceH F ζ hζ r) : ℂ) := by
  simp only [sourceCharacter, MonoidHom.comp_apply, MonoidHom.mul_apply,
    sourceH_coordinate_hN F ζ hζ r x c hc, Units.coeHom_apply, Units.val_mul]
  rfl

lemma source_covariant (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ) (s : ℂ) (h : C(K, ℂ))
    (c : KPSpatialSmoothing.actualC F ζ hζ) (g : G F ζ hζ) :
    source F ζ hζ K hK μ f a s h (c.val * g) =
      sourceCharacter F ζ hζ c * source F ζ hζ K hK μ f a s h g := by
  obtain ⟨r, x, hc⟩ := (KPSpatialSmoothing.mem_actualC_iff F ζ hζ c.val).mp c.property
  rw [sourceCharacter_hN F ζ hζ r x c hc, hc]
  exact source_covariance F ζ hζ K hK μ f a s h (sourceH F ζ hζ r) x g

def levelSource (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (J : Subgroup (G F ζ hζ))
    (hJ : ∀ (s : ℂ) (h : C(K, ℂ)) (g : G F ζ hζ) (j : J),
      source F ζ hζ K hK μ f a s h (g * j.val) = source F ζ hζ K hK μ f a s h g)
    (s : ℂ) : C(K, ℂ) →ₗ[ℂ]
      CovariantSampling.V_J (KPSpatialSmoothing.actualC F ζ hζ) J (sourceCharacter F ζ hζ) :=
  (sourceMap F ζ hζ K hK μ f a s).codRestrict _ (fun h =>
    ⟨source_covariant F ζ hζ K hK μ f a s h, fun j g => hJ s h g j⟩)

def levelIntertwiner (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (J : Subgroup (G F ζ hζ))
    (hn : ∀ (b : K) (j : J), b.val⁻¹ * j.val * b.val ∈ J)
    (hJ : ∀ (s : ℂ) (h : C(K, ℂ)) (g : G F ζ hζ) (j : J),
      source F ζ hζ K hK μ f a s h (g * j.val) = source F ζ hζ K hK μ f a s h g)
    (W : Submodule ℂ C(K, ℂ))
    (hi : ∀ b : K, ∀ h ∈ W, kernelTranslate F ζ hζ K b h ∈ W) (s : ℂ) :
    (kernelOn F ζ hζ K W hi).IntertwiningMap
      (CovariantSampling.rho_J (KPSpatialSmoothing.actualC F ζ hζ) K J (sourceCharacter F ζ hζ) hn) :=
  LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    ((levelSource F ζ hζ K hK μ f a J hJ s).comp W.subtype) (by
      intro b w
      apply Subtype.ext
      exact source_intertwines F ζ hζ K hK μ f a s w.val b)

def evaluateIntertwiner {G₀ : Type*} [Group G₀] (C K J : Subgroup G₀) (chi : C →* ℂ)
    (hn : ∀ (b : K) (j : J), b.val⁻¹ * j.val * b.val ∈ J)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (tau : Representation ℂ K W) :
    tau.IntertwiningMap (CovariantSampling.rho_J C K J chi hn) →ₗ[ℂ]
      W →ₗ[ℂ] (G₀ → ℂ) where
  toFun T := (CovariantSampling.V_J C J chi).subtype.comp T.toLinearMap
  map_add' := by intros; ext; rfl
  map_smul' := by intros; ext; rfl

def sourceStage (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) : Submodule ℂ (Functions F ζ hζ) :=
  Submodule.span ℂ (Set.range (fun p : ℂ × W => source F ζ hζ K hK μ f a p.1 p.2.val))

lemma sourceStage_contains (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (s : ℂ) (w : W) :
    source F ζ hζ K hK μ f a s w.val ∈ sourceStage F ζ hζ K hK μ f a W :=
  Submodule.subset_span ⟨(s,w), rfl⟩

lemma sourceStage_finite (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (J : Subgroup (G F ζ hζ))
    (hn : ∀ (b : K) (j : J), b.val⁻¹ * j.val * b.val ∈ J)
    (hJ : ∀ (s : ℂ) (h : C(K, ℂ)) (g : G F ζ hζ) (j : J),
      source F ζ hζ K hK μ f a s h (g * j.val) = source F ζ hζ K hK μ f a s h g)
    (n : ℕ) (r : Fin n → G F ζ hζ)
    (hc : ∀ g : G F ζ hζ, ∃ (i : Fin n) (c : KPSpatialSmoothing.actualC F ζ hζ)
      (b : K) (j : J), g = c.val * r i * b.val * j.val)
    (W : Submodule ℂ C(K, ℂ)) [Module.Finite ℂ W]
    (hi : ∀ b : K, ∀ h ∈ W, kernelTranslate F ζ hζ K b h ∈ W) :
    Module.Finite ℂ (sourceStage F ζ hζ K hK μ f a W) := by
  let tau := kernelOn F ζ hζ K W hi
  let C := KPSpatialSmoothing.actualC F ζ hζ
  let chi := sourceCharacter F ζ hζ
  letI : FiniteDimensional ℂ (tau.IntertwiningMap (CovariantSampling.rho_J C K J chi hn)) :=
    CovariantSampling.intertwiningMap_finiteDimensional C K J chi n r hc hn (W := W) tau
  let L := evaluateIntertwiner C K J chi hn (W := W) tau
  let M := Submodule.map₂ L ⊤ ⊤
  have hM : M.FG := Submodule.FG.map₂ L (Module.Finite.fg_top) (Module.Finite.fg_top)
  letI : Module.Finite ℂ M := Module.Finite.of_fg hM
  apply Module.Finite.of_injective
    (Submodule.inclusion (show sourceStage F ζ hζ K hK μ f a W ≤ M from ?_))
    (Submodule.inclusion_injective _)
  apply Submodule.span_le.mpr
  rintro v ⟨⟨s,w⟩, rfl⟩
  exact Submodule.apply_mem_map₂ L (show levelIntertwiner F ζ hζ K hK μ f a J hn hJ W hi s ∈ ⊤ from trivial)
    (show w ∈ ⊤ from trivial)

lemma sourceStage_continuous (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ sourceStage F ζ hζ K hK μ f a W) : Continuous v := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨⟨s,w⟩, rfl⟩ := hv
      exact source_continuous F ζ hζ K hK μ f a s w.val
  | zero => exact continuous_const
  | add v w _ _ hv hw => exact hv.add hw
  | smul c v _ hv => exact continuous_const.smul hv

lemma sourceStage_covariant (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ sourceStage F ζ hζ K hK μ f a W)
    (c : KPSpatialSmoothing.actualC F ζ hζ) (g : G F ζ hζ) :
    v (c.val * g) = sourceCharacter F ζ hζ c * v g := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨⟨s,w⟩, rfl⟩ := hv
      exact source_covariant F ζ hζ K hK μ f a s w.val c g
  | zero => simp
  | add v w _ _ hv hw => simp only [Pi.add_apply, hv, hw, mul_add]
  | smul z v _ hv => simp only [Pi.smul_apply, smul_eq_mul, hv, mul_left_comm z]

lemma sourceStage_right_fixed (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (J : Subgroup (G F ζ hζ))
    (hJ : ∀ (s : ℂ) (h : C(K, ℂ)) (g : G F ζ hζ) (j : J),
      source F ζ hζ K hK μ f a s h (g * j.val) = source F ζ hζ K hK μ f a s h g)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ sourceStage F ζ hζ K hK μ f a W) (g : G F ζ hζ) (j : J) :
    v (g * j.val) = v g := by
  induction hv using Submodule.span_induction with
  | mem v hv => obtain ⟨⟨s,w⟩, rfl⟩ := hv; exact hJ s w.val g j
  | zero => rfl
  | add v w _ _ hv hw => simp only [Pi.add_apply, hv, hw]
  | smul c v _ hv => simp only [Pi.smul_apply, hv]

lemma sourceStage_invariant (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ))
    (hi : ∀ b : K, ∀ h ∈ W, kernelTranslate F ζ hζ K b h ∈ W)
    (b : K) (v : Functions F ζ hζ) (hv : v ∈ sourceStage F ζ hζ K hK μ f a W) :
    rightAction F ζ hζ b.val v ∈ sourceStage F ζ hζ K hK μ f a W := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨⟨s,w⟩, rfl⟩ := hv
      rw [← source_intertwines F ζ hζ K hK μ f a s w.val b]
      exact sourceStage_contains F ζ hζ K hK μ f a W s
        ⟨kernelTranslate F ζ hζ K b w.val, hi b w.val w.property⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => rw [map_add]; exact Submodule.add_mem _ hv hw
  | smul c v _ hv => rw [map_smul]; exact Submodule.smul_mem _ c hv

lemma actual_finite_parameter_stage
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (h : C(K, ℂ)) (hh : h ∈ TauCeti.representativeSubmodule ℂ K) :
    ∃ (W : Submodule ℂ C(K, ℂ)) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ),
      Module.Finite ℂ W ∧ h ∈ W ∧
      Module.Finite ℂ (sourceStage F ζ hζ K hK μ f a W) ∧
      (∀ s, source F ζ hζ K hK μ f a s h ∈ sourceStage F ζ hζ K hK μ f a W) ∧
      (∀ (b : K) (v : Functions F ζ hζ), v ∈ sourceStage F ζ hζ K hK μ f a W →
        rightAction F ζ hζ b.val v ∈ sourceStage F ζ hζ K hK μ f a W) ∧
      (∀ (v : Functions F ζ hζ), v ∈ sourceStage F ζ hζ K hK μ f a W → Continuous v) ∧
      (∀ (v : Functions F ζ hζ), v ∈ sourceStage F ζ hζ K hK μ f a W →
        ∀ (c : KPSpatialSmoothing.actualC F ζ hζ) (g : G F ζ hζ),
          v (c.val * g) = sourceCharacter F ζ hζ c * v g) ∧
      (∀ (v : Functions F ζ hζ), v ∈ sourceStage F ζ hζ K hK μ f a W →
        ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J), v (g * j.val) = v g) := by
  obtain ⟨W, hW, hhW, hi⟩ := representative_kernelFinite F ζ hζ K h hh
  let := hW
  obtain ⟨U, hU⟩ := CommonLevel.source_uniform_level F ζ hζ K hK f a
  obtain ⟨J, n, r, hle, hn, hc, _⟩ := KPSpatialSmoothing.actual_covariant_finite_cover F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) U
  have hJ (s : ℂ) (l : C(K, ℂ)) (g : G F ζ hζ)
      (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J) :
      source F ζ hζ K hK μ f a s l (g * j.val) = source F ζ hζ K hK μ f a s l g :=
    hU μ s l g j.val (hle j.property)
  have hcover (g : G F ζ hζ) : ∃ (i : Fin n) (c : KPSpatialSmoothing.actualC F ζ hζ)
      (b : K) (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
      g = c.val * (r i).val * b.val * j.val := by
    obtain ⟨i, t, x, b, j, hg⟩ := hc g
    exact ⟨i, ⟨t.val.val * KPGlobalTorusFunctionData.N F ζ hζ x,
      (KPSpatialSmoothing.mem_actualC_iff F ζ hζ _).mpr ⟨t,x,rfl⟩⟩, b, j, hg⟩
  refine ⟨W, J, hW, hhW,
    sourceStage_finite F ζ hζ K hK μ f a _ hn hJ n (fun i => (r i).val) hcover W hi,
    fun s => sourceStage_contains F ζ hζ K hK μ f a W s ⟨h,hhW⟩,
    sourceStage_invariant F ζ hζ K hK μ f a W hi,
    sourceStage_continuous F ζ hζ K hK μ f a W,
    sourceStage_covariant F ζ hζ K hK μ f a W,
    fun v hv g j => sourceStage_right_fixed F ζ hζ K hK μ f a _ hJ W v hv g j⟩

private lemma functional_mem_evaluations {X : Type*} (V : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ V] (L : V →ₗ[ℂ] ℂ) :
    L ∈ Submodule.span ℂ (Set.range (fun x : X => (LinearMap.proj x).domRestrict V)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro v hv
  have hz : v = 0 := by
    apply Subtype.ext
    funext x
    exact (Submodule.mem_iInf _).mp hv x
  rw [hz]
  exact LinearMap.mem_ker.mpr (map_zero L)

private lemma functional_entire {X : Type*} (V : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ V] (v : ℂ → V) (L : V →ₗ[ℂ] ℂ)
    (hv : ∀ x : X, Differentiable ℂ (fun s => (v s).val x)) :
    Differentiable ℂ (fun s => L (v s)) := by
  induction functional_mem_evaluations V L using Submodule.span_induction with
  | mem L hL => obtain ⟨x, rfl⟩ := hL; exact hv x
  | zero => exact differentiable_const _
  | add L M _ _ hL hM => exact hL.add hM
  | smul c L _ hL => exact hL.const_smul c

lemma sourceStage_entire_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) [Module.Finite ℂ (sourceStage F ζ hζ K hK μ f a W)]
    (h : C(K, ℂ)) (hh : h ∈ W) :
    ∃ (n : ℕ) (b : Fin n → sourceStage F ζ hζ K hK μ f a W)
      (c : Fin n → ℂ → ℂ),
      (∀ i, Differentiable ℂ (c i)) ∧
      ∀ s : ℂ, source F ζ hζ K hK μ f a s h = ∑ i, c i s • (b i).val := by
  let V := sourceStage F ζ hζ K hK μ f a W
  let v : ℂ → V := fun s => ⟨source F ζ hζ K hK μ f a s h,
    sourceStage_contains F ζ hζ K hK μ f a W s ⟨h,hh⟩⟩
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, b, fun i s => b.coord i (v s), ?_, ?_⟩
  · intro i
    exact functional_entire V v (b.coord i) (fun g => normalized_source_entire F ζ hζ K hK μ f a h g)
  · intro s
    have he := congrArg Subtype.val (b.sum_repr (v s))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Module.Basis.coord_apply, v] using he.symm

lemma original_integral_finite_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) [Module.Finite ℂ (sourceStage F ζ hζ K hK μ f a W)]
    (h : C(K, ℂ)) (hh : h ∈ W) :
    ∃ (n : ℕ) (b : Fin n → sourceStage F ζ hζ K hK μ f a W)
      (c : Fin n → ℂ → ℂ),
      (∀ i, Differentiable ℂ (c i)) ∧
      ∀ s g, (∫ k : K, h k * f.val s (g * k.val * a) ∂μ) =
        ∑ i, c i s * (Complex.exp (s * alpha F ζ hζ K hK g) * (b i).val g) := by
  obtain ⟨n,b,c,hc,he⟩ := sourceStage_entire_expansion F ζ hζ K hK μ f a W h hh
  refine ⟨n,b,c,hc,?_⟩
  intro s g
  have hs := congrFun (he s) g
  simp only [source, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hs
  have he := congrArg (fun z : ℂ => Complex.exp (s * alpha F ζ hζ K hK g) * z) hs
  have hcanc : Complex.exp (s * alpha F ζ hζ K hK g) *
      Complex.exp (-s * alpha F ζ hζ K hK g) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [← mul_assoc, hcanc, one_mul, Finset.mul_sum] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def flatten (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (v : Functions F ζ hζ) : ℂ → Functions F ζ hζ :=
  fun s g => Complex.exp (s * alpha F ζ hζ K hK g) * v g

@[simp] lemma flatten_zero (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (v : Functions F ζ hζ) : flatten F ζ hζ K hK v 0 = v := by
  ext g
  simp [flatten]

lemma flatten_full_fiber (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (v : Functions F ζ hζ) (s : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K) :
    flatten F ζ hζ K hK v s (t.val * k.val) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) s *
      flatten F ζ hζ K hK v 0 (t.val * k.val) := by
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPAdeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have ha : alpha F ζ hζ K hK (t.val * k.val) =
      (Real.log (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) : ℂ) := by
    unfold alpha
    rw [show t.val * k.val = (t.val * KPGlobalTorusFunctionData.N F ζ hζ 0) * k.val by rw [hn,mul_one],
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
        (KPLiteralChamber.literalIwasawa F ζ hζ K hK) t 0 k]
  simp only [flatten, ha, KPGlobalExceptionalParameter.realLogPower, zero_mul, Complex.exp_zero, one_mul]

lemma flatten_covariance (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ sourceStage F ζ hζ K hK μ f a W)
    (s : ℂ) (r : R F ζ hζ) (x : KPAdeles F) (g : G F ζ hζ) :
    flatten F ζ hζ K hK v s ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ r.val : NNReal) : ℝ)) (1 / 2 + s) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r : ℂ) *
      flatten F ζ hζ K hK v s g := by
  let t : (KPSpatialSmoothing.P0 F ζ hζ).H := ⟨r.val, (targetH_eq_R F ζ hζ).symm ▸ r.property⟩
  let c : KPSpatialSmoothing.actualC F ζ hζ :=
    ⟨r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x,
      (KPSpatialSmoothing.mem_actualC_iff F ζ hζ _).mpr ⟨t,x,rfl⟩⟩
  have hc := sourceStage_covariant F ζ hζ K hK μ f a W v hv c g
  rw [sourceCharacter_hN F ζ hζ t x c rfl] at hc
  have ht : sourceH F ζ hζ t = r := rfl
  rw [ht] at hc
  change v ((r.val.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) = _ at hc
  simp only [flatten, alpha_borel, hc, KPGlobalExceptionalParameter.realLogPower]
  rw [add_mul, Complex.exp_add, mul_add, Complex.exp_add]
  ring

lemma flatten_continuous (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) [IsFiniteMeasure μ] (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) (v : Functions F ζ hζ)
    (hv : v ∈ sourceStage F ζ hζ K hK μ f a W) (s : ℂ) :
    Continuous (flatten F ζ hζ K hK v s) := by
  have ha : Continuous (alpha F ζ hζ K hK) := Complex.continuous_ofReal.comp
    (KPLiteralChamber.JointProfile.literal_log_modulus_continuous F ζ hζ K hK)
  exact (continuous_const.mul ha).cexp.mul (sourceStage_continuous F ζ hζ K hK μ f a W v hv)

lemma flatten_common_level (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (μ : Measure K) (f : Flat F ζ hζ K) (a : G F ζ hζ)
    (W : Submodule ℂ C(K, ℂ)) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (s : ℂ) (v : Functions F ζ hζ), v ∈ sourceStage F ζ hζ K hK μ f a W →
        ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
          flatten F ζ hζ K hK v s (g * j.val) = flatten F ζ hζ K hK v s g := by
  obtain ⟨U,hU⟩ := CommonLevel.source_uniform_level F ζ hζ K hK f a
  obtain ⟨V,hV⟩ :=
    KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level
      (KPLiteralChamber.literalIwasawa F ζ hζ K hK)
  let J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  have hle (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J) :
      j.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U ∧
      j.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V := by
    obtain ⟨u,hu,he⟩ := j.property
    exact ⟨⟨u,hu.1,he⟩,⟨u,hu.2,he⟩⟩
  refine ⟨J,?_⟩
  intro s v hv g j
  have hvJ : v (g * j.val) = v g := sourceStage_right_fixed F ζ hζ K hK μ f a _
    (fun s h g j => hU μ s h g j.val j.property) W v hv g ⟨j.val,(hle j).1⟩
  have ha : alpha F ζ hζ K hK (g * j.val) = alpha F ζ hζ K hK g := by
    unfold alpha
    rw [hV g ⟨j.val,(hle j).2⟩]
  simp only [flatten,ha,hvJ]

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation.ConvolutionSpan.ActualSourceStage.ParameterStage

end
