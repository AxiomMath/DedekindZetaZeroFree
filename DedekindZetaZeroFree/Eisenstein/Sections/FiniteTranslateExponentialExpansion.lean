module

public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets
public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteNormCutRegularity
public import DedekindZetaZeroFree.Metaplectic.Torus.PolarizationFiniteLevelCovers
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.FiniteTranslationRegularity

@[expose] public section

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField
namespace DedekindZetaZeroFree.KPLiteralTensorEquivariance.FiniteClearedCovariance
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem finite_translate_orbit {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N K : Subgroup G) [N.Normal]
    (hK : IsCompact (K : Set G)) (U : OpenSubgroup N)
    (hnorm : ∀ k : K, ∀ j : U, k.val⁻¹ * j.val.val * k.val ∈ U.toSubgroup.map N.subtype)
    (f : V) (hU : ∀ j : U, ρ j.val.val f = f)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : K => ρ k.val f))))
    (a : N) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : K => ρ k.val (ρ a.val f)))) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let W := Submodule.span ℂ (Set.range (fun k : K => ρ k.val f))
  let : FiniteDimensional ℂ W := hfin
  have hUW (j : U) : ∀ w ∈ W, ρ j.val.val w = w := by
    intro w hw
    apply Submodule.span_induction (p := fun w _ => ρ j.val.val w = w) ?_ ?_ ?_ ?_ hw
    · rintro w ⟨k, rfl⟩
      obtain ⟨b, hb, he⟩ := hnorm k j
      have h := hU ⟨b, hb⟩
      change b.val = k.val⁻¹ * j.val.val * k.val at he
      have he' : k.val * b.val = j.val.val * k.val := by rw [he]; group
      calc
        ρ j.val.val (ρ k.val f) = ρ (j.val.val * k.val) f := by rw [map_mul]; rfl
        _ = ρ k.val (ρ b.val f) := by rw [← he', map_mul]; rfl
        _ = ρ k.val f := by rw [h]
    · simp
    · intro x y hx hy hxe hye
      simp only [map_add, hxe, hye]
    · intro c x hx hxe
      simp only [map_smul, hxe]
  let b : K → N := fun k => ⟨k.val * a.val * k.val⁻¹, Subgroup.Normal.conj_mem inferInstance a.val a.property k.val⟩
  have hb : Continuous b := by
    exact ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.inv).subtype_mk _
  let c : K → N ⧸ U.toSubgroup := fun k => QuotientGroup.mk (b k)
  have hc : Continuous c := QuotientGroup.continuous_mk.comp hb
  have : DiscreteTopology (N ⧸ U.toSubgroup) := inferInstance
  have hB := ((IsLocallyConstant.iff_continuous c).mpr hc).range_finite
  let B := Set.range c
  let : Finite B := hB.to_subtype
  let r : B → K := fun m => Classical.choose m.property
  have hr (m : B) : c (r m) = m.val := Classical.choose_spec m.property
  let spaces : B → Submodule ℂ V := fun m => W.map (ρ (b (r m)).val)
  have : ∀ m, FiniteDimensional ℂ (spaces m) := fun _ => inferInstance
  have : FiniteDimensional ℂ ↥(⨆ m, spaces m) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := ⨆ m, spaces m)
  apply Submodule.span_le.mpr
  rintro w ⟨k, rfl⟩
  let m : B := ⟨c k, Set.mem_range_self k⟩
  have hmk : c (r m) = c k := hr m
  have hj : (b (r m))⁻¹ * b k ∈ U := QuotientGroup.eq.mp hmk
  let j : U := ⟨(b (r m))⁻¹ * b k, hj⟩
  have he : b k = b (r m) * j.val := by simp [j]
  have he' : (b k).val * k.val = k.val * a.val := by simp [b, mul_assoc]
  apply Submodule.mem_iSup_of_mem m
  apply Submodule.mem_map.mpr
  refine ⟨ρ k.val f, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
  calc
    ρ (b (r m)).val (ρ k.val f) = ρ (b (r m)).val (ρ j.val.val (ρ k.val f)) := by
      rw [hUW j _ (Submodule.subset_span ⟨k, rfl⟩)]
    _ = ρ (b k).val (ρ k.val f) := by rw [he]; simp [map_mul]
    _ = ρ k.val (ρ a.val f) := by
      change (ρ (b k).val * ρ k.val) f = (ρ k.val * ρ a.val) f
      rw [← map_mul, ← map_mul, he']

 def orbitMask {G : Type*} (m : G → ℝ) (a : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun f g := if m g = a then f g else 0
  map_add' f h := by ext g; by_cases hh : m g = a <;> simp [hh]
  map_smul' c f := by ext g; by_cases hh : m g = a <;> simp [hh]

private theorem masked_orbit_finite {G : Type*} [Group G]
    (K : Subgroup G) (f : G → ℂ) (m : G → ℝ) (a : ℝ)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : K => fun g => f (g * k.val)))))
    (hm : (Set.range (fun k : K => fun g => m (g * k.val))).Finite) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : K =>
      fun g => if m (g * k.val) = a then f (g * k.val) else 0))) := by
  let W := Submodule.span ℂ (Set.range (fun k : K => fun g => f (g * k.val)))
  let : FiniteDimensional ℂ W := hf
  let B := Set.range (fun k : K => fun g => m (g * k.val))
  let : Finite B := hm.to_subtype
  let spaces : B → Submodule ℂ (G → ℂ) := fun h => W.map (orbitMask h.val a)
  have : ∀ h, FiniteDimensional ℂ (spaces h) := fun _ => inferInstance
  have : FiniteDimensional ℂ ↥(⨆ h, spaces h) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := ⨆ h, spaces h)
  apply Submodule.span_le.mpr
  rintro w ⟨k, rfl⟩
  apply Submodule.mem_iSup_of_mem (⟨_, Set.mem_range_self k⟩ : B)
  exact Submodule.mem_map.mpr ⟨_, Submodule.subset_span ⟨k, rfl⟩, rfl⟩

private theorem kfinite_iff_finite_orbit {G : Type*} [Group G]
    (ρ : Representation ℂ G (G → ℂ)) (K : Subgroup G) (f : G → ℂ) :
    (∃ S : Submodule ℂ (G → ℂ), Module.Finite ℂ S ∧ f ∈ S ∧
      ∀ k : K, ∀ v ∈ S, ρ k.val v ∈ S) ↔
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : K => ρ k.val f))) := by
  constructor
  · rintro ⟨S, hS, hf, hs⟩
    let : Module.Finite ℂ S := hS
    apply Submodule.finiteDimensional_of_le (S₂ := S)
    apply Submodule.span_le.mpr
    rintro v ⟨k, rfl⟩
    exact hs k f hf
  · intro h
    let W := Submodule.span ℂ (Set.range (fun k : K => ρ k.val f))
    refine ⟨W, h, ?_, ?_⟩
    · have h1 : ρ (1 : K).val f = f := by rw [Subgroup.coe_one, map_one]; rfl
      rw [← h1]
      exact Submodule.subset_span ⟨1, rfl⟩
    · intro k v hv
      apply Submodule.span_induction (p := fun v _ => ρ k.val v ∈ W) ?_ ?_ ?_ ?_ hv
      · rintro v ⟨l, rfl⟩
        have he : ρ k.val (ρ l.val f) = ρ (k * l).val f := by
          rw [Subgroup.coe_mul, map_mul]; rfl
        rw [he]
        exact Submodule.subset_span ⟨k * l, rfl⟩
      · simpa using W.zero_mem
      · intro x y hx hy hxe hye
        simpa only [map_add] using W.add_mem hxe hye
      · intro c x hx hxe
        simpa only [map_smul] using W.smul_mem c hxe

open DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibility (finitePart_normal)
open _root_.DedekindZetaZeroFree.KPSpatialSmoothing renaming compact_normalized_finite_core → compact_normalized_finite_core
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.RawFiniteCompact renaming smooth_translate → smooth_translate

private theorem raw_finite_translate_kfinite
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f) (hfin : KFinite F ζ hζ K f)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    KFinite F ζ hζ K (rightAction F ζ hζ a.val f) := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  let := finitePart_normal F ζ hζ
  obtain ⟨J, hJ⟩ := hf.2.2
  obtain ⟨U, hUJ, hU⟩ := compact_normalized_finite_core F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) J
  apply (kfinite_iff_finite_orbit (rightAction F ζ hζ) K _).mpr
  apply finite_translate_orbit (rightAction F ζ hζ)
    (KPGlobalTorusFunctionData.finitePart F ζ hζ) K hK.1 U.toOpenSubgroup
  · intro k j
    exact hU k ⟨j.val.val, Subgroup.mem_map.mpr ⟨j.val, j.property, rfl⟩⟩
  · intro j
    ext g
    exact hJ g j.val.val (hUJ (Subgroup.mem_map.mpr ⟨j.val, j.property, rfl⟩))
  · exact (kfinite_iff_finite_orbit (rightAction F ζ hζ) K f).mp hfin

 def localFiniteTranslate
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  refine ⟨_, Subgroup.mem_map.mpr ⟨KPAdelicCoverRestrictedProduct.localToRestricted
    F ζ hζ (Sum.inr q) a, ?_, rfl⟩⟩
  apply Subgroup.mem_iInf.mpr
  intro w
  simp [KPAdelicCoverRestrictedProduct.localToRestricted,
    RestrictedProduct.coe_mulSingle_apply]

private theorem localFiniteTranslate_val
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    (localFiniteTranslate F ζ hζ q a).val =
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a) := rfl

open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming diagonalUnit → diagonalUnit

private theorem chart_continuousOn :
    ContinuousOn (KPGlobalResidualConstruction.archChart F ζ hζ)
      (KPGlobalResidualConstruction.archDomain F) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (fun x : KPGlobalResidualConstruction.archDomain F =>
      KPGlobalResidualConstruction.archChart F ζ hζ x.val) =
      (fun x => KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.rightMatrix (x.val w)))) := by
    funext x
    exact KPLiteralChamber.right_insertion F ζ hζ x.val
  change Continuous (fun x : KPGlobalResidualConstruction.archDomain F =>
    KPGlobalResidualConstruction.archChart F ζ hζ x.val)
  rw [he]
  apply (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.1.comp
  apply continuous_pi
  intro w
  apply QuotientGroup.continuous_mk.comp
  let x : KPGlobalResidualConstruction.archDomain F → Fin 3 → ℂ := fun p => p.val w
  have hx (i : Fin 3) : Continuous (fun p => x p i) := by
    exact (continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val)
  have hN : Continuous (fun p => KubotaRankTwo.n ℂ (x p 0)) := by
    rw [Units.continuous_iff]
    constructor <;> apply continuous_matrix <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.n, Matrix.inv_def, Matrix.det_fin_two] <;> fun_prop
  have hL : Continuous (fun p => KPStandardLocalRootLifts.lowerN ℂ (x p 2)) := by
    rw [Units.continuous_iff]
    constructor <;> apply continuous_matrix <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [KPStandardLocalRootLifts.lowerN, Matrix.inv_def, Matrix.det_fin_two] <;> fun_prop
  let u : KPGlobalResidualConstruction.archDomain F → ℂˣ := fun p => Units.mk0 (x p 1) (p.property w)
  have hu : Continuous u := by
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    exact hx 1
  have hui : Continuous (fun p => ((u p : ℂ)⁻¹)) :=
    (Units.continuous_val.comp hu).inv₀ (fun p => (u p).ne_zero)
  have hD : Continuous (fun p => KubotaRankTwo.d ℂ (u p) 1) := by
    rw [Units.continuous_iff]
    constructor <;> apply continuous_matrix <;> intro i j <;> fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, Matrix.inv_def, Matrix.det_fin_two] <;> fun_prop
  convert (hN.mul hD).mul hL using 1
  funext p
  unfold KPLiteralChamber.rightMatrix
  congr 2
  simp [diagonalUnit, x, u, p.property w]

private theorem smooth_clopen_mask
    (h : Functions F ζ hζ) (hh : Smooth F ζ hζ h)
    (m : G F ζ hζ → ℝ) (hm : IsLocallyConstant m) (c : ℝ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (hJ : ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J), m (g * j.val) = m g) :
    Smooth F ζ hζ (fun g => if m g = c then h g else 0) := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  have he (g : G F ζ hζ) :
      (fun x => if m x = c then h x else 0) =ᶠ[nhds g]
        (if m g = c then h else fun _ => 0) := by
    filter_upwards [hm.eventually_eq g] with x hx
    simp only [hx]
    split_ifs <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g
    apply ContinuousAt.congr_of_eventuallyEq _ (he g)
    split_ifs
    · exact hh.1.continuousAt
    · exact continuousAt_const
  · intro g x hx
    let b : KPGlobalResidualConstruction.ArchCoordinates F → G F ζ hζ :=
      fun x => g * KPGlobalResidualConstruction.archChart F ζ hζ x
    have hb : ContinuousOn b (KPGlobalResidualConstruction.archDomain F) :=
      continuousOn_const.mul (chart_continuousOn F ζ hζ)
    have H := hb.continuousWithinAt hx (he (b x))
    have Heq : (fun y => if m (b y) = c then h (b y) else 0) =ᶠ[nhdsWithin x
        (KPGlobalResidualConstruction.archDomain F)]
        (if m (b x) = c then fun y => h (b y) else fun _ => 0) := by
      filter_upwards [H] with y hy
      change (if m (b y) = c then h (b y) else 0) =
        (if m (b x) = c then h else fun _ => 0) (b y) at hy
      by_cases hx' : m (b x) = c <;> simpa [hx'] using hy
    apply ContDiffWithinAt.congr_of_eventuallyEq _ Heq (by split_ifs <;> rfl)
    split_ifs
    · exact hh.2.1 g x hx
    · exact contDiffWithinAt_const
  · obtain ⟨U, hU⟩ := hh.2.2
    let V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
      ⟨J.toOpenSubgroup ⊓ U.toOpenSubgroup,
        J.isCompact.inter_right U.toOpenSubgroup.isClosed⟩
    have hVJ : KPGlobalTorusFunctionData.globalLevel F ζ hζ V ≤
        KPGlobalTorusFunctionData.globalLevel F ζ hζ J := Subgroup.map_mono inf_le_left
    have hVU : KPGlobalTorusFunctionData.globalLevel F ζ hζ V ≤
        KPGlobalTorusFunctionData.globalLevel F ζ hζ U := Subgroup.map_mono inf_le_right
    refine ⟨V, ?_⟩
    intro g j hj
    change (if m (g * j) = c then h (g * j) else 0) =
      (if m g = c then h g else 0)
    rw [hJ g ⟨j, hVJ hj⟩, hU g j (hVU hj)]

private theorem smooth_const_mul (c : ℂ) (h : Functions F ζ hζ)
    (hh : Smooth F ζ hζ h) : Smooth F ζ hζ (fun g => c * h g) := by
  refine ⟨continuous_const.mul hh.1, ?_, ?_⟩
  · intro g
    exact contDiffOn_const.mul (hh.2.1 g)
  · obtain ⟨J, hJ⟩ := hh.2.2
    exact ⟨J, fun g j hj => congrArg (fun x => c * x) (hJ g j hj)⟩

 abbrev logInc
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) (g : G F ζ hζ) :=
  KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement
    (D := D) g a.val

private theorem logInc_right_level
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (a : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    ∃ J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ g (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J),
        logInc F ζ hζ D a (g * j.val) = logInc F ζ hζ D a g := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨U, hU⟩ := KPGlobalResidualKernel.ResidualChamberConstruction.RegularSymmetrySteps.exists_iwasawaNorm_right_level D
  let e := (MulAut.conj a⁻¹).toMonoidHom
  let C := U.toOpenSubgroup.comap e (IsTopologicalGroup.continuous_conj a⁻¹)
  let J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ C, U.isCompact.inter_right C.isClosed⟩
  refine ⟨J, ?_⟩
  intro g j
  obtain ⟨b, hb, he⟩ := j.property
  change b.val = j.val at he
  have hbU : b.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.mem_map.mpr ⟨b, hb.1, rfl⟩
  have hc : (a⁻¹ * b * a).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U := by
    refine Subgroup.mem_map.mpr ⟨a⁻¹ * b * a, ?_, rfl⟩
    have hbc := hb.2
    change a⁻¹ * b * (a⁻¹)⁻¹ ∈ U.toOpenSubgroup at hbc
    exact (show a⁻¹ * b * a ∈ U.toOpenSubgroup from by simpa only [inv_inv] using hbc)
  have h₁ := hU g ⟨b.val, hbU⟩
  have h₂ := hU (g * a.val) ⟨(a⁻¹ * b * a).val, hc⟩
  have heq : (g * a.val) * (a⁻¹ * b * a).val = (g * j.val) * a.val := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, he]
    group
  rw [heq] at h₂
  unfold logInc KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement
  rw [← he, h₁]
  have h₂' : KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D ((g * j.val) * a.val) =
      KPGlobalTorusBorelTwistCompatibility.iwasawaNorm F ζ hζ D (g * a.val) := h₂
  rw [he, h₂']

 def correctedValue
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) (z : ℂ) (g : G F ζ hζ) : ℂ :=
  Complex.exp (-(z * (c : ℂ))) *
    (if logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a g = c
      then f.val z (g * a.val) else 0)

private theorem correctedValue_smooth
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) (z : ℂ) : Smooth F ζ hζ (correctedValue F ζ hζ K hK f a c z) := by
  let D := KPLiteralChamber.literalIwasawa F ζ hζ K hK
  obtain ⟨J, hJ⟩ := logInc_right_level F ζ hζ D a
  apply smooth_const_mul
  apply smooth_clopen_mask F ζ hζ _ _ _ _ c J hJ
  · exact smooth_translate F ζ hζ a (f.val z) (f.property.1 z).1
  · exact KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement_finite_global_locallyConstant a

 theorem correctedValue_induced
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) (z : ℂ) : Induced F ζ hζ z (correctedValue F ζ hζ K hK f a c z) := by
  refine ⟨correctedValue_smooth F ζ hζ K hK f a c z, ?_⟩
  intro r x g
  unfold correctedValue logInc
  rw [KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement_borel_mul]
  by_cases hg : KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement
      (D := KPLiteralChamber.literalIwasawa F ζ hζ K hK) g a.val = c
  · simp only [hg, ↓reduceIte]
    rw [mul_assoc, (f.property.1 z).2 r x (g * a.val)]
    ring
  · simp [hg]

private theorem correctedValue_multiplier
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) (z : ℂ) (g : G F ζ hζ) :
    correctedValue F ζ hζ K hK f a c z g =
      Complex.exp (z * (Real.log (((KPGlobalTorusBorelTwistCompatibility.iwasawaNorm
        F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) g : NNReal) : ℝ)) : ℂ)) *
      correctedValue F ζ hζ K hK f a c 0 g := by
  unfold correctedValue
  by_cases hg : logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a g = c
  · simp only [hg, ↓reduceIte, zero_mul, neg_zero, Complex.exp_zero, one_mul]
    rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f z (g * a.val)]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    unfold logInc KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement at hg
    have h := congrArg (fun x : ℝ => (x : ℂ)) hg
    simp only [Complex.ofReal_sub] at h
    linear_combination z * h
  · simp [hg]

 theorem correctedValue_flat
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) (z : ℂ) (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K) :
    correctedValue F ζ hζ K hK f a c z (t.val * k.val) =
      KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) z *
      correctedValue F ζ hζ K hK f a c 0 (t.val * k.val) := by
  rw [correctedValue_multiplier]
  have hnorm := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_formula F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) t 0 k
  have hN : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 := by
    unfold KPGlobalTorusFunctionData.N
    have ht : KPGlobalTorusFunctionData.rootTuple F ζ hζ 0 = 1 := by
      apply Subtype.ext
      funext v
      change KPStandardLocalRootLifts.N F ζ hζ v (KPAdelicCoverRestrictedProduct.adeleEval F v 0) = 1
      simp [KPAdelicCoverRestrictedProduct.adeleEval]
    rw [ht, map_one, map_one]
  simp only [hN, mul_one] at hnorm
  rw [hnorm]
  rfl

 theorem correctedValue_kfinite
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) : KFinite F ζ hζ K (correctedValue F ζ hζ K hK f a c 0) := by
  have hf := raw_finite_translate_kfinite F ζ hζ K hK (f.val 0) (f.property.1 0).1 f.property.2.2 a
  have hzero : correctedValue F ζ hζ K hK f a c 0 =
      (fun g => if logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a g = c
        then f.val 0 (g * a.val) else 0) := by
    funext g
    simp only [correctedValue, zero_mul, neg_zero, Complex.exp_zero, one_mul]
  rw [hzero]
  apply (kfinite_iff_finite_orbit (rightAction F ζ hζ) K _).mpr
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : K => fun g =>
    if logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a (g * k.val) = c
      then f.val 0 ((g * k.val) * a.val) else 0)))
  apply masked_orbit_finite K (fun g => f.val 0 (g * a.val))
    (logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a) c
  · exact (kfinite_iff_finite_orbit (rightAction F ζ hζ) K (fun g => f.val 0 (g * a.val))).mp hf
  · exact KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement_compact_right_orbit_finite
      (D := KPLiteralChamber.literalIwasawa F ζ hζ K hK) a

 def correctedFlat
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (c : ℝ) : Flat F ζ hζ K :=
  ⟨correctedValue F ζ hζ K hK f a c,
    fun z => correctedValue_induced F ζ hζ K hK f a c z,
    fun z t k => correctedValue_flat F ζ hζ K hK f a c z t k,
    correctedValue_kfinite F ζ hζ K hK f a c⟩

theorem finite_translate_exponential_expansion
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K)
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    ∃ (n : ℕ) (c : Fin n → ℝ) (v : Fin n → Flat F ζ hζ K),
      ∀ z g, f.val z
        (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
          (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) =
        ∑ i, Complex.exp (z * (c i : ℂ)) * (v i).val z g := by
  let a' := localFiniteTranslate F ζ hζ q a
  let D := KPLiteralChamber.literalIwasawa F ζ hζ K hK
  have hfinite : (Set.range (logInc F ζ hζ D a')).Finite :=
    KPGlobalResidualKernelSplit.RawStageL2.OutgoingSplit.ZeroProfileSteps.FiniteNormPartition.logIncrement_finite_range a'
  let B := Set.range (logInc F ζ hζ D a')
  let : Finite B := hfinite.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin B
  let c : Fin n → ℝ := fun i => (e.symm i).val
  have hc : Function.Injective c := by
    intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij
  refine ⟨n, c, (fun i => correctedFlat F ζ hζ K hK f a' (c i)), ?_⟩
  intro z g
  let b : B := ⟨logInc F ζ hζ D a' g, Set.mem_range_self g⟩
  let i : Fin n := e b
  have hi : logInc F ζ hζ D a' g = c i := by
    dsimp [c, i]
    rw [e.symm_apply_apply]
  rw [Finset.sum_eq_single i]
  · change f.val z (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) =
      Complex.exp (z * (c i : ℂ)) * correctedValue F ζ hζ K hK f a' (c i) z g
    rw [← localFiniteTranslate_val F ζ hζ q a]
    unfold correctedValue
    rw [show logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a' g = c i from hi]
    simp only [↓reduceIte]
    rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  · intro j _ hji
    have hj : logInc F ζ hζ D a' g ≠ c j := by
      intro hj
      exact hji (hc (hi.symm.trans hj)).symm
    change Complex.exp (z * (c j : ℂ)) * correctedValue F ζ hζ K hK f a' (c j) z g = 0
    simp only [correctedValue, show logInc F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK) a' g ≠ c j from hj,
      ↓reduceIte, mul_zero]
  · simp

end DedekindZetaZeroFree.KPLiteralTensorEquivariance.FiniteClearedCovariance

end
