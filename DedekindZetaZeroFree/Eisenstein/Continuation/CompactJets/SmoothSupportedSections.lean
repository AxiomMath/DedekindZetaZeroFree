module

public import DedekindZetaZeroFree.Analysis.RightFrame.CauchyCoefficient
public import DedekindZetaZeroFree.Eisenstein.Continuation.CompactJets.Defs

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology Filter

namespace DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

open KPContSectorSmoothFramesSupport KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorLineL2Isometry
open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContCotangentActualGenuineTwistIsotropy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

section ScalarCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem scalar_point_holomorphic (U : Set E) (O : Set ℂ) (f : ℂ → E → ℂ)
    (hh : ∀ (C : Set E) (hC : IsCompact C), C ⊆ U →
      ∀ (n : ℕ) (v : Fin n → E),
        letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
        ∃ j : ℂ → ContinuousMap C ℂ, DifferentiableOn ℂ j O ∧
          ∀ s ∈ O, ∀ x : C, j s x = iteratedFDerivWithin ℝ n (f s) U x.val v)
    (x : E) (hx : x ∈ U) : DifferentiableOn ℂ (fun s => f s x) O := by
  have hC : IsCompact ({x} : Set E) := isCompact_singleton
  letI : CompactSpace ({x} : Set E) := isCompact_iff_compactSpace.mp hC
  obtain ⟨j,hj,heq⟩ := hh {x} hC (Set.singleton_subset_iff.mpr hx) 0 (fun i => Fin.elim0 i)
  have hdiff := (ContinuousMap.evalCLM ℂ (⟨x, Set.mem_singleton x⟩ : ({x} : Set E))).differentiable.comp_differentiableOn hj
  apply hdiff.congr
  intro s hs
  simpa [iteratedFDerivWithin_zero_apply] using (heq s hs ⟨x, Set.mem_singleton x⟩).symm

private theorem scalar_jet_joint (U : Set E) (O : Set ℂ) (f : ℂ → E → ℂ)
    (hh : ∀ (C : Set E) (hC : IsCompact C), C ⊆ U →
      ∀ (n : ℕ) (v : Fin n → E),
        letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
        ∃ j : ℂ → ContinuousMap C ℂ, DifferentiableOn ℂ j O ∧
          ∀ s ∈ O, ∀ x : C, j s x = iteratedFDerivWithin ℝ n (f s) U x.val v)
    (C : Set E) (hC : IsCompact C) (hCU : C ⊆ U) (n : ℕ) (v : Fin n → E) :
    ContinuousOn (fun p : ℂ × E => iteratedFDerivWithin ℝ n (f p.1) U p.2 v) (O ×ˢ C) := by
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  obtain ⟨j,hj,heq⟩ := hh C hC hCU n v
  have hjoint : ContinuousOn (fun p : ℂ × C => j p.1 p.2) (O ×ˢ Set.univ) :=
    continuous_eval.comp_continuousOn ((hj.continuousOn.comp continuous_fst.continuousOn
      (fun _ hp => hp.1)).prodMk continuous_snd.continuousOn)
  apply continuousOn_iff_continuous_restrict.mpr
  let g : (O ×ˢ C) → ℂ × C := fun p => (p.val.1, ⟨p.val.2, p.property.2⟩)
  have hg : Continuous g := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.property.2))
  have hc : Continuous (fun p : (O ×ˢ C) => j p.val.1 ⟨p.val.2, p.property.2⟩) :=
    hjoint.comp_continuous hg (fun p => ⟨p.property.1, Set.mem_univ _⟩)
  apply hc.congr
  intro p
  exact heq p.val.1 p.property.1 ⟨p.val.2, p.property.2⟩
private theorem jet_constant_word (n : ℕ) (u : E → ℂ) (U : Set E) (hU : IsOpen U)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (x : E) (hx : x ∈ U) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n u U x v =
      RightFrame.PullbackWords.constantDirectionWord (List.ofFn v) u x := by
  rw [iteratedFDerivWithin_of_isOpen n hU hx]
  induction n generalizing x with
  | zero => simp [RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord, iteratedFDeriv_zero_apply]
  | succ n ih =>
    rw [((hu x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
      (m := n) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) |>.iteratedFDeriv_succ_apply_left']
    have heq : (fun y => iteratedFDeriv ℝ n u y (Fin.tail v)) =ᶠ[𝓝 x]
        RightFrame.PullbackWords.constantDirectionWord (List.ofFn (Fin.tail v)) u :=
      eventually_of_mem (hU.mem_nhds hx) fun y hy => ih y hy _
    rw [heq.fderiv_eq]
    simp only [List.ofFn_succ, RightFrame.PullbackWords.constantDirectionWord,
      RightFrame.PullbackWords.directionalWord]
    rfl

private theorem basis_word (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (w : List (Fin (Module.finrank ℝ E))) (u : E → ℂ) :
    RightFrame.PullbackWords.directionalWord (fun i _ => b i) w u =
      RightFrame.PullbackWords.constantDirectionWord (w.map b) u := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [RightFrame.PullbackWords.directionalWord, List.map_cons,
      RightFrame.PullbackWords.constantDirectionWord] at ih ⊢
    rw [ih]

theorem scalar_parameter_jet_smooth (U : Set E) (hU : IsOpen U) (O : Set ℂ) (hO : IsOpen O)
    (f : ℂ → E → ℂ) (hsp : ∀ s ∈ O, ContDiffOn ℝ (⊤ : ℕ∞) (f s) U)
    (hh : ∀ (C : Set E) (hC : IsCompact C), C ⊆ U →
      ∀ (n : ℕ) (v : Fin n → E),
        letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
        ∃ j : ℂ → ContinuousMap C ℂ, DifferentiableOn ℂ j O ∧
          ∀ s ∈ O, ∀ x : C, j s x = iteratedFDerivWithin ℝ n (f s) U x.val v)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => iteratedDerivWithin k (fun z => f z x) O s) U := by
  obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp hO s hs
  let r := ε/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdisk : Metric.closedBall s r ⊆ O := fun z hz =>
    hεO (lt_of_le_of_lt hz (by change ε / 2 < ε; linarith))
  let b := Module.finBasis ℝ E
  have hj : ∀ (w : List (Fin (Module.finrank ℝ E))) (C : Set E), IsCompact C → C ⊆ U →
      ContinuousOn (fun p : ℂ × E => RightFrame.PullbackWords.directionalWord (fun i _ => b i) w (f p.1) p.2)
        (Metric.closedBall s r ×ˢ C) := by
    intro w C hC hCU
    have ht := scalar_jet_joint U O f hh C hC hCU (w.map b).length (w.map b).get
    apply (ht.mono (Set.prod_mono hdisk (Set.Subset.refl C))).congr
    intro p hp
    dsimp only
    rw [basis_word]
    have hword := (jet_constant_word _ _ U hU (hsp p.1 (hdisk hp.1)) _ (hCU hp.2) (w.map b).get).symm
    simpa only [List.ofFn_get] using hword
  have hc := RightFrame.CauchyCoefficient.coefficient_smooth U hU
    (fun i _ => b i) (fun _ => contDiffOn_const) (fun _ _ => ⟨b, fun _ => rfl⟩)
    O hO f s r hr hdisk hsp hj (fun x hx => scalar_point_holomorphic U O f hh x hx) k
  have heq (x : E) (hx : x ∈ U) :
      iteratedDerivWithin k (fun z => f z x) O s =
        (k.factorial : ℂ) * RightFrame.CauchyCoefficient.cauchyCoefficient f s r k x := by
    rw [iteratedDerivWithin_of_isOpen hO hs]
    have hf := (scalar_point_holomorphic U O f hh x hx).mono hdisk
    have hi := hf.circleIntegral_one_div_sub_center_pow_smul hr k
    have hkernel : (fun z => (z-s) ^ (-((k : ℤ)+1)) * f z x) =
        (fun z => (1 / (z-s) ^ (k+1)) • f z x) := by
      funext z
      rw [show -((k : ℤ)+1) = -((k+1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
      simp only [one_div, smul_eq_mul]
    unfold RightFrame.CauchyCoefficient.cauchyCoefficient
    rw [hkernel, hi, smul_eq_mul]
    have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
    field_simp
  exact (contDiffOn_const.mul hc).congr (fun x hx => heq x hx)

end ScalarCalculus

def pointwiseJets (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (k : ℕ) (s : ℂ) : Sections F ζ hζ U R P H := fun i =>
  ⟨fun x => iteratedDerivWithin k (fun z => (w z i).val x) O s, by
    constructor
    · intro x ε hε
      have heq : (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (w z i).val x) =
          (fun z => (w z i).val x) := by
        funext z
        exact (w z i).property.1 x ε hε
      rw [← iteratedDerivWithin_const_mul_field, heq]
    · intro γ x
      have heq : (fun z => (w z i).val ((γ : KPCuspArithmetic.PGL2 F) • x)) =
          (fun z => (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) * (w z i).val x) := by
        funext z
        exact (w z i).property.2 γ x
      dsimp only
      rw [heq, iteratedDerivWithin_const_mul_field]⟩

@[simp] theorem pointwiseJets_zero (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ) (s : ℂ) :
    pointwiseJets w O 0 s = w s := by
  funext i
  apply Subtype.ext
  simp [pointwiseJets]

@[simp] theorem pointwiseJets_apply (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (k : ℕ) (s : ℂ) (i) (x) :
    (pointwiseJets w O k s i).val x = iteratedDerivWithin k (fun z => (w z i).val x) O s := rfl

theorem pointwiseJets_frame (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (k : ℕ) (s : ℂ) (a : ActualChart (U := U) (H := H)) (x : M F) :
    (isotropyChart a).coefficient (pointwiseJets w O k s) x =
      iteratedDerivWithin k (fun z => (isotropyChart a).coefficient (w z) x) O s := by
  simp only [LiftedChart.coefficient, pointwiseJets_apply, iteratedDerivWithin_const_mul_field]

theorem pointwiseJets_support (w : ℂ → Sections F ζ hζ U R P H) (O : Set ℂ)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsClosed K)
    (hsupport : ∀ s ∈ O, tsupport (sectionNorm F ζ hζ U R P H (w s)) ⊆ K)
    (k : ℕ) (s : ℂ) (hs : s ∈ O) :
    tsupport (sectionNorm F ζ hζ U R P H (pointwiseJets w O k s)) ⊆ K := by
  apply closure_minimal _ hK
  intro b hb
  by_contra hbK
  let p := (H.atlas U).components.symm b
  obtain ⟨x, hx⟩ := Quotient.mk_surjective p.2
  have hbase : (H.atlas U).components ⟨p.1, Quotient.mk _ x⟩ = b := by
    rw [hx]
    exact (H.atlas U).components.apply_symm_apply b
  have hzero : Set.EqOn (fun z => (w z p.1).val x) (fun _ => (0 : ℂ)) O := by
    intro z hz
    apply norm_eq_zero.mp
    rw [← sectionNorm_component, hbase]
    exact image_eq_zero_of_notMem_tsupport (fun h => hbK (hsupport z hz h))
  have hz := iteratedDerivWithin_congr (n := k) hzero hs
  simp only [iteratedDerivWithin_fun_const_zero] at hz
  have hnorm : sectionNorm F ζ hζ U R P H (pointwiseJets w O k s) b = 0 := by
    rw [← hbase, sectionNorm_component, pointwiseJets_apply, hz, norm_zero]
  exact hb hnorm
private theorem labeledAInv_smooth (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F)) :
    ContDiff ℝ (⊤ : ℕ∞) (labeledAInv p) := by
  unfold labeledAInv
  apply (CotangentLogCoframe.A (d F)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro k
  exact contDiff_apply ℝ (ℂ × ℝ) (p k)

private theorem action_smooth (g : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => g • x) := by
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  rw [← hG]
  have he : (fun x : KPCuspGenuineMonodromy.SymmetricSpace F =>
      (Matrix.ProjGenLinGroup.mk G : KPCuspArithmetic.PGL2 F) • x) = KPCuspSiegel.glAction F G := by
    funext x; exact KPCuspSiegel.action_mk F G x
  rw [he]
  exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
    (fun k => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F k).embedding G)).of_le le_top

private theorem labeledA_labeledAInv' (p : Fin (d F) ≃ Fin (KPCuspLogShape.dimension F))
    (x : KPCuspGenuineMonodromy.SymmetricSpace F) : labeledA p (labeledAInv p x) = x := by
  funext k
  simp [labeledA, labeledAInv]

private theorem chart_smooth_to_domain (v : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H))
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) ((isotropyChart a).coefficient v) (omega a)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (v a.component).val a.domain := by
  have hm : Set.MapsTo (labeledAInv (placeEquiv F ζ hζ)) a.domain (omega a) := by
    intro x hx
    simpa only [omega, Set.mem_preimage, labeledA_labeledAInv'] using hx
  have hh := hv.comp (labeledAInv_smooth (placeEquiv F ζ hζ)).contDiffOn hm
  apply hh.congr
  intro x hx
  simp only [Function.comp_apply, LiftedChart.coefficient, isotropyChart,
    ChartKind.representative, labeledA_labeledAInv', one_smul, map_one, Units.val_one, one_mul]

theorem finite_chart_smooth_sections (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hK : IsClosed K) (v : Sections F ζ hζ U R P H)
    (hvK : tsupport (sectionNorm F ζ hζ U R P H v) ⊆ K)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (hcover : K ⊆ ⋃ i, (charts i).baseDomain)
    (hv : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) ((isotropyChart (charts j)).coefficient v)
      (omega (charts j))) : IsSmoothSections F ζ hζ U R P H v := by
  intro i
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let b : KPFiniteCuspAtlas.rawXU F ζ hζ U := (H.atlas U).components ⟨i, Quotient.mk _ x⟩
  by_cases hbK : b ∈ K
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover hbK)
    obtain ⟨y, hy⟩ := hj
    have hxy : (H.atlas U).components ⟨(charts j).component, Quotient.mk _ y.val⟩ =
        (H.atlas U).components ⟨i, Quotient.mk _ x⟩ := by
      rw [(H.atlas U).components_formula]
      exact hy
    have hij : (charts j).component = i := congrArg Sigma.fst ((H.atlas U).components.injective hxy)
    subst i
    have hloc := chart_smooth_to_domain v (charts j) (hv j)
    have hq : (Quotient.mk _ y.val : KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative (charts j).component))) =
        Quotient.mk _ x := by
      exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective hxy)).2
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
    have hlocAt := hloc.contDiffAt ((charts j).domain_open.mem_nhds y.property)
    rw [← hγ] at hlocAt
    have hcomp := hlocAt.comp x (action_smooth (γ : KPCuspArithmetic.PGL2 F)).contDiffAt
    let c : ℂ := (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line (charts j).component).rho γ) : ℂ)
    have hc : c ≠ 0 := Units.ne_zero _
    have hh := hcomp.const_smul c⁻¹
    apply hh.congr_of_eventuallyEq
    apply Filter.Eventually.of_forall
    intro z
    change (v (charts j).component).val z = c⁻¹ * (v (charts j).component).val ((γ : KPCuspArithmetic.PGL2 F) • z)
    rw [(v (charts j).component).property.2 γ z]
    simp [c, ← mul_assoc, hc]
  · have hbase : Continuous (fun z : KPCuspGenuineMonodromy.SymmetricSpace F =>
        (H.atlas U).components ⟨i, Quotient.mk _ z⟩) :=
      (H.atlas U).components.continuous.comp (continuous_sigmaMk.comp continuous_quotient_mk')
    have he : (v i).val =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
      have hnh : ∀ᶠ z in 𝓝 x, (H.atlas U).components ⟨i, Quotient.mk _ z⟩ ∉ K :=
        hbase.continuousAt.eventually (hK.isOpen_compl.mem_nhds hbK)
      filter_upwards [hnh] with z hz
      apply norm_eq_zero.mp
      rw [← sectionNorm_component]
      exact image_eq_zero_of_notMem_tsupport (fun h => hz (hvK h))
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem parameter_jets_sections_source
    (O : Set ℂ) (_hO : IsOpen O)
    (K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (_hK : IsCompact K)
    (w : ℂ → Sections F ζ hζ U R P H)
    (_smooth : ∀ s ∈ O, IsSmoothSections F ζ hζ U R P H (w s))
    (_support : ∀ s ∈ O, tsupport (sectionNorm F ζ hζ U R P H (w s)) ⊆ K)
    (m : ℕ) (charts : Fin m → ActualChart (U := U) (H := H))
    (_cover : K ⊆ ⋃ i, (charts i).baseDomain)
    (_holomorphic : ∀ i, ChartHolomorphicOn (charts i) w O) :
    ∃ wk : ℕ → ℂ → Sections F ζ hζ U R P H,
      (∀ s ∈ O, wk 0 s = w s) ∧
      (∀ k s, s ∈ O → IsSmoothSections F ζ hζ U R P H (wk k s) ∧
        tsupport (sectionNorm F ζ hζ U R P H (wk k s)) ⊆ K) ∧
      (∀ k s, s ∈ O → ∀ i x,
        (wk k s i).val x = iteratedDerivWithin k (fun z => (w z i).val x) O s) ∧
      (∀ k s, s ∈ O → ∀ a : ActualChart (U := U) (H := H),
        (fun y : a.domain => (isotropyChart a).coefficient (wk k s)
          (KPContActualCotangentPieceHilbertSum.coordinates a y).val) =ᵐ[a.liftedMeasure]
        (fun y : a.domain => iteratedDerivWithin k
          (fun z => (isotropyChart a).coefficient (w z)
            (KPContActualCotangentPieceHilbertSum.coordinates a y).val) O s)) := by
  refine ⟨pointwiseJets w O, fun s _ => pointwiseJets_zero w O s, ?_, ?_, ?_⟩
  · intro k s hs
    have hsupp := pointwiseJets_support w O K _hK.isClosed _support k s hs
    refine ⟨finite_chart_smooth_sections K _hK.isClosed (pointwiseJets w O k s)
      hsupp m charts _cover ?_, hsupp⟩
    intro j
    have hA : ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
      apply contDiff_pi.mpr
      intro q
      exact (contDiff_apply ℝ (ℂ × ℝ) ((placeEquiv F ζ hζ).symm q)).comp
        (CotangentLogCoframe.A (d F)).contDiff
    have hU : IsOpen (omega (charts j)) := (charts j).domain_open.preimage hA.continuous
    have hsp : ∀ z ∈ O, ContDiffOn ℝ (⊤ : ℕ∞)
        ((isotropyChart (charts j)).coefficient (w z)) (omega (charts j)) := by
      intro z hz
      have heq : (isotropyChart (charts j)).coefficient (w z) =
          (w z (charts j).component).val ∘ labeledA (placeEquiv F ζ hζ) := by
        funext x
        simp [LiftedChart.coefficient, isotropyChart, ChartKind.representative]
      rw [heq]
      exact ((_smooth z hz (charts j).component).comp hA).contDiffOn
    have hh := scalar_parameter_jet_smooth (omega (charts j)) hU O _hO
      (fun z => (isotropyChart (charts j)).coefficient (w z)) hsp (_holomorphic j) k s hs
    exact hh.congr (fun x _ => pointwiseJets_frame w O k s (charts j) x)
  · intro k s hs i x
    rfl
  · intro k s hs a
    exact Filter.Eventually.of_forall (fun y => pointwiseJets_frame w O k s a
      (KPContActualCotangentPieceHilbertSum.coordinates a y).val)

end DedekindZetaZeroFree.KPContActualCompactSectionL2Jets

end
