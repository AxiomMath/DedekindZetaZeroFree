module

public import DedekindZetaZeroFree.Metaplectic.Torus.Averaging.WeightedChartExtension
public import DedekindZetaZeroFree.Metaplectic.Torus.Averaging.FiniteCompactRepresentatives
public import DedekindZetaZeroFree.Metaplectic.Torus.CompactNormalizedWeightBound

@[expose] public section

open scoped NumberField Classical NNReal BigOperators Topology
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.TorusChartTransport
open KPGlobalTorusBorelNormTwistTransport KPGlobalTorusFiniteStagesCofinality
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem inducedFunctions_fiber_eval (P : Polarization F ζ hζ)
    (f : InducedFunctions F ζ hζ P) (g₀ : G F ζ hζ) (t : E F ζ hζ) :
    (f.val g₀).val.val t = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
      (f.val (t.val * g₀)).val.val 1 := by
  have hc := f.property t 0 g₀
  have he := congrArg (fun v : Smooth F ζ hζ P => v.val.val 1) hc
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2
      (NNReal.coe_pos.2 (pos_iff_ne_zero.2
        (Units.ne_zero (KPGlobalTorusFunctionData.delta F ζ hζ t))))))
  have hn : KPGlobalTorusFunctionData.N F ζ hζ (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  simp only [hn, mul_one, KPGlobalTorusPeriodizationInverse.rightAction_formula,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, one_mul] at he
  calc (f.val g₀).val.val t
      = (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ *
          (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t * (f.val g₀).val.val t) := by
        rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    _ = _ := congrArg (fun z : ℂ => (KPGlobalTorusFunctionData.deltaHalf F ζ hζ t)⁻¹ * z)
        he.symm

theorem groupArchChart_commutes_finite (a : G F ζ hζ)
    (ha : a ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ) (z : GroupArch F) :
    Commute (groupArchChart F ζ hζ z) a := by
  obtain ⟨b, hb, rfl⟩ := ha
  have hc : Commute (groupArchTuple F ζ hζ z) b := by
    show (groupArchTuple F ζ hζ z) * b = b * (groupArchTuple F ζ hζ z)
    apply RestrictedProduct.ext
    intro v
    cases v with
    | inl w =>
      have hw : b (Sum.inl w) = 1 := (Subgroup.mem_iInf.mp hb) w
      simp [hw]
    | inr q =>
      change 1 * b (Sum.inr q) = b (Sum.inr q) * 1
      simp
  exact hc.map ((KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ))

theorem complex_diagonal_chart_absorption (w : InfinitePlace F)
    (a y : (KPHilbert.Completion F (Sum.inl w))ˣ)
    (l u : KPHilbert.Completion F (Sum.inl w)) :
    KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) a *
        (KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) l *
          KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) y *
          KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) u) =
      KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (l / (a : KPHilbert.Completion F (Sum.inl w))) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) (a * y) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) u := by
  unfold KPStandardLocalRootLifts.A KPStandardLocalRootLifts.LowerN KPStandardLocalRootLifts.N
  simp only [KPLocalCover.sectionMap_mul, KPLocalChartTopology.complex_sigmaTwo_eq_one,
    map_one, one_mul]
  congr 1
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPStandardLocalRootLifts.lowerN, KubotaRankTwo.coe_d, KubotaRankTwo.coe_n,
      Matrix.mul_apply, Fin.sum_univ_two]
  · ring
  · field_simp
  · left; field_simp

def groupArchDiagonalTransport (a : InfinitePlace F → ℂˣ) (z : GroupArch F) :
    GroupArch F := fun w i =>
  if i = 0 then z w i / (a w : ℂ) else
  if i = 1 then (a w : ℂ) * z w i else z w i

theorem groupArchDiagonalTransport_contDiff (a : InfinitePlace F → ℂˣ) :
    ContDiff ℝ (⊤ : ℕ∞) (groupArchDiagonalTransport F a) := by
  apply contDiff_pi.mpr
  intro w
  apply contDiff_pi.mpr
  intro i
  by_cases hi0 : i = 0
  · simp only [groupArchDiagonalTransport, hi0, ↓reduceIte]
    exact ((contDiff_apply ℝ _ 0).comp (contDiff_apply ℝ _ w)).div_const _
  · by_cases hi1 : i = 1
    · simp only [groupArchDiagonalTransport, hi0, hi1, ↓reduceIte]
      exact contDiff_const.mul ((contDiff_apply ℝ _ 1).comp (contDiff_apply ℝ _ w))
    · simp only [groupArchDiagonalTransport, hi0, hi1, ↓reduceIte]
      exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ w)

theorem groupArchDiagonalTransport_domain (a : InfinitePlace F → ℂˣ)
    (z : GroupArch F) :
    groupArchDiagonalTransport F a z ∈ groupArchDomain F ↔
      z ∈ groupArchDomain F := by
  simp [groupArchDomain, groupArchDiagonalTransport, Units.ne_zero]

def groupArchDiagonalTransport_compact (a : InfinitePlace F → ℂˣ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)) :
    KPGlobalTorusFunctionData.JetCompact (groupArchDomain F) where
  set := groupArchDiagonalTransport F a '' K.set
  compact := K.compact.image (groupArchDiagonalTransport_contDiff F a).continuous
  inside := by
    rintro _ ⟨z, hz, rfl⟩
    exact (groupArchDiagonalTransport_domain F a z).2 (K.inside hz)

theorem groupArchDiagonalTransport_absorption (a : InfinitePlace F → ℂˣ)
    (z : GroupArch F) (hz : z ∈ groupArchDomain F) :
    KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (a w : ℂ)) *
      groupArchChart F ζ hζ z =
      groupArchChart F ζ hζ (groupArchDiagonalTransport F a z) := by
  unfold KPGlobalTorusFunctionData.archDiagonalLift groupArchChart
  rw [← map_mul]
  apply congrArg
  rw [← map_mul]
  apply congrArg
  apply DFunLike.coe_injective
  funext v
  change KPGlobalTorusFunctionData.archDiagonalTuple F ζ hζ (fun w => (a w : ℂ)) v *
    groupArchTuple F ζ hζ z v =
    groupArchTuple F ζ hζ (groupArchDiagonalTransport F a z) v
  cases v with
  | inr q => simp [KPGlobalTorusFunctionData.archDiagonalTuple, groupArchTuple]
  | inl w =>
    have hz0 := hz w
    have haz0 : (a w : ℂ) * z w 1 ≠ 0 := mul_ne_zero (Units.ne_zero _) hz0
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
        (if h : (a w : ℂ) = 0 then 1 else Units.mk0 (e.symm (a w)) _) *
        (KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (z w 0)) *
          KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
            (if h : z w 1 = 0 then 1 else Units.mk0 (e.symm (z w 1)) _) *
          KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (z w 2))) =
      KPStandardLocalRootLifts.LowerN F ζ hζ (Sum.inl w) (e.symm (z w 0 / (a w : ℂ))) *
        KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w)
          (if h : (a w : ℂ) * z w 1 = 0 then 1 else Units.mk0 (e.symm ((a w : ℂ) * z w 1)) _) *
        KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) (e.symm (z w 2))
    simp only [hz0, haz0, Units.ne_zero, ↓reduceDIte]
    rw [complex_diagonal_chart_absorption F ζ hζ]
    congr 2
    · apply congrArg
      simp only [map_div₀, Units.val_mk0]
    · apply congrArg
      apply Units.ext
      simp only [Units.val_mul, Units.val_mk0, map_mul]

def groupArchDiagonalTransportCLM (a : InfinitePlace F → ℂˣ) :
    GroupArch F →L[ℝ] GroupArch F where
  toFun := groupArchDiagonalTransport F a
  map_add' := by
    intro z y
    funext w i
    simp only [groupArchDiagonalTransport, Pi.add_apply]
    split_ifs <;> ring
  map_smul' := by
    intro c z
    funext w i
    simp only [groupArchDiagonalTransport, Pi.smul_apply, Complex.real_smul, RingHom.id_apply]
    split_ifs <;> ring
  cont := (groupArchDiagonalTransport_contDiff F a).continuous

theorem inducedJet_pointwise (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ P J) (z : GroupArch F) (hz : z ∈ K.set) :
    ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1)
      (groupArchDomain F) z‖ ≤ inducedJet F ζ hζ P J g n K f := by
  change _ ≤ inducedJetBound F ζ hζ P J g n K f
  apply le_csSup _ (Set.mem_image_of_mem _ hz)
  apply K.compact.bddAbove_image
  apply ContinuousOn.mono _ K.inside
  exact ((f.property.1 g).continuousOn_iteratedFDerivWithin (by simp)
    (groupArchDomain_open F).uniqueDiffOn).norm

set_option maxHeartbeats 4000000 in

theorem groupArchDiagonalTransport_jet_bound (a : InfinitePlace F → ℂˣ)
    (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (f : InducedLevel F ζ hζ P J) (z : GroupArch F) (hz : z ∈ K.set) :
    ‖iteratedFDerivWithin ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ
        (groupArchDiagonalTransport F a y) * g)).val.val 1)
      (groupArchDomain F) z‖ ≤
      ‖groupArchDiagonalTransportCLM F a‖ ^ n *
        inducedJet F ζ hζ P J g n (groupArchDiagonalTransport_compact F a K) f := by
  let L := groupArchDiagonalTransportCLM F a
  let H := fun y => (f.val.val (groupArchChart F ζ hζ y * g)).val.val 1
  have hpre : L ⁻¹' groupArchDomain F = groupArchDomain F := by
    ext y
    exact groupArchDiagonalTransport_domain F a y
  have hx : L z ∈ groupArchDomain F :=
    (groupArchDiagonalTransport_domain F a z).2 (K.inside hz)
  have hpreDiff : UniqueDiffOn ℝ (L ⁻¹' groupArchDomain F) := by
    rw [hpre]
    exact (groupArchDomain_open F).uniqueDiffOn
  have hid := L.iteratedFDerivWithin_comp_right (f.property.1 g)
    (groupArchDomain_open F).uniqueDiffOn hpreDiff hx (i := n) (by simp)
  change ‖iteratedFDerivWithin ℝ n (H ∘ L) (groupArchDomain F) z‖ ≤ _
  rw [hpre] at hid
  rw [hid]
  have hm := (iteratedFDerivWithin ℝ n H (groupArchDomain F) (L z)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hm
  rw [mul_comm] at hm
  refine hm.trans (mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) n))
  exact inducedJet_pointwise F ζ hζ P J g n
    (groupArchDiagonalTransport_compact F a K) f (L z) (Set.mem_image_of_mem _ hz)

theorem weightedChartIntegrand_representative (C : ModelData F ζ hζ) (s : ℂ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedFunctions F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s))
    (g : G F ζ hζ) (z : GroupArch F)
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)
    (b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C)
    (hb : KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C b = x) :
    weightedChartIntegrand F ζ hζ C s r f g z x =
      (((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) *
      (f.val (groupArchChart F ζ hζ z * g)).val.val b.val := by
  let r' : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C :=
    { lift := fun y => if y = x then b else r.lift y
      projects := fun y => by split_ifs with h; exact hb.trans h.symm; exact r.projects y }
  have h := congrFun (weightedChartIntegrand_independent F ζ hζ C s r r' f g z) x
  simpa only [weightedChartIntegrand, r', ↓reduceIte] using h

theorem finite_representative_level_formula (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g a : G F ζ hζ)
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)
    (b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C)
    (hb : KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C b = x)
    (hbfin : b.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J)
    (hj : b.val.val * g = a * j.val) (z : GroupArch F) :
    weightedChartIntegrand F ζ hζ C s r f.val g z x =
      (((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) *
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹ *
      (f.val.val (groupArchChart F ζ hζ z * a)).val.val 1 := by
  rw [weightedChartIntegrand_representative F ζ hζ C s r f.val g z x b hb,
    inducedFunctions_fiber_eval F ζ hζ _ f.val _ b.val]
  have hm : b.val.val * (groupArchChart F ζ hζ z * g) =
      (groupArchChart F ζ hζ z * a) * j.val := by
    calc
      _ = (b.val.val * groupArchChart F ζ hζ z) * g := (mul_assoc _ _ _).symm
      _ = (groupArchChart F ζ hζ z * b.val.val) * g :=
        congrArg (fun t : G F ζ hζ => t * g)
          (groupArchChart_commutes_finite F ζ hζ _ hbfin z).symm.eq
      _ = groupArchChart F ζ hζ z * (b.val.val * g) := mul_assoc _ _ _
      _ = _ := by rw [hj, mul_assoc]
  rw [hm, f.property.2 _ j]
  ring

theorem inducedJet_le_finite_sup (P : Polarization F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
 (A : Finset (G F ζ hζ)) (n : ℕ) (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
 (a : G F ζ hζ) (ha : a ∈ A) (f : InducedLevel F ζ hζ P J) :
 inducedJet F ζ hζ P J a n K f ≤
 ((A.image (fun a => (a,n,K))).sup (fun i => inducedJet F ζ hζ P J i.1 i.2.1 i.2.2)) f := by
  exact Finset.le_sup (s := A.image (fun a => (a,n,K))) (f := fun i => inducedJet F ζ hζ P J i.1 i.2.1 i.2.2)
    (Finset.mem_image.mpr ⟨a,ha,rfl⟩) f
theorem finite_representative_jet_estimate (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J)
    (g a : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F))
    (x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C)
    (b : KPGlobalTorusPeriodizationInverse.B F ζ hζ C)
    (hb : KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C b = x)
    (hbfin : b.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J)
    (hj : b.val.val * g = a * j.val) (z : GroupArch F) (hz : z ∈ K.set) :
    ‖iteratedFDerivWithin ℝ n
      (fun y => weightedChartIntegrand F ζ hζ C s r f.val g y x)
      (groupArchDomain F) z‖ ≤
    ‖(((((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) : ℂ) *
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹)‖ *
      inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J a n K f := by
  let c : ℂ := (((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) *
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹
  have he : (fun y => weightedChartIntegrand F ζ hζ C s r f.val g y x) =
      c • (fun y => (f.val.val (groupArchChart F ζ hζ y * a)).val.val 1) := by
    funext y
    exact finite_representative_level_formula F ζ hζ C s J r f g a x b hb hbfin j hj y
  have hf : ContDiffWithinAt ℝ n
      (fun y => (f.val.val (groupArchChart F ζ hζ y * a)).val.val 1)
      (groupArchDomain F) z := (f.property.1 a z (K.inside hz)).of_le (by simp)
  calc
    _ = ‖iteratedFDerivWithin ℝ n
        (c • (fun y => (f.val.val (groupArchChart F ζ hζ y * a)).val.val 1))
        (groupArchDomain F) z‖ := congrArg
          (fun q : GroupArch F → ℂ => ‖iteratedFDerivWithin ℝ n q (groupArchDomain F) z‖) he
    _ = ‖c‖ * ‖iteratedFDerivWithin ℝ n
        (fun y => (f.val.val (groupArchChart F ζ hζ y * a)).val.val 1)
        (groupArchDomain F) z‖ := by
      rw [iteratedFDerivWithin_const_smul_apply (R := ℂ) hf
        (groupArchDomain_open F).uniqueDiffOn (K.inside hz), norm_smul]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (inducedJet_pointwise F ζ hζ _ J a n K f z hz) (norm_nonneg c)

theorem compact_finite_conjugated_level_partition
    (C : ModelData F ζ hζ) (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (T : Set (KPGlobalTorusPeriodizationInverse.B F ζ hζ C))
    (hT : IsCompact T)
    (hfin : ∀ b ∈ T, b.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    ∃ A : Finset (G F ζ hζ), ∀ b ∈ T, ∃ a ∈ A,
      ∃ j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J,
        b.val.val * g = a * j.val := by
  have hn : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.finiteSubgroup_normal F ζ hζ
  let e : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ*
      KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    { toFun := fun u => ⟨g⁻¹ * u.val * g, by
        have h := hn.conj_mem u.val u.property g⁻¹
        simpa only [inv_inv, mul_assoc] using h⟩
      invFun := fun u => ⟨g * u.val * g⁻¹, hn.conj_mem u.val u.property g⟩
      left_inv := by intro u; apply Subtype.ext; dsimp; group
      right_inv := by intro u; apply Subtype.ext; dsimp; group
      map_mul' := by intro u v; apply Subtype.ext; dsimp; group
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have he (u : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
      (e u).val = g⁻¹ * u.val * g := rfl
  let q : T → KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    fun b => ⟨b.val.val.val, hfin b.val b.property⟩
  have hq : Continuous q := by
    exact (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  let U : T → Set T := fun b =>
    {c | e ((q b)⁻¹ * q c) ∈ J.toOpenSubgroup}
  have hU (b : T) : IsOpen (U b) :=
    J.toOpenSubgroup.isOpen.preimage (e.continuous.comp (continuous_const.mul hq))
  have hbU (b : T) : b ∈ U b := by
    change e ((q b)⁻¹ * q b) ∈ J.toOpenSubgroup
    simp
  letI : CompactSpace T := isCompact_iff_compactSpace.mp hT
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro b _
    exact Set.mem_iUnion.mpr ⟨b, hbU b⟩)
  refine ⟨t.image (fun b => b.val.val.val * g), ?_⟩
  intro b hb
  obtain ⟨c, hc, hbc⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (⟨b, hb⟩ : T)))
  let u := e ((q c)⁻¹ * q ⟨b, hb⟩)
  let j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J :=
    ⟨u.val, ⟨u, hbc, rfl⟩⟩
  refine ⟨c.val.val.val * g, Finset.mem_image.mpr ⟨c, hc, rfl⟩, j, ?_⟩
  have hj : j.val = g⁻¹ * (c.val.val.val)⁻¹ * b.val.val * g := by
    change u.val = _
    rw [he]
    change g⁻¹ * ((c.val.val.val)⁻¹ * b.val.val) * g = _
    simp only [mul_assoc]
  rw [hj]
  group

theorem weightedChart_source_jet_bound (C : ModelData F ζ hζ) (s : ℂ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (r : KPGlobalTorusPeriodizationInverse.AveragingRepresentatives F ζ hζ C)
    (g : G F ζ hζ) (n : ℕ)
    (K : KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)) :
    ∃ S : Finset (G F ζ hζ × ℕ ×
        KPGlobalTorusFunctionData.JetCompact (groupArchDomain F)),
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ f : InducedLevel F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s) J,
          ∀ z ∈ K.set,
            ∀ x : KPGlobalTorusPeriodizationInverse.CompactIndex F ζ hζ C,
              ‖iteratedFDerivWithin ℝ n
                (fun y => weightedChartIntegrand F ζ hζ C s r f.val g y x)
                (groupArchDomain F) z‖ ≤
              B * (S.sup (fun i =>
                inducedJet F ζ hζ (twist F ζ hζ (rationalModel F ζ hζ) s)
                  J i.1 i.2.1 i.2.2)) f := by
  have hh : ∃ T : Set (KPGlobalTorusPeriodizationInverse.B F ζ hζ C), IsCompact T ∧
      (∀ b ∈ T, b.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ) ∧
      KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C '' T = Set.univ :=
    actual_finite_compact_averaging_representatives F ζ hζ C
  obtain ⟨T, hTc, hTf, hTx⟩ := hh
  have hhA : ∃ A : Finset (G F ζ hζ), ∀ b ∈ T, ∃ a ∈ A,
      ∃ j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J,
        b.val.val * g = a * j.val :=
    compact_finite_conjugated_level_partition F ζ hζ C J g T hTc hTf
  obtain ⟨A, hA⟩ := hhA
  have hhB : ∃ B : ℝ, 0 ≤ B ∧ ∀ b ∈ T,
      ‖(((((twist F ζ hζ (productModel F ζ hζ C) s).character b)⁻¹ : ℂˣ) : ℂ) *
        (KPGlobalTorusFunctionData.deltaHalf F ζ hζ b.val)⁻¹)‖ ≤ B :=
    RepresentationTheory.torus_weighted_chart_quantitative_prove.compact_normalized_weight_bound
      F ζ hζ C s T hTc
  obtain ⟨B, hB, hBw⟩ := hhB
  refine ⟨A.image (fun a => (a, n, K)), B, hB, ?_⟩
  intro f z hz x
  have hx : x ∈ KPGlobalTorusPeriodizationInverse.averagingClass F ζ hζ C '' T := by
    rw [hTx]
    exact Set.mem_univ x
  obtain ⟨b, hb, hbx⟩ := hx
  have hAa : ∃ a : G F ζ hζ, a ∈ A ∧
      ∃ j : KPGlobalTorusFunctionData.globalLevel F ζ hζ J,
        b.val.val * g = a * j.val := hA b hb
  obtain ⟨a, ha, j, hj⟩ := hAa
  have hjb := finite_representative_jet_estimate F ζ hζ C s J r f g a n K
    x b hbx (hTf b hb) j hj z hz
  have hjs := inducedJet_le_finite_sup F ζ hζ
    (twist F ζ hζ (rationalModel F ζ hζ) s) J A n K a ha f
  have hp := inducedJet_pointwise F ζ hζ
    (twist F ζ hζ (rationalModel F ζ hζ) s) J a n K f z hz
  have hnonneg : 0 ≤ inducedJet F ζ hζ
      (twist F ζ hζ (rationalModel F ζ hζ) s) J a n K f :=
    (norm_nonneg _).trans hp
  exact hjb.trans (mul_le_mul (hBw b hb) hjs hnonneg hB)

end
end DedekindZetaZeroFree.TorusChartTransport
