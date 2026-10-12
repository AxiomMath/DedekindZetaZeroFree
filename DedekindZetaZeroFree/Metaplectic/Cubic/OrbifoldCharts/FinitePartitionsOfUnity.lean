module

public import DedekindZetaZeroFree.Adeles.Quotients.SmoothPartitions.PositiveBumps

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualSectorFiniteSupportPartition
open KPContActualCotangentCountableShrinking KPContSectorCoveredQuotientVocabulary
open KPContSectorFixedPushforwardSupport KPContSectorSmoothFramesSupport
open KPContSectorLineL2Isometry
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def IsSmoothMultiplier (η : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) : Prop :=
  ∀ c : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => η (Quotient.mk _ (x,c)))

structure FinitePartition {n : ℕ} (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) where
  neighborhood : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)
  neighborhood_open : IsOpen neighborhood
  contains_compact : K ⊆ neighborhood
  neighborhood_subset : neighborhood ⊆ O
  multiplier : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ
  continuous : ∀ i, Continuous (multiplier i)
  smooth : ∀ i, IsSmoothMultiplier F ζ hζ U (multiplier i)
  nonnegative : ∀ i x, 0 ≤ multiplier i x
  at_most_one : ∀ i x, multiplier i x ≤ 1
  compact_support : ∀ i, HasCompactSupport (multiplier i)
  support_subset : ∀ i, tsupport (multiplier i) ⊆ (C i).baseDomain ∩ O
  partition : ∀ x ∈ neighborhood, ∑ i, multiplier i x = 1
  differential_cancel : ∀ (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ)
    (x : SymmetricSpace F), Quotient.mk _ (x,c) ∈ neighborhood →
    (∑ i, fderiv ℝ (fun y : SymmetricSpace F => multiplier i (Quotient.mk _ (y,c))) x) = 0
  lift : Fin n → SymmetricSpace F → ℝ
  lift_smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (lift i)
  lift_compact_support : ∀ i, HasCompactSupport (lift i)
  lift_support_subset : ∀ i, tsupport (lift i) ⊆ (C i).domain
  lift_invariant : ∀ i (σ : (C i).Isotropy) (x : SymmetricSpace F),
    lift i ((σ.val : KPCuspArithmetic.PGL2 F) • x) = lift i x
  lift_restriction : ∀ i (x : (C i).domain), lift i x.val = multiplier i ((C i).toBase x)
  lift_zero_outside : ∀ i x, x ∉ (C i).domain → lift i x = 0

  line_reconstruction : ∀ (s : Sections F ζ hζ U R P H),
    (∀ j, Measurable (s j).val) →
    (∀ᵐ v ∂coveredMeasure F ζ hζ R U,
      q F ζ hζ U v ∉ K → (scalarRepresentative F ζ hζ U R P H s).val v = 0) →
    (scalarRepresentative F ζ hζ U R P H s).val =ᵐ[coveredMeasure F ζ hζ R U]
      (fun v => ∑ i, (multiplier i (q F ζ hζ U v) : ℂ) *
        (scalarRepresentative F ζ hζ U R P H s).val v)

  chart_line_reconstruction : ∀ (s : Sections F ζ hζ U R P H),
    (∀ j, Measurable (s j).val) →
    (∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
      b ∉ K → sectionNorm F ζ hζ U R P H s b = 0) →
    ∀ i, (C i).coefficient s =ᵐ[(C i).liftedMeasure]
      (fun y => ∑ j, (multiplier j ((C i).toBase y) : ℂ) • (C i).coefficient s y)
  same_chart_measure : ∀ i, Measure.map (C i).toBase (C i).liftedMeasure =
    (KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U).restrict (C i).baseDomain

namespace Construction
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

 theorem line_identity {n : ℕ}
    (K N : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hKN : K ⊆ N)
    (η : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : ∀ x ∈ N, ∑ i, η i x = 1)
    (s : Sections F ζ hζ U R P H)
    (hs : ∀ᵐ v ∂coveredMeasure F ζ hζ R U,
      q F ζ hζ U v ∉ K → (scalarRepresentative F ζ hζ U R P H s).val v = 0) :
    (scalarRepresentative F ζ hζ U R P H s).val =ᵐ[coveredMeasure F ζ hζ R U]
      (fun v => ∑ i, (η i (q F ζ hζ U v) : ℂ) * (scalarRepresentative F ζ hζ U R P H s).val v) := by
  filter_upwards [hs] with v hv
  by_cases h : q F ζ hζ U v ∈ K
  · rw [← Finset.sum_mul]
    have ht : (∑ i, (η i (q F ζ hζ U v) : ℂ)) = 1 := by
      exact_mod_cast hη _ (hKN h)
    rw [ht, one_mul]
  · rw [hv h]; simp

 theorem chart_identity {n : ℕ}
    (K N : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hKN : K ⊆ N)
    (η : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : ∀ x ∈ N, ∑ i, η i x = 1)
    (s : Sections F ζ hζ U R P H) (C : ShrunkChart F ζ hζ U R P H)
    (hs : ∀ᵐ b ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U,
      b ∉ K → sectionNorm F ζ hζ U R P H s b = 0) :
    C.coefficient s =ᵐ[C.liftedMeasure]
      (fun y => ∑ j, (η j (C.toBase y) : ℂ) • C.coefficient s y) := by
  have hp := every_shrunkChart_properties F ζ hζ U R P H C
  have ht := ae_of_ae_map hp.measurable.aemeasurable
    (show ∀ᵐ b ∂Measure.map C.toBase C.liftedMeasure,
      b ∉ K → sectionNorm F ζ hζ U R P H s b = 0 from by
        rw [hp.exact_pushforward]
        exact hs.filter_mono (ae_mono Measure.restrict_le_self))
  filter_upwards [ht] with y hy
  by_cases h : C.toBase y ∈ K
  · rw [← Finset.sum_smul]
    have hh : (∑ j, (η j (C.toBase y) : ℂ)) = 1 := by exact_mod_cast hη _ (hKN h)
    rw [hh, one_smul]
  · have hh := hy h
    have he : sectionNorm F ζ hζ U R P H s (C.toBase y) = ‖C.coefficient s y‖ := by
      change sectionNorm F ζ hζ U R P H s
        (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative C.component)
          (KPCuspSiegel.projection F _ y.val)) = _
      rw [← (H.atlas U).components_formula]
      exact sectionNorm_component F ζ hζ U R P H s C.component y.val
    have hz : C.coefficient s y = 0 := norm_eq_zero.mp (he ▸ hh)
    rw [hz]; simp

private theorem derivative_identity {n : ℕ}
    (N : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hN : IsOpen N)
    (η : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (hη : ∀ x ∈ N, ∑ i, η i x = 1)
    (hsm : ∀ i, IsSmoothMultiplier F ζ hζ U (η i))
    (c : KPFiniteCuspAtlas.FiniteCover F ζ hζ) (x : SymmetricSpace F)
    (hx : Quotient.mk _ (x,c) ∈ N) :
    (∑ i, fderiv ℝ (fun y : SymmetricSpace F => η i (Quotient.mk _ (y,c))) x) = 0 := by
  have he : (fun y : SymmetricSpace F => ∑ i, η i (Quotient.mk _ (y,c))) =ᶠ[𝓝 x]
      (fun _ => (1 : ℝ)) := by
    have hc : Continuous (fun y : SymmetricSpace F => (Quotient.mk _ (y,c) : KPFiniteCuspAtlas.rawXU F ζ hζ U)) :=
      continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)
    filter_upwards [(hN.preimage hc).mem_nhds hx] with y hy
    exact hη _ hy
  have hh := he.fderiv_eq (𝕜 := ℝ)
  simp only [fderiv_fun_const] at hh
  have heq : (fun y : SymmetricSpace F => ∑ i, η i (Quotient.mk _ (y,c))) =
      ∑ i, (fun y : SymmetricSpace F => η i (Quotient.mk _ (y,c))) := by
    funext y; exact (Finset.sum_apply y (Finset.univ : Finset (Fin n))
      (fun i (z : SymmetricSpace F) => η i (Quotient.mk _ (z,c)))).symm
  rw [heq, fderiv_sum (fun i _ => (hsm i c).differentiable (by simp) x)] at hh
  exact hh

 def empty_partition {n : ℕ} (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) : FinitePartition F ζ hζ U R P H C ∅ O := by
  refine { neighborhood := ∅
           neighborhood_open := isOpen_empty
           contains_compact := Set.Subset.rfl
           neighborhood_subset := Set.empty_subset O
           multiplier := fun _ _ => 0
           continuous := fun _ => continuous_const
           smooth := fun _ _ => contDiff_const
           nonnegative := fun _ _ => le_rfl
           at_most_one := fun _ _ => zero_le_one
           compact_support := by simp [HasCompactSupport]
           support_subset := by simp
           partition := by simp
           differential_cancel := by simp
           lift := fun _ _ => 0
           lift_smooth := fun _ => contDiff_const
           lift_compact_support := by simp [HasCompactSupport]
           lift_support_subset := by simp
           lift_invariant := fun _ _ _ => rfl
           lift_restriction := fun _ _ => rfl
           lift_zero_outside := fun _ _ _ => rfl
           line_reconstruction := ?_
           chart_line_reconstruction := ?_
           same_chart_measure := fun i => (every_shrunkChart_properties F ζ hζ U R P H (C i)).exact_pushforward }
  · intro s _ hs
    exact line_identity ∅ ∅ Set.Subset.rfl (fun _ _ => 0) (by simp) s hs
  · intro s _ hs i
    exact chart_identity ∅ ∅ Set.Subset.rfl (fun _ _ => 0) (by simp) s (C i) hs

private theorem normalize {n : ℕ} (C : Fin n → ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U)) (hK : IsCompact K) (hne : K.Nonempty)
    (B : KPContActualSectorPositiveBumps.PositiveBumps C K O) : Nonempty (FinitePartition F ζ hζ U R P H C K O) := by
  let S : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := fun x => ∑ i, B.bump i x
  have hS : Continuous S := continuous_finset_sum _ (fun i _ => B.continuous i)
  have hS0 : ∀ x, 0 ≤ S x := fun x => Finset.sum_nonneg (fun i _ => B.nonnegative i x)
  obtain ⟨a,ha,haK⟩ := hK.exists_forall_le' hS.continuousOn B.positive_sum
  let δ := a / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let D : ℝ → ℝ := fun t => t + δ * Real.smoothTransition (2 - 2 * t / δ)
  have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
    contDiff_id.add (contDiff_const.mul (Real.smoothTransition.contDiff.comp
      (contDiff_const.sub ((contDiff_const.mul contDiff_id).div_const δ))))
  have hDpos : ∀ t, 0 ≤ t → 0 < D t := by
    intro t ht
    by_cases h : 0 < t
    · exact add_pos_of_pos_of_nonneg h (mul_nonneg hδ.le (Real.smoothTransition.nonneg _))
    · have ht0 : t = 0 := le_antisymm (not_lt.mp h) ht
      simp only [D, ht0, mul_zero, zero_div, sub_zero, zero_add,
        Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2), mul_one]
      exact hδ
  have hDle : ∀ t, t ≤ D t := fun t => le_add_of_nonneg_right
    (mul_nonneg hδ.le (Real.smoothTransition.nonneg _))
  have hDeq : ∀ t, δ ≤ t → D t = t := by
    intro t ht
    have hd : 2 - 2*t/δ ≤ 0 := by
      have hh := (le_div_iff₀ hδ).mpr (by nlinarith : 2*δ ≤ 2*t)
      linarith
    simp [D, Real.smoothTransition.zero_of_nonpos hd]
  let η : Fin n → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ := fun i x => B.bump i x / D (S x)
  let N : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) := {x | δ < S x}
  have hN : IsOpen N := isOpen_lt continuous_const hS
  have hKN : K ⊆ N := by
    intro x hx
    have hh := haK x hx
    change δ < S x
    dsimp [δ]; linarith
  have hNO : N ⊆ O := by
    intro x hx
    change δ < S x at hx
    by_contra ho
    have hz : ∀ i, B.bump i x = 0 := by
      intro i
      apply image_eq_zero_of_notMem_tsupport
      intro hh; exact ho ((B.support_subset i hh).2)
    have : S x = 0 := by simp [S,hz]
    linarith
  have hηts : ∀ i, tsupport (η i) ⊆ tsupport (B.bump i) := by
    intro i
    apply closure_mono
    intro x hx
    exact fun hh => hx (by simp [η,hh])
  have hSS : ∀ c : KPFiniteCuspAtlas.FiniteCover F ζ hζ,
      ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => S (Quotient.mk _ (x,c))) :=
    fun c => ContDiff.sum (fun i _ => B.smooth i c)
  have hηsm : ∀ i, IsSmoothMultiplier F ζ hζ U (η i) := by
    intro i c
    exact (B.smooth i c).div (hD.comp (hSS c)) (fun x => ne_of_gt (hDpos _ (hS0 _)))
  have hpart : ∀ x ∈ N, ∑ i, η i x = 1 := by
    intro x hx
    change δ < S x at hx
    change (∑ i, B.bump i x / D (S x)) = 1
    rw [← Finset.sum_div,hDeq _ hx.le]
    exact div_self (ne_of_gt (hδ.trans hx))
  let Q : Fin n → SymmetricSpace F → KPFiniteCuspAtlas.rawXU F ζ hζ U := fun i x =>
    Quotient.mk _ (x,(H.atlas U).representative (C i).component)
  let L : Fin n → SymmetricSpace F → ℝ := fun i x => B.lift i x / D (S (Q i x))
  have hLts : ∀ i, tsupport (L i) ⊆ tsupport (B.lift i) := by
    intro i
    apply closure_mono
    intro x hx
    exact fun hh => hx (by simp [L,hh])
  have hQinv : ∀ i (σ : (C i).Isotropy) x, Q i ((σ.val : KPCuspArithmetic.PGL2 F) • x) = Q i x := by
    intro i σ x
    change KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (C i).component)
      (KPCuspSiegel.projection F _ (σ.val • x)) =
      KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (C i).component)
        (KPCuspSiegel.projection F _ x)
    apply congrArg (KPFiniteCuspAtlas.componentMap F ζ hζ U ((H.atlas U).representative (C i).component))
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    exact MulAction.mem_orbit_iff.mpr ⟨σ.val,rfl⟩
  refine ⟨{ neighborhood := N
            neighborhood_open := hN
            contains_compact := hKN
            neighborhood_subset := hNO
            multiplier := η
            continuous := fun i => (B.continuous i).div (hD.continuous.comp hS)
              (fun x => ne_of_gt (hDpos _ (hS0 x)))
            smooth := hηsm
            nonnegative := fun i x => div_nonneg (B.nonnegative i x) (hDpos _ (hS0 x)).le
            at_most_one := ?_
            compact_support := fun i => (B.compact_support i).of_isClosed_subset (isClosed_tsupport _) (hηts i)
            support_subset := fun i => (hηts i).trans (B.support_subset i)
            partition := hpart
            differential_cancel := ?_
            lift := L
            lift_smooth := ?_
            lift_compact_support := fun i => (B.lift_compact_support i).of_isClosed_subset (isClosed_tsupport _) (hLts i)
            lift_support_subset := fun i => (hLts i).trans (B.lift_support_subset i)
            lift_invariant := ?_
            lift_restriction := ?_
            lift_zero_outside := ?_
            line_reconstruction := ?_
            chart_line_reconstruction := ?_
            same_chart_measure := fun i => (every_shrunkChart_properties F ζ hζ U R P H (C i)).exact_pushforward }⟩
  · intro i x
    apply (div_le_one (hDpos _ (hS0 x))).mpr
    exact (Finset.single_le_sum (fun j _ => B.nonnegative j x) (Finset.mem_univ i)).trans (hDle _)
  · exact derivative_identity N hN η hpart hηsm
  · intro i
    exact (B.lift_smooth i).div (hD.comp (hSS _)) (fun x => ne_of_gt (hDpos _ (hS0 _)))
  · intro i σ x
    change B.lift i _ / D (S (Q i _)) = _
    rw [B.lift_invariant,hQinv]
  · intro i x
    change B.lift i x.val / D (S (Q i x.val)) = _
    rw [B.lift_restriction]
    rfl
  · intro i x hx
    change B.lift i x / _ = 0
    rw [B.lift_zero_outside i x hx, zero_div]
  · intro s _ hs
    exact line_identity K N hKN η hpart s hs
  · intro s _ hs i
    exact chart_identity K N hKN η hpart s (C i) hs

end Construction

end DedekindZetaZeroFree.KPContActualSectorFiniteSupportPartition

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_finite_support_partition_in_charts
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (n : ℕ) (C : Fin n → KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O)
    (hcover : K ⊆ ⋃ i, (C i).baseDomain) :
    Nonempty (KPContActualSectorFiniteSupportPartition.FinitePartition F ζ hζ U R P H C K O) := by
  by_cases he : K = ∅
  · subst K
    exact ⟨KPContActualSectorFiniteSupportPartition.Construction.empty_partition C O⟩
  · obtain ⟨B⟩ := KPContActualSectorPositiveBumps.actual_positive_bumps
      F ζ hζ U R P H n C K O hK hO hKO hcover
    exact KPContActualSectorFiniteSupportPartition.Construction.normalize C K O hK
      (Set.nonempty_iff_ne_empty.mpr he) B

theorem kp_cont_actual_sector_finite_support_partition
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (K O : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U))
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ (n : ℕ) (C : Fin n → KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H),
      (K = ∅ → n = 0) ∧ K ⊆ ⋃ i, (C i).baseDomain ∧
        Nonempty (KPContActualSectorFiniteSupportPartition.FinitePartition F ζ hζ U R P H C K O) := by
  by_cases he : K = ∅
  · let C : Fin 0 → KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H := Fin.elim0
    have hc : K ⊆ ⋃ i, (C i).baseDomain := by simp [he]
    exact ⟨0,C,fun _ => rfl,hc,
      kp_cont_actual_sector_finite_support_partition_in_charts F ζ hζ U R P H 0 C K O hK hO hKO hc⟩
  · obtain ⟨_, A⟩ := kp_cont_actual_cotangent_countable_shrinking F ζ hζ U R P H
    let A := Classical.choice A
    obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun n => (A.chart n).baseDomain)
      (fun n => (A.properties n).base_open) (by rw [A.covers]; exact Set.subset_univ K)
    let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
    let C : Fin (Fintype.card s) → KPContActualCotangentCountableShrinking.ShrunkChart F ζ hζ U R P H := fun i => A.chart (e i)
    have hc : K ⊆ ⋃ i, (C i).baseDomain := by
      intro x hx
      obtain ⟨n, hn, hxn⟩ := Set.mem_iUnion₂.mp (hs hx)
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨n,hn⟩, ?_⟩
      simpa [C] using hxn
    exact ⟨Fintype.card s,C,fun h => (he h).elim,hc,
      kp_cont_actual_sector_finite_support_partition_in_charts F ζ hζ U R P H _ C K O hK hO hKO hc⟩

end DedekindZetaZeroFree

end
