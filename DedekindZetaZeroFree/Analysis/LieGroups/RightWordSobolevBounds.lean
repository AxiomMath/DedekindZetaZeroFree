module

public import DedekindZetaZeroFree.Analysis.RightFrame.PullbackWords
public import DedekindZetaZeroFree.Eisenstein.Continuation.SpatialRegularity.ExponentialPullbackBounds

@[expose] public section

section

noncomputable section
open MeasureTheory
open scoped Classical
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue.CoordinateSobolevBound
open KPContLocalNorm

private theorem zero_derivative {n k : ℕ} (f : Space n → ℂ) :
    coordinateDerivative (⟨fun _ => 0, by simp⟩ : MultiIndex n k) f = f := by
  have he : ∀ l : List (Fin n), l.flatMap (fun _ => ([] : List (Fin n))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih => simpa using ih
  simp [coordinateDerivative, MultiIndex.directions, coordinateDerivativeList, he]

theorem exists_sobolev_bound_of_coordinate_lpNorm {n k : ℕ} (A : LocalBall n) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Space n → ℂ,
      ContDiffOn ℝ (⊤ : ℕ∞) f A.carrier →
      ∀ hLp : ∀ α : MultiIndex n k,
        MemLp (coordinateDerivative α f) 2 (volume.restrict A.carrier),
      ∀ B : ℝ, 0 ≤ B →
      (∀ α : MultiIndex n k, ‖(hLp α).toLp (coordinateDerivative α f)‖ ≤ B) →
      ∃ u : IntegerSobolev A k,
        f =ᵐ[volume.restrict A.carrier]
          (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) ∧
        u.sobolevNorm ≤ C * B := by
  let C : ℝ := 1 + Real.sqrt (Fintype.card (MultiIndex n k))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hf hLp B hB hb
  obtain ⟨u, hu⟩ := smooth_has_integerSobolev_data A f hf hLp
  refine ⟨u, ?_, ?_⟩
  · have hz := (hLp (⟨fun _ => 0, by simp⟩ : MultiIndex n k)).coeFn_toLp
    rw [hu]
    simpa only [zero_derivative] using hz.symm
  · have hn : u.normSq ≤ (Fintype.card (MultiIndex n k) : ℝ) * B ^ 2 := by
      unfold IntegerSobolev.normSq
      calc
        ∑ α : MultiIndex n k, ‖u.derivatives α‖ ^ 2 ≤ ∑ _α : MultiIndex n k, B ^ 2 := by
          apply Finset.sum_le_sum
          intro α _
          rw [hu α]
          exact pow_le_pow_left₀ (norm_nonneg _) (hb α) _
        _ = (Fintype.card (MultiIndex n k) : ℝ) * B ^ 2 := by simp
    have hnorm : u.sobolevNorm ≤ Real.sqrt (Fintype.card (MultiIndex n k)) * B := by
      unfold IntegerSobolev.sobolevNorm
      calc
        Real.sqrt u.normSq ≤ Real.sqrt ((Fintype.card (MultiIndex n k) : ℝ) * B ^ 2) :=
          Real.sqrt_le_sqrt hn
        _ = Real.sqrt (Fintype.card (MultiIndex n k)) * B := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hB]
    exact hnorm.trans (by dsimp [C]; nlinarith)

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue.CoordinateSobolevBound

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue.RightWordSobolev
open KPContLocalNorm RightFrame.PullbackWords

private theorem coordinate_as_word {n : ℕ} (l : List (Fin n)) (f : Space n → ℂ) :
    constantDirectionWord (l.map (fun i => EuclideanSpace.single i 1)) f =
      coordinateDerivativeList l f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    change (fun x => fderiv ℝ
      (constantDirectionWord (l.map (fun i => EuclideanSpace.single i 1)) f) x
        (EuclideanSpace.single i 1)) = _
    rw [ih]
    rfl

private theorem finite_lp_combination {E I : Type*} [MeasurableSpace E] [Fintype I]
    (μ : Measure E) (c : I → E → ℝ) (v : I → E → ℂ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hv : ∀ i, MemLp (v i) 2 μ)
    (b : I → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hbound : ∀ i, ∀ᵐ x ∂μ, ‖c i x‖ ≤ b i) :
    ∃ h : MemLp (fun x => ∑ i, c i x • v i x) 2 μ,
      ‖h.toLp (fun x => ∑ i, c i x • v i x)‖ ≤
        ∑ i, b i * ‖(hv i).toLp (v i)‖ := by
  let t := fun i x => c i x • v i x
  have ht (i : I) : MemLp (t i) 2 μ := by
    apply (hv i).of_le_mul (c := b i) ((hc i).smul (hv i).aestronglyMeasurable)
    filter_upwards [hbound i] with x hx
    change ‖c i x • v i x‖ ≤ b i * ‖v i x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg (v i x))
  have hn (i : I) : ‖(ht i).toLp (t i)‖ ≤ b i * ‖(hv i).toLp (v i)‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(ht i).coeFn_toLp, (hv i).coeFn_toLp, hbound i] with x hx hy hz
    rw [hx, hy]
    exact (norm_smul _ _).le.trans (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
  have hsum : MemLp (fun x => ∑ i, t i x) 2 μ := memLp_finsetSum _ (fun i _ => ht i)
  refine ⟨hsum, ?_⟩
  have heq : hsum.toLp (fun x => ∑ i, t i x) = ∑ i, (ht i).toLp (t i) := by
    apply Lp.ext
    filter_upwards [hsum.coeFn_toLp, Lp.coeFn_fun_finsetSum (Finset.univ) (fun i => (ht i).toLp (t i)),
      ae_all_iff.mpr (fun i => (ht i).coeFn_toLp)] with x hx hy hz
    rw [hx, hy]
    change (∑ i, t i x) = ∑ i, ((ht i).toLp (t i)) x
    exact Finset.sum_congr rfl (fun i _ => (hz i).symm)
  rw [heq]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hn i))

theorem exists_finite_frame_word_sobolev_bound {n k : ℕ} {B : Type*} [Fintype B]
    (U : Set (Space n)) (hU : IsOpen U)
    (fields : B → Space n → Space n)
    (hfields : ∀ b, ContDiffOn ℝ (⊤ : ℕ∞) (fields b) U)
    (hframe : ∀ x ∈ U, ∃ e : Module.Basis B ℝ (Space n), ∀ b, e b = fields b x)
    (A : LocalBall n) (hA : Metric.closedBall A.center A.radius ⊆ U) :
    ∃ S : Finset (List B), (∀ w ∈ S, w.length ≤ k) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : Space n → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) f U →
        ∀ hLp : ∀ w ∈ S, MemLp (directionalWord fields w f) 2 (volume.restrict A.carrier),
        ∀ M : ℝ, 0 ≤ M →
        (∀ w (hw : w ∈ S), ‖(hLp w hw).toLp (directionalWord fields w f)‖ ≤ M) →
        ∃ u : IntegerSobolev A k,
          f =ᵐ[volume.restrict A.carrier]
            (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex n k) x) ∧
          u.sobolevNorm ≤ C * M := by
  classical
  have hsub : A.carrier ⊆ U := Metric.ball_subset_closedBall.trans hA
  have htransport (α : MultiIndex n k) := transport U U hU hU fields hfields hframe
    id contDiffOn_id (fun x hx => hx) (α.directions.map (fun i => EuclideanSpace.single i 1))
  choose N c w hc hw he using htransport
  have hclosed : IsCompact (Metric.closedBall A.center A.radius) := isCompact_closedBall _ _
  choose b hb using fun (α : MultiIndex n k) (i : Fin (N α)) =>
    hclosed.exists_bound_of_continuousOn ((hc α i).continuousOn.mono hA)
  let J := Σ α : MultiIndex n k, Fin (N α)
  let S : Finset (List B) := Finset.univ.image (fun p : J => w p.1 p.2)
  have hmem (α : MultiIndex n k) (i : Fin (N α)) : w α i ∈ S :=
    Finset.mem_image.mpr ⟨⟨α, i⟩, Finset.mem_univ _, rfl⟩
  let b' := fun α i => max (b α i) 0
  let D : ℝ := 1 + ∑ α : MultiIndex n k, ∑ i : Fin (N α), b' α i
  have hD : 0 < D := by dsimp [D, b']; positivity
  obtain ⟨C, hC, hSob⟩ := CoordinateSobolevBound.exists_sobolev_bound_of_coordinate_lpNorm (k := k) A
  refine ⟨S, ?_, C * D, mul_pos hC hD, ?_⟩
  · intro r hr
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hr
    exact (hw p.1 p.2).trans (by
      rw [List.length_map]
      have hh : p.1.directions.length = p.1.degree := by
        simp [MultiIndex.directions, MultiIndex.degree, List.length_flatMap,
          List.finRange, List.sum_ofFn, Function.comp_def]
      rw [hh]
      exact p.1.property)
  intro f hf hLp M hM hm
  have hcLp (α : MultiIndex n k) :
      ∃ h : MemLp (coordinateDerivative α f) 2 (volume.restrict A.carrier),
        ‖h.toLp (coordinateDerivative α f)‖ ≤ D * M := by
    have heq : coordinateDerivative α f =ᵐ[volume.restrict A.carrier]
        (fun x => ∑ i : Fin (N α), c α i x • directionalWord fields (w α i) f x) := by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
      have hh := he α f hf x (hsub hx)
      simpa only [Function.comp_id, id_eq, coordinate_as_word, coordinateDerivative] using hh
    obtain ⟨hh, hhn⟩ := finite_lp_combination (volume.restrict A.carrier) (c α)
      (fun i => directionalWord fields (w α i) f)
      (fun i => ((hc α i).continuousOn.mono hsub).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
      (fun i => hLp (w α i) (hmem α i)) (b' α)
      (fun i => le_max_right _ _) (fun i => by
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        exact (hb α i x (Metric.ball_subset_closedBall hx)).trans (le_max_left _ _))
    have hh' : MemLp (coordinateDerivative α f) 2 (volume.restrict A.carrier) := hh.ae_eq heq.symm
    refine ⟨hh', ?_⟩
    have hclass : hh'.toLp (coordinateDerivative α f) =
        hh.toLp (fun x => ∑ i : Fin (N α), c α i x • directionalWord fields (w α i) f x) := by
      apply Lp.ext
      exact hh'.coeFn_toLp.trans (heq.trans hh.coeFn_toLp.symm)
    rw [hclass]
    calc
      _ ≤ ∑ i : Fin (N α), b' α i * ‖(hLp (w α i) (hmem α i)).toLp (directionalWord fields (w α i) f)‖ := hhn
      _ ≤ ∑ i : Fin (N α), b' α i * M := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hm (w α i) (hmem α i)) (le_max_right _ _))
      _ = (∑ i : Fin (N α), b' α i) * M := (Finset.sum_mul _ _ _).symm
      _ ≤ D * M := mul_le_mul_of_nonneg_right (by
        have hh := Finset.single_le_sum (s := Finset.univ)
          (f := fun β : MultiIndex n k => ∑ i : Fin (N β), b' β i)
          (fun β _ => Finset.sum_nonneg (fun i _ => le_max_right _ _)) (Finset.mem_univ α)
        dsimp [D]; linarith) hM
  choose hCoord hnorm using hcLp
  obtain ⟨u, hu, hn⟩ := hSob f (hf.mono hsub) hCoord (D * M) (mul_nonneg hD.le hM) hnorm
  exact ⟨u, hu, hn.trans_eq (by ring)⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue.RightWordSobolev

end

end

section

noncomputable section
open MeasureTheory
open scoped Classical NumberField BigOperators
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue.GroupChartSobolev
open KPContLocalNorm KPContActualSphericalRightFieldIdentification

private theorem rightWord_eq_directional {n b : ℕ}
    (fields : Fin b → Space n → Space n) (w : List (Fin b)) (f : Space n → ℂ) :
    KPContRightJets.rightWord fields w f = RightFrame.PullbackWords.directionalWord fields w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [KPContRightJets.rightWord, RightFrame.PullbackWords.directionalWord, ih]

theorem exists_actual_group_chart_word_sobolev_bound
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
    {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
    {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
    {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
    (chart : GroupChart F ζ hζ U R P H) (A : LocalBall (groupDimension F))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chart.T.carrier) (k : ℕ) :
    ∃ S : Finset (List (Fin (groupDimension F))), (∀ w ∈ S, w.length ≤ k) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : KPSmoothLocalQuotientCharts.ActualCover F ζ hζ → ℂ,
        ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (chart.groupLift x)) chart.T.carrier →
        ∀ hLp : ∀ w ∈ S, MemLp (fun x => actualRightWord F ζ hζ w f (chart.groupLift x))
          2 (volume.restrict A.carrier),
        ∀ M : ℝ, 0 ≤ M →
        (∀ w (hw : w ∈ S),
          ‖(hLp w hw).toLp (fun x => actualRightWord F ζ hζ w f (chart.groupLift x))‖ ≤ M) →
        ∃ u : IntegerSobolev A k,
          (fun x => f (chart.groupLift x)) =ᵐ[volume.restrict A.carrier]
            (fun x => u.derivatives (⟨fun _ => 0, by simp⟩ : MultiIndex (groupDimension F) k) x) ∧
          u.sobolevNorm ≤ C * M := by
  obtain ⟨S, hS, C, hC, hb⟩ := RightWordSobolev.exists_finite_frame_word_sobolev_bound
    chart.T.carrier Metric.isOpen_ball chart.fields chart.fields_smooth_actual
    (KPSpatialExponentialPullback.group_chart_fields_basis chart) A hA
  refine ⟨S, hS, C, hC, ?_⟩
  intro f hf hLp M hM hm
  have heq (w : List (Fin (groupDimension F))) :
      (fun x => actualRightWord F ζ hζ w f (chart.groupLift x)) =ᵐ[volume.restrict A.carrier]
        RightFrame.PullbackWords.directionalWord chart.fields w (fun x => f (chart.groupLift x)) := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
    have hxT := hA (Metric.ball_subset_closedBall hx)
    exact (chart.identification.right_iteration f hf w x hxT).trans
      (congrFun (rightWord_eq_directional chart.fields w _) x)
  have hd (w : List (Fin (groupDimension F))) (hw : w ∈ S) :
      MemLp (RightFrame.PullbackWords.directionalWord chart.fields w (fun x => f (chart.groupLift x)))
        2 (volume.restrict A.carrier) := (hLp w hw).ae_eq (heq w)
  apply hb (fun x => f (chart.groupLift x)) hf hd M hM
  intro w hw
  have he : (hd w hw).toLp (RightFrame.PullbackWords.directionalWord chart.fields w
      (fun x => f (chart.groupLift x))) =
        (hLp w hw).toLp (fun x => actualRightWord F ζ hζ w f (chart.groupLift x)) := by
    apply Lp.ext
    exact (hd w hw).coeFn_toLp.trans ((heq w).symm.trans (hLp w hw).coeFn_toLp.symm)
  rw [he]
  exact hm w hw

end DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.NativeWordInverse.ActualInverseValue.GroupChartSobolev

end

end
