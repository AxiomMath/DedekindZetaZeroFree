module

public import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import DedekindZetaZeroFree.Arithmetic.LocalFields.DifferentDiscriminantNormalization

@[expose] public section

section

noncomputable section
open scoped Classical nonZeroDivisors WithZero Pointwise ENNReal NNReal
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.PoissonS.BallMeasureBalance

attribute [local instance] PoissonS.completionMeasurable PoissonS.completionBorel

private theorem norm_lt_one_iff_le_inv_absNorm (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (x : v.adicCompletion F) :
    ‖x‖ < 1 ↔ ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ) := by
  have hq : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  by_cases hx : x = 0
  · simp [hx, (zpow_pos hq (-1)).le]
  · have hv : Valued.v x ≠ 0 :=
      (Valuation.ne_zero_iff (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).mpr hx
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow]
    rw [← zpow_zero (v.asIdeal.absNorm : ℝ)]
    have hq1 : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    change (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log < _ ↔
      (v.asIdeal.absNorm : ℝ) ^ (Valued.v x).log ≤ _
    rw [zpow_lt_zpow_iff_right₀ hq1, zpow_le_zpow_iff_right₀ hq1]
    omega

private theorem mem_maximalIdeal_iff_norm_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) (x : v.adicCompletionIntegers F) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ↔
      ‖(x : v.adicCompletion F)‖ < 1 := by
  have h := Valuation.mem_maximalIdeal_iff (v.adicCompletion F)
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰) (a := x)
  exact h.trans Valued.toNormedField.norm_lt_one_iff.symm

 noncomputable def residueEquiv (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    (RingOfIntegers F ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
  (finitePlaceIdealResidueEquivCompletion v).trans
    (IsLocalRing.ResidueField.mapEquiv (finitePlaceCompletionIntegerRingEquiv v))

private theorem residue_card (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) =
      v.asIdeal.absNorm := by
  rw [← Nat.card_congr (residueEquiv F v).toEquiv, Ideal.absNorm_apply]
  rfl

set_option maxHeartbeats 800000 in

theorem local_ball_volume_one_step (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (hfinite : μ {x | ‖x‖ ≤ 1} ≠ ⊤) :
    (v.asIdeal.absNorm : ℝ) * μ.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-1 : ℤ)} =
      μ.real {x | ‖x‖ ≤ 1} := by
  let O := v.adicCompletionIntegers F
  let κ := IsLocalRing.ResidueField O
  letI : Finite κ := Finite.of_equiv (RingOfIntegers F ⧸ v.asIdeal)
    (residueEquiv F v).toEquiv
  letI : Fintype κ := Fintype.ofFinite κ
  let r : κ → O := fun z => (IsLocalRing.residue_surjective (R := O) z).choose
  have hr (z : κ) : IsLocalRing.residue O (r z) = z :=
    (IsLocalRing.residue_surjective (R := O) z).choose_spec
  let U : Set (v.adicCompletion F) := {x | ‖x‖ < 1}
  let a : κ → v.adicCompletion F := fun z => r z
  have hU : MeasurableSet U := by
    exact (isOpen_lt continuous_norm continuous_const).measurableSet
  have hUfin : μ U ≠ ⊤ := ne_top_of_le_ne_top hfinite
    (measure_mono (by intro x hx; exact le_of_lt (show ‖x‖ < 1 from hx)))
  have hcoset (x : v.adicCompletion F) (hx : ‖x‖ ≤ 1) (z : κ) :
      x ∈ a z +ᵥ U ↔ IsLocalRing.residue O ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ = z := by
    rw [Set.mem_vadd_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hn : ‖x - a z‖ < 1 := by
        change ‖y‖ < 1 at hy
        have heq : x - a z = y := by change a z + y = x at hxy; rw [← hxy]; abel
        simpa only [heq] using hy
      have hm : (⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z ∈
          IsLocalRing.maximalIdeal O :=
        (mem_maximalIdeal_iff_norm_lt_one F v _).mpr hn
      have heq := (IsLocalRing.residue_eq_zero_iff _).mpr hm
      rw [map_sub, hr, sub_eq_zero] at heq
      exact heq
    · intro heq
      have hm : (⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z ∈
          IsLocalRing.maximalIdeal O := by
        apply (IsLocalRing.residue_eq_zero_iff _).mp
        rw [map_sub, heq, hr, sub_self]
      have hn := (mem_maximalIdeal_iff_norm_lt_one F v
        ((⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩ : O) - r z)).mp hm
      refine ⟨x - a z, ?_, ?_⟩
      · exact hn
      · change a z + (x - a z) = x
        abel
  have hsub (z : κ) : a z +ᵥ U ⊆ {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
    change ‖a z + y‖ ≤ 1
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (norm_le_one_of_mem_adicCompletionIntegers v (r z).property) (le_of_lt hy))
  have hcover : {x : v.adicCompletion F | ‖x‖ ≤ 1} = ⋃ z : κ, a z +ᵥ U := by
    ext x
    constructor
    · intro hx
      apply Set.mem_iUnion.mpr
      exact ⟨IsLocalRing.residue O ⟨x, mem_adicCompletionIntegers_of_norm_le_one v hx⟩,
        (hcoset x hx _).mpr rfl⟩
    · intro hx
      obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
      exact hsub z hz
  have hdisj : Pairwise (fun z w : κ => Disjoint (a z +ᵥ U) (a w +ᵥ U)) := by
    intro z w hzw
    apply Set.disjoint_left.mpr
    intro x hxz hxw
    have hx := hsub z hxz
    exact hzw (((hcoset x hx z).mp hxz).symm.trans ((hcoset x hx w).mp hxw))
  have hmass : μ.real {x | ‖x‖ ≤ 1} = (Nat.card κ : ℝ) * μ.real U := by
    rw [hcover, measureReal_iUnion_fintype hdisj (fun z => hU.const_vadd (a z))
      (fun z => by simpa only [measure_vadd] using hUfin)]
    simp only [Measure.real, measure_vadd, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]
  rw [residue_card F v] at hmass
  rw [hmass]
  congr 2
  ext x
  exact (norm_lt_one_iff_le_inv_absNorm F v x).symm

private theorem smul_ball {K : Type*} [NormedField K] (d : Kˣ) :
    d • {x : K | ‖x‖ ≤ 1} = {x : K | ‖x‖ ≤ ‖(d : K)‖} := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(d : K) * y‖ ≤ ‖(d : K)‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro hx
    refine ⟨(d : K)⁻¹ * x, ?_, ?_⟩
    · change ‖(d : K)⁻¹ * x‖ ≤ 1
      rw [norm_mul, norm_inv]
      exact (inv_mul_le_iff₀ (norm_pos_iff.mpr d.ne_zero)).mpr (by simpa using hx)
    · change (d : K) * ((d : K)⁻¹ * x) = x
      rw [← mul_assoc, mul_inv_cancel₀ d.ne_zero, one_mul]

private theorem mass_scale {K : Type*} [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (d : Kˣ) :
    μ.real {x | ‖x‖ ≤ ‖(d : K)‖} = (distribHaarChar K d : ℝ) * μ.real {x | ‖x‖ ≤ 1} := by
  have hs : IsOpen {x : K | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (0 : K) (one_ne_zero : (1 : ℝ) ≠ 0))
  have h := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (DomMulAct.mk d • μ) μ hs
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ d] at h
  have hm : μ {x | ‖x‖ ≤ ‖(d : K)‖} = (distribHaarChar K d : ℝ≥0∞) * μ {x | ‖x‖ ≤ 1} := by
    simpa only [Measure.domSMul_apply, Equiv.symm_apply_apply, ENNReal.smul_def, smul_eq_mul, smul_ball] using h
  exact congrArg ENNReal.toReal hm |>.trans (by simp [Measure.real, ENNReal.toReal_mul])

theorem local_ball_volume (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure]
    (h1 : μv {x | ‖x‖ ≤ 1} = ENNReal.ofReal (PoissonS.integerVolume F v)) (k : ℤ) :
    μv.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)}
      = (v.asIdeal.absNorm : ℝ) ^ (-k) * PoissonS.integerVolume F v := by
  letI : LocallyCompactSpace (NumberField.HeightOneSpectrum.adicAbv F v).Completion :=
    AbsoluteValue.Completion.locallyCompactSpace (finitePlaceCompletionBaseMap_isometry v)
  letI : LocallyCompactSpace (v.adicCompletion F) :=
    (finitePlaceCompletionContinuousMulEquiv v).toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  let q : ℝ := v.asIdeal.absNorm
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hV : 0 ≤ PoissonS.integerVolume F v := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hreal : μv.real {x | ‖x‖ ≤ 1} = PoissonS.integerVolume F v := by
    rw [Measure.real, h1, ENNReal.toReal_ofReal hV]
  have hfinite : μv {x | ‖x‖ ≤ 1} ≠ ⊤ := by rw [h1]; exact ENNReal.ofReal_ne_top
  have hs : IsOpen {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (IsUltrametricDist.isOpen_closedBall (0 : v.adicCompletion F) (one_ne_zero : (1 : ℝ) ≠ 0))
  have hmasspos : 0 < μv.real {x | ‖x‖ ≤ 1} :=
    ENNReal.toReal_pos (hs.measure_ne_zero μv ⟨0, by simp⟩) hfinite
  obtain ⟨p, hp⟩ := v.valuation_exists_uniformizer F
  let π := FinitePlace.embedding v p
  have hnorm : ‖π‖ = q ^ (-1 : ℤ) := by
    have hqn : (v.asIdeal.absNorm : ℝ≥0) ≠ 0 := HeightOneSpectrum.absNorm_ne_zero v
    have hπ : (WithZero.exp (-1 : ℤ)) ≠ (0 : ℤᵐ⁰) := by simp
    rw [FinitePlace.norm_embedding', hp, WithZeroMulInt.toNNReal_neg_apply hqn hπ, NNReal.coe_zpow]
    rfl
  have hπ : π ≠ 0 := norm_pos_iff.mp (hnorm ▸ zpow_pos hq (-1))
  let d : (v.adicCompletion F)ˣ := Units.mk0 π hπ
  have hd : ‖(d : v.adicCompletion F)‖ = q ^ (-1 : ℤ) := hnorm
  have hscale := mass_scale μv d
  rw [hd] at hscale
  have hone := local_ball_volume_one_step F v μv hfinite
  change q * μv.real {x | ‖x‖ ≤ q ^ (-1 : ℤ)} = _ at hone
  rw [hscale] at hone
  have hc : (distribHaarChar (v.adicCompletion F) d : ℝ) = q ^ (-1 : ℤ) := by
    have he : q * (distribHaarChar (v.adicCompletion F) d : ℝ) = 1 := by nlinarith
    rw [zpow_neg_one]
    rw [← one_div]
    apply (eq_div_iff hq.ne').mpr
    simpa [mul_comm] using he
  have hdk : ‖((d ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖ = q ^ (-k) := by
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hd, ← zpow_mul]
    congr 1
    omega
  have h := mass_scale μv (d ^ k)
  rw [hdk, map_zpow, NNReal.coe_zpow, hc, ← zpow_mul, hreal] at h
  convert h using 2 <;> congr 1 <;> omega

end DedekindZetaZeroFree.PoissonS.BallMeasureBalance

end

end

section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree
namespace PoissonS

attribute [local instance] completionMeasurable completionBorel

def finiteBall (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    Set (PoissonFinite.Space F S) :=
  {x | ∀ v : S, ‖x v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)}

def ballFractionalIdeal (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    FractionalIdeal (RingOfIntegers F)⁰ F :=
  ∏ v : S, (FractionalIdeal.coeIdeal v.val.asIdeal) ^ k v

def ballArchLattice (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    Submodule ℤ (PoissonArch.Space F) :=
  Submodule.map
    (((NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearMap.restrictScalars ℤ).comp
      (NumberField.mixedEmbedding F).toIntAlgHom.toLinearMap)
    ((ballFractionalIdeal F S k : Submodule (RingOfIntegers F) F).restrictScalars ℤ)

def finiteBallVolume (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ)
    (μ : (v : S) → Measure (v.val.adicCompletion F)) : ℝ :=
  (Measure.pi μ).real (finiteBall F S k)

def ballArchCovolume (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) : ℝ :=
  ZLattice.covolume (ballArchLattice F S k) (PoissonArch.traceMeasure F)

theorem ballFractionalIdeal_ne_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    ballFractionalIdeal F S k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro v hv
  apply zpow_ne_zero
  exact FractionalIdeal.coeIdeal_ne_zero.mpr v.val.ne_bot

theorem ballArchLattice_eq (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    ballArchLattice F S k = PoissonArch.idealLattice F
      (Units.mk0 (ballFractionalIdeal F S k) (ballFractionalIdeal_ne_zero F S k)) := by
  ext y
  rw [PoissonArch.mem_idealLattice]
  change (∃ x : F, x ∈ ballFractionalIdeal F S k ∧ _ = y) ↔ _
  rfl

theorem ballArchCovolume_eq (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ) :
    ballArchCovolume F S k = Real.sqrt |(NumberField.discr F : ℝ)| *
      ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ k v := by
  rw [ballArchCovolume, ballArchLattice_eq]
  rw [← PoissonArch.covolume, PoissonArch.covolume_eq_sqrt_discr_mul_absNorm]
  congr 1
  simp [ballFractionalIdeal, map_prod, map_zpow₀, FractionalIdeal.coeIdeal_absNorm]

theorem completion_secondCountable (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : SecondCountableTopology (v.adicCompletion F) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    TopologicalSpace.SeparableSpace.of_denseRange _ (v.denseRange_algebraMap F)
  infer_instance
attribute [local instance] completion_secondCountable

theorem completion_sigmaFinite (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F)))
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ)
    (v : S) : SigmaFinite (μ v) := by
  letI : IsLocallyFiniteMeasure (μ v) :=
    isLocallyFiniteMeasure_of_vaddInvariant (v.val.adicCompletion F)
      (show IsOpen {x : v.val.adicCompletion F | ‖x‖ ≤ 1} from by
        simpa [Metric.closedBall, dist_zero_right] using
          IsUltrametricDist.isOpen_closedBall (0 : v.val.adicCompletion F) one_ne_zero)
      ⟨0, by simp⟩ (by rw [hnorm v]; exact ENNReal.ofReal_ne_top)
  infer_instance

theorem integerVolume_pos (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F)) : 0 < integerVolume F v := by
  have hqv : (0 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
    have := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (lt_trans Nat.zero_lt_one this)
  unfold integerVolume
  exact inv_pos.mpr (Real.sqrt_pos.mpr (zpow_pos hqv _))

theorem local_ball_volume (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (RingOfIntegers F))
    (μv : Measure (v.adicCompletion F)) [μv.IsAddHaarMeasure]
    (h1 : μv {x | ‖x‖ ≤ 1} = ENNReal.ofReal (integerVolume F v)) (k : ℤ) :
    μv.real {x | ‖x‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-k)}
      = (v.asIdeal.absNorm : ℝ) ^ (-k) * integerVolume F v := by
  exact BallMeasureBalance.local_ball_volume F v μv h1 k

theorem finiteBallVolume_eq_prod (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (k : (v : S) → ℤ)
    (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ) :
    finiteBallVolume F S k μ = ∏ v : S,
      (μ v).real {x | ‖x‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)} := by
  letI : ∀ v, SigmaFinite (μ v) := fun v => completion_sigmaFinite F S μ hnorm v
  unfold finiteBallVolume finiteBall
  have hset : {x : PoissonFinite.Space F S | ∀ v : S,
      ‖x v‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)} =
      Set.pi Set.univ (fun v => {x | ‖x‖ ≤ (v.val.asIdeal.absNorm : ℝ) ^ (-k v)}) := by
    ext x
    simp
  rw [hset]
  simp [Measure.real, Measure.pi_pi, ENNReal.toReal_prod]

theorem ball_measure_balance (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (RingOfIntegers F))) (hS : ContainsDifferent F S)
    (k : (v : S) → ℤ) (μ : (v : S) → Measure (v.val.adicCompletion F))
    [hμ : ∀ v, (μ v).IsAddHaarMeasure] (hnorm : LocalNormalization F S μ) :
    0 < finiteBallVolume F S k μ ∧
    0 < ballArchCovolume F S k ∧
    ballArchCovolume F S k * finiteBallVolume F S k μ = 1 ∧
    finiteBallVolume F S k μ = (ballArchCovolume F S k)⁻¹ := by
  have hqv : ∀ v : S, (0 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    intro v
    have := NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm v.val
    exact_mod_cast (lt_trans Nat.zero_lt_one this)

  have hvol : finiteBallVolume F S k μ =
      ∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ (- k v) * integerVolume F v.val) := by
    rw [finiteBallVolume_eq_prod F S k μ hnorm]
    exact Finset.prod_congr rfl (fun v _ =>
      BallMeasureBalance.local_ball_volume F v.val (μ v) (hnorm v) (k v))

  have hcov := ballArchCovolume_eq F S k

  have hprod : ∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val).sqrt
      = Real.sqrt |(NumberField.discr F : ℝ)| :=
    BallMeasureBalance.prod_sqrt_absNorm_pow_differentExponent F S hS
  have hsqrt_pos : 0 < Real.sqrt |(NumberField.discr F : ℝ)| := by
    apply Real.sqrt_pos.mpr
    exact abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero F)
  have hP_pos : 0 < ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v) :=
    Finset.prod_pos (fun v _ => zpow_pos (hqv v) _)
  have hP_ne : (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v)) ≠ 0 := ne_of_gt hP_pos
  have h1 : (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (- k v))
      = (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl (fun v _ => zpow_neg _ _)
  have h2 : (∏ v : S, integerVolume F v.val)
      = (Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ := by
    have : (∏ v : S, integerVolume F v.val)
        = (∏ v : S, ((v.val.asIdeal.absNorm : ℝ) ^ differentExponent F v.val).sqrt)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      simp only [integerVolume]
    rw [this, hprod]
  have hvol' : finiteBallVolume F S k μ =
      (∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (k v))⁻¹ *
        (Real.sqrt |(NumberField.discr F : ℝ)|)⁻¹ := by
    rw [hvol, Finset.prod_mul_distrib, h1, h2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hvol]
    exact Finset.prod_pos (fun v _ => mul_pos (zpow_pos (hqv v) _) (integerVolume_pos F v.val))
  · rw [hcov]
    exact mul_pos hsqrt_pos hP_pos
  · rw [hcov, hvol']
    field_simp
  · rw [hcov, hvol', mul_inv_rev]

end PoissonS
end DedekindZetaZeroFree

end

end
