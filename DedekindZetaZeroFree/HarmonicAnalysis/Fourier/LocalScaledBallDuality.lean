module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.LocalBallMasses
public import DedekindZetaZeroFree.Metaplectic.Weil.QuadraticFourierOperatorsAndPhases

@[expose] public section

noncomputable section

open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

local instance scaledBallCompletionMeasurable (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSpace (v.adicCompletion F) := borel _

local instance scaledBallCompletionBorel (v : HeightOneSpectrum (𝓞 F)) :
    BorelSpace (v.adicCompletion F) := ⟨rfl⟩

def finiteCompletionUnitOrder (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) : ℤ :=
  -WithZero.log (Valued.v (b : v.adicCompletion F))

theorem finiteCompletionUnitOrder_valuation (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) :
    Valued.v (b : v.adicCompletion F) =
      WithZero.exp (-finiteCompletionUnitOrder F v b) := by
  simpa [finiteCompletionUnitOrder] using
    (WithZero.exp_log (Valued.v.ne_zero_iff.mpr b.ne_zero)).symm

theorem finiteCompletionUnitOrder_norm (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) :
    ‖(b : v.adicCompletion F)‖ =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-finiteCompletionUnitOrder F v b) := by
  rw [FinitePlace.norm_def, finiteCompletionUnitOrder_valuation,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  simp

def localScaledBallDual (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) (m : ℤ) : AddSubgroup (v.adicCompletion F) :=
  (localFiniteAnnihilator F v (finiteCompletionBall F v m)).comap
    (AddMonoidHom.mulLeft (b : v.adicCompletion F))

@[simp] theorem mem_localScaledBallDual (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) (m : ℤ) (x : v.adicCompletion F) :
    x ∈ localScaledBallDual F v b m ↔
      (b : v.adicCompletion F) * x ∈
        localFiniteAnnihilator F v (finiteCompletionBall F v m) := Iff.rfl

theorem localScaledBallDual_eq_finiteCompletionBall
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    localScaledBallDual F v b m =
      finiteCompletionBall F v
        (-m - (localDifferentExponent F v : ℤ) - finiteCompletionUnitOrder F v b) := by
  ext x
  simp only [mem_localScaledBallDual, localFiniteAnnihilator_finiteCompletionBall,
    mem_finiteCompletionBall, map_mul, finiteCompletionUnitOrder_valuation]
  have he : WithZero.exp (-(-m - ↑(localDifferentExponent F v))) =
      WithZero.exp (-finiteCompletionUnitOrder F v b) *
        WithZero.exp (-(-m - ↑(localDifferentExponent F v) - finiteCompletionUnitOrder F v b)) := by
    rw [← WithZero.exp_add]
    congr 1
    omega
  rw [he]
  exact mul_le_mul_iff_of_pos_left WithZero.exp_pos

theorem localScaledBallDual_map_mul_eq_annihilator
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    (localScaledBallDual F v b m).map
        (AddMonoidHom.mulLeft (b : v.adicCompletion F)) =
      localFiniteAnnihilator F v (finiteCompletionBall F v m) := by
  apply AddSubgroup.map_comap_eq_self
  intro x hx
  exact ⟨(↑b⁻¹ : v.adicCompletion F) * x, by simp [mul_assoc]⟩

theorem localFiniteAnnihilator_map_localScaledBallDual
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    localFiniteAnnihilator F v
        ((localScaledBallDual F v b m).map
          (AddMonoidHom.mulLeft (b : v.adicCompletion F))) =
      finiteCompletionBall F v m := by
  rw [localScaledBallDual_map_mul_eq_annihilator,
    localFiniteAnnihilator_localFiniteAnnihilator_finiteCompletionBall]

theorem localScaledBallDual_masses_pos_finite
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    0 < (localNormalizedHaar F v
        (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal ∧
    0 < (localNormalizedHaar F v
        (localScaledBallDual F v b m : Set (v.adicCompletion F))).toReal ∧
    localNormalizedHaar F v
        (finiteCompletionBall F v m : Set (v.adicCompletion F)) < ⊤ ∧
    localNormalizedHaar F v
        (localScaledBallDual F v b m : Set (v.adicCompletion F)) < ⊤ := by
  rw [localScaledBallDual_eq_finiteCompletionBall]
  simp only [localNormalizedHaar_finiteCompletionBall,
    ENNReal.toReal_ofReal (localBallMass_pos F v _).le]
  exact ⟨localBallMass_pos F v _, localBallMass_pos F v _,
    ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

theorem localScaledBallDual_mass_product
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ) :
    (localNormalizedHaar F v
        (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal *
      (localNormalizedHaar F v
        (localScaledBallDual F v b m : Set (v.adicCompletion F))).toReal =
      ‖(b : v.adicCompletion F)‖⁻¹ := by
  rw [localScaledBallDual_eq_finiteCompletionBall,
    localNormalizedHaar_finiteCompletionBall_toReal,
    localNormalizedHaar_finiteCompletionBall_toReal, finiteCompletionUnitOrder_norm]
  have hQ : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (show 0 < Ideal.absNorm v.asIdeal from by
      have := finiteCompletion_residueCard_gt_one F v; omega)
  rw [localBallMass, localBallMass, ← Real.rpow_add hQ,
    ← Real.rpow_intCast, ← Real.rpow_neg hQ.le]
  congr 1
  push_cast
  ring

abbrev localScaledBallDualQuotient (v : HeightOneSpectrum (𝓞 F))
    (b : (v.adicCompletion F)ˣ) (m : ℤ) :=
  localScaledBallDual F v b m ⧸
    (finiteCompletionBall F v m).comap (localScaledBallDual F v b m).subtype

theorem finite_localScaledBallDualQuotient
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) :
    Finite (localScaledBallDualQuotient F v b m) := by
  unfold localScaledBallDualQuotient
  rw [localScaledBallDual_eq_finiteCompletionBall]
  apply finite_finiteCompletionBallQuotient
  apply (finiteCompletionBall_le_iff F v _ m).mp
  simpa only [localScaledBallDual_eq_finiteCompletionBall] using hHL

theorem natCard_localScaledBallDualQuotient
    (v : HeightOneSpectrum (𝓞 F)) (b : (v.adicCompletion F)ˣ) (m : ℤ)
    (hHL : finiteCompletionBall F v m ≤ localScaledBallDual F v b m) :
    (Nat.card (localScaledBallDualQuotient F v b m) : ℝ) =
      (localNormalizedHaar F v
        (localScaledBallDual F v b m : Set (v.adicCompletion F))).toReal /
      (localNormalizedHaar F v
        (finiteCompletionBall F v m : Set (v.adicCompletion F))).toReal := by
  letI := finite_localScaledBallDualQuotient F v b m hHL
  letI := Fintype.ofFinite (localScaledBallDualQuotient F v b m)
  let r : localScaledBallDualQuotient F v b m → localScaledBallDual F v b m :=
    Quotient.out
  let C : localScaledBallDualQuotient F v b m → Set (v.adicCompletion F) :=
    fun i => {x | x - (r i : v.adicCompletion F) ∈ finiteCompletionBall F v m}
  have hr (i) : QuotientAddGroup.mk (r i) = i := Quotient.out_eq _
  have hdis : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hs : (r i : v.adicCompletion F) - r j ∈ finiteCompletionBall F v m := by
      convert (finiteCompletionBall F v m).sub_mem hj hi using 1 <;> abel
    have he : (QuotientAddGroup.mk (r i) : localScaledBallDualQuotient F v b m) =
        QuotientAddGroup.mk (r j) := QuotientAddGroup.eq_iff_sub_mem.mpr hs
    rw [hr, hr] at he
    exact hij he
  have hunion : (localScaledBallDual F v b m : Set (v.adicCompletion F)) = ⋃ i, C i := by
    ext x
    constructor
    · intro hx
      let y : localScaledBallDual F v b m := ⟨x, hx⟩
      let i : localScaledBallDualQuotient F v b m := QuotientAddGroup.mk y
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have he : (QuotientAddGroup.mk y : localScaledBallDualQuotient F v b m) =
          QuotientAddGroup.mk (r i) := (hr i).symm
      exact QuotientAddGroup.eq_iff_sub_mem.mp he
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have := (localScaledBallDual F v b m).add_mem (hHL hi) (r i).property
      simpa only [sub_add_cancel, SetLike.mem_coe] using this
  have hmeasure : localNormalizedHaar F v
      (localScaledBallDual F v b m : Set (v.adicCompletion F)) =
      (Nat.card (localScaledBallDualQuotient F v b m) : ENNReal) *
        localNormalizedHaar F v (finiteCompletionBall F v m : Set (v.adicCompletion F)) := by
    rw [hunion, measure_iUnion hdis]
    · simp only [C, localNormalizedHaar_finiteCompletionBall_coset]
      rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← Nat.card_eq_fintype_card, localNormalizedHaar_finiteCompletionBall]
    · intro i
      exact (isOpen_finiteCompletionBall_coset F v (r i) m).measurableSet
  have hreal := congrArg ENNReal.toReal hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  exact (eq_div_iff (ne_of_gt (localScaledBallDual_masses_pos_finite F v b m).1)).mpr
    hreal.symm

end DedekindZetaZeroFree

end
