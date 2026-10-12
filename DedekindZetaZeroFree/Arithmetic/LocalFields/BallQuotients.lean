module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LocalBallsAndCosetIndicators

@[expose] public section

noncomputable section

open scoped NumberField Classical WithZero
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

variable (F : Type) [Field F] [NumberField F]

theorem finiteCompletionBall_zero (v : HeightOneSpectrum (𝓞 F)) :
    finiteCompletionBall F v 0 =
      (v.adicCompletionIntegers F).toSubring.toAddSubgroup := by
  ext x
  simp [finiteCompletionBall, HeightOneSpectrum.adicCompletionIntegers,
    Valuation.mem_valuationSubring_iff]

theorem finiteCompletion_residueCard_gt_one (v : HeightOneSpectrum (𝓞 F)) :
    1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 :=
    Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 :=
    Ideal.absNorm_eq_one_iff.not.mpr v.isPrime.ne_top
  omega

theorem finiteCompletionBall_le_iff (v : HeightOneSpectrum (𝓞 F)) (m n : ℤ) :
    finiteCompletionBall F v n ≤ finiteCompletionBall F v m ↔ m ≤ n := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-n))
    have hle := h (show x ∈ finiteCompletionBall F v n by simp [hx])
    simpa [hx] using hle
  · intro h x hx
    change Valued.v x ≤ WithZero.exp (-n) at hx
    exact hx.trans (by simpa using h)

theorem isCompact_finiteCompletionBall (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    IsCompact (finiteCompletionBall F v n : Set (v.adicCompletion F)) := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-n))
  have heq : (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
      Metric.closedBall 0 ‖x‖ := by
    ext y
    simp [mem_finiteCompletionBall, ← hx, Valued.toNormedField.norm_le_iff]
  rw [heq]
  exact isCompact_closedBall 0 ‖x‖

theorem isOpen_finiteCompletionBall (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    IsOpen (finiteCompletionBall F v n : Set (v.adicCompletion F)) := by
  obtain ⟨x, hx⟩ := v.valuedAdicCompletion_surjective F (WithZero.exp (-n))
  have hx0 : x ≠ 0 := by intro h; exact WithZero.exp_ne_zero (hx.symm.trans (by simp [h]))
  have heq : (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
      {y | Valued.v.restrict y ≤ Valued.v.restrict x} := by
    ext y
    simp [mem_finiteCompletionBall, Valuation.restrict_le_iff, hx]
  rw [heq]
  exact Valued.isOpen_closedBall _ (by simpa using hx0)

theorem isCompact_finiteCompletionBall_coset (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (n : ℤ) :
    IsCompact {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v n} := by
  have heq : {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v n} =
      (fun x : v.adicCompletion F => b + x) '' (finiteCompletionBall F v n) := by
    ext x
    constructor
    · intro h; exact ⟨x - b, h, by simp⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [heq]
  exact (isCompact_finiteCompletionBall F v n).image (by fun_prop)

theorem isOpen_finiteCompletionBall_coset (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) (n : ℤ) :
    IsOpen {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v n} := by
  exact (isOpen_finiteCompletionBall F v n).preimage (by fun_prop)

theorem finiteCompletionBall_hasBasis_nhds (v : HeightOneSpectrum (𝓞 F))
    (b : v.adicCompletion F) :
    (nhds b).HasBasis (fun _ : ℤ => True)
      (fun n => {x : v.adicCompletion F | x - b ∈ finiteCompletionBall F v n}) := by
  rw [Filter.hasBasis_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp hs
    let g : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
    have hg : g ≠ 0 := by simp [g]
    refine ⟨1 - WithZero.log g, trivial, fun x hx => hγ ?_⟩
    change Valued.v.restrict (x - b) < γ.val
    rw [Valuation.restrict_lt_iff_lt_embedding]
    change Valued.v (x - b) ≤ WithZero.exp (-(1 - WithZero.log g)) at hx
    apply lt_of_le_of_lt hx
    change WithZero.exp (-(1 - WithZero.log g)) < g
    nth_rw 2 [← WithZero.exp_log hg]
    rw [WithZero.exp_lt_exp]
    omega
  · rintro ⟨n, _, hn⟩
    apply Filter.mem_of_superset
      ((isOpen_finiteCompletionBall_coset F v b n).mem_nhds (by simp)) hn

theorem iUnion_finiteCompletionBall_neg_nat (v : HeightOneSpectrum (𝓞 F)) :
    (⋃ k : ℕ, (finiteCompletionBall F v (-(k : ℤ)) :
      Set (v.adicCompletion F))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  refine Set.mem_iUnion.mpr ⟨(WithZero.log (Valued.v x)).toNat, ?_⟩
  change Valued.v x ≤ WithZero.exp (-(-((WithZero.log (Valued.v x)).toNat : ℤ)))
  apply WithZero.le_exp_of_log_le
  simpa using Int.le_toNat (WithZero.log (Valued.v x))

theorem exists_finiteCompletionUniformizer (v : HeightOneSpectrum (𝓞 F)) :
    ∃ π : v.adicCompletion F, Valued.v π = WithZero.exp (-1 : ℤ) := by
  exact v.valuedAdicCompletion_surjective F (WithZero.exp (-1 : ℤ))

def finiteCompletionUniformizer (v : HeightOneSpectrum (𝓞 F)) :
    v.adicCompletion F :=
  Classical.choose (exists_finiteCompletionUniformizer F v)

theorem finiteCompletionUniformizer_valuation (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (finiteCompletionUniformizer F v) = WithZero.exp (-1 : ℤ) := by
  exact Classical.choose_spec (exists_finiteCompletionUniformizer F v)

theorem finiteCompletionUniformizer_ne_zero (v : HeightOneSpectrum (𝓞 F)) :
    finiteCompletionUniformizer F v ≠ 0 := by
  intro h
  have hv := finiteCompletionUniformizer_valuation F v
  exact WithZero.exp_ne_zero (hv.symm.trans (by simp [h]))

theorem finiteCompletionBall_eq_uniformizer_image (v : HeightOneSpectrum (𝓞 F))
    (π : v.adicCompletion F) (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) (n : ℤ) :
    (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
      (fun a : v.adicCompletion F => π ^ n * a) ''
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hπ0 : π ≠ 0 := by
    intro h
    exact WithZero.exp_ne_zero (hπ.symm.trans (by simp [h]))
  have hvn : Valued.v (π ^ n) = WithZero.exp (-n) := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  ext x
  constructor
  · intro hx
    refine ⟨(π ^ n)⁻¹ * x, ?_, by simp [zpow_ne_zero n hπ0]⟩
    change Valued.v ((π ^ n)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hvn]
    exact (inv_mul_le_one₀ WithZero.exp_pos).mpr hx
  · rintro ⟨a, ha, rfl⟩
    change Valued.v (π ^ n * a) ≤ WithZero.exp (-n)
    rw [map_mul, hvn]
    change Valued.v a ≤ 1 at ha
    simpa using mul_le_mul_right ha (WithZero.exp (-n))

def finiteCompletionBallSubgroup (v : HeightOneSpectrum (𝓞 F)) (m n : ℤ) :
    AddSubgroup (finiteCompletionBall F v m) :=
  (finiteCompletionBall F v n).comap (finiteCompletionBall F v m).subtype

abbrev finiteCompletionBallQuotient (v : HeightOneSpectrum (𝓞 F)) (m n : ℤ) :=
  (finiteCompletionBall F v m) ⧸ finiteCompletionBallSubgroup F v m n

theorem finiteCompletionUniformizer_mul_mem_ball (v : HeightOneSpectrum (𝓞 F))
    (n : ℤ) (a : Valued.integer (v.adicCompletion F)) :
    finiteCompletionUniformizer F v ^ n * (a : v.adicCompletion F) ∈
      finiteCompletionBall F v n := by
  rw [← SetLike.mem_coe, finiteCompletionBall_eq_uniformizer_image F v
    _ (finiteCompletionUniformizer_valuation F v) n]
  exact ⟨a, a.property, rfl⟩

 theorem ballIntegerScale_mem (v : HeightOneSpectrum (𝓞 F)) (n : ℤ)
    (x : finiteCompletionBall F v n) :
    (finiteCompletionUniformizer F v ^ n)⁻¹ * (x : v.adicCompletion F) ∈
      Valued.integer (v.adicCompletion F) := by
  obtain ⟨a, ha, he⟩ := (Set.ext_iff.mp
    (finiteCompletionBall_eq_uniformizer_image F v _
      (finiteCompletionUniformizer_valuation F v) n) x).mp x.property
  rw [← he]
  simpa [zpow_ne_zero n (finiteCompletionUniformizer_ne_zero F v)] using (show a ∈ Valued.integer (v.adicCompletion F) from ha)

 def ballIntegerScale (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    finiteCompletionBall F v n ≃+ Valued.integer (v.adicCompletion F) where
  toFun x := ⟨(finiteCompletionUniformizer F v ^ n)⁻¹ * x, ballIntegerScale_mem F v n x⟩
  invFun a := ⟨finiteCompletionUniformizer F v ^ n * a,
    finiteCompletionUniformizer_mul_mem_ball F v n a⟩
  left_inv x := by ext; simp [zpow_ne_zero n (finiteCompletionUniformizer_ne_zero F v)]
  right_inv a := by ext; simp [zpow_ne_zero n (finiteCompletionUniformizer_ne_zero F v)]
  map_add' x y := by ext; simp [mul_add]

 def ballResidueMap (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    finiteCompletionBall F v n →+ IsLocalRing.ResidueField
      (Valued.integer (v.adicCompletion F)) :=
  (IsLocalRing.residue _).toAddMonoidHom.comp (ballIntegerScale F v n).toAddMonoidHom

 theorem ballResidueMap_surjective (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    Function.Surjective (ballResidueMap F v n) :=
  IsLocalRing.residue_surjective.comp (ballIntegerScale F v n).surjective

private theorem exp_le_neg_one_iff (g : ℤᵐ⁰) :
    g ≤ WithZero.exp (-1 : ℤ) ↔ g < 1 := by
  induction g using WithZero.expRecOn with
  | zero => simp
  | exp a => simp only [WithZero.exp_le_exp, WithZero.exp_lt_one_iff]; omega

 theorem ballResidueMap_ker (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    (ballResidueMap F v n).ker = finiteCompletionBallSubgroup F v n (n + 1) := by
  ext x
  change IsLocalRing.residue _ (ballIntegerScale F v n x) = 0 ↔
    Valued.v (x : v.adicCompletion F) ≤ WithZero.exp (-(n + 1))
  have hz : ∀ a : Valued.integer (v.adicCompletion F),
      IsLocalRing.residue _ a = 0 ↔ a ∈ IsLocalRing.maximalIdeal _ := by
    intro a
    change Ideal.Quotient.mk _ a = 0 ↔ _
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hz]
  change (ballIntegerScale F v n x) ∈ IsLocalRing.maximalIdeal
    (Valued.v.valuationSubring) ↔ _
  rw [Valuation.mem_maximalIdeal_iff]
  change Valued.v ((finiteCompletionUniformizer F v ^ n)⁻¹ *
    (x : v.adicCompletion F)) < 1 ↔ _
  rw [map_mul, map_inv₀, map_zpow₀, finiteCompletionUniformizer_valuation,
    ← WithZero.exp_zsmul]
  simp only [zsmul_eq_mul, mul_neg, mul_one]
  rw [← exp_le_neg_one_iff]
  rw [inv_mul_le_iff₀ WithZero.exp_pos]
  rw [← WithZero.exp_add]
  simp only [neg_add]
  rfl

def finiteCompletionBallResidueEquiv (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    finiteCompletionBallQuotient F v n (n + 1) ≃+ (𝓞 F ⧸ v.asIdeal) :=
  ((QuotientAddGroup.quotientAddEquivOfEq (ballResidueMap_ker F v n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (ballResidueMap F v n)
      (ballResidueMap_surjective F v n))).trans
    (GlobalClassFieldTheory.ClassFieldAxiom.ringOfIntegersQuotientEquivAdicResidueField
      v).symm.toAddEquiv

theorem finite_finiteCompletionBallQuotient_succ (v : HeightOneSpectrum (𝓞 F))
    (n : ℤ) : Finite (finiteCompletionBallQuotient F v n (n + 1)) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv (𝓞 F ⧸ v.asIdeal) (finiteCompletionBallResidueEquiv F v n).symm.toEquiv

theorem natCard_finiteCompletionBallQuotient_succ (v : HeightOneSpectrum (𝓞 F))
    (n : ℤ) :
    Nat.card (finiteCompletionBallQuotient F v n (n + 1)) =
      Ideal.absNorm v.asIdeal := by
  exact Nat.card_congr (finiteCompletionBallResidueEquiv F v n).toEquiv

theorem finiteCompletionBall_disjoint_coset_decomposition
    (v : HeightOneSpectrum (𝓞 F)) (n : ℤ) :
    ∃ r : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletion F,
      (∀ i, r i ∈ finiteCompletionBall F v n) ∧
      (∀ i j, i ≠ j → Disjoint
        {x : v.adicCompletion F | x - r i ∈ finiteCompletionBall F v (n + 1)}
        {x : v.adicCompletion F | x - r j ∈ finiteCompletionBall F v (n + 1)}) ∧
      (finiteCompletionBall F v n : Set (v.adicCompletion F)) =
        ⋃ i, {x : v.adicCompletion F | x - r i ∈ finiteCompletionBall F v (n + 1)} := by
  letI := finite_finiteCompletionBallQuotient_succ F v n
  letI := Fintype.ofFinite (finiteCompletionBallQuotient F v n (n + 1))
  let e : finiteCompletionBallQuotient F v n (n + 1) ≃ Fin (Ideal.absNorm v.asIdeal) :=
    Fintype.equivFinOfCardEq (by
      rw [← Nat.card_eq_fintype_card, natCard_finiteCompletionBallQuotient_succ F v n])
  let a : Fin (Ideal.absNorm v.asIdeal) → finiteCompletionBall F v n :=
    fun i => Quotient.out (e.symm i)
  have ha (i) : QuotientAddGroup.mk (a i) = e.symm i := Quotient.out_eq _
  refine ⟨fun i => a i, fun i => (a i).property, ?_, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hi hj
    have hsub : (a i : v.adicCompletion F) - a j ∈ finiteCompletionBall F v (n + 1) := by
      convert (finiteCompletionBall F v (n + 1)).sub_mem hj hi using 1 <;> abel
    have heq : QuotientAddGroup.mk (a i) =
        (QuotientAddGroup.mk (a j) : finiteCompletionBallQuotient F v n (n + 1)) :=
      QuotientAddGroup.eq_iff_sub_mem.mpr hsub
    rw [ha, ha] at heq
    exact hij (e.symm.injective heq)
  · ext x
    constructor
    · intro hx
      let y : finiteCompletionBall F v n := ⟨x, hx⟩
      let i := e (QuotientAddGroup.mk y)
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      have heq : QuotientAddGroup.mk y =
          (QuotientAddGroup.mk (a i) : finiteCompletionBallQuotient F v n (n + 1)) := by
        rw [ha]
        exact (e.symm_apply_apply _).symm
      exact QuotientAddGroup.eq_iff_sub_mem.mp heq
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have hn : finiteCompletionBall F v (n + 1) ≤ finiteCompletionBall F v n :=
        (finiteCompletionBall_le_iff F v n (n + 1)).mpr (by omega)
      change x ∈ finiteCompletionBall F v n
      have h := (finiteCompletionBall F v n).add_mem (hn hi) (a i).property
      simpa only [sub_add_cancel] using h

theorem finite_finiteCompletionBallQuotient (v : HeightOneSpectrum (𝓞 F))
    (m n : ℤ) (hmn : m ≤ n) :
    Finite (finiteCompletionBallQuotient F v m n) := by
  letI : CompactSpace (finiteCompletionBall F v m) :=
    isCompact_iff_compactSpace.mp (isCompact_finiteCompletionBall F v m)
  exact AddSubgroup.quotient_finite_of_isOpen _
    ((isOpen_finiteCompletionBall F v n).preimage continuous_subtype_val)

end DedekindZetaZeroFree

end
