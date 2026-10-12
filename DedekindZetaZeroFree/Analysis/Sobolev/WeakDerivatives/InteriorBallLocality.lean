module

public import DedekindZetaZeroFree.Analysis.Sobolev.WeightedCovariant.CoordinateData
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.LocalH1EnergyEstimates

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree

open MeasureTheory Topology
open scoped Classical
open KPContLocalNorm KPContLocalEnergy

private theorem interior_ball {n : ℕ} (hn : 0 < n) (Ω : TopologicalSpace.Opens (Space n))
    (x : Space n) (hx : x ∈ Ω) :
    ∃ B : LocalBall n, x ∈ B.carrier ∧ closure B.carrier ⊆ (Ω : Set (Space n)) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  refine ⟨⟨hn, x, r / 2, half_pos hr⟩, ?_, ?_⟩
  · exact Metric.mem_ball_self (half_pos hr)
  · rw [LocalBall.carrier, closure_ball _ (ne_of_gt (half_pos hr))]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hsub

private theorem compact_memLp {n : ℕ} (hn : 0 < n) (Ω : TopologicalSpace.Opens (Space n))
    (f : Space n → ℂ) (hf : Measurable f)
    (hl : ∀ B : LocalBall n, closure B.carrier ⊆ (Ω : Set (Space n)) →
      MemLp f 2 (volume.restrict B.carrier))
    (K : Set (Space n)) (hK : IsCompact K) (hKO : K ⊆ Ω) :
    MemLp f 2 (volume.restrict K) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  have hloc : LocallyIntegrableOn (fun x => ‖f x‖ ^ 2) (Ω : Set (Space n)) := by
    intro x hx
    obtain ⟨B, hxB, hBO⟩ := interior_ball hn Ω x hx
    refine ⟨B.carrier, ?_, ?_⟩
    · exact mem_nhdsWithin_of_mem_nhds (Metric.isOpen_ball.mem_nhds hxB)
    · exact (memLp_two_iff_integrable_sq_norm (hl B hBO).aestronglyMeasurable).mp (hl B hBO)
  exact hloc.integrableOn_compact_subset hKO hK

 def derivativeTest {n : ℕ} {Ω : TopologicalSpace.Opens (Space n)}
    (φ : TestFunction Ω ℂ ⊤) (j : Fin n) : TestFunction Ω ℂ ⊤ :=
  TestFunction.lineDerivCLM ℝ (EuclideanSpace.single j 1) φ

private theorem derivativeTest_eq {n : ℕ} {Ω : TopologicalSpace.Opens (Space n)}
    (φ : TestFunction Ω ℂ ⊤) (j : Fin n) :
    (fun x => derivativeTest φ j x) = KPCompactInteriorH1.coordinatePartial j (fun x => φ x) := by
  funext x
  rw [derivativeTest, TestFunction.lineDerivCLM_eq_fderivCLM,
    TestFunction.fderivCLM_apply_of_le _ (by simp)]
  rfl

private theorem test_mul_integrable {n : ℕ} (B : LocalBall n) (f : Space n → ℂ)
    (hf : MemLp f 2 (volume.restrict B.carrier)) (φ : TestFunction B.toOpens ℂ ⊤) :
    Integrable (fun x => f x * φ x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset (s := B.carrier) ?_).mp
  · exact hf.integrable_mul
      (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport)
  · intro x hx
    apply φ.tsupport_subset
    apply subset_tsupport
    intro h
    apply hx
    simp [h]

private theorem ball_IBP {n : ℕ} (B : LocalBall n) (f : Space n → ℂ)
    (g : Fin n → Space n → ℂ) (h : IntegerSobolev B 1)
    (h0 : (fun x => value h x) =ᵐ[volume.restrict B.carrier] f)
    (h1 : ∀ j, (fun x => gradient h j x) =ᵐ[volume.restrict B.carrier] g j)
    (φ : TestFunction B.toOpens ℂ ⊤) (j : Fin n) :
    (∫ x, f x * KPCompactInteriorH1.coordinatePartial j (fun x => φ x) x) =
      -(∫ x, g j x * φ x) := by
  have hw := h.weak_derivatives (firstIndex j) φ
  have hd : (firstIndex j).directions = [j] := KPContLocalEnergy.SobolevEnergyEstimates.firstIndex_directions j
  have hdeg : (firstIndex j).degree = 1 := by
    simp only [MultiIndex.degree, firstIndex, apply_ite Fin.val, Fin.val_one, Fin.val_zero]
    simp
  change (∫ x in B.carrier, value h x * coordinateDerivative (firstIndex j) (fun x => φ x) x) =
    (-1 : ℂ) ^ (firstIndex j).degree * (∫ x in B.carrier, gradient h j x * φ x) at hw
  simp only [coordinateDerivative, hd, coordinateDerivativeList, hdeg, pow_one, neg_one_mul] at hw
  have hL : (∫ x in B.carrier, f x * KPCompactInteriorH1.coordinatePartial j (fun x => φ x) x) =
      ∫ x, f x * KPCompactInteriorH1.coordinatePartial j (fun x => φ x) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [← derivativeTest_eq φ j]
    simpa only [Pi.zero_apply, mul_zero] using congrArg (fun z : ℂ => f x * z)
      ((derivativeTest φ j).zero_on_compl hx)
  have hR : (∫ x in B.carrier, g j x * φ x) = ∫ x, g j x * φ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simpa only [Pi.zero_apply, mul_zero] using congrArg (fun z : ℂ => g j x * z) (φ.zero_on_compl hx)
  rw [← hL, ← hR]
  calc
    _ = ∫ x in B.carrier, value h x * KPCompactInteriorH1.coordinatePartial j (fun x => φ x) x := by
      apply integral_congr_ae
      filter_upwards [h0] with x hx
      rw [hx]
    _ = -(∫ x in B.carrier, gradient h j x * φ x) := hw
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [h1 j] with x hx
      rw [hx]

private theorem finite_test_decomposition {n : ℕ} (hn : 0 < n)
    (Ω : TopologicalSpace.Opens (Space n)) (ψ : TestFunction Ω ℂ ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (B : ι → LocalBall n),
      (∀ i, closure (B i).carrier ⊆ (Ω : Set (Space n))) ∧
      ∃ φ : ∀ i, TestFunction (B i).toOpens ℂ ⊤,
        (fun x => ∑ i, φ i x) = fun x => ψ x := by
  let I := {B : LocalBall n // closure B.carrier ⊆ (Ω : Set (Space n))}
  have hcover : tsupport ψ ⊆ ⋃ i : I, i.val.carrier := by
    intro x hx
    obtain ⟨B, hxB, hBO⟩ := interior_ball hn Ω x (ψ.tsupport_subset hx)
    exact Set.mem_iUnion.mpr ⟨⟨B, hBO⟩, hxB⟩
  obtain ⟨S, hS⟩ := ψ.hasCompactSupport.elim_finite_subcover
    (fun i : I => i.val.carrier) (fun _ => Metric.isOpen_ball) hcover
  let ι := ↥S
  letI : Fintype ι := inferInstance
  let B : ι → LocalBall n := fun i => i.val.val
  have hcover' : tsupport ψ ⊆ ⋃ i : ι, (B i).carrier := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hS hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (Space n)) (isClosed_tsupport ψ)
    (fun i : ι => (B i).carrier) (fun _ => Metric.isOpen_ball) hcover'
  have hρdiff i : ContDiff ℝ (⊤ : ℕ∞) (fun x => (ρ i x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp (ρ i).contMDiff)
  let φ : ∀ i : ι, TestFunction (B i).toOpens ℂ ⊤ := fun i =>
    ⟨fun x => (ρ i x : ℂ) * ψ x, (hρdiff i).mul ψ.contDiff,
      ψ.hasCompactSupport.mul_left,
      (tsupport_mul_subset_left.trans (tsupport_comp_subset Complex.ofReal_zero (ρ i))).trans (hρ i)⟩
  refine ⟨ι, inferInstance, B, fun i => i.val.property, φ, ?_⟩
  funext x
  change (∑ i : ι, (ρ i x : ℂ) * ψ x) = ψ x
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  by_cases hx : x ∈ tsupport ψ
  · have hsum := ρ.sum_eq_one hx
    rw [finsum_eq_sum_of_fintype] at hsum
    simp [hsum]
  · simp [image_eq_zero_of_notMem_tsupport hx]

private theorem global_IBP {n : ℕ} (hn : 0 < n) (Ω : TopologicalSpace.Opens (Space n))
    (f : Space n → ℂ) (g : Fin n → Space n → ℂ)
    (hlocal : ∀ B : LocalBall n, closure B.carrier ⊆ (Ω : Set (Space n)) →
      ∃ h : IntegerSobolev B 1,
        (fun x => value h x) =ᵐ[volume.restrict B.carrier] f ∧
        ∀ j, (fun x => gradient h j x) =ᵐ[volume.restrict B.carrier] g j)
    (ψ : TestFunction Ω ℂ ⊤) (j : Fin n) :
    (∫ x, f x * KPCompactInteriorH1.coordinatePartial j (fun x => ψ x) x) =
      -(∫ x, g j x * ψ x) := by
  obtain ⟨ι, hι, B, hBO, φ, hsum⟩ := finite_test_decomposition hn Ω ψ
  letI : Fintype ι := hι
  have hlocal' i := hlocal (B i) (hBO i)
  choose h h0 h1 using hlocal'
  have hflp i : MemLp f 2 (volume.restrict (B i).carrier) :=
    (Lp.memLp (value (h i))).ae_eq (h0 i)
  have hglp i : MemLp (g j) 2 (volume.restrict (B i).carrier) :=
    (Lp.memLp (gradient (h i) j)).ae_eq (h1 i j)
  have hdsum : (fun x => ∑ i, KPCompactInteriorH1.coordinatePartial j (fun x => φ i x) x) =
      KPCompactInteriorH1.coordinatePartial j (fun x => ψ x) := by
    funext x
    unfold KPCompactInteriorH1.coordinatePartial
    have hd := fderiv_sum (fun i (_ : i ∈ Finset.univ) =>
      (φ i).contDiff.differentiable (by simp) |>.differentiableAt (x := x))
    have he : (∑ i, fun x => φ i x) = (fun x => ψ x) := by
      funext x
      simpa only [Finset.sum_apply] using congrFun hsum x
    rw [he] at hd
    rw [hd]
    simp
  calc
    _ = ∫ x, ∑ i, f x * KPCompactInteriorH1.coordinatePartial j (fun x => φ i x) x := by
      congr 1
      funext x
      rw [← Finset.mul_sum, congrFun hdsum x]
    _ = ∑ i, ∫ x, f x * KPCompactInteriorH1.coordinatePartial j (fun x => φ i x) x := by
      apply integral_finsetSum
      intro i hi
      rw [← derivativeTest_eq (φ i) j]
      exact test_mul_integrable (B i) f (hflp i) (derivativeTest (φ i) j)
    _ = ∑ i, -(∫ x, g j x * φ i x) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ball_IBP (B i) f g (h i) (h0 i) (h1 i) (φ i) j
    _ = -(∫ x, ∑ i, g j x * φ i x) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      rw [integral_finsetSum]
      intro i hi
      exact test_mul_integrable (B i) (g j) (hglp i) (φ i)
    _ = _ := by
      congr 1
      congr 1
      funext x
      rw [← Finset.mul_sum, congrFun hsum x]

private theorem scalar_lift_memLp {n : ℕ} (f : Space n → ℂ) (hf : Measurable f)
    (K : Set (Space n)) (hlp : MemLp f 2 (volume.restrict K)) :
    MemLp (fun x => WithLp.toLp 2 (fun _ : Fin 1 => f x)) 2 (volume.restrict K) := by
  have hm : Measurable (fun x => WithLp.toLp 2 (fun _ : Fin 1 => f x)) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℂ)).measurable.comp (measurable_pi_iff.mpr (fun _ => hf))
  apply hlp.of_le_mul hm.aestronglyMeasurable (c := 1)
  apply Filter.Eventually.of_forall
  intro x
  rw [one_mul, EuclideanSpace.norm_eq]
  simp

theorem weakFirst_of_all_interior_balls (n : ℕ) (hn : 0 < n)
    (Ω : TopologicalSpace.Opens (Space n))
    (f : Space n → ℂ) (g : Fin n → Space n → ℂ)
    (hf : Measurable f) (hg : ∀ j, Measurable (g j))
    (hlocal : ∀ B : LocalBall n, closure B.carrier ⊆ (Ω : Set (Space n)) →
      ∃ h : IntegerSobolev B 1,
        (fun x => value h x) =ᵐ[volume.restrict B.carrier] f ∧
        ∀ j, (fun x => gradient h j x) =ᵐ[volume.restrict B.carrier] g j) :
    KPCompactInteriorH1.WeakFirst Ω
      (fun x => WithLp.toLp 2 (fun _ : Fin 1 => f x))
      (fun j x => WithLp.toLp 2 (fun _ : Fin 1 => g j x)) := by
  have hflp : ∀ B : LocalBall n, closure B.carrier ⊆ (Ω : Set (Space n)) →
      MemLp f 2 (volume.restrict B.carrier) := by
    intro B hB
    obtain ⟨h, h0, h1⟩ := hlocal B hB
    exact (Lp.memLp (value h)).ae_eq h0
  have hglp : ∀ j, ∀ B : LocalBall n, closure B.carrier ⊆ (Ω : Set (Space n)) →
      MemLp (g j) 2 (volume.restrict B.carrier) := by
    intro j B hB
    obtain ⟨h, h0, h1⟩ := hlocal B hB
    exact (Lp.memLp (gradient h j)).ae_eq (h1 j)
  have hlift (f : Space n → ℂ) (hf : Measurable f)
      (hl : ∀ B : LocalBall n, closure B.carrier ⊆ (Ω : Set (Space n)) →
        MemLp f 2 (volume.restrict B.carrier)) :
      KPCompactInteriorH1.LocallyL2 Ω (fun x => WithLp.toLp 2 (fun _ : Fin 1 => f x)) := by
    constructor
    · exact ((PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℂ)).measurable.comp
        (measurable_pi_iff.mpr (fun _ => hf))).aestronglyMeasurable
    · intro K hK hKO
      exact scalar_lift_memLp f hf K (compact_memLp hn Ω f hf hl K hK hKO)
  refine ⟨hlift f hf hflp, fun j => hlift (g j) (hg j) (hglp j), ?_⟩
  intro j ψ a
  change (∫ x in (Ω : Set (Space n)), f x *
      KPCompactInteriorH1.coordinatePartial j (fun x => ψ x) x) = -(∫ x in (Ω : Set (Space n)), g j x * ψ x)
  have hL : (∫ x in (Ω : Set (Space n)), f x * KPCompactInteriorH1.coordinatePartial j (fun x => ψ x) x) =
      ∫ x, f x * KPCompactInteriorH1.coordinatePartial j (fun x => ψ x) x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [← derivativeTest_eq ψ j]
    simpa only [Pi.zero_apply, mul_zero] using congrArg (fun z : ℂ => f x * z)
      ((derivativeTest ψ j).zero_on_compl hx)
  have hR : (∫ x in (Ω : Set (Space n)), g j x * ψ x) = ∫ x, g j x * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simpa only [Pi.zero_apply, mul_zero] using congrArg (fun z : ℂ => g j x * z) (ψ.zero_on_compl hx)
  rw [hL, hR]
  exact global_IBP hn Ω f g hlocal ψ j

end DedekindZetaZeroFree

end
