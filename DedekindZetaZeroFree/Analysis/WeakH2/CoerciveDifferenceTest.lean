module

public import DedekindZetaZeroFree.Analysis.SmoothFunctions.UniformConcentricCutoffs
public import DedekindZetaZeroFree.Analysis.EllipticRegularity.DifferenceQuotientEnergy

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.WeakH2

open MeasureTheory Filter Topology KPContLocalNorm
open KPContLocalEnergy.SobolevEnergyEstimates.Raw

def WeightedFirstBound {n : ℕ} {B : LocalBall n} {cρ Cρ κ Λ : ℝ}
    (D : Coefficients B cρ Cρ κ Λ) (L : ℝ) : Prop :=
  ∀ x ∈ B.carrier, ∀ i j k : Fin n,
    ‖fderiv ℝ (fun y => D.density y * D.matrix y i j) x
      (EuclideanSpace.single k 1)‖ ≤ L

def cutoffValue {n : ℕ} {B : LocalBall n} (η : TestFunction B.toOpens ℝ ⊤)
    (q : IntegerSobolev B 1) : Space n → ℂ :=
  B.carrier.indicator (fun x => (η x : ℂ) ^ 2 * value q x)

def cutoffGradient {n : ℕ} {B : LocalBall n} (η : TestFunction B.toOpens ℝ ⊤)
    (q : IntegerSobolev B 1) (j : Fin n) : Space n → ℂ :=
  B.carrier.indicator (fun x => (η x : ℂ) ^ 2 * gradient q j x +
    2 * (η x : ℂ) * coordinateDerivativeList [j] (fun y => (η y : ℂ)) x * value q x)

namespace DifferenceTestAtoms

theorem zeroExtension_memLp {n : ℕ} {B : LocalBall n} (f : BallL2 B) :
    MemLp (zeroExtension f) 2 volume := by
  exact (memLp_indicator_iff_restrict Metric.isOpen_ball.measurableSet.nullMeasurableSet).2 (Lp.memLp f)

theorem quotient_memLp {n : ℕ} (f : Space n → ℂ) (hf : MemLp f 2 volume)
    (k : Fin n) (t : ℝ) : MemLp (differenceQuotient k t f) 2 volume := by
  exact ((hf.comp_measurePreserving (measurePreserving_add_right volume _)).sub hf).const_mul _

theorem exactIBP {n : ℕ} (f g : Space n → ℂ) (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (k : Fin n) (t : ℝ) :
    (∫ x, f x * (-differenceQuotient k (-t) g x)) =
      ∫ x, differenceQuotient k t f x * g x := by
  have hfg := hf.integrable_mul hg
  have hfgt := hf.integrable_mul
    (hg.comp_measurePreserving (measurePreserving_add_right volume ((-t) • EuclideanSpace.single k 1)))
  have hftg := (hf.comp_measurePreserving
    (measurePreserving_add_right volume (t • EuclideanSpace.single k 1))).integrable_mul hg
  change Integrable (fun x => f x * g x) volume at hfg
  change Integrable (fun x => f x * g (x + (-t) • EuclideanSpace.single k 1)) volume at hfgt
  change Integrable (fun x => f (x + t • EuclideanSpace.single k 1) * g x) volume at hftg
  have hshift : (∫ x, f x * g (x + (-t) • EuclideanSpace.single k 1)) =
      ∫ x, f (x + t • EuclideanSpace.single k 1) * g x := by
    have h := integral_add_right_eq_self
      (fun x => f x * g (x + (-t) • EuclideanSpace.single k 1))
      (t • EuclideanSpace.single k 1) (μ := volume)
    simpa only [neg_smul, add_neg_cancel_right] using h.symm
  simp only [differenceQuotient, Complex.ofReal_neg, inv_neg, neg_mul, neg_neg]
  have hleft : (∫ x, f x * ((t : ℂ)⁻¹ *
      (g (x + (-t) • EuclideanSpace.single k 1) - g x))) =
      (t : ℂ)⁻¹ * ((∫ x, f x * g (x + (-t) • EuclideanSpace.single k 1)) - ∫ x, f x * g x) := by
    simp_rw [mul_left_comm (f _) (t : ℂ)⁻¹]
    change (∫ x, (t : ℂ)⁻¹ * (f x * (g (x + (-t) • EuclideanSpace.single k 1) - g x))) = _
    rw [integral_const_mul]
    simp_rw [mul_sub]
    rw [integral_sub hfgt hfg, mul_sub]
  have hright : (∫ x, (t : ℂ)⁻¹ *
      (f (x + t • EuclideanSpace.single k 1) - f x) * g x) =
      (t : ℂ)⁻¹ * ((∫ x, f (x + t • EuclideanSpace.single k 1) * g x) - ∫ x, f x * g x) := by
    simp_rw [mul_assoc, sub_mul]
    rw [integral_const_mul, integral_sub hftg hfg]
  rw [hleft, hright, hshift]

theorem cutoffValue_memLp {n : ℕ} {B : LocalBall n}
    (η : TestFunction B.toOpens ℝ ⊤) (q : IntegerSobolev B 1) :
    MemLp (cutoffValue η q) 2 volume := by
  change MemLp (B.carrier.indicator (fun x => (η x : ℂ)^2 * KPContLocalEnergy.SobolevEnergyEstimates.Raw.value q x)) 2 volume
  apply (memLp_indicator_iff_restrict (s := B.carrier) Metric.isOpen_ball.measurableSet.nullMeasurableSet).2
  have hη : MemLp (fun x => (η x : ℂ)) ⊤ (volume.restrict B.carrier) := η.memLp_top.ofReal
  have hprod : MemLp (fun x => (η x : ℂ) * KPContLocalEnergy.SobolevEnergyEstimates.Raw.value q x) 2
      (volume.restrict B.carrier) := hη.fun_mul (Lp.memLp _)
  simpa only [pow_two, mul_assoc] using hη.fun_mul hprod

theorem cutoffValue_zero_off {n : ℕ} {B : LocalBall n}
    (η : TestFunction B.toOpens ℝ ⊤) (q : IntegerSobolev B 1) (x : Space n)
    (hx : x ∉ tsupport (fun y => η y)) : cutoffValue η q x = 0 := by
  unfold cutoffValue
  by_cases hxB : x ∈ B.carrier
  · simp [Set.indicator_of_mem hxB, image_eq_zero_of_notMem_tsupport hx]
  · simp [hxB]

theorem cutoffDifference_zero_off {n : ℕ} {B : LocalBall n}
    (η : TestFunction B.toOpens ℝ ⊤) (q : IntegerSobolev B 1)
    (k : Fin n) (t : ℝ) (x : Space n)
    (hx : x ∉ Metric.cthickening |t| (tsupport (fun y => η y))) :
    -differenceQuotient k (-t) (cutoffValue η q) x = 0 := by
  have hx0 : x ∉ tsupport (fun y => η y) := by
    intro h
    exact hx (Metric.mem_cthickening_of_dist_le x x |t| _ h (by simp))
  have hx1 : x + (-t) • EuclideanSpace.single k 1 ∉ tsupport (fun y => η y) := by
    intro h
    apply hx
    apply Metric.mem_cthickening_of_dist_le x (x + (-t) • EuclideanSpace.single k 1) |t| _ h
    simp [dist_eq_norm, norm_smul, EuclideanSpace.norm_single]
  unfold differenceQuotient
  rw [cutoffValue_zero_off η q x hx0, cutoffValue_zero_off η q _ hx1]
  simp

theorem cutoff_exactIBP {n : ℕ} (mid outer : LocalBall n)
    (η : TestFunction mid.toOpens ℝ ⊤) (q : IntegerSobolev mid 1)
    (k : Fin n) (t : ℝ)
    (f : BallL2 outer) :
    (∫ x in outer.carrier, f x * (-differenceQuotient k (-t) (cutoffValue η q) x)) =
      ∫ x in mid.carrier,
        differenceQuotient k t (zeroExtension f) x * (η x : ℂ) ^ 2 *
          KPContLocalEnergy.SobolevEnergyEstimates.Raw.value q x := by
  have hl : (∫ x in outer.carrier, f x *
      (-differenceQuotient k (-t) (cutoffValue η q) x)) =
      ∫ x, zeroExtension f x * (-differenceQuotient k (-t) (cutoffValue η q) x) := by
    calc
      _ = ∫ x in outer.carrier, zeroExtension f x *
          (-differenceQuotient k (-t) (cutoffValue η q) x) := by
        apply setIntegral_congr_fun (s := outer.carrier) Metric.isOpen_ball.measurableSet
        intro x hx
        change x ∈ outer.carrier at hx
        simp [zeroExtension, hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [zeroExtension, hx])
  rw [hl, exactIBP _ _ (zeroExtension_memLp f) (cutoffValue_memLp η q) k t]
  calc
    _ = ∫ x in mid.carrier, differenceQuotient k t (zeroExtension f) x * cutoffValue η q x := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [cutoffValue, hx])
    _ = _ := by
      apply setIntegral_congr_fun (s := mid.carrier) Metric.isOpen_ball.measurableSet
      intro x hx
      simp [cutoffValue, hx, mul_assoc]

theorem localized_weighted_quotient_memLp {n : ℕ} (mid outer : LocalBall n)
    (η : TestFunction mid.toOpens ℝ ⊤) (f : BallL2 outer) (k : Fin n) (t : ℝ) :
    MemLp (fun x => (η x : ℂ) * differenceQuotient k t (zeroExtension f) x)
      2 (volume.restrict mid.carrier) := by
  have hf := (quotient_memLp _ (zeroExtension_memLp f) k t).mono_measure
    (Measure.restrict_le_self (s := mid.carrier))
  have hη : MemLp (fun x => (η x : ℂ)) ⊤ (volume.restrict mid.carrier) := η.memLp_top.ofReal
  exact hη.fun_mul hf

theorem derivativeDifference {n : ℕ} (α : MultiIndex n 1)
    (φ : Space n → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (k : Fin n) (t : ℝ) :
    coordinateDerivative α (differenceQuotient k t φ) =
      differenceQuotient k t (coordinateDerivative α φ) := by
  have hlen : α.directions.length ≤ 1 := by
    rw [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.directions_length_h1]
    exact α.property
  obtain hnil | ⟨i, hi⟩ : α.directions = [] ∨ ∃ i, α.directions = [i] := by
    cases h : α.directions with
    | nil => exact Or.inl rfl
    | cons i l =>
      right
      have : l = [] := by simpa [h] using hlen
      exact ⟨i, by simp [this]⟩
  · simp [coordinateDerivative, hnil, coordinateDerivativeList]
  · funext x
    have hd := hφ.differentiable (by simp)
    simp only [coordinateDerivative, hi, coordinateDerivativeList, differenceQuotient]
    change (fderiv ℝ (fun y => (t : ℂ)⁻¹ * (φ (y + t • EuclideanSpace.single k 1) - φ y)) x) _ = _
    have hds : Differentiable ℝ (fun y => φ (y + t • EuclideanSpace.single k 1)) := by fun_prop
    have hdsub : DifferentiableAt ℝ (fun y => φ (y + t • EuclideanSpace.single k 1) - φ y) x :=
      (hds x).sub (hd x)
    rw [fderiv_const_mul hdsub,
      fderiv_fun_sub (hds x) (hd x),
      fderiv_comp_add_right]
    simp

theorem global_indicator_ae {n : ℕ} {B : LocalBall n}
    (K : Set (Space n)) (hKB : K ⊆ B.carrier) (f : BallL2 B) (g : Space n → ℂ)
    (hfg : ∀ᵐ x ∂volume.restrict B.carrier, f x = g x)
    (hg : ∀ x, x ∉ K → g x = 0) :
    KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K f =ᵐ[volume]
      B.carrier.indicator g := by
  filter_upwards [(ae_restrict_iff' Metric.isOpen_ball.measurableSet).1 hfg] with x hx
  by_cases hxK : x ∈ K
  · simp [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension,
      hxK, hKB hxK, hx (hKB hxK)]
  · by_cases hxB : x ∈ B.carrier
    · simp [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hxK, hxB, hg x hxK]
    · simp [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension, hxK, hxB]

private theorem derivative_support {n : ℕ} (l : List (Fin n)) (f : Space n → ℂ) :
    tsupport (coordinateDerivativeList l f) ⊆ tsupport f := by
  induction l with
  | nil => exact Set.Subset.rfl
  | cons i l ih => exact (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1)).trans ih

private theorem test_derivative_memLp {n : ℕ} {B : LocalBall n}
    (φ : TestFunction B.toOpens ℂ ⊤) (α : MultiIndex n 1) :
    MemLp (coordinateDerivative α (fun y => φ y)) 2 volume := by
  have hlen : α.directions.length ≤ 1 := by
    rw [KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.directions_length_h1]
    exact α.property
  obtain hnil | ⟨i, hi⟩ : α.directions = [] ∨ ∃ i, α.directions = [i] := by
    cases h : α.directions with
    | nil => exact Or.inl rfl
    | cons i l =>
      have : l = [] := by simpa [h] using hlen
      exact Or.inr ⟨i, by simp [this]⟩
  · simpa [coordinateDerivative, hnil, coordinateDerivativeList] using
      φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport
  · have hs : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun y => φ y)) :=
      φ.contDiff.fderiv_right (by simp)
    have hc : HasCompactSupport (fun x => fderiv ℝ (fun y => φ y) x (EuclideanSpace.single i 1)) :=
      φ.hasCompactSupport.isCompact.of_isClosed_subset isClosed_closure
        (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))
    simpa [coordinateDerivative, hi, coordinateDerivativeList] using
      (hs.continuous.clm_apply continuous_const).memLp_of_hasCompactSupport (p := 2) hc

theorem compact_difference_data {n : ℕ} (mid outer : LocalBall n)
    (v : IntegerSobolev mid 1) (K : Set (Space n)) (hK : IsCompact K)
    (hKB : K ⊆ mid.carrier)
    (hv : ∀ᵐ x ∂volume.restrict mid.carrier, x ∉ K → value v x = 0)
    (k : Fin n) (t : ℝ) :
    ∃ w : IntegerSobolev outer 1, ∀ α : MultiIndex n 1,
      ∀ᵐ x ∂volume.restrict outer.carrier, w.derivatives α x =
        -differenceQuotient k (-t)
          (KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (v.derivatives α)) x := by
  let F := fun α => KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension K (v.derivatives α)
  have hF : ∀ α, MemLp (F α) 2 volume := fun α =>
    KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension_memLp hK hKB _
  let G := fun α => fun x => -differenceQuotient k (-t) (F α) x
  have hG : ∀ α, MemLp (G α) 2 (volume.restrict outer.carrier) := fun α =>
    ((quotient_memLp _ (hF α) k (-t)).neg).mono_measure Measure.restrict_le_self
  let d := fun α => (hG α).toLp (G α)
  have hd : ∀ α, ∀ᵐ x ∂volume.restrict outer.carrier, d α x = G α x := fun α => MemLp.coeFn_toLp _
  refine ⟨⟨d, ?_⟩, hd⟩
  intro α φ
  change (∫ x in outer.carrier, d (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x) =
    (-1 : ℂ) ^ α.degree * (∫ x in outer.carrier, d α x * φ x)
  have hs (x : Space n) (hx : x ∉ outer.carrier) : φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h))
  have hds (x : Space n) (hx : x ∉ outer.carrier) : coordinateDerivative α (fun y => φ y) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset (derivative_support _ _ h)))
  have hleft : (∫ x in outer.carrier, d (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x) =
      ∫ x, G (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x := by
    calc
      _ = ∫ x in outer.carrier, G (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x := by
        apply integral_congr_ae
        filter_upwards [hd (zeroIndex n 1)] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hds x hx, mul_zero])
  have hright : (∫ x in outer.carrier, d α x * φ x) = ∫ x, G α x * φ x := by
    calc
      _ = ∫ x in outer.carrier, G α x * φ x := by
        apply integral_congr_ae
        filter_upwards [hd α] with x hx
        rw [hx]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hs x hx, mul_zero])
  rw [hleft, hright]
  have hφ := φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport (μ := volume)
  have he := KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension_weak_identity
    mid v K hK hKB hv α (differenceQuotient k t (fun y => φ y)) (by
      unfold differenceQuotient
      apply ContDiff.mul contDiff_const
      apply ContDiff.sub
      · exact φ.contDiff.comp (contDiff_id.add contDiff_const)
      · exact φ.contDiff)
  rw [derivativeDifference α _ φ.contDiff k t] at he
  have hl := exactIBP (coordinateDerivative α (fun y => φ y)) (F (zeroIndex n 1))
    (test_derivative_memLp φ α) (hF _) k t
  have hr := exactIBP (fun y => φ y) (F α) hφ (hF α) k t
  simp_rw [mul_comm (coordinateDerivative α (fun y => φ y) _) _,
    mul_comm (differenceQuotient k t (coordinateDerivative α (fun y => φ y)) _) _] at hl
  simp_rw [mul_comm (φ _) _, mul_comm (differenceQuotient k t (fun y => φ y) _) _] at hr
  change (∫ x, G (zeroIndex n 1) x * coordinateDerivative α (fun y => φ y) x) = _ at hl
  change (∫ x, G α x * φ x) = _ at hr
  rw [hl, hr]
  exact he
open KPContLocalEnergy.SobolevEnergyEstimates KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation

theorem construct_difference_test {n : ℕ} (mid outer : LocalBall n)
    (hsub : mid.carrier ⊆ outer.carrier) (η : TestFunction mid.toOpens ℝ ⊤)
    (q : IntegerSobolev mid 1) (k : Fin n) (t : ℝ) (ht : t ≠ 0) :
    ∃ w : IntegerSobolev outer 1,
      (∀ᵐ x ∂volume.restrict outer.carrier,
        KPContLocalEnergy.SobolevEnergyEstimates.Raw.value w x = -differenceQuotient k (-t) (cutoffValue η q) x) ∧
      (∀ j : Fin n, ∀ᵐ x ∂volume.restrict outer.carrier,
        KPContLocalEnergy.SobolevEnergyEstimates.Raw.gradient w j x = -differenceQuotient k (-t) (cutoffGradient η q j) x) := by
  obtain ⟨v, hv, hgv⟩ := KPContLocalEnergy.SobolevEnergyEstimates.multiply_smooth_compact mid η q
  let S := tsupport (fun x => η x)
  have hS : IsCompact S := η.hasCompactSupport
  have hSB : S ⊆ mid.carrier := η.tsupport_subset
  have hvs : ∀ᵐ x ∂volume.restrict mid.carrier, x ∉ S → value v x = 0 := by
    filter_upwards [hv] with x hx hnot
    rw [hx, image_eq_zero_of_notMem_tsupport hnot]
    simp
  have hvalue : KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension S (value v)
      =ᵐ[volume] cutoffValue η q := by
    exact DifferenceTestAtoms.global_indicator_ae S hSB _ _ hv (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp)
  have hgradient (j : Fin n) :
      KPContLocalEnergy.SobolevEnergyEstimates.CompactApproximation.compactZeroExtension S (gradient v j)
        =ᵐ[volume] cutoffGradient η q j := by
    exact DifferenceTestAtoms.global_indicator_ae S hSB _ _ (hgv j) (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp)
  have hdq (f g : Space n → ℂ) (hfg : f =ᵐ[volume] g) :
      differenceQuotient k (-t) f =ᵐ[volume] differenceQuotient k (-t) g := by
    filter_upwards [hfg, (measurePreserving_add_right volume
      ((-t) • EuclideanSpace.single k 1)).quasiMeasurePreserving.ae_eq_comp hfg] with x hx hxs
    change f (x + (-t) • EuclideanSpace.single k 1) = g (x + (-t) • EuclideanSpace.single k 1) at hxs
    simp only [differenceQuotient, hx, hxs]
  obtain ⟨w, hw⟩ := DifferenceTestAtoms.compact_difference_data mid outer v S hS hSB hvs k t
  refine ⟨w, ?_, ?_⟩
  · filter_upwards [hw (zeroIndex n 1), (hdq _ _ hvalue).filter_mono
      (ae_mono Measure.restrict_le_self)] with x hx hy
    exact hx.trans (congrArg Neg.neg hy)
  · intro j
    filter_upwards [hw (firstIndex j), (hdq _ _ (hgradient j)).filter_mono
      (ae_mono Measure.restrict_le_self)] with x hx hy
    exact hx.trans (congrArg Neg.neg hy)

theorem difference_energy_absorption {a A B E N : ℝ}
    (ha : 0 < a) (hE : 0 ≤ E) (henergy : a * E ≤ A * N ^ 2 + B * N * Real.sqrt E) :
    E ≤ (2 * A / a + B ^ 2 / a ^ 2) * N ^ 2 := by
  have hsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have hyoung : B * N * Real.sqrt E ≤ a / 2 * E + B ^ 2 / (2 * a) * N ^ 2 := by
    have hs := sq_nonneg (a * Real.sqrt E - B * N)
    have hm : 0 ≤ a * (a * E + B ^ 2 / a * N ^ 2 - 2 * B * N * Real.sqrt E) := by
      field_simp
      nlinarith
    have hh := (mul_nonneg_iff_of_pos_left ha).mp hm
    have heq : B ^ 2 / (2 * a) = (B ^ 2 / a) / 2 := by field_simp
    rw [heq]
    linarith
  have he : a / 2 * E ≤ (A + B ^ 2 / (2 * a)) * N ^ 2 := by
    nlinarith
  have hid : (a / 2) * ((2 * A / a + B ^ 2 / a ^ 2) * N ^ 2) =
      (A + B ^ 2 / (2 * a)) * N ^ 2 := by
    field_simp
    <;> ring
  apply (mul_le_mul_iff_right₀ (half_pos ha)).mp
  rw [hid]
  exact he

end DifferenceTestAtoms

theorem admissible_difference_test {n : ℕ} (mid outer : LocalBall n)
    (hsub : mid.carrier ⊆ outer.carrier) (η : TestFunction mid.toOpens ℝ ⊤)
    (q : IntegerSobolev mid 1) (k : Fin n) (t : ℝ) (ht : t ≠ 0)
    (hsafe : Metric.cthickening |t| (tsupport (fun x => η x)) ⊆ mid.carrier) :
    ∃ w : IntegerSobolev outer 1,
      (∀ᵐ x ∂volume.restrict outer.carrier,
        value w x = -differenceQuotient k (-t) (cutoffValue η q) x) ∧
      (∀ j : Fin n, ∀ᵐ x ∂volume.restrict outer.carrier,
        gradient w j x = -differenceQuotient k (-t) (cutoffGradient η q j) x) ∧
      (∀ᵐ x ∂volume.restrict outer.carrier,
        x ∉ Metric.cthickening |t| (tsupport (fun y => η y)) → value w x = 0) ∧
      (∃ φ : ℕ → TestFunction outer.toOpens ℂ ⊤,
        ∀ α : MultiIndex n 1,
          Tendsto (fun m => ∫ x in outer.carrier,
            ‖coordinateDerivative α (fun y => φ m y) x - w.derivatives α x‖ ^ 2)
            atTop (𝓝 0)) ∧
      (∀ f : BallL2 outer,
        (∫ x in outer.carrier, f x * value w x) =
          ∫ x in mid.carrier,
            differenceQuotient k t (zeroExtension f) x * (η x : ℂ) ^ 2 * value q x) := by
  obtain ⟨w, hwvalue, hwgradient⟩ :=
    DifferenceTestAtoms.construct_difference_test mid outer hsub η q k t ht
  have hwsupport : ∀ᵐ x ∂volume.restrict outer.carrier,
      x ∉ Metric.cthickening |t| (tsupport (fun y => η y)) → value w x = 0 := by
    filter_upwards [hwvalue] with x hx
    intro hnot
    rw [hx]
    exact DifferenceTestAtoms.cutoffDifference_zero_off η q k t x hnot
  obtain ⟨φ, hφ⟩ := KPContLocalEnergy.SobolevEnergyEstimates.approximate_compact_integerSobolev outer w
    (Metric.cthickening |t| (tsupport (fun y => η y)))
    η.hasCompactSupport.cthickening (hsafe.trans hsub) hwsupport
  refine ⟨w, hwvalue, hwgradient, hwsupport, ⟨φ, hφ⟩, ?_⟩
  intro f
  calc
    _ = ∫ x in outer.carrier, f x *
        (-differenceQuotient k (-t) (cutoffValue η q) x) := by
      apply integral_congr_ae
      filter_upwards [hwvalue] with x hx
      rw [hx]
    _ = _ := DifferenceTestAtoms.cutoff_exactIBP mid outer η q k t f

theorem weak_equation_difference_test {n : ℕ} (mid outer : LocalBall n)
    (hsub : mid.carrier ⊆ outer.carrier) (η : TestFunction mid.toOpens ℝ ⊤)
    (q : IntegerSobolev mid 1) (k : Fin n) (t : ℝ) (ht : t ≠ 0)
    (hsafe : Metric.cthickening |t| (tsupport (fun y => η y)) ⊆ mid.carrier)
    {cρ Cρ κ Λ : ℝ} (hcρ : 0 < cρ) (hκ : 0 < κ)
    (D : Coefficients outer cρ Cρ κ Λ) (z : ℂ)
    (u : IntegerSobolev outer 1) (h : BallL2 outer) (heq : WeakEquation D z u h) :
    ∃ w : IntegerSobolev outer 1,
      (∀ᵐ x ∂volume.restrict outer.carrier,
        value w x = -differenceQuotient k (-t) (cutoffValue η q) x) ∧
      (∀ j : Fin n, ∀ᵐ x ∂volume.restrict outer.carrier,
        gradient w j x = -differenceQuotient k (-t) (cutoffGradient η q j) x) ∧
      (∫ x in outer.carrier, (D.density x : ℂ) *
        ∑ i, ∑ j, (D.matrix x i j : ℂ) * gradient u j x * star (gradient w i x)) -
        z * (∫ x in outer.carrier, (D.density x : ℂ) * value u x * star (value w x)) =
          ∫ x in outer.carrier, (D.density x : ℂ) * h x * star (value w x) := by
  obtain ⟨w, hwv, hwg, _, ⟨φ, hφ⟩, _⟩ :=
    admissible_difference_test mid outer hsub η q k t ht hsafe
  exact ⟨w, hwv, hwg, KPContLocalEnergy.SobolevEnergyEstimates.weakEquation_of_test_limit outer
    cρ Cρ κ Λ hcρ hκ D z u h heq w φ hφ⟩

theorem coercive_difference_estimate (n : ℕ) (hn : 0 < n)
    (r R cρ Cρ κ Λ L M : ℝ) (hr : 0 < r) (hrR : r < R)
    (hcρ : 0 < cρ) (hκ : 0 < κ) (hL : 0 ≤ L) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (inner mid outer : LocalBall n),
      inner.center = outer.center → mid.center = outer.center →
      inner.radius = r → mid.radius = (r + R) / 2 → outer.radius = R →
      ∃ η : TestFunction mid.toOpens ℝ ⊤,
        (∀ x ∈ inner.carrier, η x = 1) ∧
        ∀ D : Coefficients outer cρ Cρ κ Λ, WeightedFirstBound D L →
          ∀ z : ℂ, ‖z‖ ≤ M → ∀ (u : IntegerSobolev outer 1) (h : BallL2 outer),
            WeakEquation D z u h → ∀ (k : Fin n) (t : ℝ),
              t ≠ 0 → |t| < (R - r) / 8 →
              (∀ j : Fin n, MemLp (fun x => (η x : ℂ) *
                differenceQuotient k t (zeroExtension (gradient u j)) x)
                2 (volume.restrict mid.carrier)) ∧
              (∑ j : Fin n, ∫ x in mid.carrier,
                ‖(η x : ℂ) * differenceQuotient k t (zeroExtension (gradient u j)) x‖ ^ 2)
                ≤ K ^ 2 * (u.sobolevNorm + ‖h‖) ^ 2 := by
  obtain ⟨G, hG, hcutoff⟩ :=
    CoerciveDifference.uniform_concentric_cutoff n r R hr hrR
  obtain ⟨A, B, hA, hB, henergy⟩ :=
    CoerciveDifference.uniform_difference_energy_inequality n hn
      r R cρ Cρ κ Λ L M G hr hrR hcρ hκ hL hM hG
  let C : ℝ := 2 * A / (cρ * κ) + B ^ 2 / (cρ * κ) ^ 2
  have ha : 0 < cρ * κ := mul_pos hcρ hκ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.sqrt C + 1, by positivity, ?_⟩
  intro inner mid outer hic hmc hir hmr hor
  obtain ⟨η, hηone, hηrange, hηgradient, hηmargin⟩ :=
    hcutoff inner mid outer hic hmc hir hmr hor
  refine ⟨η, hηone, ?_⟩
  intro D hD z hz u h heq k t ht htsmall
  have hgap : mid.radius < outer.radius := by rw [hmr, hor]; linarith
  have hsub : mid.carrier ⊆ outer.carrier := by
    rw [LocalBall.carrier, LocalBall.carrier, hmc]
    exact Metric.ball_subset_ball hgap.le
  have htsafe : |t| < outer.radius - mid.radius := by rw [hor, hmr]; linarith
  have hηsafe : Metric.cthickening |t| (tsupport (fun x => η x)) ⊆ mid.carrier :=
    (Metric.cthickening_mono htsmall.le _).trans hηmargin
  obtain ⟨q, hqv, hqg⟩ :=
    localized_difference_quotient_data mid outer hmc hgap u k t htsafe
  obtain ⟨w, hwv, hwg, hweq⟩ := weak_equation_difference_test mid outer hsub
    η q k t ht hηsafe hcρ hκ D z u h heq
  refine ⟨fun j => DifferenceTestAtoms.localized_weighted_quotient_memLp
    mid outer η (gradient u j) k t, ?_⟩
  have he := henergy mid outer hmc hmr hor η hηrange hηgradient hηmargin
    D hD z hz u h k t ht htsmall q w hqv hqg hwv hwg hweq
  have hEnonneg : 0 ≤ ∑ j : Fin n, ∫ x in mid.carrier,
      ‖(η x : ℂ) * differenceQuotient k t (zeroExtension (gradient u j)) x‖ ^ 2 := by
    apply Finset.sum_nonneg
    intro j _
    exact integral_nonneg (fun x => sq_nonneg _)
  have habs := DifferenceTestAtoms.difference_energy_absorption ha hEnonneg he
  have hK : C ≤ (Real.sqrt C + 1) ^ 2 := by
    nlinarith [Real.sq_sqrt hC, Real.sqrt_nonneg C]
  exact habs.trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))

end DedekindZetaZeroFree.WeakH2

end
