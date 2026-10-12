module

public import DedekindZetaZeroFree.Theta.Profiles.ParityShapeBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.ShiftedGaussianSummability
public import DedekindZetaZeroFree.Geometry.TranslatedLatticeGap
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.UniformGaussianTail
public import DedekindZetaZeroFree.Theta.Profiles.RayThetaKernelsAndZeroModes

@[expose] public section

noncomputable section

open Classical NumberField MeasureTheory
open NumberField.mixedEmbedding

namespace DedekindZetaZeroFree

open AbelianQuotient

set_option maxHeartbeats 1000000

variable {K : Type} [Field K] [NumberField K]

private theorem kernel_cont (δ : Finset (RayCoset.RealPlaces K)) (t : ℝ) (ht : 0<t)
 (x : euclidean.mixedSpace K) (neg : Bool) :
 Continuous (fun h : RayCoset.logHyperplane K => RayParity.gδ K δ
  (RayParity.Q K (RayTheta.q K t (if neg then -h else h)) x)) := by
 cases neg
 · unfold RayTheta.q
   simpa [Function.comp_def, one_div] using continuousOn_univ.mp
    ((continuousOn_thetaParityShape K δ).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
      (fun h (_ : h ∈ Set.univ) => ht))
 · unfold RayTheta.q
   simpa [Function.comp_def, one_div] using continuousOn_univ.mp
    ((continuousOn_thetaParityShape_neg K δ).comp
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
      (fun h (_ : h ∈ Set.univ) => ht))
private theorem phase_norm (x z : euclidean.mixedSpace K) :
 ‖Complex.exp ((2 * Real.pi : ℝ) * Complex.I * (inner ℝ x z : ℂ))‖ = 1 := by
 rw [Complex.norm_exp]; simp
private theorem Q_zero (q : InfinitePlace K → ℝ) : RayParity.Q K q 0 = 0 := by
 simp [RayParity.Q]
private theorem series_integrable
 (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
 (L : Submodule ℤ (euclidean.mixedSpace K)) [DiscreteTopology L] [Countable L]
 (z : euclidean.mixedSpace K) (a : L → ℂ) (ha : ∀ l, ‖a l‖ ≤ 1)
 (neg : Bool) (t : ℝ) (ht : 0 < t) :
 (∀ h ∈ RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
   Summable (fun l : L => a l * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l : euclidean.mixedSpace K))))) ∧
 IntegrableOn (fun h => ∑' l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0},
   a l.val * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l.val : euclidean.mixedSpace K))))
 (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot) (Theta.normalizedLogHaar K) := by
 let S := RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot
 let μ := (Theta.normalizedLogHaar K).restrict S
 haveI : IsFiniteMeasure μ := ⟨by
   dsimp [μ]; rw [Measure.restrict_apply_univ]
   exact RayCoset.measure_rayUnitHalfOpenDomain_lt_top K D.m D.modulus_ne_bot⟩
 obtain ⟨P,c,hP,hc,hbound⟩ := thetaParityShapeBounds K δ (closure S)
   (RayCoset.isCompact_closure_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
 let G := fun l : L => P * Real.exp (- (c * t ^ (2 / (Module.finrank ℚ K : ℝ))) * ‖z + (l : euclidean.mixedSpace K)‖ ^ 2)
 have hG : Summable G := (summable_shiftedGaussian L z (mul_pos hc (Real.rpow_pos_of_pos ht _))).mul_left P
 have hb : ∀ h ∈ S, ∀ l : L, ‖a l * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l : euclidean.mixedSpace K)))‖ ≤ G l := by
   intro h hh l
   rw [norm_mul]
   apply (mul_le_mul_of_nonneg_right (ha l) (norm_nonneg _)).trans
   rw [one_mul]
   have H := hbound t ht h (subset_closure hh) (z + (l : euclidean.mixedSpace K))
   unfold RayTheta.q
   cases neg
   · simpa [RayTheta.q, one_div, G, neg_mul, mul_assoc] using H.1
   · simpa [RayTheta.q, one_div, G, neg_mul, mul_assoc] using H.2
 have hs : ∀ h ∈ S, Summable (fun l : L => a l * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l : euclidean.mixedSpace K)))) :=
   fun h hh => hG.of_norm_bounded (hb h hh)
 refine ⟨hs, ?_⟩
 let F := fun h => ∑' l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0},
   a l.val * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l.val : euclidean.mixedSpace K)))
 have hm : Measurable F := Measurable.tsum (fun l =>
   (continuous_const.mul (kernel_cont δ t ht _ neg)).measurable)
 have hGp : Summable (fun l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0} => G l.val) :=
   hG.comp_injective Subtype.val_injective
 have hnorm : ∀ h ∈ S, ‖F h‖ ≤ ∑' l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0}, G l.val := by
   intro h hh
   exact (norm_tsum_le_tsum_norm (hGp.of_norm_bounded (fun l => hb h hh l.val)).norm).trans
     ((hGp.of_norm_bounded (fun l => hb h hh l.val)).norm.tsum_le_tsum (fun l => hb h hh l.val) hGp)
 exact (integrable_const (μ := μ) _).mono' hm.aestronglyMeasurable
   ((ae_restrict_mem (RayCoset.measurableSet_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)).mono hnorm)

private theorem puncture_sum {ι : Type*} (x : ι → euclidean.mixedSpace K)
 (hx : Function.Injective x) (f : ι → ℂ) (hf : Summable f) (v : ℂ)
 (hv : ∀ i, x i = 0 → f i = v) :
 ∑' i, f i = (if ∃ i, x i = 0 then v else 0) + ∑' i : {i // x i ≠ 0}, f i.val := by
 classical
 by_cases h : ∃ i, x i = 0
 · obtain ⟨i,hi⟩ := h
   have eq : {j | x j = 0} = ({i} : Set ι) := by
     ext j; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
     exact ⟨fun hj => hx (hj.trans hi.symm), fun hj => hj ▸ hi⟩
   have H := hf.tsum_subtype_add_tsum_subtype_compl {j | x j = 0}
   have hz : (∑' j : ({j | x j = 0} : Set ι), f j.val) = v := by
     rw [show {j | x j = 0} = ({i} : Set ι) from eq]
     simpa [hv i hi] using (tsum_subtype ({i} : Set ι) f).trans
       (tsum_eq_single i (fun j hj => by simp [Set.indicator, hj]))
   rw [hz] at H
   rw [if_pos (show ∃ j, x j = 0 from ⟨i,hi⟩)]
   exact H.symm
 · rw [if_neg h, zero_add]
   symm
   apply tsum_subtype_eq_of_support_subset
   intro i _; exact fun hi => h ⟨i,hi⟩
private theorem puncture_integral
 (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
 (L : Submodule ℤ (euclidean.mixedSpace K)) [DiscreteTopology L] [Countable L]
 (z : euclidean.mixedSpace K) (a : L → ℂ) (ha : ∀ l, ‖a l‖ ≤ 1)
 (hz : ∀ l : L, z + (l : euclidean.mixedSpace K) = 0 → a l = 1)
 (neg : Bool) (t : ℝ) (ht : 0 < t) :
 (∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
   ∑' l : L, a l * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l : euclidean.mixedSpace K))) ∂Theta.normalizedLogHaar K) =
 (RayCoset.rayUnitDomainVolume K D.m D.modulus_ne_bot : ℂ) *
   (if δ = ∅ ∧ ∃ l : L, z + (l : euclidean.mixedSpace K) = 0 then 1 else 0) +
 (∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
   ∑' l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0},
   a l.val * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l.val : euclidean.mixedSpace K))) ∂Theta.normalizedLogHaar K) := by
 let S := RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot
 let v : ℂ := if δ = ∅ ∧ ∃ l : L, z + (l : euclidean.mixedSpace K) = 0 then 1 else 0
 have H := series_integrable D δ L z a ha neg t ht
 have he : ∀ h ∈ S,
   (∑' l : L, a l * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l : euclidean.mixedSpace K)))) =
   v + ∑' l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0},
   a l.val * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l.val : euclidean.mixedSpace K))) := by
   intro h hh
   rw [puncture_sum (fun l : L => z + (l : euclidean.mixedSpace K))
     (fun l j he => Subtype.ext (add_left_cancel he)) _ (H.1 h hh)
     (if δ = ∅ then 1 else 0) (fun l hl => by rw [hl,Q_zero,thetaParity_zero,hz l hl,one_mul])]
   congr 1
   dsimp [v]
   split_ifs <;> simp_all
 rw [setIntegral_congr_fun (RayCoset.measurableSet_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot) he]
 have hvint : IntegrableOn (fun _ : RayCoset.logHyperplane K => v) S (Theta.normalizedLogHaar K) :=
   integrableOn_const (RayCoset.measure_rayUnitHalfOpenDomain_lt_top K D.m D.modulus_ne_bot).ne
 rw [integral_add hvint H.2, integral_const]
 congr 1
 simp only [Measure.real, Measure.restrict_apply_univ, RayCoset.rayUnitDomainVolume, smul_eq_mul, Complex.real_smul, S, v]
private theorem averaged_tail
 (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
 (L : Submodule ℤ (euclidean.mixedSpace K)) [DiscreteTopology L] [Countable L]
 (z : euclidean.mixedSpace K) (a : L → ℂ) (ha : ∀ l, ‖a l‖ ≤ 1)
 (neg : Bool) (N : ℂ) :
 ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
 ‖N * ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
   ∑' l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0},
   a l.val * RayParity.gδ K δ (RayParity.Q K
      (RayTheta.q K t (if neg then -h else h)) (z + (l.val : euclidean.mixedSpace K))) ∂Theta.normalizedLogHaar K‖ ≤
   A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ K : ℝ))) := by
 let S := RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot
 let μ := (Theta.normalizedLogHaar K).restrict S
 haveI : IsFiniteMeasure μ := ⟨by
   dsimp [μ]; rw [Measure.restrict_apply_univ]
   exact RayCoset.measure_rayUnitHalfOpenDomain_lt_top K D.m D.modulus_ne_bot⟩
 obtain ⟨P,c,hP,hc,hbound⟩ := thetaParityShapeBounds K δ (closure S)
   (RayCoset.isCompact_closure_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
 obtain ⟨η,hη,hgap⟩ := thetaTranslateGap L z
 let p : ℝ := 2 / (Module.finrank ℚ K : ℝ)
 have hp : 0 < p := div_pos (by norm_num) (by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K))
 let F := fun t h (l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0}) =>
   a l.val * RayParity.gδ K δ (RayParity.Q K (RayTheta.q K t (if neg then -h else h)) (z + (l.val : euclidean.mixedSpace K)))
 have hb : ∀ t : ℝ, 1 ≤ t → ∀ h ∈ S, ∀ l,
   ‖F t h l‖ ≤ P * Real.exp (-c * t ^ p * ‖z + (l.val : euclidean.mixedSpace K)‖ ^ 2) := by
   intro t ht h hh l
   dsimp only [F]
   rw [norm_mul]
   apply (mul_le_mul_of_nonneg_right (ha l.val) (norm_nonneg _)).trans
   rw [one_mul]
   have H := hbound t (lt_of_lt_of_le zero_lt_one ht) h (subset_closure hh) (z + (l.val : euclidean.mixedSpace K))
   unfold RayTheta.q
   cases neg
   · simpa [one_div,p] using H.1
   · simpa [one_div,p] using H.2
 obtain ⟨A,hA,H⟩ := thetaUniformGaussianTail
   (fun l : {l : L // z + (l : euclidean.mixedSpace K) ≠ 0} => z + (l.val : euclidean.mixedSpace K))
   S F P c p η hP hc hp hη (fun l => hgap l.val l.property)
   (summable_shiftedGaussian_punctured L z (half_pos hc)) hb
 let B := c * η ^ 2 / 2
 have hB : 0 < B := by dsimp [B]; positivity
 let A' := ‖N‖ * A * μ.real Set.univ
 have hA' : 0 ≤ A' := by dsimp [A']; positivity
 refine ⟨A'+1,B,by linarith,hB,?_⟩
 intro t ht
 have hi : ‖∫ h, ∑' l, F t h l ∂μ‖ ≤ (A * Real.exp (-B * t ^ p)) * μ.real Set.univ :=
   norm_integral_le_of_norm_le_const
    ((ae_restrict_mem (RayCoset.measurableSet_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)).mono
      (fun h hh => (H t ht h hh).2))
 change ‖N * ∫ h, ∑' l, F t h l ∂μ‖ ≤ _
 rw [norm_mul]
 calc
   _ ≤ ‖N‖ * ((A * Real.exp (-B * t ^ p)) * μ.real Set.univ) := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
   _ = A' * Real.exp (-B * t ^ p) := by dsimp [A']; ring
   _ ≤ (A' + 1) * Real.exp (-B * t ^ p) := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)

variable (K : Type) [Field K] [NumberField K]

theorem rayTheta_fδ_sub_f0δ
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
    (t : ℝ) (ht : 0 < t) :
    RayTheta.fδ D δ t - RayTheta.f0δ D δ =
      (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹ *
        ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
          ∑' ℓ : {ℓ : RayCoset.normalizedLattice D //
              RayCoset.normalizedBasepoint D + (ℓ : euclidean.mixedSpace K) ≠ 0},
            RayParity.gδ K δ (RayParity.Q K (RayTheta.q K t h)
              (RayCoset.normalizedBasepoint D + (ℓ.val : euclidean.mixedSpace K)))
          ∂Theta.normalizedLogHaar K := by
 have he : (∃ l : RayCoset.normalizedLattice D, RayCoset.normalizedBasepoint D + (l : euclidean.mixedSpace K) = 0) ↔
   (0 : euclidean.mixedSpace K) ∈ RayCoset.normalizedAffineCoset D := by
   constructor
   · rintro ⟨l,hl⟩
     change 0 - RayCoset.normalizedBasepoint D ∈ RayCoset.normalizedLattice D
     have eq : (l : euclidean.mixedSpace K) = 0 - RayCoset.normalizedBasepoint D := by
       exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using hl)
     exact eq ▸ l.property
   · intro h
     change 0 - RayCoset.normalizedBasepoint D ∈ RayCoset.normalizedLattice D at h
     exact ⟨⟨_,h⟩,by simp⟩
 have H := puncture_integral D δ (RayCoset.normalizedLattice D) (RayCoset.normalizedBasepoint D)
   (fun _ => 1) (fun _ => by simp) (fun _ _ => rfl) false t ht
 simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at H
 rw [RayTheta.fδ, if_pos ht, H, RayTheta.f0δ]
 rw [he]
 split_ifs <;> ring

theorem rayTheta_gδDual_sub_g0δ
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K))
    (t : ℝ) (ht : 0 < t) :
    RayTheta.gδDual D δ t - RayTheta.g0δ D δ =
      ((RayCoset.rayUnitTorsionCard K D.m : ℂ) *
        (RayCoset.modulusCovolume K D.m : ℂ))⁻¹ *
        ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
          ∑' lam : {lam : Theta.dualLattice (RayCoset.normalizedLattice D) //
              (lam : euclidean.mixedSpace K) ≠ 0},
            Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
              (inner ℝ (lam.val : euclidean.mixedSpace K)
                (RayCoset.normalizedBasepoint D) : ℂ)) *
              RayParity.gδ K δ (RayParity.Q K (RayTheta.q K t (-h))
                (lam.val : euclidean.mixedSpace K))
          ∂Theta.normalizedLogHaar K := by
 let L := Theta.dualLattice (RayCoset.normalizedLattice D)
 letI : Countable L := countable_of_Lindelof_of_discrete
 let a : L → ℂ := fun l => Complex.exp ((2 * Real.pi : ℝ) * Complex.I * (inner ℝ (l : euclidean.mixedSpace K) (RayCoset.normalizedBasepoint D) : ℂ))
 have hz : ∀ l : L, (0 : euclidean.mixedSpace K) + (l : euclidean.mixedSpace K) = 0 → a l = 1 := by
   intro l hl
   simp only [zero_add] at hl
   simp [a,hl]
 have H := puncture_integral D δ L 0 a (fun l => (phase_norm _ _).le) hz true t ht
 have hex : ∃ l : L, (0 : euclidean.mixedSpace K) + (l : euclidean.mixedSpace K) = 0 := ⟨0,by simp⟩
 simp only [zero_add, Bool.true_eq, ↓reduceIte] at H hex
 simp only [RayTheta.gδDual, if_pos ht, RayTheta.g0δ]
 change _ - _ = _
 rw [show (∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot, ∑' l : L, a l * RayParity.gδ K δ (RayParity.Q K (RayTheta.q K t (-h)) (l : euclidean.mixedSpace K)) ∂Theta.normalizedLogHaar K) = _ from H]
 simp only [hex, and_true]
 dsimp only [a]
 split_ifs <;> ring_nf
 all_goals congr 2
 all_goals funext h
 all_goals
   have eqp : (fun l : L => (0 : euclidean.mixedSpace K) + (l : euclidean.mixedSpace K) ≠ 0) =
       (fun l : L => (l : euclidean.mixedSpace K) ≠ 0) := funext (fun l => by simp)
   change (∑' l : Subtype (fun l : L => (0 : euclidean.mixedSpace K) + (l : euclidean.mixedSpace K) ≠ 0), _) = _
   rw [eqp]

theorem rayTheta_zeroModeTail
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ t : ℝ, 1 ≤ t →
      ‖RayTheta.fδ D δ t - RayTheta.f0δ D δ‖ ≤
        A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ K : ℝ))) ∧
      ‖RayTheta.gδDual D δ t - RayTheta.g0δ D δ‖ ≤
        A * Real.exp (-B * t ^ (2 / (Module.finrank ℚ K : ℝ))) := by
  obtain ⟨A1,B1,hA1,hB1,H1⟩ := averaged_tail D δ (RayCoset.normalizedLattice D)
    (RayCoset.normalizedBasepoint D) (fun _ => 1) (fun _ => by simp) false
    (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹
  let L := Theta.dualLattice (RayCoset.normalizedLattice D)
  letI : Countable L := countable_of_Lindelof_of_discrete
  let a : L → ℂ := fun l => Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
    (inner ℝ (l : euclidean.mixedSpace K) (RayCoset.normalizedBasepoint D) : ℂ))
  obtain ⟨A2,B2,hA2,hB2,H2⟩ := averaged_tail D δ L 0 a
    (fun l => (phase_norm _ _).le) true
    ((RayCoset.rayUnitTorsionCard K D.m : ℂ) * (RayCoset.modulusCovolume K D.m : ℂ))⁻¹
  refine ⟨A1+A2,min B1 B2,by linarith,lt_min hB1 hB2,?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hp : 0 ≤ t ^ (2 / (Module.finrank ℚ K : ℝ)) := Real.rpow_nonneg ht0.le _
  have e1 : Real.exp (-B1 * t ^ (2 / (Module.finrank ℚ K : ℝ))) ≤
      Real.exp (-min B1 B2 * t ^ (2 / (Module.finrank ℚ K : ℝ))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hp
  have e2 : Real.exp (-B2 * t ^ (2 / (Module.finrank ℚ K : ℝ))) ≤
      Real.exp (-min B1 B2 * t ^ (2 / (Module.finrank ℚ K : ℝ))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hp
  constructor
  · rw [rayTheta_fδ_sub_f0δ K D δ t ht0]
    have H := H1 t ht
    simp only [Bool.false_eq_true, ↓reduceIte, one_mul] at H
    exact H.trans ((mul_le_mul_of_nonneg_left e1 hA1.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)))
  · rw [rayTheta_gδDual_sub_g0δ K D δ t ht0]
    have H := H2 t ht
    dsimp only [a] at H
    have eqp : (fun l : L => (0 : euclidean.mixedSpace K) + (l : euclidean.mixedSpace K) ≠ 0) =
      (fun l : L => (l : euclidean.mixedSpace K) ≠ 0) := funext (fun _ => by simp)
    change ‖_ * ∫ h in _, ∑' l : Subtype (fun l : L => (0 : euclidean.mixedSpace K) + (l : euclidean.mixedSpace K) ≠ 0), _ ∂_‖ ≤ _ at H
    rw [eqp] at H
    simp only [zero_add, Bool.true_eq, ↓reduceIte] at H
    exact H.trans ((mul_le_mul_of_nonneg_left e2 hA2.le).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)))

end DedekindZetaZeroFree

end
