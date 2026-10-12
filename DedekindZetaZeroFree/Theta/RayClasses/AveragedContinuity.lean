module

public import DedekindZetaZeroFree.Theta.Profiles.RayThetaKernelsAndZeroModes
public import DedekindZetaZeroFree.Theta.Profiles.DominatedAngularContinuity
public import DedekindZetaZeroFree.Theta.Profiles.ParityShapeBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.ShiftedGaussianSummability

@[expose] public section

noncomputable section

open Classical NumberField NumberField.mixedEmbedding MeasureTheory

namespace DedekindZetaZeroFree

open AbelianQuotient

variable {K : Type} [Field K] [NumberField K]

set_option maxHeartbeats 1600000

private theorem continuousOn_rayAverage
    (D : RayCoset.Data K) (L : Submodule ℤ (euclidean.mixedSpace K))
    [DiscreteTopology L] [Countable L]
    (z : euclidean.mixedSpace K)
    (F : ℝ → RayCoset.logHyperplane K → L → ℂ)
    (hF : ∀ i, ContinuousOn (fun th : ℝ × RayCoset.logHyperplane K => F th.1 th.2 i)
      (Set.Ioi 0 ×ˢ closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)))
    (hb : ∃ P c : ℝ, 0 < P ∧ 0 < c ∧ ∀ t, 0 < t →
      ∀ h ∈ closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot), ∀ i : L,
        ‖F t h i‖ ≤ P * Real.exp (-c * t ^ (2 / (Module.finrank ℚ K : ℝ)) *
          ‖z + (i : euclidean.mixedSpace K)‖ ^ 2)) :
    ContinuousOn (fun t => ∫ h in RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot,
      ∑' i : L, F t h i ∂Theta.normalizedLogHaar K) (Set.Ioi 0) := by
  obtain ⟨P, c, hP, hc, hb⟩ := hb
  refine (thetaDominatedAngularContinuity (Theta.normalizedLogHaar K)
    (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
    (closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot))
    (RayCoset.measurableSet_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
    (RayCoset.measure_rayUnitHalfOpenDomain_lt_top K D.m D.modulus_ne_bot)
    (RayCoset.isCompact_closure_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
    subset_closure F hF ?_).2.2.1
  intro a b ha hab
  let A := c * a ^ (2 / (Module.finrank ℚ K : ℝ))
  have hA : 0 < A := mul_pos hc (Real.rpow_pos_of_pos ha _)
  refine ⟨fun i : L => P * Real.exp (-A * ‖z + (i : euclidean.mixedSpace K)‖ ^ 2),
    (summable_shiftedGaussian L z hA).mul_left P,
    fun i => mul_nonneg hP.le (Real.exp_pos _).le, ?_⟩
  intro t ht h hh i
  refine (hb t (lt_of_lt_of_le ha ht.1) h hh i).trans ?_
  apply mul_le_mul_of_nonneg_left _ hP.le
  apply Real.exp_le_exp.mpr
  have hp : a ^ (2 / (Module.finrank ℚ K : ℝ)) ≤
      t ^ (2 / (Module.finrank ℚ K : ℝ)) :=
    Real.rpow_le_rpow ha.le ht.1 (div_nonneg (by norm_num) (Nat.cast_nonneg _))
  dsimp [A]
  nlinarith [sq_nonneg ‖z + (i : euclidean.mixedSpace K)‖,
    mul_le_mul_of_nonneg_left hp hc.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc.le)
      (sq_nonneg ‖z + (i : euclidean.mixedSpace K)‖)]

theorem rayTheta_continuousOn_fδ
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    ContinuousOn (RayTheta.fδ D δ) (Set.Ioi (0 : ℝ)) := by
  let F := fun t h (i : RayCoset.normalizedLattice D) =>
    RayParity.gδ K δ (RayParity.Q K (RayTheta.q K t h)
      (RayCoset.normalizedBasepoint D + (i : euclidean.mixedSpace K)))
  have hF : ∀ i, ContinuousOn (fun th : ℝ × RayCoset.logHyperplane K => F th.1 th.2 i)
      (Set.Ioi 0 ×ˢ closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)) := by
    intro i
    change ContinuousOn (fun th : ℝ × RayCoset.logHyperplane K =>
      RayParity.gδ K δ (RayParity.Q K
        (fun v => th.1 ^ (Module.finrank ℚ K : ℝ)⁻¹ * Real.exp (th.2.val v))
        (RayCoset.normalizedBasepoint D + (i : euclidean.mixedSpace K)))) _
    simpa only [one_div, Function.comp_def] using
      (continuousOn_thetaParityShape K δ).comp
        ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
        (fun th hth => hth.1)
  have hb := thetaParityShapeBounds K δ
    (closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot))
    (RayCoset.isCompact_closure_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
  obtain ⟨P, c, hP, hc, hb⟩ := hb
  have hav := continuousOn_rayAverage D (RayCoset.normalizedLattice D)
    (RayCoset.normalizedBasepoint D) F hF ⟨P, c, hP, hc, fun t ht h hh i => by
      change ‖RayParity.gδ K δ (RayParity.Q K
        (fun v => t ^ (Module.finrank ℚ K : ℝ)⁻¹ * Real.exp (h.val v))
        (RayCoset.normalizedBasepoint D + (i : euclidean.mixedSpace K)))‖ ≤ _
      simpa only [one_div] using
        (hb t ht h hh (RayCoset.normalizedBasepoint D + (i : euclidean.mixedSpace K))).1⟩
  refine ((continuousOn_const (c := (RayCoset.rayUnitTorsionCard K D.m : ℂ)⁻¹)).mul hav).congr ?_
  intro t ht
  change (if 0 < t then _ else _) = _
  rw [if_pos (show 0 < t from ht)]
  rfl

theorem rayTheta_continuousOn_gδDual
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    ContinuousOn (RayTheta.gδDual D δ) (Set.Ioi (0 : ℝ)) := by
  let L := Theta.dualLattice (RayCoset.normalizedLattice D)
  letI : Countable L := countable_of_Lindelof_of_discrete
  let phase := fun i : L => Complex.exp ((2 * Real.pi : ℝ) * Complex.I *
    (inner ℝ (i : euclidean.mixedSpace K) (RayCoset.normalizedBasepoint D) : ℂ))
  have hphase : ∀ i, ‖phase i‖ = 1 := by
    intro i
    rw [Complex.norm_exp]
    simp
  let F := fun t h (i : L) => phase i *
    RayParity.gδ K δ (RayParity.Q K (RayTheta.q K t (-h)) (i : euclidean.mixedSpace K))
  have hF : ∀ i, ContinuousOn (fun th : ℝ × RayCoset.logHyperplane K => F th.1 th.2 i)
      (Set.Ioi 0 ×ˢ closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)) := by
    intro i
    have hm : Continuous (fun th : ℝ × RayCoset.logHyperplane K =>
        (th.1, (th.2, (i : euclidean.mixedSpace K)))) :=
      continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
    have h := (continuousOn_thetaParityShape_neg K δ).comp
      (s := Set.Ioi 0 ×ˢ closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot))
      hm.continuousOn (fun th hth => hth.1)
    change ContinuousOn (fun th : ℝ × RayCoset.logHyperplane K => phase i *
      RayParity.gδ K δ (RayParity.Q K
        (fun v => th.1 ^ (Module.finrank ℚ K : ℝ)⁻¹ * Real.exp ((-th.2).val v))
        (i : euclidean.mixedSpace K))) _
    have h' : ContinuousOn (fun th : ℝ × RayCoset.logHyperplane K =>
      RayParity.gδ K δ (RayParity.Q K
        (fun v => th.1 ^ (Module.finrank ℚ K : ℝ)⁻¹ * Real.exp ((-th.2).val v))
        (i : euclidean.mixedSpace K)))
      (Set.Ioi 0 ×ˢ closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)) := by
      simpa only [one_div, Function.comp_def] using h
    exact (continuousOn_const (c := phase i)).mul h'
  obtain ⟨P, c, hP, hc, hb⟩ := thetaParityShapeBounds K δ
    (closure (RayCoset.rayUnitHalfOpenDomain K D.m D.modulus_ne_bot))
    (RayCoset.isCompact_closure_rayUnitHalfOpenDomain K D.m D.modulus_ne_bot)
  have hav := continuousOn_rayAverage D L 0 F hF ⟨P, c, hP, hc, fun t ht h hh i => by
    change ‖phase i * RayParity.gδ K δ (RayParity.Q K
      (fun v => t ^ (Module.finrank ℚ K : ℝ)⁻¹ * Real.exp ((-h).val v))
      (i : euclidean.mixedSpace K))‖ ≤ _
    simpa only [norm_mul, hphase, one_mul, one_div, zero_add] using
      (hb t ht h hh (i : euclidean.mixedSpace K)).2⟩
  refine ((continuousOn_const (c := ((RayCoset.rayUnitTorsionCard K D.m : ℂ) *
    (RayCoset.modulusCovolume K D.m : ℂ))⁻¹)).mul hav).congr ?_
  intro t ht
  change (if 0 < t then _ else _) = _
  rw [if_pos (show 0 < t from ht)]
  rfl

theorem rayTheta_locallyIntegrableOn_fδ
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    LocallyIntegrableOn (RayTheta.fδ D δ) (Set.Ioi (0 : ℝ)) volume := by
  exact (rayTheta_continuousOn_fδ D δ).locallyIntegrableOn measurableSet_Ioi

theorem rayTheta_locallyIntegrableOn_gδDual
    (D : RayCoset.Data K) (δ : Finset (RayCoset.RealPlaces K)) :
    LocallyIntegrableOn (RayTheta.gδDual D δ) (Set.Ioi (0 : ℝ)) volume := by
  exact (rayTheta_continuousOn_gδDual D δ).locallyIntegrableOn measurableSet_Ioi

end DedekindZetaZeroFree

end
