module

public import DedekindZetaZeroFree.Theta.Profiles.MixedThetaDefinitions
public import DedekindZetaZeroFree.Theta.Profiles.MixedGaussian
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.UniformGaussianTail
public import DedekindZetaZeroFree.Geometry.TranslatedLatticeGap

@[expose] public section

noncomputable section

open Classical NumberField NumberField.InfinitePlace
open NumberField.mixedEmbedding.fundamentalCone
open scoped nonZeroDivisors

namespace DedekindZetaZeroFree.AbelianQuotient.Theta

variable (K : Type*) [Field K] [NumberField K]

private theorem continuous_angularLift : Continuous (angularLift K) := by
  apply continuous_pi
  intro v
  by_cases h : v = NumberField.Units.dirichletUnitTheorem.w₀
  · simpa [angularLift, h] using (continuous_const : Continuous (fun _ : Angular K => (0 : ℝ)))
  · simpa [angularLift, h] using (continuous_apply (⟨v,h⟩ : {v : InfinitePlace K // v ≠ NumberField.Units.dirichletUnitTheorem.w₀}))
private theorem continuous_radialLift : Continuous (radialLift K) := by
  apply continuous_pi
  intro v
  by_cases h : v = NumberField.Units.dirichletUnitTheorem.w₀
  · change Continuous (fun x : ℝ => if v = NumberField.Units.dirichletUnitTheorem.w₀ then x else 0)
    simp only [if_pos h]
    fun_prop
  · simpa [radialLift, h] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
private theorem continuousOn_shape (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
  ContinuousOn (fun p : ℝ × Angular K => mixedThetaShape K I p.1 p.2)
    (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  apply (continuous_expMapBasis K).comp_continuousOn
  apply ((continuous_angularLift K).comp continuous_snd).continuousOn.add
  apply (continuous_radialLift K).comp_continuousOn
  apply ContinuousOn.div_const
  apply ContinuousOn.sub _ continuousOn_const
  apply Real.continuousOn_log.comp continuous_fst.continuousOn
  intro p hp
  exact ne_of_gt hp.1
private theorem continuous_scale_family :
  Continuous (fun p : (InfinitePlace K → ℝ) × NumberField.mixedEmbedding.euclidean.mixedSpace K =>
    (traceToMixed K).symm (NumberField.mixedEmbedding.mixedSpaceOfRealSpace p.1 * traceToMixed K p.2)) := by
  apply (traceToMixed K).symm.continuous.comp
  apply Continuous.mul _ ((traceToMixed K).continuous.comp continuous_snd)
  exact (NumberField.mixedEmbedding.mixedSpaceOfRealSpace (K := K)).continuous.comp continuous_fst
private theorem uniform_lower_scale
    (T : Set (InfinitePlace K → ℝ)) (hT : IsCompact T)
    (hpos : ∀ q ∈ T, ∀ v, q v ≠ 0) :
    ∃ d : ℝ, 0 < d ∧ ∀ q, ∀ hq : q ∈ T, ∀ x : NumberField.mixedEmbedding.euclidean.mixedSpace K,
      d * ‖x‖ ≤ ‖traceRadialScale K q (hpos q hq) x‖ := by
  let E := NumberField.mixedEmbedding.euclidean.mixedSpace K
  let F : (InfinitePlace K → ℝ) × E → E := fun p =>
    (traceToMixed K).symm (NumberField.mixedEmbedding.mixedSpaceOfRealSpace p.1 * traceToMixed K p.2)
  have hc : IsCompact (T ×ˢ Metric.sphere (0 : E) 1) := hT.prod (isCompact_sphere _ _)
  obtain ⟨d, hd, hbound⟩ := hc.exists_forall_le' (continuous_scale_family K).norm.continuousOn (a := 0) (by
    intro p hp
    have heq : F p = traceRadialScale K p.1 (hpos _ hp.1) p.2 := by
      apply (traceToMixed K).injective
      simp [F, traceToMixed_traceRadialScale]
    change 0 < ‖F p‖
    rw [heq, norm_pos_iff]
    intro hz
    have : p.2 = 0 := (traceRadialScale K p.1 (hpos _ hp.1)).injective (by simpa using hz)
    have hs : dist p.2 0 = 1 := hp.2
    rw [this, dist_self] at hs
    norm_num at hs)
  refine ⟨d, hd, ?_⟩
  intro q hq x
  by_cases hx : x = 0
  · simp [hx]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hy : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hnorm.ne']
  have hb := hbound (q, (‖x‖⁻¹ : ℝ) • x) ⟨hq, by simpa [Metric.mem_sphere, dist_eq_norm] using hy⟩
  have heq : F (q, (‖x‖⁻¹ : ℝ) • x) = traceRadialScale K q (hpos q hq) ((‖x‖⁻¹ : ℝ) • x) := by
    apply (traceToMixed K).injective
    simp [F, traceToMixed_traceRadialScale]
  change d ≤ ‖F (q, (‖x‖⁻¹ : ℝ) • x)‖ at hb
  rw [heq, map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] at hb
  calc
    d * ‖x‖ ≤ (‖x‖⁻¹ * ‖traceRadialScale K q (hpos q hq) x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = _ := by field_simp
private theorem theta_tsum_fixed (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (q : InfinitePlace K → ℝ) (hq : ∀ v, q v ≠ 0) :
    fractionalShapeIdealTheta K I q hq =
      ∑' x : traceIdealLattice K I, latticeGaussian Real.pi (traceRadialScale K q hq x) := by
  let e : traceIdealLattice K I ≃ shapeIdealLattice K I q hq := {
    toFun := fun x => ⟨traceRadialScale K q hq x, by
      change (traceRadialScale K q hq).symm (traceRadialScale K q hq x) ∈ traceIdealLattice K I
      simpa using x.prop⟩
    invFun := fun x => ⟨(traceRadialScale K q hq).symm x, x.prop⟩
    left_inv := fun x => by ext; simp
    right_inv := fun x => by ext; simp }
  exact (e.tsum_eq (fun x => latticeGaussian Real.pi (x : NumberField.mixedEmbedding.euclidean.mixedSpace K))).symm

private theorem shape_radial (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) (u : Angular K) :
    mixedThetaShape K I t u = t ^ (1 / (Module.finrank ℚ K : ℝ)) • mixedThetaShape K I 1 u := by
  let n : ℝ := Module.finrank ℚ K
  have hshape (s : ℝ) : mixedThetaShape K I s u =
      Real.exp ((Real.log s - Real.log (mixedThetaCovolume K I)) / n) • expMapBasis (angularLift K u) := by
    rw [mixedThetaShape, expMapBasis_apply'']
    congr 1
    · simp [angularLift, radialLift, n]
    · congr 1
      funext v
      by_cases hv : v = NumberField.Units.dirichletUnitTheorem.w₀
      · simp [angularLift, radialLift, hv]
      · simp [angularLift, radialLift, hv]
  rw [hshape t, hshape 1, smul_smul, Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 2
  simp only [Real.log_one]
  ring
set_option maxHeartbeats 800000 in
private theorem scale_shape_radial (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (t : ℝ) (ht : 0 < t) (u : Angular K)
    (x : NumberField.mixedEmbedding.euclidean.mixedSpace K) :
    traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x =
    t ^ (1 / (Module.finrank ℚ K : ℝ)) •
      traceRadialScale K (mixedThetaShape K I 1 u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x := by
  apply (traceToMixed K).injective
  simp only [traceToMixed_traceRadialScale, map_smul]
  rw [shape_radial K I t ht u, map_smul, smul_mul_assoc]

set_option maxHeartbeats 3000000 in

theorem mixedRadialTheta_uniform_exponential_tail
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (S : Set (Angular K)) (hS : IsCompact S) :
    ∃ B b : ℝ, 0 < B ∧ 0 < b ∧
      ∀ t : ℝ, 1 ≤ t → ∀ u ∈ S,
        ‖mixedRadialTheta K I t u - 1‖ ≤
          B * Real.exp (-b * t ^ (2 / (Module.finrank ℚ K : ℝ))) := by
  let L := traceIdealLattice K I
  let E := NumberField.mixedEmbedding.euclidean.mixedSpace K
  let X := {x : L // x ≠ 0}
  let T := (mixedThetaShape K I 1) '' S
  have hT : IsCompact T := by
    apply hS.image_of_continuousOn
    change ContinuousOn (fun u => expMapBasis (angularLift K u + radialLift K ((Real.log 1 - Real.log (mixedThetaCovolume K I)) / (Module.finrank ℚ K : ℝ)))) S
    exact ((continuous_expMapBasis K).comp ((continuous_angularLift K).add continuous_const)).continuousOn
  have hn : ∀ q ∈ T, ∀ v, q v ≠ 0 := by
    intro q hq v
    obtain ⟨u, hu, rfl⟩ := hq
    exact ne_of_gt (expMapBasis_pos _ _)
  obtain ⟨d, hd, hb⟩ := uniform_lower_scale K T hT hn
  obtain ⟨η, hη, hgap⟩ := DedekindZetaZeroFree.thetaTranslateGap L (0 : E)
  let c := Real.pi * d ^ 2
  let p := 2 / (Module.finrank ℚ K : ℝ)
  have hc : 0 < c := mul_pos Real.pi_pos (sq_pos_of_pos hd)
  have hp : 0 < p := div_pos (by norm_num) (Nat.cast_pos.mpr (Module.finrank_pos (R := ℚ) (M := K)))
  let F : ℝ → Angular K → X → ℂ := fun t u x => latticeGaussian Real.pi
    (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E))
  have hs : Summable (fun x : X => Real.exp (-(c / 2) * ‖(x.val : E)‖ ^ 2)) := by
    have hh := ((summable_latticeGaussian L (half_pos hc)).norm).subtype (fun x => x ≠ 0)
    change Summable (fun x : {x : L // x ≠ 0} => Real.exp (-(c / 2) * ‖(x.val : E)‖ ^ 2))
    simpa only [Function.comp_def, norm_latticeGaussian] using hh
  have hg : ∀ x : X, η ≤ ‖(x.val : E)‖ := by
    intro x
    have hxx : (x.val : E) ≠ 0 := fun hz => x.prop (Subtype.ext hz)
    have hgg := hgap x.val (by simpa only [zero_add] using hxx)
    simpa only [zero_add] using hgg
  have hbound : ∀ t : ℝ, 1 ≤ t → ∀ u ∈ S, ∀ x : X,
      ‖F t u x‖ ≤ 1 * Real.exp (-c * t ^ p * ‖(x.val : E)‖ ^ 2) := by
    intro t ht u hu x
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    change ‖latticeGaussian Real.pi _‖ ≤ _
    rw [norm_latticeGaussian, scale_shape_radial K I t ht0 u, norm_smul,
      Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _), mul_pow, one_mul]
    have hpow : (t ^ (1 / (Module.finrank ℚ K : ℝ))) ^ 2 = t ^ p := by
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht0.le]
      congr 1
      dsimp [p]
      ring
    rw [hpow]
    apply Real.exp_le_exp.mpr
    have hh := hb _ ⟨u, hu, rfl⟩ (x.val : E)
    have hh2 : d ^ 2 * ‖(x.val : E)‖ ^ 2 ≤
        ‖traceRadialScale K (mixedThetaShape K I 1 u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E)‖ ^ 2 := by
      simpa only [mul_pow] using (sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg _)) (norm_nonneg _)).mpr hh
    have hmm := mul_le_mul_of_nonneg_left hh2 (mul_nonneg Real.pi_pos.le (Real.rpow_nonneg ht0.le p))
    dsimp [c]
    nlinarith [hmm]
  obtain ⟨B, hB, hres⟩ := DedekindZetaZeroFree.thetaUniformGaussianTail
    (fun x : X => (x.val : E)) S F 1 c p η one_pos hc hp hη hg hs hbound
  refine ⟨B, c * η ^ 2 / 2, hB, div_pos (mul_pos hc (sq_pos_of_pos hη)) (by norm_num), ?_⟩
  intro t ht u hu
  have hres' := hres t ht u hu
  have hfull : Summable (fun x : L => latticeGaussian Real.pi
      (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x : E))) := by
    let e : L ≃ shapeIdealLattice K I (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) := {
      toFun := fun x => ⟨traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x, by
        change (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v))).symm (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) x) ∈ traceIdealLattice K I
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact x.prop⟩
      invFun := fun x => ⟨(traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v))).symm x, x.prop⟩
      left_inv := fun x => by ext; simp
      right_inv := fun x => by ext; simp }
    exact e.summable_iff.mpr (summable_latticeGaussian _ Real.pi_pos)
  have heq : mixedRadialTheta K I t u - 1 = ∑' x : X, F t u x := by
    rw [mixedRadialTheta, theta_tsum_fixed]
    have hh := hfull.tsum_subtype_add_tsum_subtype_compl ({0} : Set L)
    have hsingle : (∑' x : ↥({0} : Set L), latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E))) = latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (0 : L)) :=
      tsum_singleton (0 : L) (fun x : L => latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x : E)))
    rw [hsingle] at hh
    have hz : latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (0 : L)) = 1 := by
      simp [latticeGaussian]
    rw [hz] at hh
    have he : (∑' x : ↥({0} : Set L)ᶜ, latticeGaussian Real.pi (traceRadialScale K (mixedThetaShape K I t u) (fun v => ne_of_gt (expMapBasis_pos _ v)) (x.val : E))) = ∑' x : X, F t u x := by
      rfl
    rw [he] at hh
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using hh.symm)
  rw [heq]
  exact hres'.2

theorem mixedRadialTheta_hasSumUniformlyOn
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a b' : ℝ) (ha : 0 < a) (hab : a ≤ b')
    (S : Set (Angular K)) (hS : IsCompact S) :
    HasSumUniformlyOn
      (fun (x : ↥(traceIdealLattice K I)) (p : ℝ × Angular K) ↦
        latticeGaussian Real.pi
          (traceRadialScale K (mixedThetaShape K I p.1 p.2)
            (fun v ↦ ne_of_gt (expMapBasis_pos _ v))
            (x : NumberField.mixedEmbedding.euclidean.mixedSpace K)))
      (fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2)
      (Set.Icc a b' ×ˢ S) := by
  let C := Set.Icc a b' ×ˢ S
  have hC : IsCompact C := isCompact_Icc.prod hS
  have hsub : C ⊆ Set.Ioi (0 : ℝ) ×ˢ Set.univ := fun p hp => ⟨lt_of_lt_of_le ha hp.1.1, Set.mem_univ _⟩
  have hc := (continuousOn_shape K I).mono hsub
  let T := (fun p : ℝ × Angular K => mixedThetaShape K I p.1 p.2) '' C
  have hT : IsCompact T := hC.image_of_continuousOn hc
  have hn : ∀ q ∈ T, ∀ v, q v ≠ 0 := by
    intro q hq v
    obtain ⟨p, hp, rfl⟩ := hq
    exact ne_of_gt (expMapBasis_pos _ _)
  obtain ⟨d, hd, hb⟩ := uniform_lower_scale K T hT hn
  have hs := (summable_latticeGaussian (traceIdealLattice K I) (mul_pos Real.pi_pos (sq_pos_of_pos hd))).norm
  have heq : (fun p : ℝ × Angular K => mixedRadialTheta K I p.1 p.2) =
    (fun p => ∑' x : traceIdealLattice K I, latticeGaussian Real.pi
      (traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x)) := by
    funext p
    exact theta_tsum_fixed K I _ _
  rw [heq]
  apply HasSumUniformlyOn.of_norm_le_summable hs
  intro x p hp
  rw [norm_latticeGaussian, norm_latticeGaussian]
  apply Real.exp_le_exp.mpr
  have hb' := hb _ ⟨p, hp, rfl⟩ x
  have hsquare : d ^ 2 * ‖(x : NumberField.mixedEmbedding.euclidean.mixedSpace K)‖ ^ 2 ≤
    ‖traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x‖ ^ 2 := by
    have hh := sq_le_sq₀ (mul_nonneg hd.le (norm_nonneg (x : NumberField.mixedEmbedding.euclidean.mixedSpace K))) (norm_nonneg (traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x))
    simpa only [mul_pow] using hh.mpr hb'
  nlinarith [Real.pi_pos]

private theorem continuousOn_summand (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (x : traceIdealLattice K I) : ContinuousOn
      (fun p : ℝ × Angular K => latticeGaussian Real.pi
        (traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x))
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have heq : (fun p : ℝ × Angular K => traceRadialScale K (mixedThetaShape K I p.1 p.2) (fun v => ne_of_gt (expMapBasis_pos _ v)) x) =
    (fun p => (traceToMixed K).symm (NumberField.mixedEmbedding.mixedSpaceOfRealSpace (mixedThetaShape K I p.1 p.2) * traceToMixed K x)) := by
    funext p
    apply (traceToMixed K).injective
    simp [traceToMixed_traceRadialScale]
  have hgauss : Continuous (latticeGaussian Real.pi (E := NumberField.mixedEmbedding.euclidean.mixedSpace K)) := by
    unfold latticeGaussian
    fun_prop
  apply hgauss.comp_continuousOn
  rw [heq]
  apply (traceToMixed K).symm.continuous.comp_continuousOn
  apply ContinuousOn.mul _ continuousOn_const
  exact NumberField.mixedEmbedding.mixedSpaceOfRealSpace.continuous.comp_continuousOn (continuousOn_shape K I)

theorem continuousOn_mixedRadialTheta
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (fun p : ℝ × Angular K ↦ mixedRadialTheta K I p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Angular K))) := by
  intro p hp
  have hpp : 0 < p.1 := hp.1
  let a := p.1 / 2
  let b := p.1 + 1
  let S := Metric.closedBall p.2 1
  have ha : 0 < a := half_pos hp.1
  have hab : a ≤ b := by dsimp [a, b]; linarith [hpp]
  have hc : ContinuousOn (fun p : ℝ × Angular K => mixedRadialTheta K I p.1 p.2) (Set.Icc a b ×ˢ S) := by
    apply (mixedRadialTheta_hasSumUniformlyOn K I a b ha hab S (isCompact_closedBall _ _)).tendstoUniformlyOn.continuousOn
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    apply continuousOn_finset_sum
    intro x hx
    apply (continuousOn_summand K I x).mono
    intro q hq
    exact ⟨lt_of_lt_of_le ha hq.1.1, Set.mem_univ _⟩
  apply (hc.continuousAt ?_).continuousWithinAt
  rw [show p = (p.1, p.2) from rfl, nhds_prod_eq]
  exact Filter.Eventually.prod_mk (Icc_mem_nhds (by dsimp [a]; linarith [hpp]) (by dsimp [b]; linarith)) (Metric.closedBall_mem_nhds _ (by norm_num : (0 : ℝ) < 1))

end DedekindZetaZeroFree.AbelianQuotient.Theta

end
