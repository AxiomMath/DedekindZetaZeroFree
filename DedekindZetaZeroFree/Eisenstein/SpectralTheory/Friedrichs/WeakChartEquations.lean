module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.TestCodifferential
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.VariationalChartEquation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.TestFriedrichsRealization

@[expose] public section

attribute [-instance] DedekindZetaZeroFree.PGLComplex.AdelicSlices.instMeasurableSpaceActualCover

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualFriedrichsWeakChart

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

def inverseMetric (p : Space (KPCuspLogShape.dimension F * 3)) :
    Matrix (Fin (KPCuspLogShape.dimension F * 3))
      (Fin (KPCuspLogShape.dimension F * 3)) ℝ :=
  Matrix.diagonal (fun j =>
    let ik := finProdFinEquiv.symm j
    if ik.2 = 2 then 1 else
      Real.exp (2 * (coordinates F p ik.1).2))

structure ChartCoefficients (A : LocalBall (KPCuspLogShape.dimension F * 3)) where
  lowerDensity : ℝ
  upperDensity : ℝ
  lowerEllipticity : ℝ
  upperEllipticity : ℝ
  lowerDensity_pos : 0 < lowerDensity
  upperDensity_pos : 0 < upperDensity
  lowerEllipticity_pos : 0 < lowerEllipticity
  upperEllipticity_pos : 0 < upperEllipticity
  data : KPContLocalEnergy.Coefficients A lowerDensity upperDensity
    lowerEllipticity upperEllipticity
  density_exact : data.density = density F
  matrix_exact : data.matrix = inverseMetric F
  smooth_near_closed : ∃ V : Set (Space (KPCuspLogShape.dimension F * 3)),
    IsOpen V ∧ KPContLocalCubeEmbedding.closedCarrier A ⊆ V ∧
      ContDiffOn ℝ (⊤ : ℕ∞) data.density V ∧
      ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (fun p => data.matrix p i j) V
  closed_density_bounds : ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A,
    lowerDensity ≤ data.density p ∧ data.density p ≤ upperDensity
  closed_ellipticity_bounds : ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A,
    ∀ v : Space (KPCuspLogShape.dimension F * 3),
      lowerEllipticity * ‖v‖ ^ 2 ≤ ∑ i, ∑ j, data.matrix p i j * v i * v j
  closed_upper_bound : ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A,
    ∀ v : Space (KPCuspLogShape.dimension F * 3),
      (∑ i, ∑ j, data.matrix p i j * v i * v j) ≤ upperEllipticity * ‖v‖ ^ 2

private lemma coordinates_snd (p : Space (KPCuspLogShape.dimension F * 3))
    (i : Fin (KPCuspLogShape.dimension F)) :
    (coordinates F p i).2 = p (finProdFinEquiv (i, 2)) := rfl

 def diagFun (p : Space (KPCuspLogShape.dimension F * 3)) :
    Fin (KPCuspLogShape.dimension F * 3) → ℝ :=
  fun j => let ik := finProdFinEquiv.symm j
    if ik.2 = 2 then 1 else Real.exp (2 * p (finProdFinEquiv (ik.1, 2)))

 lemma inverseMetric_eq_diagonal (p : Space (KPCuspLogShape.dimension F * 3)) :
    inverseMetric F p = Matrix.diagonal (diagFun F p) := by
  funext i j
  rw [inverseMetric, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · rw [if_pos h, if_pos h]; simp only [diagFun, coordinates_snd]
  · rw [if_neg h, if_neg h]

private lemma contDiff_diagFun (j : Fin (KPCuspLogShape.dimension F * 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space (KPCuspLogShape.dimension F * 3) => diagFun F p j) := by
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [diagFun, h, if_true]; fun_prop
  · simp only [diagFun, h, if_false]; fun_prop

 lemma contDiff_inverseMetric_entry (i j : Fin (KPCuspLogShape.dimension F * 3)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Space (KPCuspLogShape.dimension F * 3) => inverseMetric F p i j) := by
  by_cases h : i = j
  · have he : (fun p => inverseMetric F p i j) = (fun p => diagFun F p i) := by
      funext p; rw [inverseMetric_eq_diagonal, ← h, Matrix.diagonal_apply_eq]
    rw [he]; exact contDiff_diagFun F i
  · have he : (fun p => inverseMetric F p i j) = (fun _ => (0 : ℝ)) := by
      funext p; rw [inverseMetric_eq_diagonal, Matrix.diagonal_apply_ne _ h]
    rw [he]; exact contDiff_const

 def entryLo (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : ℝ :=
  let ik := finProdFinEquiv.symm j
  if ik.2 = 2 then 1
  else Real.exp (2 * (A.center (finProdFinEquiv (ik.1, 2)) - A.radius))

 def entryHi (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : ℝ :=
  let ik := finProdFinEquiv.symm j
  if ik.2 = 2 then 1
  else Real.exp (2 * (A.center (finProdFinEquiv (ik.1, 2)) + A.radius))

 lemma entryLo_pos (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : 0 < entryLo F A j := by
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [entryLo, h, if_true]; norm_num
  · simp only [entryLo, h, if_false]; exact Real.exp_pos _

 lemma entry_bounds (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3))
    {p : Space (KPCuspLogShape.dimension F * 3)} (hp : p ∈ KPContLocalCubeEmbedding.closedCarrier A) :
    entryLo F A j ≤ diagFun F p j ∧ diagFun F p j ≤ entryHi F A j := by
  have hd : dist p A.center ≤ A.radius := Metric.mem_closedBall.mp hp
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [entryLo, entryHi, diagFun, h, if_true]; exact ⟨le_rfl, le_rfl⟩
  · simp only [entryLo, entryHi, diagFun, h, if_false]
    have hk : |p (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) -
        A.center (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2))| ≤ A.radius := by
      have h1 := PiLp.norm_apply_le (p - A.center)
        (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2))
      rw [PiLp.sub_apply] at h1
      rw [dist_eq_norm] at hd
      simpa using h1.trans hd
    have hlo : A.center (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) - A.radius ≤
        p (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) := by
      have := (abs_le.mp hk).1; linarith
    have hhi : p (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) ≤
        A.center (finProdFinEquiv ((finProdFinEquiv.symm j).1, 2)) + A.radius := by
      have := (abs_le.mp hk).2; linarith
    exact ⟨Real.exp_le_exp.mpr (by linarith), Real.exp_le_exp.mpr (by linarith)⟩

 lemma entryHi_pos (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (j : Fin (KPCuspLogShape.dimension F * 3)) : 0 < entryHi F A j := by
  by_cases h : (finProdFinEquiv.symm j).2 = 2
  · simp only [entryHi, h, if_true]; norm_num
  · simp only [entryHi, h, if_false]; exact Real.exp_pos _

 lemma diag_quad (d : Fin (KPCuspLogShape.dimension F * 3) → ℝ)
    (v : Space (KPCuspLogShape.dimension F * 3)) :
    ∑ i, ∑ j, Matrix.diagonal d i j * v i * v j = ∑ i, d i * (v i) ^ 2 := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj; rw [Matrix.diagonal_apply_ne' _ hj]; ring
  · intro hi; exact absurd (Finset.mem_univ i) hi

def chartCoefficients (A : LocalBall (KPCuspLogShape.dimension F * 3)) :
    ChartCoefficients F A := by
  classical
  let hbnd := density_bounds F A
  let a : ℝ := hbnd.choose
  let b : ℝ := hbnd.choose_spec.choose
  have ha : 0 < a := hbnd.choose_spec.choose_spec.1
  have hb : ∀ p ∈ KPContLocalCubeEmbedding.closedCarrier A, a ≤ density F p ∧ density F p ≤ b :=
    hbnd.choose_spec.choose_spec.2
  have hbc : 0 < b := by
    have hmem : A.center ∈ KPContLocalCubeEmbedding.closedCarrier A := Metric.mem_closedBall_self A.radius_pos.le
    exact (lt_of_lt_of_le ha (hb A.center hmem).1).trans_le (hb A.center hmem).2
  haveI : Nonempty (Fin (KPCuspLogShape.dimension F * 3)) :=
    ⟨⟨0, A.dimension_pos⟩⟩
  let κ : ℝ := Finset.univ.inf' Finset.univ_nonempty (entryLo F A)
  let Λ : ℝ := Finset.univ.sup' Finset.univ_nonempty (entryHi F A)
  have hκpos : 0 < κ :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun j _ => entryLo_pos F A j)
  have hΛpos : 0 < Λ := by
    obtain ⟨j, -⟩ := Finset.univ_nonempty (α := Fin (KPCuspLogShape.dimension F * 3))
    exact (entryHi_pos F A j).trans_le (Finset.le_sup' (entryHi F A) (Finset.mem_univ j))
  refine
    { lowerDensity := a
      upperDensity := b
      lowerEllipticity := κ
      upperEllipticity := Λ
      lowerDensity_pos := ha
      upperDensity_pos := hbc
      lowerEllipticity_pos := hκpos
      upperEllipticity_pos := hΛpos
      data :=
        { density := density F
          matrix := inverseMetric F
          density_smooth := (density_smooth F).contDiffOn
          matrix_smooth := fun i j => (contDiff_inverseMetric_entry F i j).contDiffOn
          density_bounds := fun x hx => hb x (Metric.ball_subset_closedBall hx)
          symmetric := fun x _ i j => by
            rw [inverseMetric_eq_diagonal]
            by_cases hij : i = j
            · rw [hij]
            · rw [Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij)]
          ellipticity := fun x hx ξ => by
            calc κ * ‖ξ‖ ^ 2 = κ * ∑ i, (ξ i) ^ 2 := by
                  rw [EuclideanSpace.real_norm_sq_eq]
              _ = ∑ i, κ * (ξ i) ^ 2 := by rw [Finset.mul_sum]
              _ ≤ ∑ i, diagFun F x i * (ξ i) ^ 2 :=
                  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                    ((Finset.inf'_le (entryLo F A) (Finset.mem_univ i)).trans
                      (entry_bounds F A i (Metric.ball_subset_closedBall hx)).1) (sq_nonneg _)
              _ = ∑ i, ∑ j, inverseMetric F x i j * ξ i * ξ j := by
                  rw [inverseMetric_eq_diagonal, diag_quad]
          upper_bound := fun x hx ξ => by
            calc ∑ i, ∑ j, inverseMetric F x i j * ξ i * ξ j
                = ∑ i, diagFun F x i * (ξ i) ^ 2 := by
                  rw [inverseMetric_eq_diagonal, diag_quad]
              _ ≤ ∑ i, Λ * (ξ i) ^ 2 :=
                  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                    ((entry_bounds F A i (Metric.ball_subset_closedBall hx)).2.trans
                      (Finset.le_sup' (entryHi F A) (Finset.mem_univ i))) (sq_nonneg _)
              _ = Λ * ∑ i, (ξ i) ^ 2 := by rw [Finset.mul_sum]
              _ = Λ * ‖ξ‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq] }
      density_exact := rfl
      matrix_exact := rfl
      smooth_near_closed :=
        ⟨Set.univ, isOpen_univ, fun _ _ => trivial,
          (density_smooth F).contDiffOn,
          fun i j => (contDiff_inverseMetric_entry F i j).contDiffOn⟩
      closed_density_bounds := fun p hp => hb p hp
      closed_ellipticity_bounds := fun p hp v => by
        calc κ * ‖v‖ ^ 2 = κ * ∑ i, (v i) ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]
          _ = ∑ i, κ * (v i) ^ 2 := by rw [Finset.mul_sum]
          _ ≤ ∑ i, diagFun F p i * (v i) ^ 2 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                ((Finset.inf'_le (entryLo F A) (Finset.mem_univ i)).trans
                  (entry_bounds F A i hp).1) (sq_nonneg _)
          _ = ∑ i, ∑ j, inverseMetric F p i j * v i * v j := by
              rw [inverseMetric_eq_diagonal, diag_quad]
      closed_upper_bound := fun p hp v => by
        calc ∑ i, ∑ j, inverseMetric F p i j * v i * v j
            = ∑ i, diagFun F p i * (v i) ^ 2 := by
              rw [inverseMetric_eq_diagonal, diag_quad]
          _ ≤ ∑ i, Λ * (v i) ^ 2 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right
                ((entry_bounds F A i hp).2.trans
                  (Finset.le_sup' (entryHi F A) (Finset.mem_univ i))) (sq_nonneg _)
          _ = Λ * ∑ i, (v i) ^ 2 := by rw [Finset.mul_sum]
          _ = Λ * ‖v‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq] }

private theorem matrix_pin (A : LocalBall (KPCuspLogShape.dimension F * 3)) :
    (chartCoefficients F A).data.matrix =
      (fun p => Matrix.diagonal (fun j =>
        let ik := finProdFinEquiv.symm j
        if ik.2 = 2 then 1 else Real.exp (2 * (coordinates F p ik.1).2))) := by
  funext p
  rw [show (chartCoefficients F A).data.matrix = inverseMetric F from
    (chartCoefficients F A).matrix_exact, inverseMetric_eq_diagonal F p]
  apply congrArg Matrix.diagonal
  funext j
  simp only [diagFun, coordinates_snd]

private theorem restriction_section
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U)
    (s : BorelL2Sections F ζ hζ U R P H)
    (hs : sectorLineIsometry F ζ hζ U R P H u = mk F ζ hζ U R P H s) :
    ∀ᵐ p ∂volume.restrict A.carrier,
      restriction F ζ hζ U R P H i x O m A hA u p =
        (liftFrame F ζ hζ U (coordinates F p)
          (phaseCoefficient F ζ hζ U R P H s.val i m (coordinates F p)) : ℂ) := by
  let f := (borelS F ζ hζ U R P H).symm s
  have hf : scalarEmbedding F ζ hζ U R P H f = u := by
    apply (sectorLineIsometry F ζ hζ U R P H).injective
    change sectorLineIsometry F ζ hζ U R P H
      (toSector F ζ hζ U R P H (borelS F ζ hζ U R P H f)) = _
    rw [sectorLineIsometry_toSector, show borelS F ζ hζ U R P H f = s from
      (borelS F ζ hζ U R P H).apply_symm_apply s, hs]
  have ha := restriction_representative F ζ hζ U R P H i x O m A hA u f hf
  have hS : KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f.val = s.val :=
    congrArg Subtype.val ((borelS F ζ hζ U R P H).apply_symm_apply s)
  change _ =ᵐ[_] (fun p => (liftFrame F ζ hζ U (coordinates F p)
    (phaseCoefficient F ζ hζ U R P H (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H f.val)
      i m (coordinates F p)) : ℂ)) at ha
  filter_upwards [ha] with p hp
  rw [hS] at hp
  exact hp

private theorem value_stabilizer
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (ξ : IntegerSobolev A 1)
    (hξ : KPContLocalEnergy.value ξ = restriction F ζ hζ U R P H i x O m A hA u)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x) :
    ∀ᵐ p ∂volume.restrict
      (A.carrier ∩ overlapCoordinate F ζ hζ U R P H i σ.val ⁻¹' A.carrier),
      KPContLocalEnergy.value ξ (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) *
          KPContLocalEnergy.value ξ p := by
  rw [hξ]
  exact (restrictionFamily F ζ hζ U R P H).stabilizer i x O m A hA σ u

private theorem ballLp_locallyIntegrable {n : ℕ} (B : LocalBall n) (u : BallL2 B) :
    LocallyIntegrableOn u B.carrier (volume.restrict B.carrier) := by
  apply (locallyIntegrableOn_iff (μ := volume.restrict B.carrier)
    (f := (fun x => u x)) (s := B.carrier) B.toOpens.isOpen.isLocallyClosed).2
  intro K hK hKc
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKc.measure_ne_top
  change Integrable _ ((volume.restrict B.carrier).restrict K)
  rw [Measure.restrict_restrict hKc.measurableSet, Set.inter_eq_left.mpr hK]
  exact ((Lp.memLp u).mono_measure (Measure.restrict_mono hK le_rfl)).integrable (by norm_num)

private theorem weakDerivative_unique {n k : ℕ} (B : LocalBall n) (α : MultiIndex n k)
    (u₁ u₂ d₁ d₂ : BallL2 B)
    (hu : u₁ =ᵐ[volume.restrict B.carrier] u₂)
    (h₁ : IsWeakDerivative B α u₁ d₁) (h₂ : IsWeakDerivative B α u₂ d₂) : d₁ = d₂ := by
  have hi₁ := ballLp_locallyIntegrable B d₁
  have hi₂ := ballLp_locallyIntegrable B d₂
  have hz : ∀ᵐ x ∂volume.restrict B.carrier, x ∈ B.carrier → d₁ x - d₂ x = 0 := by
    apply Metric.isOpen_ball.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hi₁.sub hi₂)
    intro φ hφ hφc hφs
    have hcast : ContDiff ℝ ∞ (fun x => (φ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    have hsupp : tsupport (fun x => (φ x : ℂ)) = tsupport φ := by
      unfold tsupport
      congr 1
      ext x
      simp
    let ψ : TestFunction B.toOpens ℂ ⊤ :=
      ⟨fun x => (φ x : ℂ), hcast, by change IsCompact _; rw [hsupp]; exact hφc,
        hsupp ▸ hφs⟩
    let ψR : TestFunction B.toOpens ℝ ⊤ := ⟨φ, hφ, hφc, hφs⟩
    have heq : (∫ x in B.carrier, d₁ x * ψ x) = ∫ x in B.carrier, d₂ x * ψ x := by
      apply mul_left_cancel₀ (pow_ne_zero α.degree (by norm_num : (-1 : ℂ) ≠ 0))
      rw [← h₁ ψ, ← h₂ ψ]
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      rw [hx]
    have heq' : (∫ x in B.carrier, φ x • d₁ x) = ∫ x in B.carrier, φ x • d₂ x := by
      simpa only [show (fun x => ψ x) = (fun x => (φ x : ℂ)) from rfl,
        Complex.real_smul, mul_comm] using heq
    change (∫ x in B.carrier, ψR x • (d₁ x - d₂ x)) = 0
    simp only [smul_sub]
    rw [integral_sub (ψR.integrable_smul hi₁) (ψR.integrable_smul hi₂)]
    change (∫ x in B.carrier, φ x • d₁ x) - (∫ x in B.carrier, φ x • d₂ x) = 0
    rw [heq', sub_self]
  apply Lp.ext
  filter_upwards [hz, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx hxB
  exact sub_eq_zero.mp (hx hxB)

private theorem derivatives_smaller_ball {n k : ℕ} (A B : LocalBall n)
    (hBA : B.carrier ⊆ A.carrier) (ξA : IntegerSobolev A k) (ξB : IntegerSobolev B k)
    (hvalue : ∀ᵐ p ∂volume.restrict B.carrier,
      KPContLocalEnergy.value ξB p = KPContLocalEnergy.value ξA p) :
    ∀ α : MultiIndex n k, ∀ᵐ p ∂volume.restrict B.carrier,
      ξB.derivatives α p = ξA.derivatives α p := by
  obtain ⟨ξR, hR, _⟩ := KPContLocalEnergy.SobolevEnergyEstimates.restrict_integerSobolev B A hBA ξA
  have hzero : ξB.derivatives (KPContLocalEnergy.zeroIndex n k) =ᵐ[volume.restrict B.carrier]
      ξR.derivatives (KPContLocalEnergy.zeroIndex n k) :=
    by
      filter_upwards [hvalue, hR (KPContLocalEnergy.zeroIndex n k)] with p hp hRp
      exact hp.trans hRp.symm
  intro α
  have heq := weakDerivative_unique B α _ _ _ _ hzero
    (ξB.weak_derivatives α) (ξR.weak_derivatives α)
  rw [heq]
  exact hR α

private theorem actual_derivatives_smaller_ball
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A B : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (hB : KPContLocalCubeEmbedding.closedCarrier B ⊆ chartDomain F ζ hζ U R P H i x O)
    (u : KPContSectorClosedLpSubspace.H F ζ hζ R U) (ξA : IntegerSobolev A 1)
    (ξB : IntegerSobolev B 1)
    (hξA : KPContLocalEnergy.value ξA = restriction F ζ hζ U R P H i x O m A hA u)
    (hξB : KPContLocalEnergy.value ξB = restriction F ζ hζ U R P H i x O m B hB u)
    (hBA : B.carrier ⊆ A.carrier) :
    ∀ α : MultiIndex (KPCuspLogShape.dimension F * 3) 1,
      ∀ᵐ p ∂volume.restrict B.carrier, ξB.derivatives α p = ξA.derivatives α p := by
  apply derivatives_smaller_ball A B hBA ξA ξB
  rw [hξA, hξB]
  exact restriction_smaller_ball F ζ hζ U R P H i x O m B A hB hA hBA u

variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
variable (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U
  F ζ hζ U R P H μG hμG hR realization

structure SolutionFamily where
  coefficients : ∀ A : LocalBall (KPCuspLogShape.dimension F * 3), ChartCoefficients F A

  differential_on_tests : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H),
    ∀ᵐ p ∂volume.restrict A.carrier,
      restriction F ζ hζ U R P H i x O m A hA
        (KPContActualSectorTestEmbeddings.iota
          (KPContActualSectorTestDifferentialDescent.δ_U
            (KPContActualSectorTestDifferentialDescent.D_U f))) p =
      KPContLocalEnergy.divergenceOperator (coefficients A).data
        (fun q => (liftFrame F ζ hζ U (coordinates F q)
          (phaseCoefficient F ζ hζ U R P H
            (KPContActualSectorSmoothTestModules.scalarSections f) i m
              (coordinates F q)) : ℂ)) p
  xi : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (u : (Δ).domain) (z : ℂ), IntegerSobolev A 1
  rhs : ∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (u : (Δ).domain) (z : ℂ), BallL2 A
  value_restriction : ∀ i x O m A hA u z,
    KPContLocalEnergy.value (xi i x O m A hA u z) =
      restriction F ζ hζ U R P H i x O m A hA u.val
  rhs_restriction : ∀ i x O m A hA u z,
    rhs i x O m A hA u z =
      restriction F ζ hζ U R P H i x O m A hA ((Δ) u - z • u.val)
  weak_equation : ∀ i x O m A hA u z,
    KPContLocalEnergy.WeakEquation (coefficients A).data z
      (xi i x O m A hA u z) (rhs i x O m A hA u z)

  stabilizer : ∀ i x O m A hA u z
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x),
    ∀ᵐ p ∂volume.restrict
      (A.carrier ∩ overlapCoordinate F ζ hζ U R P H i σ.val ⁻¹' A.carrier),
      KPContLocalEnergy.value (xi i x O m A hA u z)
          (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) *
          KPContLocalEnergy.value (xi i x O m A hA u z) p
  smaller_ball : ∀ i x O m A B hA hB u z, B.carrier ⊆ A.carrier →
    ∀ α : MultiIndex (KPCuspLogShape.dimension F * 3) 1,
    ∀ᵐ p ∂volume.restrict B.carrier,
      (xi i x O m B hB u z).derivatives α p =
        (xi i x O m A hA u z).derivatives α p
  smaller_ball_rhs : ∀ i x O m A B hA hB u z, B.carrier ⊆ A.carrier →
    ∀ᵐ p ∂volume.restrict B.carrier,
      rhs i x O m B hB u z p = rhs i x O m A hA u z p

  source_representative : ∀ i x O m A hA u z
    (f : BorelL2Scalars F ζ hζ U R),
    scalarEmbedding F ζ hζ U R P H f = ((Δ) u - z • u.val) →
    ∀ᵐ p ∂volume.restrict A.carrier,
      rhs i x O m A hA u z p = frameCoefficient F ζ hζ U R P H f.val i m p

  smooth_local_source : ∀ i x O m A hA u z
    (s : BorelL2Sections F ζ hζ U R P H)
    (localH : Space (KPCuspLogShape.dimension F * 3) → ℂ),
    sectorLineIsometry F ζ hζ U R P H ((Δ) u - z • u.val) = mk F ζ hζ U R P H s →
    ContDiffOn ℝ (⊤ : ℕ∞) localH (chartDomain F ζ hζ U R P H i x O) →
    (∀ᵐ p ∂volume.restrict A.carrier, localH p =
      (liftFrame F ζ hζ U (coordinates F p)
        (phaseCoefficient F ζ hζ U R P H s.val i m (coordinates F p)) : ℂ)) →
    ∀ᵐ p ∂volume.restrict A.carrier, rhs i x O m A hA u z p = localH p

end DedekindZetaZeroFree.KPContActualFriedrichsWeakChart

namespace DedekindZetaZeroFree

open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry

theorem kp_cont_actual_friedrichs_weak_chart
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    Nonempty (KPContActualFriedrichsWeakChart.SolutionFamily
      F ζ hζ U R P H μG hμG hR realization) := by
  classical
  let Δ := KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization
  let coeffs : ∀ A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3),
      KPContActualFriedrichsWeakChart.ChartCoefficients F A :=
    fun A => KPContActualFriedrichsWeakChart.chartCoefficients F A
  have hpin : ∀ A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3),
      (coeffs A).data.matrix =
        (fun p => Matrix.diagonal (fun j =>
          let ik := finProdFinEquiv.symm j
          if ik.2 = 2 then 1 else
            Real.exp (2 * (KPContActualChartRestrictionDensity.coordinates F p ik.1).2))) := by
    intro A
    exact KPContActualFriedrichsWeakChart.matrix_pin F A
  let xi : ∀ (i : Fin (H.atlas U).componentCount)
      (x : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U)
      (A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3))
      (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆
        KPContActualChartRestrictionDensity.chartDomain F ζ hζ U R P H i x O)
      (u : (Δ).domain) (z : ℂ), KPContLocalNorm.IntegerSobolev A 1 :=
    fun i x O m A hA u z =>
      (KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H μG hμG hR realization
        i x O m A hA (coeffs A).data (coeffs A).density_exact (hpin A) u z).choose
  let rhs : ∀ (i : Fin (H.atlas U).componentCount)
      (x : KPContSectorCoveredQuotientVocabulary.SymmetricSpace F)
      (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
      (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U)
      (A : KPContLocalNorm.LocalBall (KPCuspLogShape.dimension F * 3))
      (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆
        KPContActualChartRestrictionDensity.chartDomain F ζ hζ U R P H i x O)
      (u : (Δ).domain) (z : ℂ), KPContLocalNorm.BallL2 A :=
    fun i x O m A hA u z =>
      KPContActualChartRestrictionDensity.restriction F ζ hζ U R P H i x O m A hA
        ((Δ) u - z • u.val)
  refine ⟨coeffs, ?_, xi, rhs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i x O m A hA f
    exact KPContFriedrichsChartTestDifferential.differential_on_tests F ζ hζ U R P H
      μG hμG hR realization i x O m A hA (coeffs A).data (coeffs A).density_exact
      (hpin A) f
  · intro i x O m A hA u z
    exact (KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H μG hμG hR realization
      i x O m A hA (coeffs A).data (coeffs A).density_exact (hpin A) u z).choose_spec.1
  · intro i x O m A hA u z
    rfl
  · intro i x O m A hA u z
    exact (KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H μG hμG hR realization
      i x O m A hA (coeffs A).data (coeffs A).density_exact (hpin A) u z).choose_spec.2
  · intro i x O m A hA u z σ
    exact KPContActualFriedrichsWeakChart.value_stabilizer F ζ hζ U R P H i x O m A hA u.val
      (xi i x O m A hA u z)
      ((KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H μG hμG hR realization
        i x O m A hA (coeffs A).data (coeffs A).density_exact (hpin A) u z).choose_spec.1)
      σ
  · intro i x O m A B hA hB u z hBA α
    exact KPContActualFriedrichsWeakChart.actual_derivatives_smaller_ball F ζ hζ U R P H
      i x O m A B hA hB u.val (xi i x O m A hA u z) (xi i x O m B hB u z)
      ((KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H μG hμG hR realization
        i x O m A hA (coeffs A).data (coeffs A).density_exact (hpin A) u z).choose_spec.1)
      ((KPContFriedrichsChartVariational.exists_xi F ζ hζ U R P H μG hμG hR realization
        i x O m B hB (coeffs B).data (coeffs B).density_exact (hpin B) u z).choose_spec.1)
      hBA α
  · intro i x O m A B hA hB u z hBA
    exact KPContActualChartRestrictionDensity.restriction_smaller_ball F ζ hζ U R P H i x O m B A hB hA hBA ((Δ) u - z • u.val)
  · intro i x O m A hA u z f hf
    exact KPContActualChartRestrictionDensity.restriction_representative F ζ hζ U R P H i x O m A hA ((Δ) u - z • u.val) f hf
  · intro i x O m A hA u z s localH hs hcont hloc
    filter_upwards [KPContActualFriedrichsWeakChart.restriction_section F ζ hζ U R P H i x O m A hA
      ((Δ) u - z • u.val) s hs, hloc] with p h1 h2
    rw [h1, h2]

end DedekindZetaZeroFree

end
