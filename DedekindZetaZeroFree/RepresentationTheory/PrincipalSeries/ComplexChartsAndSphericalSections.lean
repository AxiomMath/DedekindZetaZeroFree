module

public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.Topology.Algebra.Group.Units
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.GlobalSmoothJetLimits
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.TwoChartJetBounds
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.JointActionContinuity
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.TwoChartReconstruction
public import Mathlib.LinearAlgebra.Projectivization.Basic

@[expose] public section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts

open KPCplxCharacterHaar Set
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable def complexAbs (z : ℂ) : ℝ := ‖z‖ ^ 2

noncomputable def upperTriangular (a d : ℂˣ) (b : ℂ) : ComplexGL2 :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℂ), b; 0, (d : ℂ)] (by
      simpa [Matrix.det_fin_two] using mul_ne_zero a.ne_zero d.ne_zero)

noncomputable def inductionWeight (s : ℝ) (a d : ℂˣ) : ℝ :=
  Real.rpow (complexAbs ((a : ℂ) / (d : ℂ))) (1 / 2 + s)

noncomputable def openCoordinate (f : ComplexGL2 → ℂ) (x : ℂ) : ℂ :=
  f (weyl * upperUnipotent x)

noncomputable def infinityCoordinate (f : ComplexGL2 → ℂ) (u : ℂ) : ℂ :=
  f (lowerUnipotent u)

noncomputable def transitionWeight (s : ℝ) (u : ℂ) : ℝ :=
  Real.rpow ‖u‖ (-2 * (1 + 2 * s))

def HasCovariance (s : ℝ) (f : ComplexGL2 → ℂ) : Prop :=
  ∀ (a d : ℂˣ) (b : ℂ) (g : ComplexGL2),
    f (upperTriangular a d b * g) = (inductionWeight s a d : ℂ) * f g

noncomputable def principalSeriesSubmodule (s : ℝ) : Submodule ℂ (ComplexGL2 → ℂ) where
  carrier := {f | HasCovariance s f ∧
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate f) ∧
      ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate f)}
  zero_mem' := by
    refine ⟨?_, contDiff_const, contDiff_const⟩
    intro a d b g
    simp
  add_mem' := by
    rintro f g ⟨hf, hf0, hfi⟩ ⟨hg, hg0, hgi⟩
    refine ⟨?_, hf0.add hg0, hfi.add hgi⟩
    intro a d b h
    simp only [Pi.add_apply, hf a d b h, hg a d b h, mul_add]
  smul_mem' := by
    rintro c f ⟨hf, hf0, hfi⟩
    refine ⟨?_, hf0.const_smul c, hfi.const_smul c⟩
    intro a d b h
    simp only [Pi.smul_apply, smul_eq_mul, hf a d b h]
    ring

abbrev PrincipalSeries (s : ℝ) := ↥(principalSeriesSubmodule s)

instance principalSeriesCoeFun (s : ℝ) : CoeFun (PrincipalSeries s) (fun _ => ComplexGL2 → ℂ) :=
  ⟨fun f => f.1⟩

noncomputable def matrixFunction (f : ComplexGL2 → ℂ)
    (g : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  if h : g.det ≠ 0 then f (Matrix.GeneralLinearGroup.mkOfDetNeZero g h) else 0

theorem principalSeries_mem_iff (s : ℝ) (f : ComplexGL2 → ℂ) :
    f ∈ principalSeriesSubmodule s ↔ HasCovariance s f ∧
      ContDiffOn ℝ ∞ (matrixFunction f) {g | g.det ≠ 0} := by
  constructor
  · rintro ⟨hc, ho, hi⟩
    exact ⟨hc, KPCplxPrincipalSeriesMatrixSmooth.covariant_matrix_smooth s f hc ho hi⟩
  · rintro ⟨hc, hm⟩
    exact ⟨hc, KPCplxPrincipalSeriesMatrixSmooth.matrix_smooth_charts f hm⟩

noncomputable abbrev positiveParameter : ℝ := 1 / 6

noncomputable abbrev negativeParameter : ℝ := -(1 / 6)

theorem central_invariance (s : ℝ) (f : PrincipalSeries s) (c : ℂˣ) (g : ComplexGL2) :
    f (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g) = f g := by
  have heq : Matrix.GeneralLinearGroup.scalar (Fin 2) c = upperTriangular c c 0 := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.coe_scalar, upperTriangular, Matrix.scalar]
  rw [heq, f.property.1]
  simp [inductionWeight, complexAbs]

theorem coordinate_transition (s : ℝ) (f : PrincipalSeries s) (u : ℂ) (hu : u ≠ 0) :
    infinityCoordinate f u = (transitionWeight s u : ℂ) * openCoordinate f u⁻¹ := by
  let d : ℂˣ := Units.mk0 u hu
  let a : ℂˣ := -(d⁻¹)
  have hm : lowerUnipotent u = upperTriangular a d 1 * (weyl * upperUnipotent u⁻¹) := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerUnipotent, upperTriangular, weyl, upperUnipotent, a, d,
        Matrix.mul_apply, Fin.sum_univ_two, hu]
  unfold infinityCoordinate
  rw [hm, f.property.1]
  congr 1
  simp only [inductionWeight, complexAbs, transitionWeight, a, d,
    Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mk0, norm_div, norm_neg, norm_inv]
  congr 1
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_two (‖u‖⁻¹ / ‖u‖), ← Real.rpow_mul (by positivity)]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hbase : ‖u‖⁻¹ / ‖u‖ = ‖u‖ ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (le_of_lt hn), Real.rpow_two]
    field_simp
  rw [hbase, ← Real.rpow_mul (by positivity)]
  congr 2
  ring

def ExtendsSmoothly (s : ℝ) (F : ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ F ∧ ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧
    ∀ (u : ℂ), u ≠ 0 → H u = (transitionWeight s u : ℂ) * F u⁻¹

 lemma row_nonzero (g : ComplexGL2) :
    (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
  have h := Matrix.GeneralLinearGroup.det_ne_zero g
  by_contra! hh
  apply h
  simp [Matrix.det_fin_two, hh.1, hh.2]
 lemma open_bruhat (g : ComplexGL2) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0) :
    ∃ (a d : ℂˣ) (b x : ℂ), g = upperTriangular a d b * (weyl * upperUnipotent x) := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := g
  have ha : M 0 1 - M 0 0 * (M 1 1 / M 1 0) ≠ 0 := by
    intro ha
    have hd := Matrix.GeneralLinearGroup.det_ne_zero g
    apply hd
    rw [Matrix.det_fin_two]
    change M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0
    have he := (sub_eq_zero.mp ha)
    rw [he]
    field_simp [show M 1 0 ≠ 0 from hg]
    ring
  refine ⟨Units.mk0 _ ha, Units.mk0 (M 1 0) hg, M 0 0, M 1 1 / M 1 0, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangular, weyl, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, M, hg, mul_div_cancel₀]
 lemma infinity_bruhat (g : ComplexGL2) (hg : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0) :
    ∃ (a d : ℂˣ) (b x : ℂ), g = upperTriangular a d b * lowerUnipotent x := by
  let M : Matrix (Fin 2) (Fin 2) ℂ := g
  have ha : M 0 0 - M 0 1 * (M 1 0 / M 1 1) ≠ 0 := by
    intro ha
    have hd := Matrix.GeneralLinearGroup.det_ne_zero g
    apply hd
    rw [Matrix.det_fin_two]
    change M 0 0 * M 1 1 - M 0 1 * M 1 0 = 0
    have he := (sub_eq_zero.mp ha)
    rw [he]
    field_simp [show M 1 1 ≠ 0 from hg]
    ring
  refine ⟨Units.mk0 _ ha, Units.mk0 (M 1 1) hg, M 0 1, M 1 0 / M 1 1, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangular, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two, M, hg, mul_div_cancel₀]

theorem openCoordinate_injective (s : ℝ) :
    Function.Injective (fun f : PrincipalSeries s => openCoordinate f) := by
  intro f h hfh
  change openCoordinate f = openCoordinate h at hfh
  have hinf : infinityCoordinate f = infinityCoordinate h := by
    funext u
    by_cases hu : u = 0
    · subst u
      have hc : Continuous (infinityCoordinate f - infinityCoordinate h) := f.property.2.2.continuous.sub h.property.2.2.continuous
      have he : ∀ u ∈ ({0}ᶜ : Set ℂ), (infinityCoordinate f - infinityCoordinate h) u = 0 := by
        intro u hu
        simp only [mem_compl_iff, mem_singleton_iff] at hu
        simp [Pi.sub_apply, coordinate_transition s f u hu, coordinate_transition s h u hu, hfh]
      have hd : Dense ({0}ᶜ : Set ℂ) := by exact dense_compl_singleton 0
      have hz := Continuous.ext_on hd hc continuous_const he
      exact sub_eq_zero.mp (congrFun hz 0)
    · rw [coordinate_transition s f u hu, coordinate_transition s h u hu, hfh]
  apply Subtype.ext
  funext g
  rcases row_nonzero g with hg | hg
  · rcases open_bruhat g hg with ⟨a, d, b, x, rfl⟩
    rw [f.property.1, h.property.1]
    exact congrArg ((inductionWeight s a d : ℂ) * ·) (congrFun hfh x)
  · rcases infinity_bruhat g hg with ⟨a, d, b, x, rfl⟩
    rw [f.property.1, h.property.1]
    exact congrArg ((inductionWeight s a d : ℂ) * ·) (congrFun hinf x)

theorem openCoordinate_range (s : ℝ) (F : ℂ → ℂ) :
    (∃ f : PrincipalSeries s, openCoordinate f = F) ↔ ExtendsSmoothly s F := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨f.property.2.1, infinityCoordinate f, f.property.2.2,
      fun u hu => coordinate_transition s f u hu⟩
  · rintro ⟨hF, H, hH, htrans⟩
    let f := KPCplxPrincipalSeriesReconstruction.reconstruct s F H
    have ho : openCoordinate f = F :=
      KPCplxPrincipalSeriesReconstruction.reconstruct_open s F H
    have hi : infinityCoordinate f = H :=
      KPCplxPrincipalSeriesReconstruction.reconstruct_infinity s F H htrans
    have hc : HasCovariance s f :=
      KPCplxPrincipalSeriesReconstruction.reconstruct_covariance s F H
    have hm : f ∈ principalSeriesSubmodule s := by
      exact ⟨hc, ho.symm ▸ hF, hi.symm ▸ hH⟩
    exact ⟨⟨f, hm⟩, ho⟩

abbrev ComplexProjectiveLine := Projectivization ℂ (Fin 2 → ℂ)

noncomputable def projectiveOpen (x : ℂ) : ComplexProjectiveLine :=
  Projectivization.mk ℂ ![1, x] (by
    intro h
    have := congrFun h 0
    simpa using this)

noncomputable def projectiveInfinity (u : ℂ) : ComplexProjectiveLine :=
  Projectivization.mk ℂ ![u, 1] (by
    intro h
    have := congrFun h 1
    simpa using this)

noncomputable instance projectiveLineTopology : TopologicalSpace ComplexProjectiveLine :=
  TopologicalSpace.coinduced
    (Sum.elim projectiveOpen projectiveInfinity : ℂ ⊕ ℂ → ComplexProjectiveLine)
    inferInstance

theorem projective_chart_cover (p : ComplexProjectiveLine) :
    (∃ x : ℂ, p = projectiveOpen x) ∨ (∃ u : ℂ, p = projectiveInfinity u) := by
  induction p using Projectivization.ind with
  | h v hv =>
    by_cases h0 : v 0 = 0
    · right
      have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> simp_all
      refine ⟨v 0 / v 1, ?_⟩
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      use v 1
      ext i
      fin_cases i <;> simp [projectiveInfinity, h1, h0]
    · left
      refine ⟨v 1 / v 0, ?_⟩
      apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
      use v 0
      ext i
      fin_cases i <;> simp [projectiveOpen, h0, mul_div_cancel₀]

theorem projective_chart_transition (u : ℂ) (hu : u ≠ 0) :
    projectiveInfinity u = projectiveOpen u⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  use u
  ext i
  fin_cases i <;> simp [projectiveInfinity, projectiveOpen, hu]

noncomputable def chartSeminormValue (s : ℝ) (n : ℕ) (f : PrincipalSeries s) : ℝ :=
  max (sSup ((fun x : ℂ => ‖iteratedFDeriv ℝ n (openCoordinate f) x‖) ''
      Metric.closedBall (0 : ℂ) 1))
    (sSup ((fun u : ℂ => ‖iteratedFDeriv ℝ n (infinityCoordinate f) u‖) ''
      Metric.closedBall (0 : ℂ) 1))

noncomputable def chartSeminorm (s : ℝ) (n : ℕ) : Seminorm ℂ (PrincipalSeries s) where
  toFun := chartSeminormValue s n
  map_zero' := by
    change max (KPCplxPrincipalSeriesJets.jetSup n 0) (KPCplxPrincipalSeriesJets.jetSup n 0) = 0
    simp [KPCplxPrincipalSeriesJets.jetZero]
  add_le' := by
    intro f g
    apply max_le
    · exact (KPCplxPrincipalSeriesJets.jetAdd n _ _ f.property.2.1 g.property.2.1).trans
        (add_le_add (le_max_left _ _) (le_max_left _ _))
    · exact (KPCplxPrincipalSeriesJets.jetAdd n _ _ f.property.2.2 g.property.2.2).trans
        (add_le_add (le_max_right _ _) (le_max_right _ _))
  neg' := by
    intro f
    change max (KPCplxPrincipalSeriesJets.jetSup n (-openCoordinate f))
      (KPCplxPrincipalSeriesJets.jetSup n (-infinityCoordinate f)) = _
    rw [KPCplxPrincipalSeriesJets.jetNeg, KPCplxPrincipalSeriesJets.jetNeg]
    rfl
  smul' := by
    intro c f
    change max (KPCplxPrincipalSeriesJets.jetSup n (c • openCoordinate f))
      (KPCplxPrincipalSeriesJets.jetSup n (c • infinityCoordinate f)) = _
    rw [KPCplxPrincipalSeriesJets.jetSmul n _ f.property.2.1,
      KPCplxPrincipalSeriesJets.jetSmul n _ f.property.2.2]
    exact (mul_max_of_nonneg _ _ (norm_nonneg c)).symm

noncomputable instance principalSeriesTopology (s : ℝ) : TopologicalSpace (PrincipalSeries s) :=
  (SeminormFamily.moduleFilterBasis (chartSeminorm s)).topology

theorem topology_withSeminorms (s : ℝ) : WithSeminorms (chartSeminorm s) :=
  ⟨rfl⟩

noncomputable instance principalSeriesTopologicalAddGroup (s : ℝ) :
    IsTopologicalAddGroup (PrincipalSeries s) :=
  (topology_withSeminorms s).isTopologicalAddGroup

noncomputable instance principalSeriesUniformity (s : ℝ) : UniformSpace (PrincipalSeries s) :=
  IsTopologicalAddGroup.rightUniformSpace (PrincipalSeries s)

theorem principalSeries_t2 (s : ℝ) : T2Space (PrincipalSeries s) := by
  open KPCplxPrincipalSeriesJets in
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  have ht1 : T1Space (PrincipalSeries s) := htop.T1_of_separating (by
    intro f hf
    refine ⟨0, ?_⟩
    intro hz
    apply hf
    have ho : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, openCoordinate f z = 0 := by
      intro z hzball
      have hle := (jetLe 0 _ f.property.2.1 z hzball).trans
        (le_max_left (jetSup 0 (openCoordinate f)) (jetSup 0 (infinityCoordinate f)))
      change ‖iteratedFDeriv ℝ 0 (openCoordinate f) z‖ ≤ chartSeminorm s 0 f at hle
      rw [hz, norm_iteratedFDeriv_zero] at hle
      exact norm_le_zero_iff.mp hle
    have hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, infinityCoordinate f z = 0 := by
      intro z hzball
      have hle := (jetLe 0 _ f.property.2.2 z hzball).trans
        (le_max_right (jetSup 0 (openCoordinate f)) (jetSup 0 (infinityCoordinate f)))
      change ‖iteratedFDeriv ℝ 0 (infinityCoordinate f) z‖ ≤ chartSeminorm s 0 f at hle
      rw [hz, norm_iteratedFDeriv_zero] at hle
      exact norm_le_zero_iff.mp hle
    apply openCoordinate_injective s
    funext z
    change openCoordinate f z = 0
    by_cases hzball : z ∈ Metric.closedBall (0 : ℂ) 1
    · exact ho z hzball
    have hzn : z ≠ 0 := by intro h; subst z; simp at hzball
    have hzi : z⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right] at hzball ⊢
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hzball))
    have htr := coordinate_transition s f z⁻¹ (inv_ne_zero hzn)
    rw [inv_inv, hi _ hzi] at htr
    have hw : (transitionWeight s z⁻¹ : ℂ) ≠ 0 := by
      apply Complex.ofReal_ne_zero.mpr
      exact ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hzn)) _)
    exact (mul_eq_zero.mp htr.symm).resolve_left hw)
  infer_instance

theorem principalSeries_metrizable (s : ℝ) : TopologicalSpace.MetrizableSpace (PrincipalSeries s) := by
  have ht : FirstCountableTopology (PrincipalSeries s) :=
    (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).firstCountableTopology
  have hu : (uniformity (PrincipalSeries s)).IsCountablyGenerated := by
    change (Filter.comap (fun p : PrincipalSeries s × PrincipalSeries s => p.2 + -p.1)
      (nhds (0 : PrincipalSeries s))).IsCountablyGenerated
    infer_instance
  have hs := principalSeries_t2 s
  exact UniformSpace.metrizableSpace

open Filter Topology KPCplxPrincipalSeriesJets

private lemma seq_jet_cauchy (s : ℝ) (f : ℕ → PrincipalSeries s) (hc : CauchySeq f) :
    ∀ n : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, chartSeminorm s n (f i - f j) < ε := by
  have ht : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  haveI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  have hd := (IsUniformAddGroup.cauchy_map_iff_tendsto atTop f).mp hc |>.2
  intro n ε hε
  have h := ((ht.continuous_seminorm n).tendsto 0).comp hd
  have he : ∀ᶠ p : ℕ × ℕ in atTop ×ˢ atTop, chartSeminorm s n (f p.1 - f p.2) < ε := by
    exact h.eventually (gt_mem_nhds (by simpa using hε))
  rw [prod_atTop_atTop_eq, eventually_atTop_prod_self'] at he
  exact he
private lemma finite_jet_cauchy (s : ℝ) (f : ℕ → PrincipalSeries s) (hc : CauchySeq f)
    (n : ℕ) : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
    ∑ k ∈ Finset.range (n+1), (jetSup k (openCoordinate (f i) - openCoordinate (f j)) +
      jetSup k (infinityCoordinate (f i) - infinityCoordinate (f j))) < ε := by
  intro ε hε
  have he : 0 < ε / (2 * (n+1 : ℝ)) := by positivity
  have hn k := seq_jet_cauchy s f hc k _ he
  choose N hN using hn
  let B := (Finset.range (n+1)).sup N
  refine ⟨B, ?_⟩
  intro i hi j hj
  have hle k (hk : k ∈ Finset.range (n+1)) : chartSeminorm s k (f i - f j) < ε / (2 * (n+1 : ℝ)) :=
    hN k i ((Finset.le_sup hk).trans hi) j ((Finset.le_sup hk).trans hj)
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), 2 * chartSeminorm s k (f i - f j) := by
      apply Finset.sum_le_sum
      intro k hk
      change jetSup k (openCoordinate (f i - f j)) + jetSup k (infinityCoordinate (f i - f j)) ≤ _
      exact (add_le_add (le_max_left _ _) (le_max_right _ _)).trans_eq (two_mul _).symm
    _ < ∑ k ∈ Finset.range (n+1), 2 * (ε / (2 * (n+1 : ℝ))) := by
      apply Finset.sum_lt_sum
      · intro k hk
        exact (mul_lt_mul_of_pos_left (hle k hk) (by norm_num)).le
      · exact ⟨0, by simp, mul_lt_mul_of_pos_left (hle 0 (by simp)) (by norm_num)⟩
    _ = ε := by simp; field_simp
private lemma open_transition (s : ℝ) (f : PrincipalSeries s) (z : ℂ) (hz : z ≠ 0) :
    openCoordinate f z = (Real.rpow ‖z‖ (-2*(1+2*s)) : ℂ) * infinityCoordinate f z⁻¹ := by
  have h := coordinate_transition s f z⁻¹ (inv_ne_zero hz)
  rw [inv_inv] at h
  have he : transitionWeight s z⁻¹ = (transitionWeight s z)⁻¹ := by
    simp only [transitionWeight, norm_inv, Real.rpow_eq_pow]
    exact Real.inv_rpow (norm_nonneg z) _
  rw [he] at h
  have hw : (transitionWeight s z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _))
  change openCoordinate f z = (transitionWeight s z : ℂ) * infinityCoordinate f z⁻¹
  rw [h, Complex.ofReal_inv, mul_inv_cancel_left₀ hw]

theorem principalSeries_complete (s : ℝ) : CompleteSpace (PrincipalSeries s) := by
  open Filter Topology KPCplxPrincipalSeriesJets in
  have ht : FirstCountableTopology (PrincipalSeries s) := (show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).firstCountableTopology
  have hu : (uniformity (PrincipalSeries s)).IsCountablyGenerated := by
    change (Filter.comap (fun p : PrincipalSeries s × PrincipalSeries s => p.2 + -p.1)
      (nhds (0 : PrincipalSeries s))).IsCountablyGenerated
    infer_instance
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro f hc
  let F := fun i => openCoordinate (f i)
  let H := fun i => infinityCoordinate (f i)
  have hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i) := fun i => (f i).property.2.1
  have hH : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (H i) := fun i => (f i).property.2.2
  have hfC n R := KPCplxPrincipalSeriesTransitionBounds.uniformCauchy_on_enlargedBall
    (-2*(1+2*s)) R n F H hF hH (fun i z hz => open_transition s (f i) z hz)
    (finite_jet_cauchy s f hc n)
  have hhC n R := KPCplxPrincipalSeriesTransitionBounds.uniformCauchy_on_enlargedBall
    (-2*(1+2*s)) R n H F hH hF (fun i z hz => coordinate_transition s (f i) z hz) (by
      simpa only [add_comm] using finite_jet_cauchy s f hc n)
  obtain ⟨G, hG, hGl⟩ := KPCplxPrincipalSeriesGlobalLimits.global_smooth_jet_limit F hF hfC
  obtain ⟨J, hJ, hJl⟩ := KPCplxPrincipalSeriesGlobalLimits.global_smooth_jet_limit H hH hhC
  have hgpt (z : ℂ) : Tendsto (fun i => F i z) atTop (𝓝 (G z)) := by
    have h := (hGl 0 (‖z‖+1)).tendsto_at (show z ∈ Metric.closedBall 0 (‖z‖+1) by
      simp only [Metric.mem_closedBall, dist_zero_right]; linarith)
    exact (continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.tendsto _ |>.comp h |>.congr' (by
      filter_upwards [] with i
      simp [iteratedFDeriv_zero_eq_comp])
  have hjpt (z : ℂ) : Tendsto (fun i => H i z) atTop (𝓝 (J z)) := by
    have h := (hJl 0 (‖z‖+1)).tendsto_at (show z ∈ Metric.closedBall 0 (‖z‖+1) by
      simp only [Metric.mem_closedBall, dist_zero_right]; linarith)
    exact (continuousMultilinearCurryFin0 ℝ ℂ ℂ).continuous.tendsto _ |>.comp h |>.congr' (by
      filter_upwards [] with i
      simp [iteratedFDeriv_zero_eq_comp])
  have htrans : ∀ z : ℂ, z ≠ 0 → J z = (transitionWeight s z : ℂ) * G z⁻¹ := by
    intro z hz
    have hl := (hgpt z⁻¹).const_mul (transitionWeight s z : ℂ)
    have he : (fun i => (transitionWeight s z : ℂ) * F i z⁻¹) = fun i => H i z := by
      funext i
      exact (coordinate_transition s (f i) z hz).symm
    rw [he] at hl
    exact tendsto_nhds_unique (hjpt z) hl
  obtain ⟨g, hg⟩ := (openCoordinate_range s G).mpr ⟨hG, J, hJ, htrans⟩
  have hj : infinityCoordinate g = J := by
    apply Continuous.ext_on (dense_compl_singleton 0) g.property.2.2.continuous hJ.continuous
    intro z hz
    rw [coordinate_transition s g z (by simpa using hz), hg, htrans z (by simpa using hz)]
  refine ⟨g, ?_⟩
  rw [(show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).tendsto_nhds]
  intro n ε hε
  have hopen := (hGl n 1)
  have hinf := (hJl n 1)
  rw [Metric.tendstoUniformlyOn_iff] at hopen hinf
  have ho := hopen (ε/2) (by positivity)
  have hi := hinf (ε/2) (by positivity)
  filter_upwards [ho, hi] with i hiO hiI
  change max (jetSup n (openCoordinate (f i - g))) (jetSup n (infinityCoordinate (f i - g))) < ε
  have hbO : jetSup n (openCoordinate (f i - g)) ≤ ε/2 := by
    apply jetSupLe
    intro x hx
    change ‖iteratedFDeriv ℝ n (openCoordinate (f i) - openCoordinate g) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply ((hF i).of_le (by simp)).contDiffAt ((g.property.2.1).of_le (by simp)).contDiffAt, hg]
    exact (by simpa [dist_eq_norm, norm_sub_rev] using (hiO x hx).le)
  have hbI : jetSup n (infinityCoordinate (f i - g)) ≤ ε/2 := by
    apply jetSupLe
    intro x hx
    change ‖iteratedFDeriv ℝ n (infinityCoordinate (f i) - infinityCoordinate g) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply ((hH i).of_le (by simp)).contDiffAt ((g.property.2.2).of_le (by simp)).contDiffAt, hj]
    exact (by simpa [dist_eq_norm, norm_sub_rev] using (hiI x hx).le)
  exact (max_le hbO hbI).trans_lt (by linarith)

theorem principalSeries_locallyConvex (s : ℝ) : LocallyConvexSpace ℝ (PrincipalSeries s) := by
  have h : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  exact h.toLocallyConvexSpace

noncomputable def rightTranslate (s : ℝ) (g : ComplexGL2)
    (f : PrincipalSeries s) : PrincipalSeries s :=
  ⟨fun h => f (h * g), by
    apply (principalSeries_mem_iff s _).mpr
    refine ⟨?_, ?_⟩
    · intro a d b h
      dsimp only
      rw [mul_assoc, f.property.1]
    have hf := ((principalSeries_mem_iff s f).mp f.property).2
    have hc : ContDiff ℝ (⊤ : ℕ∞) (fun h : Matrix (Fin 2) (Fin 2) ℂ => h * (g : Matrix (Fin 2) (Fin 2) ℂ)) := by
      exact (LinearMap.mulRight ℝ (g : Matrix (Fin 2) (Fin 2) ℂ)).toContinuousLinearMap.contDiff
    have hmap : MapsTo (fun h : Matrix (Fin 2) (Fin 2) ℂ => h * (g : Matrix (Fin 2) (Fin 2) ℂ))
        {h | h.det ≠ 0} {h | h.det ≠ 0} := by
      intro h hh
      exact (Matrix.det_mul h (g : Matrix (Fin 2) (Fin 2) ℂ)).trans_ne (mul_ne_zero hh (Matrix.GeneralLinearGroup.det_ne_zero g))
    apply (hf.comp hc.contDiffOn hmap).congr
    intro h hh
    change matrixFunction (fun h => f (h * g)) h = matrixFunction f (h * (g : Matrix (Fin 2) (Fin 2) ℂ))
    have hh' : h.det ≠ 0 := hh
    have hm' : (h * (g : Matrix (Fin 2) (Fin 2) ℂ)).det ≠ 0 := hmap hh
    unfold matrixFunction
    split_ifs
    exact congrArg f (Units.ext rfl)⟩

noncomputable instance complexPGL2Topology : TopologicalSpace ComplexPGL2 :=
  TopologicalSpace.coinduced Matrix.ProjGenLinGroup.mk inferInstance

noncomputable def pi (s : ℝ) (g : ComplexPGL2) (f : PrincipalSeries s) : PrincipalSeries s :=
  Quotient.liftOn g (fun h : ComplexGL2 => rightTranslate s h f) (by
    intro a b hab
    have hab' : Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk b := Quotient.sound hab
    rcases Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hab' with ⟨c, hc⟩
    apply Subtype.ext
    funext h
    change f (h * a) = f (h * b)
    rw [← hc, ← mul_assoc, ← Matrix.GeneralLinearGroup.scalar_commute]
    exact (central_invariance s f c (h * a)).symm)

theorem pi_mk (s : ℝ) (g : ComplexGL2) (f : PrincipalSeries s) :
    pi s (Matrix.ProjGenLinGroup.mk g) f = rightTranslate s g f := by
  rfl

theorem pi_one (s : ℝ) (f : PrincipalSeries s) : pi s 1 f = f := by
  change rightTranslate s 1 f = f
  apply Subtype.ext
  funext g
  exact congrArg f (mul_one g)

theorem pi_mul (s : ℝ) (g h : ComplexPGL2) (f : PrincipalSeries s) :
    pi s (g * h) f = pi s g (pi s h f) := by
  induction g using Quotient.inductionOn with | h g =>
  induction h using Quotient.inductionOn with | h h =>
  apply Subtype.ext
  funext a
  exact congrArg f (mul_assoc a g h).symm

private lemma evaluation_principalSeries_barrelled (s : ℝ) : BarrelledSpace ℝ (PrincipalSeries s) := by
  letI := principalSeries_t2 s
  letI := principalSeries_metrizable s
  letI := principalSeries_complete s
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := htop.continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := ⟨by
    have hh := (Complex.continuous_ofReal.comp continuous_fst).smul (continuous_snd :
      Continuous (fun p : ℝ × PrincipalSeries s => p.2))
    change Continuous (fun p : ℝ × PrincipalSeries s => (algebraMap ℝ ℂ) p.1 • p.2) at hh
    simpa only [IsScalarTower.algebraMap_smul] using hh⟩
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI := IsUniformAddGroup.uniformity_countably_generated (α := PrincipalSeries s)
  infer_instance
 lemma evaluation_principalSeries_barrelled_complex (s : ℝ) : BarrelledSpace ℂ (PrincipalSeries s) := by
  letI := principalSeries_t2 s
  letI := principalSeries_metrizable s
  letI := principalSeries_complete s
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := htop.continuousSMul
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  letI := IsUniformAddGroup.uniformity_countably_generated (α := PrincipalSeries s)
  infer_instance
open KPCplxPrincipalSeriesEvaluationContinuity
 lemma evaluation_linearMap_continuous_of_point_evaluations (s t : ℝ)
    (T : PrincipalSeries s →ₗ[ℂ] PrincipalSeries t)
    (hT : ∀ g : ComplexGL2, Continuous (fun f => T f g)) : Continuous T := by
  letI : BarrelledSpace ℝ (PrincipalSeries s) := evaluation_principalSeries_barrelled s
  letI : BarrelledSpace ℂ (PrincipalSeries s) := evaluation_principalSeries_barrelled_complex s
  have htop : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  letI : ContinuousSMul ℂ (PrincipalSeries s) := htop.continuousSMul
  letI : ContinuousSMul ℝ (PrincipalSeries s) := ⟨by
    have hh := (Complex.continuous_ofReal.comp continuous_fst).smul (continuous_snd :
      Continuous (fun p : ℝ × PrincipalSeries s => p.2))
    change Continuous (fun p : ℝ × PrincipalSeries s => (algebraMap ℝ ℂ) p.1 • p.2) at hh
    simpa only [IsScalarTower.algebraMap_smul] using hh⟩
  letI : IsUniformAddGroup (PrincipalSeries s) := isUniformAddGroup_of_addCommGroup
  let O : PrincipalSeries s →ₗ[ℝ] (ℂ → ℂ) :=
    { toFun := fun f => openCoordinate (T f)
      map_add' := by intros; ext; simp [openCoordinate]
      map_smul' := by intros; ext; simp [openCoordinate] }
  let I : PrincipalSeries s →ₗ[ℝ] (ℂ → ℂ) :=
    { toFun := fun f => infinityCoordinate (T f)
      map_add' := by intros; ext; simp [infinityCoordinate]
      map_smul' := by intros; ext; simp [infinityCoordinate] }
  have ho := derivativeEvaluation_continuous O (fun f => (T f).property.2.1)
    (fun x => hT (weyl * upperUnipotent x))
  have hi := derivativeEvaluation_continuous I (fun f => (T f).property.2.2)
    (fun x => hT (lowerUnipotent x))
  have ht : WithSeminorms (chartSeminorm t) := ⟨rfl⟩
  apply ht.continuous_of_continuous_comp T
  intro n
  apply Seminorm.continuous_of_lowerSemicontinuous
  change LowerSemicontinuous (fun f => chartSeminormValue t n (T f))
  unfold chartSeminormValue
  apply LowerSemicontinuous.sup
  · apply closedDiscSup_lowerSemicontinuous
    · intro x; exact (ho n x).norm
    · intro f; exact ((T f).property.2.1.continuous_iteratedFDeriv (by simp)).norm
  · apply closedDiscSup_lowerSemicontinuous
    · intro x; exact (hi n x).norm
    · intro f; exact ((T f).property.2.2.continuous_iteratedFDeriv (by simp)).norm

private lemma evaluation_disc_eval_continuous (s : ℝ) (x : ℂ) (hx : x ∈ Metric.closedBall (0 : ℂ) 1)
    (north : Bool) : Continuous (fun f : PrincipalSeries s =>
      (if north then openCoordinate f else infinityCoordinate f) x) := by
  have ht : WithSeminorms (chartSeminorm s) := ⟨rfl⟩
  let O : PrincipalSeries s →ₗ[ℂ] ℂ :=
    { toFun := fun f => (if north then openCoordinate f else infinityCoordinate f) x
      map_add' := by intros; cases north <;> rfl
      map_smul' := by intros; cases north <;> rfl }
  apply ht.continuous_of_isBounded (norm_withSeminorms ℂ ℂ) (f := O)
  intro i
  refine ⟨{0}, 1, ?_⟩
  rw [Finset.sup_singleton, Seminorm.le_def]
  intro f
  change ‖(if north then openCoordinate f else infinityCoordinate f) x‖ ≤ _
  simp only [one_smul]
  cases north
  · have h := KPCplxPrincipalSeriesJets.jetLe 0 (infinityCoordinate f) f.property.2.2 x hx
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (le_max_right _ _)
  · have h := KPCplxPrincipalSeriesJets.jetLe 0 (openCoordinate f) f.property.2.1 x hx
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (le_max_left _ _)

private lemma evaluation_infinity_eval_continuous (s : ℝ) (x : ℂ) :
    Continuous (fun f : PrincipalSeries s => infinityCoordinate f x) := by
  by_cases hx : x ∈ Metric.closedBall (0 : ℂ) 1
  · exact evaluation_disc_eval_continuous s x hx false
  have hxn : x ≠ 0 := by intro h; subst x; simp at hx
  have hxi : x⁻¹ ∈ Metric.closedBall (0 : ℂ) 1 := by
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hx))
  exact (continuous_const.mul (evaluation_disc_eval_continuous s x⁻¹ hxi true)).congr
    (fun f => (coordinate_transition s f x hxn).symm)

private lemma evaluation_open_eval_continuous (s : ℝ) (x : ℂ) :
    Continuous (fun f : PrincipalSeries s => openCoordinate f x) := by
  by_cases hx : x = 0
  · subst x; exact evaluation_disc_eval_continuous s 0 (by simp) true
  have hw : (transitionWeight s x⁻¹ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr (inv_ne_zero hx)) _))
  apply (continuous_const.mul (evaluation_infinity_eval_continuous s x⁻¹)).congr
  intro f
  have h := coordinate_transition s f x⁻¹ (inv_ne_zero hx)
  rw [inv_inv] at h
  show (transitionWeight s x⁻¹ : ℂ)⁻¹ * infinityCoordinate f x⁻¹ = openCoordinate f x
  rw [h, ← mul_assoc, inv_mul_cancel₀ hw, one_mul]

 lemma evaluation_point_eval_continuous (s : ℝ) (g : ComplexGL2) :
    Continuous (fun f : PrincipalSeries s => f g) := by
  rcases row_nonzero g with hg | hg
  · rcases open_bruhat g hg with ⟨a,d,b,x,rfl⟩
    exact (continuous_const.mul (evaluation_open_eval_continuous s x)).congr
      (fun f => (f.property.1 a d b _).symm)
  · rcases infinity_bruhat g hg with ⟨a,d,b,x,rfl⟩
    exact (continuous_const.mul (evaluation_infinity_eval_continuous s x)).congr
      (fun f => (f.property.1 a d b _).symm)

private lemma evaluation_fixedg_continuous (s : ℝ) (g : ComplexGL2) : Continuous (rightTranslate s g) := by
  let T : PrincipalSeries s →ₗ[ℂ] PrincipalSeries s :=
    { toFun := rightTranslate s g
      map_add' := by intros; apply Subtype.ext; rfl
      map_smul' := by intros; apply Subtype.ext; rfl }
  exact evaluation_linearMap_continuous_of_point_evaluations s s T (fun h => evaluation_point_eval_continuous s (h*g))

abbrev OrbitMat := Matrix (Fin 2) (Fin 2) ℂ
noncomputable def orbit_mulL : OrbitMat →ₗ[ℝ] OrbitMat →L[ℝ] OrbitMat where
  toFun a := (LinearMap.mulLeft ℝ a).toContinuousLinearMap
  map_add' a b := by ext c i j; simp [Matrix.add_mul]
  map_smul' r a := by ext c i j; simp [Matrix.smul_mul]
noncomputable def orbit_mulCLM : OrbitMat →L[ℝ] OrbitMat →L[ℝ] OrbitMat := orbit_mulL.toContinuousLinearMap
noncomputable def selectedCoordinate (north : Bool) (f : ComplexGL2 → ℂ) : ℂ → ℂ :=
  if north then openCoordinate f else infinityCoordinate f

private lemma partial_jets_smooth {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (H : P → E → F) (U : Set P) (hU : IsOpen U)
    (hH : ∀ p ∈ U, ∀ z, ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry H) (p,z)) :
    ∀ n : ℕ, ∀ p ∈ U, ∀ z,
      ContDiffAt ℝ (⊤ : ℕ∞) (fun q : P × E => iteratedFDeriv ℝ n (H q.1) q.2) (p,z) := by
  intro n
  induction n with
  | zero =>
    intro p hp z
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (hH p hp z).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E F).symm : F →L[ℝ] E [×0]→L[ℝ] F)
  | succ n ih =>
    intro p hp z
    simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    let J : P → E → E [×n]→L[ℝ] F := fun p z => iteratedFDeriv ℝ n (H p) z
    have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
        (Function.uncurry (fun q : P × E => J q.1)) ((p,z),z) := by
      have hm : ContDiff ℝ (⊤ : ℕ∞) (fun q : (P × E) × E => (q.1.1,q.2)) := by fun_prop
      exact (ih p hp z).comp ((p,z),z) hm.contDiffAt
    have hder := hcomp.fderiv
      (g := fun q : P × E => q.2) contDiffAt_snd (m := (⊤ : ℕ∞)) (by simp)
    exact hder.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).symm :
        (E →L[ℝ] E [×n]→L[ℝ] F) →L[ℝ] E [×(n+1)]→L[ℝ] F)

private lemma matrix_locus_open :
    IsOpen {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0} := by
  have hdet : Continuous (fun m : Matrix (Fin 2) (Fin 2) ℂ => m.det) := by
    simp only [Matrix.det_fin_two]
    fun_prop
  exact isOpen_ne.preimage hdet

noncomputable def rawChart (north : Bool) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if north then !![0, 1; 1, z] else !![1, 0; z, 1]

private lemma rawChart_smooth (north : Bool) : ContDiff ℝ (⊤ : ℕ∞) (rawChart north) := by
  cases north <;>
    change ContDiff ℝ (⊤ : ℕ∞)
      (((Matrix.ofLinearEquiv ℝ : (Fin 2 → Fin 2 → ℂ) ≃ₗ[ℝ]
        Matrix (Fin 2) (Fin 2) ℂ).toLinearMap.toContinuousLinearMap) ∘ _)
  all_goals
    apply (((Matrix.ofLinearEquiv ℝ : (Fin 2 → Fin 2 → ℂ) ≃ₗ[ℝ]
      Matrix (Fin 2) (Fin 2) ℂ).toLinearMap.toContinuousLinearMap).contDiff).comp
    rw [contDiff_pi]; intro i; rw [contDiff_pi]; intro j
    fin_cases i <;> fin_cases j <;> simp [rawChart]
    all_goals first | exact contDiff_const | exact contDiff_id

private lemma rawChart_eq (north : Bool) (z : ℂ) : rawChart north z =
    ((if north then weyl * upperUnipotent z else lowerUnipotent z : ComplexGL2) :
      Matrix (Fin 2) (Fin 2) ℂ) := by
  cases north <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rawChart, weyl, upperUnipotent, lowerUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two]

private theorem evaluation_continuous_rightTranslate_chart_jets (s : ℝ) (n : ℕ) (f : PrincipalSeries s)
    (north : Bool) : Continuous (fun p : ComplexGL2 × ℂ => iteratedFDeriv ℝ n
      (selectedCoordinate north (rightTranslate s p.1 f).val) p.2) := by
  let H : Matrix (Fin 2) (Fin 2) ℂ → ℂ → ℂ :=
    fun m z => matrixFunction f (rawChart north z * m)
  have hH : ∀ m ∈ {m : Matrix (Fin 2) (Fin 2) ℂ | m.det ≠ 0}, ∀ z,
      ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry H) (m,z) := by
    intro m hm z
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun q : Matrix (Fin 2) (Fin 2) ℂ × ℂ =>
        rawChart north q.2 * q.1) := by
      exact ((orbit_mulCLM.contDiff.comp ((rawChart_smooth north).comp contDiff_snd)).clm_apply contDiff_fst)
    have hmem : (rawChart north z * m).det ≠ 0 := by
      rw [Matrix.det_mul, rawChart_eq]
      exact mul_ne_zero (Matrix.GeneralLinearGroup.det_ne_zero _) hm
    exact (((principalSeries_mem_iff s f).mp f.property).2 _ hmem).contDiffAt
      (matrix_locus_open.mem_nhds hmem) |>.comp (m,z) hs.contDiffAt
  have hjet := partial_jets_smooth H _ matrix_locus_open hH n
  have he (g : ComplexGL2) : H (g : Matrix (Fin 2) (Fin 2) ℂ) =
      selectedCoordinate north (rightTranslate s g f).val := by
    funext z
    dsimp only [H]
    rw [rawChart_eq]
    unfold selectedCoordinate rightTranslate
    cases north
    · simp only [Bool.false_eq_true, if_false]
      change matrixFunction f ((lowerUnipotent z * g : ComplexGL2) : OrbitMat) = f (lowerUnipotent z * g)
      unfold matrixFunction
      rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero _)]
      exact congrArg f (Units.ext rfl)
    · simp only [Bool.true_eq, if_true]
      change matrixFunction f ((weyl * upperUnipotent z * g : ComplexGL2) : OrbitMat) = f (weyl * upperUnipotent z * g)
      unfold matrixFunction
      rw [dif_pos (Matrix.GeneralLinearGroup.det_ne_zero _)]
      exact congrArg f (Units.ext rfl)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hm : Continuous (fun q : ComplexGL2 × ℂ =>
      ((q.1 : Matrix (Fin 2) (Fin 2) ℂ),q.2)) := by fun_prop
  have hj : ContinuousAt (fun q : OrbitMat × ℂ => iteratedFDeriv ℝ n (H q.1) q.2)
      ((p.1 : OrbitMat), p.2) :=
    (hjet (p.1 : OrbitMat) (Matrix.GeneralLinearGroup.det_ne_zero p.1) p.2).continuousAt
  simpa only [Function.comp_def, he] using
    (hj.comp (x := p) (f := fun q : ComplexGL2 × ℂ => ((q.1 : OrbitMat), q.2)) hm.continuousAt)

 theorem evaluation_rightTranslate_orbit_continuous (s : ℝ) (f : PrincipalSeries s) :
    Continuous (fun g : ComplexGL2 => rightTranslate s g f) := by
  apply continuous_iff_continuousAt.mpr
  intro g₀
  change Filter.Tendsto (fun g : ComplexGL2 => rightTranslate s g f) (nhds g₀)
    (nhds (rightTranslate s g₀ f))
  rw [(show WithSeminorms (chartSeminorm s) from ⟨rfl⟩).tendsto_nhds]
  intro n ε hε
  have hc (north : Bool) : Continuous (fun g : ComplexGL2 =>
      KPCplxPrincipalSeriesJets.jetSup n
        (selectedCoordinate north (rightTranslate s g f - rightTranslate s g₀ f).val)) := by
    have hj := evaluation_continuous_rightTranslate_chart_jets s n f north
    have hfixed : Continuous (fun p : ComplexGL2 × ℂ => iteratedFDeriv ℝ n
        (selectedCoordinate north (rightTranslate s g₀ f).val) p.2) := by
      cases north
      · exact ((rightTranslate s g₀ f).property.2.2.continuous_iteratedFDeriv (by simp)).comp continuous_snd
      · exact ((rightTranslate s g₀ f).property.2.1.continuous_iteratedFDeriv (by simp)).comp continuous_snd
    have hd : Continuous (fun p : ComplexGL2 × ℂ => ‖iteratedFDeriv ℝ n
        (selectedCoordinate north (rightTranslate s p.1 f - rightTranslate s g₀ f).val) p.2‖) := by
      convert (hj.sub hfixed).norm using 1
      funext p
      congr 1
      cases north
      · exact iteratedFDeriv_sub_apply
          (((rightTranslate s p.1 f).property.2.2.of_le (by simp)).contDiffAt)
          (((rightTranslate s g₀ f).property.2.2.of_le (by simp)).contDiffAt)
      · exact iteratedFDeriv_sub_apply
          (((rightTranslate s p.1 f).property.2.1.of_le (by simp)).contDiffAt)
          (((rightTranslate s g₀ f).property.2.1.of_le (by simp)).contDiffAt)
    exact (isCompact_closedBall (0 : ℂ) 1).continuous_sSup hd
  have hc' : Continuous (fun g : ComplexGL2 =>
      chartSeminorm s n (rightTranslate s g f - rightTranslate s g₀ f)) := by
    exact (hc true).max (hc false)
  have hv : chartSeminorm s n (rightTranslate s g₀ f - rightTranslate s g₀ f) < ε := by
    simpa only [sub_self, map_zero] using hε
  exact hc'.continuousAt.preimage_mem_nhds (Iio_mem_nhds hv)

theorem pi_continuous (s : ℝ) :
    Continuous (fun p : ComplexPGL2 × PrincipalSeries s => pi s p.1 p.2) := by
  letI : ProperSpace (Matrix (Fin 2) (Fin 2) ℂ) := FiniteDimensional.proper ℝ _
  letI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℂ) := locallyCompact_of_proper
  letI : BarrelledSpace ℂ (PrincipalSeries s) := evaluation_principalSeries_barrelled_complex s
  let T : ComplexGL2 → PrincipalSeries s →ₗ[ℂ] PrincipalSeries s := fun g =>
    { toFun := rightTranslate s g
      map_add' := by intros; apply Subtype.ext; rfl
      map_smul' := by intros; apply Subtype.ext; rfl }
  have h : Continuous (fun p : ComplexGL2 × PrincipalSeries s => rightTranslate s p.1 p.2) :=
    KPCplxPrincipalSeriesJointBS.joint_continuous (chartSeminorm s) ⟨rfl⟩ T
      (evaluation_fixedg_continuous s) (evaluation_rightTranslate_orbit_continuous s)
  have hq : IsOpenQuotientMap (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) :=
    QuotientGroup.isOpenQuotientMap_mk
  exact (hq.prodMap IsOpenQuotientMap.id).continuous_comp_iff.mp h

noncomputable def compactSubgroup : Subgroup ComplexPGL2 :=
  (Matrix.ProjGenLinGroup.mk.comp complexSU2Embedding).range

noncomputable def bottomRowNormSq (g : ComplexGL2) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
    ‖(g : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2

noncomputable def sphericalFunction (s : ℝ) (g : ComplexGL2) : ℂ :=
  (Real.rpow (‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g)
    (1 + 2 * s) : ℂ)

lemma bottom_pos (g : ComplexGL2) : 0 < bottomRowNormSq g := by
  have hd := Matrix.GeneralLinearGroup.det_ne_zero g
  have hh : (g : Matrix (Fin 2) (Fin 2) ℂ) 1 0 ≠ 0 ∨ (g : Matrix (Fin 2) (Fin 2) ℂ) 1 1 ≠ 0 := by
    by_contra! h
    apply hd
    simp [Matrix.det_fin_two, h.1, h.2]
  unfold bottomRowNormSq
  rcases hh with h | h <;> positivity
lemma inductionWeight_eq (s : ℝ) (a d : ℂˣ) :
    inductionWeight s a d = (‖(a : ℂ)‖ / ‖(d : ℂ)‖) ^ (1 + 2 * s) := by
  unfold inductionWeight complexAbs
  rw [norm_div]
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

noncomputable def sphericalSection (s : ℝ) : PrincipalSeries s :=
  ⟨sphericalFunction s, by
    refine ⟨?_, ?_, ?_⟩
    · intro a d b g
      have hb : bottomRowNormSq (upperTriangular a d b * g) = ‖(d : ℂ)‖ ^ 2 * bottomRowNormSq g := by
        simp [bottomRowNormSq, upperTriangular, Matrix.mul_apply, Fin.sum_univ_two, norm_mul, mul_pow]
        ring
      have hd : ‖((Matrix.GeneralLinearGroup.det (upperTriangular a d b * g) : ℂˣ) : ℂ)‖ =
          ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ := by
        simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, upperTriangular, Matrix.det_fin_two, norm_mul]
      simp only [sphericalFunction, hb, hd, inductionWeight_eq, Real.rpow_eq_pow, ← Complex.ofReal_mul]
      congr 1
      have he : ‖(a : ℂ)‖ * ‖(d : ℂ)‖ * ‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ /
          (‖(d : ℂ)‖ ^ 2 * bottomRowNormSq g) =
          (‖(a : ℂ)‖ / ‖(d : ℂ)‖) * (‖((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ)‖ / bottomRowNormSq g) := by
        field_simp
      rw [he, Real.mul_rpow (by positivity) (div_nonneg (norm_nonneg _) (bottom_pos g).le)]
    · have he : openCoordinate (sphericalFunction s) = fun z => (Real.rpow (1 + ‖z‖ ^ 2) (-(1 + 2 * s)) : ℂ) := by
        funext z
        simp [openCoordinate, sphericalFunction, bottomRowNormSq, weyl, upperUnipotent,
          Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_mul, Matrix.det_fin_two,
          Matrix.mul_apply, Fin.sum_univ_two, Real.rpow_eq_pow]
        rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
        congr 1 <;> ring
      rw [he]
      apply Complex.ofRealCLM.contDiff.comp
      have h : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => 1 + ‖z‖ ^ 2) := by
        simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        exact contDiff_const.add ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
          (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
      exact h.rpow_const_of_ne (by intro z; positivity)
    · have he : infinityCoordinate (sphericalFunction s) = fun z => (Real.rpow (1 + ‖z‖ ^ 2) (-(1 + 2 * s)) : ℂ) := by
        funext z
        simp [infinityCoordinate, sphericalFunction, bottomRowNormSq, lowerUnipotent,
          Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Real.rpow_eq_pow,
          add_comm]
        rw [Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
        congr 1 <;> ring
      rw [he]
      apply Complex.ofRealCLM.contDiff.comp
      have h : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => 1 + ‖z‖ ^ 2) := by
        simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        exact contDiff_const.add ((Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
          (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff))
      exact h.rpow_const_of_ne (by intro z; positivity)⟩

theorem sphericalSection_one (s : ℝ) : sphericalSection s 1 = 1 := by
  change sphericalFunction s 1 = 1
  simp [sphericalFunction, bottomRowNormSq]

private lemma gram_norm (g : ComplexGL2) :
    ((g : Matrix (Fin 2) (Fin 2) ℂ) * star (g : Matrix (Fin 2) (Fin 2) ℂ)) 1 1 =
      (bottomRowNormSq g : ℂ) := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, bottomRowNormSq,
    Matrix.star_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
 lemma spherical_su2 (s : ℝ) (g : ComplexGL2) (k : ComplexSU2) :
    sphericalFunction s (g * complexSU2Embedding k) = sphericalFunction s g := by
  have hk : Matrix.GeneralLinearGroup.det (complexSU2Embedding k) = 1 := by
    apply Units.ext
    exact (Matrix.mem_specialUnitaryGroup_iff.mp k.property).2
  have hb : bottomRowNormSq (g * complexSU2Embedding k) = bottomRowNormSq g := by
    apply Complex.ofReal_injective
    rw [← gram_norm, ← gram_norm]
    have hk' : (k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp ((Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
    change ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) *
      star ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))) 1 1 = _
    rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (k : Matrix (Fin 2) (Fin 2) ℂ), hk', Matrix.one_mul]
  simp [sphericalFunction, map_mul, hk, hb]

theorem sphericalSection_fixed (s : ℝ) (k : compactSubgroup) :
    pi s k (sphericalSection s) = sphericalSection s := by
  rcases k.property with ⟨k', hk'⟩
  change Matrix.ProjGenLinGroup.mk (complexSU2Embedding k') = k.val at hk'
  rw [← hk', pi_mk]
  apply Subtype.ext
  funext g
  change sphericalFunction s (g * complexSU2Embedding k') = sphericalFunction s g
  exact spherical_su2 s g k'

 lemma compact_chart (z : ℂ) :
    ∃ (a d : ℂˣ) (b : ℂ) (k : ComplexSU2),
      weyl * upperUnipotent z = upperTriangular a d b * complexSU2Embedding k := by
  let r : ℝ := (Real.sqrt (1 + ‖z‖ ^ 2))⁻¹
  have hp : 0 < 1 + ‖z‖ ^ 2 := by positivity
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hp)
  have he : r ^ 2 * (1 + ‖z‖ ^ 2) = 1 := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hp.le]
    exact inv_mul_cancel₀ (ne_of_gt hp)
  have hec : (r : ℂ) ^ 2 * (1 + z * (starRingEnd ℂ) z) = 1 := by
    change (r : ℂ) ^ 2 * (1 + z * (starRingEnd ℂ) z) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast he
  let M : Matrix (Fin 2) (Fin 2) ℂ := !![(r : ℂ) * (starRingEnd ℂ) z, -(r : ℂ); (r : ℂ), (r : ℂ) * z]
  have hd : M.det = 1 := by
    rw [Matrix.det_fin_two]
    change ((r : ℂ) * (starRingEnd ℂ) z) * ((r : ℂ) * z) - (-(r : ℂ)) * (r : ℂ) = 1
    calc
      _ = (r : ℂ) ^ 2 * (1 + z * (starRingEnd ℂ) z) := by ring
      _ = 1 := hec
  have hu : M * star M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply]
    all_goals ring_nf at hec ⊢
    all_goals first | exact hec | exact hec.symm

  let k : ComplexSU2 := ⟨M, Matrix.mem_specialUnitaryGroup_iff.mpr ⟨Matrix.mem_unitaryGroup_iff.mpr hu, hd⟩⟩
  refine ⟨Units.mk0 (-(r : ℂ)) (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))),
    Units.mk0 ((r : ℂ)⁻¹) (inv_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hr))), (r : ℂ) * (starRingEnd ℂ) z, k, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperTriangular, weyl, upperUnipotent, complexSU2Embedding, k, M,
      Matrix.mul_apply, Fin.sum_univ_two, ne_of_gt hr]
  all_goals ring_nf at hec ⊢
  all_goals first | exact hec | exact hec.symm

theorem sphericalSection_spans_fixed (s : ℝ) (f : PrincipalSeries s)
    (hf : ∀ k : compactSubgroup, pi s k f = f) :
    f = (f 1) • sphericalSection s := by
  apply openCoordinate_injective s
  funext z
  rcases compact_chart z with ⟨a, d, b, k, hk⟩
  have hmem : Matrix.ProjGenLinGroup.mk (complexSU2Embedding k) ∈ compactSubgroup :=
    ⟨k, rfl⟩
  have hfixed := hf ⟨_, hmem⟩
  have hfk : f (complexSU2Embedding k) = f 1 := by
    have hv := congrArg (fun v : PrincipalSeries s => v 1) hfixed
    simpa [pi_mk, rightTranslate] using hv
  have hsk : sphericalSection s (complexSU2Embedding k) = 1 := by
    have hv := congrArg (fun v : PrincipalSeries s => v 1) (sphericalSection_fixed s ⟨_, hmem⟩)
    simpa [pi_mk, rightTranslate, sphericalSection_one] using hv
  change f (weyl * upperUnipotent z) = f 1 * sphericalSection s (weyl * upperUnipotent z)
  rw [hk, f.property.1, (sphericalSection s).property.1, hfk, hsk]
  ring

theorem sphericalSection_open_diagonal (s : ℝ) (x : ℂ) (y : ℂˣ) :
    sphericalSection s (weyl * upperUnipotent x * diagonal y) =
      ((Real.rpow ‖(y : ℂ)‖ (1 + 2 * s) *
        Real.rpow (‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2) (-(1 + 2 * s))) : ℂ) := by
  change sphericalFunction s _ = _
  have hb : bottomRowNormSq (weyl * upperUnipotent x * diagonal y) = ‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2 := by
    simp [bottomRowNormSq, weyl, upperUnipotent, KPCplxCharacterHaar.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  have hd : ((Matrix.GeneralLinearGroup.det (weyl * upperUnipotent x * KPCplxCharacterHaar.diagonal y) : ℂˣ) : ℂ) = -(y : ℂ) := by
    simp [Matrix.GeneralLinearGroup.val_det_apply, weyl, upperUnipotent, KPCplxCharacterHaar.diagonal, Matrix.det_fin_two]
  simp only [sphericalFunction, hb, hd, norm_neg]
  rw [← Complex.ofReal_mul]
  congr 1
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (norm_nonneg _) (by positivity), div_eq_mul_inv, Real.rpow_neg (by positivity)]

theorem sphericalSection_positive_open_diagonal (x : ℂ) (y : ℂˣ) :
    sphericalSection positiveParameter (weyl * upperUnipotent x * diagonal y) =
      ((Real.rpow ‖(y : ℂ)‖ (4 / 3) *
        Real.rpow (‖(y : ℂ)‖ ^ 2 + ‖x‖ ^ 2) (-(4 / 3))) : ℂ) := by
  convert sphericalSection_open_diagonal positiveParameter x y using 2 <;> norm_num [positiveParameter]

end DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts

section

namespace DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts

open KPCplxCharacterHaar Set
open scoped ContDiff Matrix.Norms.Elementwise

theorem projectiveLine_compact : CompactSpace ComplexProjectiveLine := by
  apply isCompact_univ_iff.mp
  have hcover : (univ : Set ComplexProjectiveLine) =
      projectiveOpen '' Metric.closedBall 0 1 ∪ projectiveInfinity '' Metric.closedBall 0 1 := by
    symm
    apply Set.eq_univ_of_forall
    intro p
    induction p using Projectivization.ind with
    | h v hv =>
      have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
        by_contra! h
        apply hv
        ext i
        fin_cases i <;> simp_all
      by_cases h : ‖v 1‖ ≤ ‖v 0‖
      · have h0 : v 0 ≠ 0 := by
          intro h0
          simp only [h0, norm_zero, norm_le_zero_iff] at h
          exact hn.elim (fun hh => hh h0) (fun hh => hh h)
        left
        refine ⟨v 1 / v 0, ?_, ?_⟩
        · simpa [Metric.mem_closedBall, dist_zero_right, norm_div] using
            (div_le_one (norm_pos_iff.mpr h0)).mpr h
        · symm
          apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
          use v 0
          ext i
          fin_cases i <;> simp [projectiveOpen, h0, mul_div_cancel₀]
      · have h1 : v 1 ≠ 0 := by
          intro h1
          simp [h1] at h
        right
        refine ⟨v 0 / v 1, ?_, ?_⟩
        · simpa [Metric.mem_closedBall, dist_zero_right, norm_div] using
            (div_le_one (norm_pos_iff.mpr h1)).mpr (le_of_not_ge h)
        · symm
          apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
          use v 1
          ext i
          fin_cases i <;> simp [projectiveInfinity, h1, mul_div_cancel₀]
  rw [hcover]
  have hop : Continuous projectiveOpen :=
    (continuous_coinduced_rng : Continuous (Sum.elim projectiveOpen projectiveInfinity)).comp
      continuous_inl
  have hinf : Continuous projectiveInfinity :=
    (continuous_coinduced_rng : Continuous (Sum.elim projectiveOpen projectiveInfinity)).comp
      continuous_inr
  exact ((isCompact_closedBall (0 : ℂ) 1).image hop).union
    ((isCompact_closedBall (0 : ℂ) 1).image hinf)

theorem projectiveOpen_continuous : Continuous projectiveOpen := by
  exact (continuous_coinduced_rng : Continuous (Sum.elim projectiveOpen projectiveInfinity)).comp continuous_inl

theorem projectiveInfinity_continuous : Continuous projectiveInfinity := by
  exact (continuous_coinduced_rng : Continuous (Sum.elim projectiveOpen projectiveInfinity)).comp continuous_inr

open Filter Topology KPCplxPrincipalSeriesJets

open KPCplxPrincipalSeriesEvaluationContinuity

theorem compactSubgroup_isCompact : IsCompact (compactSubgroup : Set ComplexPGL2) := by
  have hc : CompactSpace ComplexSU2 := by
    apply isCompact_iff_compactSpace.mp
    convert complexSU2_isCompact using 1
    exact Subtype.range_coe.symm
  have he : Continuous complexSU2Embedding := by
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · have hi (k : ComplexSU2) :
          (↑(complexSU2Embedding k)⁻¹ : Matrix (Fin 2) (Fin 2) ℂ) =
            star (k : Matrix (Fin 2) (Fin 2) ℂ) := by
        rw [← map_inv]
        rfl
      simp_rw [hi]
      exact continuous_subtype_val.star
  have hq : Continuous (Matrix.ProjGenLinGroup.mk : ComplexGL2 → ComplexPGL2) :=
    continuous_coinduced_rng
  have hr : (compactSubgroup : Set ComplexPGL2) = Set.range (fun k : ComplexSU2 =>
      Matrix.ProjGenLinGroup.mk (complexSU2Embedding k)) := rfl
  rw [hr]
  exact isCompact_range (hq.comp he)

private lemma bottomRow_su2 (g : ComplexGL2) (k : ComplexSU2) :
    bottomRowNormSq (g * complexSU2Embedding k) = bottomRowNormSq g := by
  apply Complex.ofReal_injective
  rw [← gram_norm, ← gram_norm]
  have hk : (k : Matrix (Fin 2) (Fin 2) ℂ) * star (k : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp ((Matrix.mem_specialUnitaryGroup_iff.mp k.property).1)
  change ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ) *
    star ((g : Matrix (Fin 2) (Fin 2) ℂ) * (k : Matrix (Fin 2) (Fin 2) ℂ))) 1 1 = _
  rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (k : Matrix (Fin 2) (Fin 2) ℂ), hk, Matrix.one_mul]

end DedekindZetaZeroFree.KPCplxPrincipalSeriesCharts

end
