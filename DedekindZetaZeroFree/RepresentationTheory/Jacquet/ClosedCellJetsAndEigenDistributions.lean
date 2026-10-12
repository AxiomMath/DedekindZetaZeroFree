module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Complex.VanishingJetsAndCutoffApproximation

@[expose] public section

section

namespace DedekindZetaZeroFree.KPCplxClosedCellJets.CutoffAnnihilation

open KPCplxPrincipalSeriesCharts

theorem functional_zero_of_cutoff_approximation
    (s : ℝ) (T : PrincipalSeries s →L[ℂ] ℂ)
    (hT : ∀ g : PrincipalSeries s,
      (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, ‖u‖ < ε → infinityCoordinate g u = 0) → T g = 0)
    (F : Finset ℕ) (C : NNReal)
    (hb : ∀ f : PrincipalSeries s, ‖T f‖ ≤ C * (F.sup (chartSeminorm s)) f)
    (f : PrincipalSeries s)
    (happrox : ∀ δ : ℝ, 0 < δ → ∃ g : PrincipalSeries s,
      (∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, ‖u‖ < ε → infinityCoordinate g u = 0) ∧
        (F.sup (chartSeminorm s)) (f - g) < δ) : T f = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := happrox (ε / ((C : ℝ) + 1)) (div_pos hε (by positivity))
  have heq : T f = T (f - g) := by rw [map_sub, hT g hg, sub_zero]
  rw [heq]
  have hb' := hb (f - g)
  have hp := apply_nonneg (F.sup (chartSeminorm s)) (f - g)
  have hmul : (C : ℝ) * (F.sup (chartSeminorm s)) (f - g) ≤ ε := by
    have hh : (F.sup (chartSeminorm s)) (f - g) * ((C : ℝ) + 1) < ε :=
      (lt_div_iff₀ (by positivity : (0 : ℝ) < (C : ℝ) + 1)).mp hfg
    nlinarith
  nlinarith [hb'.trans hmul]

end DedekindZetaZeroFree.KPCplxClosedCellJets.CutoffAnnihilation

end

section

namespace DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation

open KPCplxPrincipalSeriesCharts

theorem seminorm_bound_annihilates_approximable (s : ℝ)
    (T : PrincipalSeries s →L[ℂ] ℂ) (F : Finset ℕ) (C : NNReal)
    (hC : C ≠ 0)
    (hbound : ∀ f : PrincipalSeries s, ‖T f‖ ≤ C * (F.sup (chartSeminorm s)) f)
    (hsupport : ∀ g : PrincipalSeries s,
      (∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → infinityCoordinate g u = 0) → T g = 0)
    (f : PrincipalSeries s)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : PrincipalSeries s,
      (∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ < δ → infinityCoordinate g u = 0) ∧
      (F.sup (chartSeminorm s)) (f - g) < ε) :
    T f = 0 := by
  exact KPCplxClosedCellJets.CutoffAnnihilation.functional_zero_of_cutoff_approximation
    s T hsupport F C hbound f happrox

end DedekindZetaZeroFree.KPCplxClosedCellCutoffApproximation

end

section

namespace DedekindZetaZeroFree.KPCplxClosedCellJets

open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar

def SupportedAwayInfinity (s : ℝ) (f : PrincipalSeries s) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂ, ‖u‖ < ε → infinityCoordinate f u = 0

def SupportedAtInfinity (s : ℝ) (T : PrincipalSeries s →L[ℂ] ℂ) : Prop :=
  ∀ f : PrincipalSeries s, SupportedAwayInfinity s f → T f = 0

def IsEigenDistribution (s : ℝ) (ψ : AddChar ℂ Circle)
    (T : PrincipalSeries s →L[ℂ] ℂ) : Prop :=
  ∀ (t : ℂ) (f : PrincipalSeries s),
    T (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) = (ψ t : ℂ) * T f

abbrev JetData (n : ℕ) := (k : Fin (n + 1)) → (Fin k.val → Fin 2) → ℂ

noncomputable def jetAtInfinity (s : ℝ) (n : ℕ) (f : PrincipalSeries s) : JetData n :=
  fun k v => iteratedFDeriv ℝ k.val (infinityCoordinate f) 0
    (fun i => if v i = 0 then (1 : ℂ) else Complex.I)

noncomputable def jetSubspace (s : ℝ) (n : ℕ) : Submodule ℂ (JetData n) :=
  Submodule.span ℂ (Set.range (jetAtInfinity s n))

abbrev JetSpace (s : ℝ) (n : ℕ) := ↥(jetSubspace s n)

noncomputable def sectionJet (s : ℝ) (n : ℕ) (f : PrincipalSeries s) : JetSpace s n :=
  ⟨jetAtInfinity s n f, Submodule.subset_span (Set.mem_range_self f)⟩

def IsJetAction (s : ℝ) (n : ℕ) (ρ : ℂ → Module.End ℂ (JetSpace s n)) : Prop :=
  ∀ (t : ℂ) (f : PrincipalSeries s),
    ρ t (sectionJet s n f) =
      sectionJet s n (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)

theorem jetAtInfinity_add (s : ℝ) (n : ℕ) (f g : PrincipalSeries s) :
    jetAtInfinity s n (f + g) = jetAtInfinity s n f + jetAtInfinity s n g := by
  funext k v
  simp only [jetAtInfinity, Pi.add_apply]
  have h : infinityCoordinate ((f + g : PrincipalSeries s) : ComplexGL2 → ℂ) =
      infinityCoordinate (f : ComplexGL2 → ℂ) + infinityCoordinate (g : ComplexGL2 → ℂ) := by
    funext u
    rfl
  rw [h, iteratedFDeriv_add_apply]
  · rfl
  · exact ((f.2.2.2).of_le (by simp)).contDiffAt
  · exact ((g.2.2.2).of_le (by simp)).contDiffAt

theorem jetAtInfinity_smul (s : ℝ) (n : ℕ) (c : ℂ) (f : PrincipalSeries s) :
    jetAtInfinity s n (c • f) = c • jetAtInfinity s n f := by
  funext k v
  simp only [jetAtInfinity, Pi.smul_apply]
  have h : infinityCoordinate ((c • f : PrincipalSeries s) : ComplexGL2 → ℂ) =
      c • infinityCoordinate (f : ComplexGL2 → ℂ) := by
    funext u
    rfl
  rw [h, iteratedFDeriv_const_smul_apply]
  · rfl
  · exact ((f.2.2.2).of_le (by simp)).contDiffAt

noncomputable def jetLinear (s : ℝ) (n : ℕ) : PrincipalSeries s →ₗ[ℂ] JetData n where
  toFun := jetAtInfinity s n
  map_add' := jetAtInfinity_add s n
  map_smul' := jetAtInfinity_smul s n

theorem sectionJet_surjective (s : ℝ) (n : ℕ) :
    Function.Surjective (sectionJet s n) := by
  intro j
  have hle : jetSubspace s n ≤ LinearMap.range (jetLinear s n) := by
    rw [jetSubspace]
    apply Submodule.span_le.mpr
    rintro y ⟨f, rfl⟩
    exact ⟨f, rfl⟩
  obtain ⟨f, hf⟩ := hle j.2
  exact ⟨f, Subtype.ext hf⟩

theorem distribution_finite_seminorm_bound (s : ℝ) (T : PrincipalSeries s →L[ℂ] ℂ) :
    ∃ (F : Finset ℕ) (C : NNReal), C ≠ 0 ∧
      ∀ f : PrincipalSeries s, ‖T f‖ ≤ C * (F.sup (chartSeminorm s)) f := by
  obtain ⟨F, C, hC, hbound⟩ :=
    Seminorm.bound_of_continuous (⟨rfl⟩ : WithSeminorms (chartSeminorm s))
      ((normSeminorm ℂ ℂ).comp T.toLinearMap) (continuous_norm.comp T.continuous)
  refine ⟨F, C, hC, ?_⟩
  intro f
  simpa [Seminorm.comp_apply, coe_normSeminorm, NNReal.smul_def, smul_eq_mul] using hbound f

theorem jetAtInfinity_eq_zero_iff (s : ℝ) (n : ℕ) (f : PrincipalSeries s) :
    jetAtInfinity s n f = 0 ↔ ∀ k ≤ n, iteratedFDeriv ℝ k (infinityCoordinate f) 0 = 0 := by
  constructor
  · intro h k hk
    apply ContinuousMultilinearMap.toMultilinearMap_injective
    apply (Module.Basis.ext_multilinear (fun _ : Fin k => Complex.basisOneI))
    intro v
    have hv := congrArg (fun j : JetData n => j ⟨k, by omega⟩ v) h
    change iteratedFDeriv ℝ k (infinityCoordinate f) 0
      (fun i => if v i = 0 then (1 : ℂ) else Complex.I) = 0 at hv
    change iteratedFDeriv ℝ k (infinityCoordinate f) 0 (fun i => Complex.basisOneI (v i)) = 0
    have hb : (fun i => Complex.basisOneI (v i)) =
        (fun i => if v i = 0 then (1 : ℂ) else Complex.I) := by
      funext i
      rw [Complex.coe_basisOneI]
      generalize hv : v i = a
      fin_cases a <;> simp
    rw [hb]
    exact hv
  · intro h
    funext k v
    simp only [jetAtInfinity, h k.val (by omega), ContinuousMultilinearMap.zero_apply,
      Pi.zero_apply]

noncomputable def sectionJetLinear (s : ℝ) (n : ℕ) :
    PrincipalSeries s →ₗ[ℂ] JetSpace s n where
  toFun := sectionJet s n
  map_add' := by
    intro f g
    apply Subtype.ext
    exact jetAtInfinity_add s n f g
  map_smul' := by
    intro c f
    apply Subtype.ext
    exact jetAtInfinity_smul s n c f

theorem factors_jet_iff_annihilates_kernel (s : ℝ) (n : ℕ)
    (T : PrincipalSeries s →L[ℂ] ℂ) :
    (∃ L : JetSpace s n →ₗ[ℂ] ℂ, ∀ f, T f = L (sectionJet s n f)) ↔
      ∀ f : PrincipalSeries s, jetAtInfinity s n f = 0 → T f = 0 := by
  constructor
  · rintro ⟨L, hL⟩ f hf
    rw [hL f]
    have hj : sectionJet s n f = 0 := Subtype.ext hf
    rw [hj, map_zero]
  · intro h
    let J := sectionJetLinear s n
    have hker : J.ker ≤ T.toLinearMap.ker := by
      intro f hf
      apply h f
      exact congrArg Subtype.val (LinearMap.mem_ker.mp hf)
    have hsurj : Function.Surjective J := sectionJet_surjective s n
    let e := J.quotKerEquivOfSurjective hsurj
    refine ⟨(J.ker.liftQ T.toLinearMap hker).comp e.symm.toLinearMap, ?_⟩
    intro f
    change T f = J.ker.liftQ T.toLinearMap hker (e.symm (J f))
    dsimp only [e]
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl

theorem factors_finite_jet_iff (s : ℝ) (T : PrincipalSeries s →L[ℂ] ℂ) :
    (∃ n : ℕ, ∃ L : JetSpace s n →ₗ[ℂ] ℂ,
      ∀ f : PrincipalSeries s, T f = L (sectionJet s n f)) ↔
    ∃ n : ℕ, ∀ f : PrincipalSeries s, jetAtInfinity s n f = 0 → T f = 0 := by
  exact exists_congr (fun n => factors_jet_iff_annihilates_kernel s n T)

theorem supportedAtInfinity_factors_finite_jet (s : ℝ)
    (T : PrincipalSeries s →L[ℂ] ℂ) (hT : SupportedAtInfinity s T) :
    ∃ n : ℕ, ∃ L : JetSpace s n →ₗ[ℂ] ℂ,
      ∀ f : PrincipalSeries s, T f = L (sectionJet s n f) := by

  apply (factors_finite_jet_iff s T).mpr
  obtain ⟨F, C, hC, hbound⟩ := distribution_finite_seminorm_bound s T
  obtain ⟨n, hn⟩ := KPCplxClosedCellCutoffApproximation.finite_seminorm_cutoff_approximation s F
  refine ⟨n, ?_⟩
  intro f hf
  have hflat := (jetAtInfinity_eq_zero_iff s n f).mp hf
  exact KPCplxClosedCellCutoffApproximation.seminorm_bound_annihilates_approximable
    s T F C hC hbound hT f (hn f hflat)

private theorem upperTriangular_one_one (t : ℂ) :
    upperTriangular 1 1 t = upperUnipotent t := by
  apply Matrix.GeneralLinearGroup.ext
  simp [upperTriangular, upperUnipotent]

private theorem lowerUnipotent_zero : lowerUnipotent 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  simp [lowerUnipotent]

private theorem inductionWeight_one_one (s : ℝ) : inductionWeight s 1 1 = 1 := by
  simp [inductionWeight, complexAbs]

theorem infinityCoordinate_zero_unipotent_fixed (s : ℝ) (t : ℂ) (f : PrincipalSeries s) :
    infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) 0 =
      infinityCoordinate f 0 := by
  rw [pi_mk]
  change f (lowerUnipotent 0 * upperUnipotent t) = f (lowerUnipotent 0)
  rw [lowerUnipotent_zero, one_mul, ← upperTriangular_one_one]
  conv_lhs => rw [← mul_one (upperTriangular (1 : ℂˣ) 1 t)]
  rw [f.2.1 1 1 t 1]
  simp [inductionWeight_one_one]

private theorem closedCell_matrix_factor (u t : ℂ) (h : 1 + u * t ≠ 0) :
    lowerUnipotent u * upperUnipotent t =
      upperTriangular (Units.mk0 (1 + u * t) h)⁻¹ (Units.mk0 (1 + u * t) h) t *
        lowerUnipotent (u / (1 + u * t)) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerUnipotent, upperUnipotent, upperTriangular, Matrix.mul_apply,
      Fin.sum_univ_two]
  <;> field_simp
  <;> ring

theorem infinityCoordinate_unipotent_formula (s : ℝ) (u t : ℂ) (h : 1 + u * t ≠ 0) (f : PrincipalSeries s) :
    infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) u =
      (inductionWeight s (Units.mk0 (1 + u * t) h)⁻¹
        (Units.mk0 (1 + u * t) h) : ℂ) * infinityCoordinate f (u / (1 + u * t)) := by
  rw [pi_mk]
  change f (lowerUnipotent u * upperUnipotent t) = _
  rw [closedCell_matrix_factor u t h, f.2.1]
  rfl

noncomputable def weight (s : ℝ) (t u : ℂ) : ℂ :=
  Real.rpow (Complex.normSq ((1 + u * t)⁻¹ / (1 + u * t))) (1 / 2 + s)
private theorem weight_eq (s : ℝ) (u t : ℂ) (h : 1 + u * t ≠ 0) :
    (inductionWeight s (Units.mk0 (1 + u * t) h)⁻¹
        (Units.mk0 (1 + u * t) h) : ℂ) = weight s t u := by
  simp [inductionWeight, complexAbs, weight, Complex.normSq_eq_norm_sq, div_pow]
private theorem weight_diff (s : ℝ) (t : ℂ) :
    DifferentiableAt ℝ (weight s t) 0 := by
  unfold weight
  have h : DifferentiableAt ℝ (fun u : ℂ =>
      Real.rpow (Complex.normSq ((1 + u * t)⁻¹ / (1 + u * t))) (1 / 2 + s)) 0 := by
    apply DifferentiableAt.rpow_const
    · have hd : DifferentiableAt ℝ (fun x : ℂ => (1 + x * t)⁻¹ / (1 + x * t)) 0 := by
        have ha : DifferentiableAt ℂ (fun x : ℂ => 1 + x * t) 0 := by fun_prop
        exact ((ha.inv (by simp)).div ha (by simp)).restrictScalars ℝ
      have hr := Complex.reCLM.differentiableAt.comp 0 hd
      have hi := Complex.imCLM.differentiableAt.comp 0 hd
      exact (hr.mul hr).add (hi.mul hi)
    · simp
  exact Complex.ofRealCLM.differentiableAt.comp 0 h
private theorem coord_deriv (t : ℂ) : HasFDerivAt (fun u : ℂ => u / (1 + u * t))
    (ContinuousLinearMap.id ℝ ℂ) 0 := by
  have h : HasDerivAt (fun u : ℂ => u / (1 + u * t)) 1 0 := by
    convert (hasDerivAt_id (0 : ℂ)).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).add ((hasDerivAt_id (0 : ℂ)).mul_const t))
      (by simp) using 1 <;> simp [Pi.div_def, Pi.add_def]
  convert h.hasFDerivAt.restrictScalars ℝ using 1
  ext u
  simp

private theorem weight_zero (s : ℝ) (t : ℂ) : weight s t 0 = 1 := by
  simp [weight]
private theorem coord_formula_eventually (s : ℝ) (t : ℂ) (f : PrincipalSeries s) :
    infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) =ᶠ[nhds 0]
      fun u => weight s t u * infinityCoordinate f (u / (1 + u * t)) := by
  have h : ∀ᶠ u : ℂ in nhds 0, 1 + u * t ≠ 0 :=
    (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually_ne
      (by simp : (1 : ℂ) + 0 * t ≠ 0)
  filter_upwards [h] with u hu
  rw [infinityCoordinate_unipotent_formula s u t hu f, weight_eq]

theorem infinityCoordinate_fderiv_unipotent_fixed_of_zero (s : ℝ) (t : ℂ) (f : PrincipalSeries s) (hf : infinityCoordinate f 0 = 0) :
    fderiv ℝ (infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)) 0 =
      fderiv ℝ (infinityCoordinate f) 0 := by
  have hF : DifferentiableAt ℝ (infinityCoordinate f) 0 :=
    f.2.2.2.differentiable (by simp) 0
  have hg : HasFDerivAt (fun u => infinityCoordinate f (u / (1 + u * t)))
      (fderiv ℝ (infinityCoordinate f) 0) 0 := by
    have ho : HasFDerivAt (infinityCoordinate f) (fderiv ℝ (infinityCoordinate f) 0)
        ((fun u : ℂ => u / (1 + u * t)) 0) := by simpa using hF.hasFDerivAt
    simpa [Function.comp_def] using ho.comp 0 (coord_deriv t)
  have hw := (weight_diff s t).hasFDerivAt
  have hh := hw.mul hg
  have hh' : HasFDerivAt (fun u => weight s t u * infinityCoordinate f (u / (1 + u * t)))
      (fderiv ℝ (infinityCoordinate f) 0) 0 := by
    simpa [hf, weight_zero, Pi.mul_def] using hh
  exact (hh'.congr_of_eventuallyEq (coord_formula_eventually s t f)).fderiv

theorem sectionJet_one_unipotent_fixed_of_zero (s : ℝ) (t : ℂ) (f : PrincipalSeries s) (hf : infinityCoordinate f 0 = 0) :
    sectionJet s 1 (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) = sectionJet s 1 f := by
  apply Subtype.ext
  funext k v
  fin_cases k
  · simp [sectionJet, jetAtInfinity, iteratedFDeriv_zero_apply,
      infinityCoordinate_zero_unipotent_fixed]
  · simp only [sectionJet, jetAtInfinity, Fin.val_one,
      iteratedFDeriv_one_apply]
    rw [infinityCoordinate_fderiv_unipotent_fixed_of_zero s t f hf]
theorem sectionJet_one_zero_value (s : ℝ) (f : PrincipalSeries s) (hf : sectionJet s 1 f = 0) :
    infinityCoordinate f 0 = 0 := by
  have h := congrArg (fun j : JetSpace s 1 => j.val ⟨0, by omega⟩ (fun i => Fin.elim0 i)) hf
  simpa [sectionJet, jetAtInfinity, iteratedFDeriv_zero_apply] using h
noncomputable def closedCell_action (s : ℝ) (t : ℂ) : PrincipalSeries s →ₗ[ℂ] PrincipalSeries s where
  toFun := pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t))
  map_add' := by
    intro f g
    apply Subtype.ext
    funext h
    rfl
  map_smul' := by
    intro c f
    apply Subtype.ext
    funext h
    rfl
noncomputable def rhoOne (s : ℝ) (t : ℂ) : Module.End ℂ (JetSpace s 1) :=
  let J := sectionJetLinear s 1
  let A := J.comp (closedCell_action s t)
  let hker : J.ker ≤ A.ker := by
    intro f hf
    have hf' : sectionJet s 1 f = 0 := LinearMap.mem_ker.mp hf
    apply LinearMap.mem_ker.mpr
    change sectionJet s 1 (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) = 0
    rw [sectionJet_one_unipotent_fixed_of_zero s t f (sectionJet_one_zero_value s f hf'), hf']
  (J.ker.liftQ A hker).comp (J.quotKerEquivOfSurjective (sectionJet_surjective s 1)).symm.toLinearMap

private theorem closedCell_upper_zero : upperUnipotent 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  simp [upperUnipotent]
private theorem closedCell_upper_add (t u : ℂ) : upperUnipotent (t + u) = upperUnipotent t * upperUnipotent u := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

private theorem closedCell_comp_zero (F g : ℂ → ℂ) (n : ℕ)
    (hF : ContDiffAt ℝ n F (g 0)) (hg : ContDiffAt ℝ n g 0)
    (h : ∀ k ≤ n, iteratedFDeriv ℝ k F (g 0) = 0) :
    iteratedFDeriv ℝ n (F ∘ g) 0 = 0 := by
  rw [iteratedFDeriv_comp hF hg le_rfl]
  simp only [FormalMultilinearSeries.taylorComp]
  apply Finset.sum_eq_zero
  intro c _
  ext v
  simp [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    ftaylorSeries, h c.length c.length_le]
private theorem closedCell_product_jet_zero (F g : ℂ → ℂ) (n : ℕ)
    (hF : ContDiffAt ℝ n F 0) (hg : ContDiffAt ℝ n g 0)
    (h : ∀ k ≤ n, iteratedFDeriv ℝ k g 0 = 0) :
    iteratedFDeriv ℝ n (fun u => F u * g u) 0 = 0 := by
  obtain ⟨U, hU, hFU⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨V, hV, hgV⟩ := hg.contDiffOn le_rfl (by simp)
  obtain ⟨W, hWU, hWopen, hW0⟩ := mem_nhds_iff.mp (Filter.inter_mem hU hV)
  have hs : UniqueDiffOn ℝ W := hWopen.uniqueDiffOn
  have hfw := hFU.mono (fun _ hw => (hWU hw).1)
  have hgw := hgV.mono (fun _ hw => (hWU hw).2)
  have hb := norm_iteratedFDerivWithin_mul_le hfw hgw hs hW0 (le_refl (n : WithTop ℕ∞))
  have heq (k : ℕ) : iteratedFDerivWithin ℝ k (fun u => F u * g u) W 0 =
      iteratedFDeriv ℝ k (fun u => F u * g u) 0 :=
    iteratedFDerivWithin_of_isOpen k hWopen hW0
  rw [heq] at hb
  have hz (k : ℕ) (hk : k ≤ n) : iteratedFDerivWithin ℝ k g W 0 = 0 := by
    rw [iteratedFDerivWithin_of_isOpen k hWopen hW0, h k hk]
  have hb' : ‖iteratedFDeriv ℝ n (fun u => F u * g u) 0‖ ≤ 0 := by
    simpa only [hz _ (Nat.sub_le n _), norm_zero, mul_zero, Finset.sum_const_zero] using hb
  exact norm_eq_zero.mp (le_antisymm hb' (norm_nonneg _))
private theorem closedCell_weight_smooth (s : ℝ) (t : ℂ) (n : ℕ) :
    ContDiffAt ℝ n (fun u : ℂ => (Real.rpow
      (Complex.normSq ((1 + u * t)⁻¹ / (1 + u * t))) (1 / 2 + s) : ℂ)) 0 := by
  have hd : ContDiffAt ℝ n (fun x : ℂ => (1 + x * t)⁻¹ / (1 + x * t)) 0 := by
    have ha : ContDiffAt ℂ n (fun x : ℂ => 1 + x * t) 0 := by fun_prop
    exact ((ha.inv (by simp)).div ha (by simp)).restrict_scalars ℝ
  have hr := Complex.reCLM.contDiff.contDiffAt.comp 0 hd
  have hi := Complex.imCLM.contDiff.contDiffAt.comp 0 hd
  have hn : ContDiffAt ℝ n (fun x : ℂ => Complex.normSq ((1 + x * t)⁻¹ / (1 + x * t))) 0 :=
    (hr.mul hr).add (hi.mul hi)
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (hn.rpow_const_of_ne (by simp))
private theorem closedCell_coord_smooth (t : ℂ) (n : ℕ) :
    ContDiffAt ℝ n (fun u : ℂ => u / (1 + u * t)) 0 := by
  have hd : ContDiffAt ℂ n (fun u : ℂ => u / (1 + u * t)) 0 := by
    apply contDiffAt_id.div
    · fun_prop
    · simp
  exact hd.restrict_scalars ℝ

theorem jetAtInfinity_unipotent_preserves_kernel (s : ℝ) (n : ℕ) (t : ℂ) (f : PrincipalSeries s) (hf : jetAtInfinity s n f = 0) :
    jetAtInfinity s n (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) = 0 := by
  rw [jetAtInfinity_eq_zero_iff] at hf ⊢
  intro k hk
  have hF : ContDiffAt ℝ k (infinityCoordinate f) 0 := (f.2.2.2.of_le (by simp)).contDiffAt
  have hc : iteratedFDeriv ℝ k ((infinityCoordinate f) ∘ (fun u : ℂ => u / (1 + u * t))) 0 = 0 :=
    closedCell_comp_zero _ _ k (by simpa using hF) (closedCell_coord_smooth t k) (by simpa using fun i hi => hf i (hi.trans hk))
  have hc' : ContDiffAt ℝ k ((infinityCoordinate f) ∘ (fun u : ℂ => u / (1 + u * t))) 0 :=
    (show ContDiffAt ℝ k (infinityCoordinate f) ((fun u : ℂ => u / (1 + u * t)) 0) by simpa using hF).comp 0 (closedCell_coord_smooth t k)
  have hm : iteratedFDeriv ℝ k (fun u : ℂ => (Real.rpow
      (Complex.normSq ((1 + u * t)⁻¹ / (1 + u * t))) (1 / 2 + s) : ℂ) *
      infinityCoordinate f (u / (1 + u * t))) 0 = 0 := by
    apply closedCell_product_jet_zero _ _ k (closedCell_weight_smooth s t k) hc'
    intro i hi
    exact closedCell_comp_zero _ _ i (by simpa using (hF.of_le (by exact_mod_cast hi)))
      (closedCell_coord_smooth t i) (by simpa using fun a ha => hf a ((ha.trans hi).trans hk))
  have he : infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) =ᶠ[nhds 0]
      fun u : ℂ => (Real.rpow (Complex.normSq ((1 + u * t)⁻¹ / (1 + u * t))) (1 / 2 + s) : ℂ) *
        infinityCoordinate f (u / (1 + u * t)) := by
    have hh : ∀ᶠ u : ℂ in nhds 0, 1 + u * t ≠ 0 :=
      (continuous_const.add (continuous_id.mul continuous_const)).continuousAt.eventually_ne (by simp)
    filter_upwards [hh] with u hu
    rw [infinityCoordinate_unipotent_formula s u t hu f]
    simp [inductionWeight, complexAbs, Complex.normSq_eq_norm_sq, div_pow]
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hm

noncomputable def closedCell_jetAction (s : ℝ) (n : ℕ) (t : ℂ) :
    Module.End ℂ (JetSpace s n) :=
  let J := sectionJetLinear s n
  let A := J.comp (closedCell_action s t)
  let hker : J.ker ≤ A.ker := by
    intro f hf
    have hf' : jetAtInfinity s n f = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hf)
    apply LinearMap.mem_ker.mpr
    exact Subtype.ext (jetAtInfinity_unipotent_preserves_kernel s n t f hf')
  (J.ker.liftQ A hker).comp
    (J.quotKerEquivOfSurjective (sectionJet_surjective s n)).symm.toLinearMap

private theorem closedCell_jetAction_act (s : ℝ) (n : ℕ) :
    IsJetAction s n (closedCell_jetAction s n) := by
  intro t f
  change closedCell_jetAction s n t ((sectionJetLinear s n) f) = _
  unfold closedCell_jetAction
  dsimp only
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe]
  erw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

theorem finite_jet_action_exists (s : ℝ) (n : ℕ) :
    ∃ ρ : ℂ → Module.End ℂ (JetSpace s n),
      IsJetAction s n ρ ∧ ρ 0 = 1 ∧
      (∀ t u : ℂ, ρ (t + u) = ρ t * ρ u) := by
  refine ⟨closedCell_jetAction s n, closedCell_jetAction_act s n, ?_, ?_⟩
  · ext j
    obtain ⟨f, rfl⟩ := sectionJet_surjective s n j
    rw [closedCell_jetAction_act s n 0 f, closedCell_upper_zero, map_one, pi_one]
    rfl
  · intro t u
    ext j
    obtain ⟨f, rfl⟩ := sectionJet_surjective s n j
    rw [Module.End.mul_apply, closedCell_jetAction_act s n,
      closedCell_jetAction_act s n, closedCell_jetAction_act s n,
      closedCell_upper_add, map_mul, pi_mul]

private theorem closedCell_part_size_one {n : ℕ} (c : OrderedFinpartition n) (hc : c.length = n)
    (i : Fin c.length) : c.partSize i = 1 := by
  have hsum : ∑ i : Fin c.length, c.partSize i = n := by
    simpa [Fintype.card_sigma] using Fintype.card_congr c.equivSigma
  have hsum' : ∑ i : Fin c.length, (1 : ℕ) = ∑ i : Fin c.length, c.partSize i := by
    simpa [hc] using hsum.symm
  exact ((Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (f := fun _ : Fin c.length => (1 : ℕ)) (g := c.partSize)
    (by intros j hj; exact c.partSize_pos j)).mp hsum' i (Finset.mem_univ _)).symm

private theorem closedCell_atomic_of_length {n : ℕ} (c : OrderedFinpartition n) (hc : c.length = n) :
    c = OrderedFinpartition.atomic n := by
  have hp := closedCell_part_size_one c hc
  rcases c with ⟨length, partSize, hpos, emb, hemb, hparts, hdisj, hcover⟩
  dsimp only at hc hp
  subst length
  have hp' : partSize = fun _ => 1 := funext hp
  subst partSize
  have hm : StrictMono (fun m : Fin n => emb m 0) := by simpa using hparts
  have he (i : Fin n) (j : Fin 1) : emb i j = i := by
    rw [Subsingleton.elim j 0]
    exact hm.apply_eq
  simp only [OrderedFinpartition.ext_iff]
  constructor
  · rfl
  · exact ⟨HEq.rfl, heq_of_eq (funext fun i => funext fun j => he i j)⟩

private theorem closedCell_comp_flat_top (n : ℕ) (F C : ℂ → ℂ)
    (hF : ContDiffAt ℝ n F 0) (hC : ContDiffAt ℝ n C 0) (h0 : C 0 = 0)
    (h1 : fderiv ℝ C 0 = ContinuousLinearMap.id ℝ ℂ)
    (hf : ∀ k < n, iteratedFDeriv ℝ k F 0 = 0) :
    iteratedFDeriv ℝ n (F ∘ C) 0 = iteratedFDeriv ℝ n F 0 := by
  classical
  rw [iteratedFDeriv_comp (by simpa [h0] using hF) hC le_rfl]
  simp only [FormalMultilinearSeries.taylorComp]
  rw [Finset.sum_eq_single (OrderedFinpartition.atomic n)]
  · ext v
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      OrderedFinpartition.atomic_length, ftaylorSeries, h0]
    congr 1
    funext i
    change (iteratedFDeriv ℝ 1 C 0) (fun _ => v i) = v i
    simp [iteratedFDeriv_one_apply, h1]
  · intro c hc hca
    have hlt : c.length < n := lt_of_le_of_ne c.length_le (fun he => hca (closedCell_atomic_of_length c he))
    ext v
    simp [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries,
      h0, hf c.length hlt]
  · simp

private theorem closedCell_mul_flat_top (n : ℕ) (W F : ℂ → ℂ)
    (hW : ContDiffAt ℝ n W 0) (hF : ContDiffAt ℝ n F 0) (h0 : W 0 = 0)
    (hf : ∀ k < n, iteratedFDeriv ℝ k F 0 = 0) :
    iteratedFDeriv ℝ n (fun x => W x * F x) 0 = 0 := by
  obtain ⟨u, hu, hWu⟩ := hW.contDiffOn le_rfl (by simp)
  obtain ⟨v, hv, hFv⟩ := hF.contDiffOn le_rfl (by simp)
  obtain ⟨s, hsuv, hsopen, hs0⟩ := mem_nhds_iff.mp (Filter.inter_mem hu hv)
  have hbound := norm_iteratedFDerivWithin_mul_le
    (hWu.mono (hsuv.trans Set.inter_subset_left))
    (hFv.mono (hsuv.trans Set.inter_subset_right)) hsopen.uniqueDiffOn hs0 (n := n) le_rfl
  have heq (k : ℕ) (G : ℂ → ℂ) : iteratedFDerivWithin ℝ k G s 0 = iteratedFDeriv ℝ k G 0 :=
    iteratedFDerivWithin_of_isOpen k hsopen hs0
  simp only [heq] at hbound
  apply norm_le_zero_iff.mp
  refine hbound.trans_eq (Finset.sum_eq_zero ?_)
  intro i hi
  by_cases hi0 : i = 0
  · subst i
    simp [norm_iteratedFDeriv_zero, h0]
  · rw [hf (n-i) (by have := Finset.mem_range.mp hi; omega)]
    simp

theorem infinityCoordinate_iteratedFDeriv_unipotent_fixed_of_lower_zero
    (s : ℝ) (t : ℂ) (n : ℕ) (f : PrincipalSeries s)
    (hf : ∀ k < n, iteratedFDeriv ℝ k (infinityCoordinate f) 0 = 0) :
    iteratedFDeriv ℝ n
      (infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)) 0 =
      iteratedFDeriv ℝ n (infinityCoordinate f) 0 := by
  let F : ℂ → ℂ := infinityCoordinate f
  let C : ℂ → ℂ := fun u => u / (1 + u * t)
  let G : ℂ → ℂ := F ∘ C
  have hF : ContDiffAt ℝ n F 0 := (f.2.2.2.of_le (by simp)).contDiffAt
  have hC : ContDiffAt ℝ n C 0 := closedCell_coord_smooth t n
  have hC0 : C 0 = 0 := by simp [C]
  have hG : ContDiffAt ℝ n G 0 :=
    (show ContDiffAt ℝ n F (C 0) by simpa [hC0] using hF).comp 0 hC
  have hW : ContDiffAt ℝ n (weight s t) 0 := closedCell_weight_smooth s t n
  have hlow : ∀ k < n, iteratedFDeriv ℝ k G 0 = 0 := by
    intro k hk
    exact closedCell_comp_zero F C k (by simpa [hC0] using hF.of_le (by exact_mod_cast hk.le))
      (hC.of_le (by exact_mod_cast hk.le)) (by simpa [hC0] using fun i hi => hf i (hi.trans_lt hk))
  have hzero : iteratedFDeriv ℝ n (fun u => (weight s t u - 1) * G u) 0 = 0 :=
    closedCell_mul_flat_top n _ G (hW.sub contDiffAt_const) hG
      (by simp [weight_zero]) hlow
  have htop : iteratedFDeriv ℝ n G 0 = iteratedFDeriv ℝ n F 0 :=
    closedCell_comp_flat_top n F C hF hC hC0 (coord_deriv t).fderiv hf
  have he : (fun u => weight s t u * G u) =
      (fun u => (weight s t u - 1) * G u) + G := by
    funext u
    simp only [Pi.add_apply]
    ring
  rw [((coord_formula_eventually s t f).iteratedFDeriv ℝ n).eq_of_nhds]
  change iteratedFDeriv ℝ n (fun u => weight s t u * G u) 0 = _
  rw [he, iteratedFDeriv_add_apply ((hW.sub contDiffAt_const).mul hG) hG, hzero, zero_add, htop]

private theorem closedCell_difference_flat (s : ℝ) (t : ℂ) (m : ℕ)
    (f : PrincipalSeries s)
    (hf : ∀ k < m, iteratedFDeriv ℝ k (infinityCoordinate f) 0 = 0) :
    ∀ k ≤ m, iteratedFDeriv ℝ k
      (infinityCoordinate ((closedCell_action s t - 1) f)) 0 = 0 := by
  intro k hk
  have hfix := infinityCoordinate_iteratedFDeriv_unipotent_fixed_of_lower_zero
    s t k f (fun i hi => hf i (hi.trans_le hk))
  have hsmooth : ContDiffAt ℝ k (infinityCoordinate f) 0 :=
    (f.2.2.2.of_le (by simp)).contDiffAt
  have hactsmooth : ContDiffAt ℝ k
      (infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f)) 0 :=
    (((pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f).2.2.2).of_le (by simp)).contDiffAt
  change iteratedFDeriv ℝ k
    (infinityCoordinate (pi s (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f) -
      infinityCoordinate f) 0 = 0
  rw [iteratedFDeriv_sub_apply hactsmooth hsmooth, hfix, sub_self]

theorem finite_jet_unipotent_action (s : ℝ) (n : ℕ) :
    ∃ ρ : ℂ → Module.End ℂ (JetSpace s n),
      IsJetAction s n ρ ∧
      ρ 0 = 1 ∧
      (∀ t u : ℂ, ρ (t + u) = ρ t * ρ u) ∧
      (∀ t : ℂ, (ρ t - (1 : Module.End ℂ (JetSpace s n))) ^ (n + 1) = 0) := by
  obtain ⟨ρ, hact, h0, hmul⟩ := finite_jet_action_exists s n
  refine ⟨ρ, hact, h0, hmul, ?_⟩
  intro t
  let D : Module.End ℂ (PrincipalSeries s) := closedCell_action s t - 1
  have hdiff : ∀ f : PrincipalSeries s,
      (ρ t - 1) (sectionJet s n f) = sectionJet s n (D f) := by
    intro f
    rw [LinearMap.sub_apply, Module.End.one_apply, hact]
    change _ = sectionJetLinear s n (D f)
    rw [show D f = closedCell_action s t f - f by rfl, map_sub]
    rfl
  have hpow : ∀ m : ℕ, ∀ f : PrincipalSeries s,
      ((ρ t - 1) ^ m) (sectionJet s n f) = sectionJet s n ((D ^ m) f) := by
    intro m
    induction m with
    | zero => intro f; rfl
    | succ m ih =>
      intro f
      rw [pow_succ, Module.End.mul_apply, hdiff, ih, pow_succ, Module.End.mul_apply]
  have hflat : ∀ m : ℕ, ∀ f : PrincipalSeries s,
      ∀ k < m, iteratedFDeriv ℝ k (infinityCoordinate ((D ^ m) f)) 0 = 0 := by
    intro m
    induction m with
    | zero => intro f k hk; omega
    | succ m ih =>
      intro f k hk
      rw [pow_succ', Module.End.mul_apply]
      exact closedCell_difference_flat s t m ((D ^ m) f) (ih f) k (by omega)
  apply LinearMap.ext
  intro j
  obtain ⟨f, rfl⟩ := sectionJet_surjective s n j
  rw [hpow]
  apply Subtype.ext
  change jetAtInfinity s n ((D ^ (n + 1)) f) = 0
  rw [jetAtInfinity_eq_zero_iff]
  intro k hk
  apply hflat (n + 1) f k
  omega

theorem finite_jet_only_trivial_character (s : ℝ) (n : ℕ)
    (ρ : ℂ → Module.End ℂ (JetSpace s n)) (hρ : IsJetAction s n ρ)
    (ψ : AddChar ℂ Circle) (L : JetSpace s n →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (heigen : ∀ (t : ℂ) (j : JetSpace s n), L (ρ t j) = (ψ t : ℂ) * L j) :
    ψ = 1 := by

  obtain ⟨ρ', hρ'act, _, _, hρ'nil⟩ := finite_jet_unipotent_action s n
  have hρ_eq : ρ = ρ' := by
    funext t
    ext j
    obtain ⟨f, rfl⟩ := sectionJet_surjective s n j
    rw [hρ t f, hρ'act t f]
  obtain ⟨j0, hj0⟩ : ∃ j : JetSpace s n, L j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hL (LinearMap.ext h)
  ext t
  have hnil : (ρ t - 1) ^ (n + 1) = 0 := by
    rw [hρ_eq]; exact hρ'nil t
  have hstep : ∀ m : ℕ, ∀ j : JetSpace s n,
      L (((ρ t - 1) ^ m) j) = ((ψ t : ℂ) - 1) ^ m * L j := by
    intro m
    induction m with
    | zero => intro j; simp
    | succ m ih =>
        intro j
        rw [pow_succ, Module.End.mul_apply, ih]
        have h1 : L ((ρ t - 1) j) = ((ψ t : ℂ) - 1) * L j := by
          have hsub : (ρ t - 1) j = ρ t j - j := by
            rw [LinearMap.sub_apply, Module.End.one_apply]
          rw [hsub, map_sub, heigen]
          ring
        rw [h1]; ring
  have hkey := hstep (n + 1) j0
  rw [hnil] at hkey
  simp only [LinearMap.zero_apply, map_zero] at hkey
  have hpow : ((ψ t : ℂ) - 1) ^ (n + 1) = 0 :=
    (mul_eq_zero.mp hkey.symm).resolve_right hj0
  have hc : (ψ t : ℂ) = 1 :=
    sub_eq_zero.mp ((pow_eq_zero_iff (Nat.succ_ne_zero n)).mp hpow)
  rw [AddChar.one_apply]
  exact hc.trans Circle.coe_one.symm

theorem closed_cell_no_nontrivial_eigen_distribution
    (ψ : AddChar ℂ Circle) (hne : ψ ≠ 1)
    (T : PrincipalSeries positiveParameter →L[ℂ] ℂ)
    (hsupport : SupportedAtInfinity positiveParameter T)
    (heigen : IsEigenDistribution positiveParameter ψ T) : T = 0 := by
  obtain ⟨n, L, hL⟩ := supportedAtInfinity_factors_finite_jet positiveParameter T hsupport
  obtain ⟨ρ, hρact, -, -, -⟩ := finite_jet_unipotent_action positiveParameter n
  have hLzero : L = 0 := by
    by_contra hLne
    exact hne (finite_jet_only_trivial_character positiveParameter n ρ hρact ψ L hLne
      (fun t j => by
        obtain ⟨f, rfl⟩ := sectionJet_surjective positiveParameter n j
        rw [hρact t f, ← hL (pi positiveParameter
          (Matrix.ProjGenLinGroup.mk (upperUnipotent t)) f), ← hL f]
        exact heigen t f))
  apply ContinuousLinearMap.ext
  intro f
  rw [hL f, hLzero]
  rfl

end DedekindZetaZeroFree.KPCplxClosedCellJets

end
