module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SphericalCoefficientSupport
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CompactOrbits.FiniteDimensionality
public import DedekindZetaZeroFree.Eisenstein.Induction.Cubic.SphericalFlatFamilies

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators NNReal
open NumberField
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem finiteSubgroup_eq_finitePart :
    PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ =
      KPGlobalTorusFunctionData.finitePart F ζ hζ := by
  unfold PGLComplex.AdelicSlicesRaw.finiteSubgroup KPGlobalTorusFunctionData.finitePart
  congr 1
  ext x
  simp [PGLComplex.AdelicSlicesRaw.finiteTuples, Subgroup.mem_iInf]

 theorem exists_archFiniteEquiv :
    ∃ e : (KPSmoothActualFlowData.GInfinity F × KPGlobalTorusFunctionData.finitePart F ζ hζ) ≃ₜ*
      KPGlobalTorusFunctionData.G F ζ hζ,
      ∀ a c, e (a, c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have h : ∃ e : (PGLComplex.AdelicSlicesRaw.ArchGroup F ×
      PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) ≃ₜ*
      PGLComplex.AdelicSlicesRaw.ActualCover F ζ hζ,
      ∀ a c, e (a, c) = PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * c.val :=
    ⟨e, he⟩
  rw [finiteSubgroup_eq_finitePart F ζ hζ] at h
  exact h

def archFiniteEquiv :
    (KPSmoothActualFlowData.GInfinity F × KPGlobalTorusFunctionData.finitePart F ζ hζ) ≃ₜ*
      KPGlobalTorusFunctionData.G F ζ hζ :=
  (exists_archFiniteEquiv F ζ hζ).choose

@[simp] theorem archFiniteEquiv_apply (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    archFiniteEquiv F ζ hζ (a, c) = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * c.val :=
  (exists_archFiniteEquiv F ζ hζ).choose_spec a c

def sphericalPGL (a : KPSmoothActualFlowData.GInfinity F) : ℂ :=
  ∏ w, (KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.positiveParameter (a w)
    (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter)) 1

@[simp] theorem sphericalPGL_mk
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    sphericalPGL F (fun w => Matrix.ProjGenLinGroup.mk (a w)) = sphericalProduct F a := by
  simp only [sphericalPGL, sphericalProduct, KPCplxPrincipalSeriesCharts.pi_mk,
    KPCplxPrincipalSeriesCharts.rightTranslate, one_mul]

def scalarSeed
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
    (A : Fin m → ℂ) (g : KPGlobalTorusFunctionData.G F ζ hζ) : ℂ :=
  sphericalPGL F ((archFiniteEquiv F ζ hζ).symm g).1 *
    evalCoefficient F ζ hζ t k A ((archFiniteEquiv F ζ hζ).symm g).2

@[simp] theorem scalarSeed_arch_finite
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ)
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    scalarSeed F ζ hζ t k A (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
      sphericalProduct F a * evalCoefficient F ζ hζ t k A c := by
  rw [← archFiniteEquiv_apply]
  simp only [scalarSeed, (archFiniteEquiv F ζ hζ).symm_apply_apply, sphericalPGL_mk]

private theorem diagonal_projective (B : KPCplxCharacterHaar.ComplexGL2)
    (h10 : B 1 0 = 0) (h01 : B 0 1 = 0) :
    ∃ z : ℂˣ, Matrix.ProjGenLinGroup.mk B = Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ z 1) := by
  let u := (KPGlobalTorusMatrixCertificates.diagonal_units B h10).1.unit
  let v := (KPGlobalTorusMatrixCertificates.diagonal_units B h10).2.unit
  refine ⟨u / v, ?_⟩
  have hB : B = Matrix.GeneralLinearGroup.scalar (Fin 2) v * KubotaRankTwo.d ℂ (u / v) 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
      KubotaRankTwo.d, Matrix.mul_apply, Fin.sum_univ_two, u, v, h10, h01, div_eq_mul_inv]
    have hv : B 1 1 ≠ 0 := (KPGlobalTorusMatrixCertificates.diagonal_units B h10).2.ne_zero
    field_simp
  rw [hB, map_mul, Matrix.ProjGenLinGroup.mk_scalar, one_mul]

private theorem archProjection_torus_diagonal (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    ∃ z : InfinitePlace F → ℂˣ,
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ e.val =
        fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (z w) 1) := by
  obtain ⟨B, hB, h10, h01⟩ := e.property
  let f := fun w : InfinitePlace F => (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom.comp
    (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w))
  have hd : ∀ w, ∃ z : ℂˣ,
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (f w) B) =
        Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ z 1) := by
    intro w
    apply diagonal_projective
    · change f w (B 1 0) = 0
      rw [h10, map_zero]
    · change f w (B 0 1) = 0
      rw [h01, map_zero]
  choose z hz using hd
  refine ⟨z, ?_⟩
  unfold PGLComplex.AdelicSlicesRaw.archProjection
  rw [MonoidHom.comp_apply, ← hB]
  change PGLComplex.AdelicSlicesRaw.glArchProjection F ζ hζ B = _
  funext w
  exact hz w

 theorem full_torus_split (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    ∃ (z : InfinitePlace F → ℂˣ) (ef : KPGlobalTorusFunctionData.E F ζ hζ),
      ef.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ ∧
      e = KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (z w : ℂ)) * ef := by
  obtain ⟨z, hz⟩ := archProjection_torus_diagonal F ζ hζ e
  let d := KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (z w : ℂ))
  let ef := d⁻¹ * e
  refine ⟨z, ef, ?_, ?_⟩
  · have hi : d.val = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (z w) 1)) := by
      exact (KPContinuation.ChamberFlatCasimir.arch_diagonal_insertion F ζ hζ
        (fun w => (z w : ℂ)) (fun w => Units.ne_zero (z w))).symm
    have hp : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ d.val =
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ e.val := by
      rw [hi]
      change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
        (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ _) = _
      rw [PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion, hz]
    have hker := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.2.2.2.1
    have hf : ef.val ∈ (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
      change PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ (d.val⁻¹ * e.val) = 1
      rw [map_mul, map_inv, hp, inv_mul_cancel]
    rw [hker] at hf
    unfold PGLComplex.AdelicSlicesRaw.finiteSubgroup KPGlobalTorusFunctionData.finitePart at *
    have hh : PGLComplex.AdelicSlicesRaw.finiteTuples F ζ hζ =
        ⨅ w : InfinitePlace F, (RestrictedProduct.evalMonoidHom
          (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v) (Sum.inl w)).ker := by
      ext t
      simp [PGLComplex.AdelicSlicesRaw.finiteTuples, Subgroup.mem_iInf]
    rw [hh] at hf
    exact hf
  · change e = d * (d⁻¹ * e)
    simp

private theorem sphericalProduct_diagonal_covariance (F : Type) [Field F] [NumberField F]
    (z : InfinitePlace F → ℂˣ) (a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    sphericalProduct F (fun w => KubotaRankTwo.d ℂ (z w) 1 * a w) =
      (((∏ w : InfinitePlace F, ‖(z w : ℂ)‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) : ℂ) * sphericalProduct F a := by
  have hd (w : InfinitePlace F) : KubotaRankTwo.d ℂ (z w) 1 =
      KPCplxPrincipalSeriesCharts.upperTriangular (z w) 1 0 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.d, KPCplxPrincipalSeriesCharts.upperTriangular]
  have hc (w : InfinitePlace F) := (KPCplxPrincipalSeriesCharts.sphericalSection
    KPCplxPrincipalSeriesCharts.positiveParameter).property.1 (z w) 1 0 (a w)
  simp only [← hd, KPCplxPrincipalSeriesCharts.inductionWeight,
    KPCplxPrincipalSeriesCharts.complexAbs, Units.val_one, div_one,
    KPCplxPrincipalSeriesCharts.positiveParameter] at hc
  have hexp : (1 / 2 : ℝ) + 1 / 6 = 2 / 3 := by norm_num
  simp only [hexp] at hc
  unfold sphericalProduct
  simp_rw [hc]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod]
  change (((∏ w, (‖(z w : ℂ)‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) : ℂ) * _) = _
  rw [Real.finsetProd_rpow Finset.univ (fun w => ‖(z w : ℂ)‖ ^ 2) (by intros; positivity)]

variable (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
variable {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ)

theorem scalarSeed_right_level
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (htU : t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U)
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (u : U.toOpenSubgroup) :
    scalarSeed F ζ hζ t k A (g * u.val.val) = scalarSeed F ζ hζ t k A g := by
  let e := archFiniteEquiv F ζ hζ
  have hex : ∃ a c, (a, c) = e.symm g := ⟨(e.symm g).1, (e.symm g).2, rfl⟩
  obtain ⟨a, c, hac⟩ := hex
  have hg : e (a, c) = g := by rw [hac]; exact e.apply_symm_apply g
  have hu : e (1, u.val) = u.val.val := by
    rw [archFiniteEquiv_apply, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul]
  rw [← hg, ← hu, ← map_mul]
  change sphericalPGL F (e.symm (e (a * 1, c * u.val))).1 *
      evalCoefficient F ζ hζ t k A (e.symm (e (a * 1, c * u.val))).2 = _
  change sphericalPGL F (e.symm (e (a * 1, c * u.val))).1 *
      evalCoefficient F ζ hζ t k A (e.symm (e (a * 1, c * u.val))).2 =
    sphericalPGL F (e.symm (e (a, c))).1 * evalCoefficient F ζ hζ t k A (e.symm (e (a, c))).2
  simp only [e.symm_apply_apply, mul_one]
  exact congrArg (fun z => sphericalPGL F a * z)
    (evalCoefficient_right_level F ζ hζ t k A U htU c u)

def seedFibre (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ) : ℂ :=
  (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e)⁻¹ * scalarSeed F ζ hζ t k A (e.val * g)

theorem scalarSeed_finite_borel_covariance
    (h : (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).H)
    (x : KPGlobalTorusFunctionData.Adeles F)
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (hb : b.val = h.val.val * KPGlobalTorusFunctionData.N F ζ hζ x)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    scalarSeed F ζ hζ t k A (b.val * g) =
      (KPGlobalTorusFunctionData.deltaHalf F ζ hζ h.val *
        ((KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0).character h : ℂ)) *
      scalarSeed F ζ hζ t k A g := by
  let e := archFiniteEquiv F ζ hζ
  have hex : ∃ a c, (a, c) = e.symm g := ⟨(e.symm g).1, (e.symm g).2, rfl⟩
  obtain ⟨a, c, hac⟩ := hex
  have hg : e (a, c) = g := by rw [hac]; exact e.apply_symm_apply g
  have hb' : e (1, b) = b.val := by
    rw [archFiniteEquiv_apply, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul]
  rw [← hg, ← hb', ← map_mul]
  change sphericalPGL F (e.symm (e (1 * a, b * c))).1 *
      evalCoefficient F ζ hζ t k A (e.symm (e (1 * a, b * c))).2 =
    _ * (sphericalPGL F (e.symm (e (a, c))).1 * evalCoefficient F ζ hζ t k A (e.symm (e (a, c))).2)
  simp only [e.symm_apply_apply, one_mul]
  rw [evalCoefficient_finite_borel_covariance F ζ hζ t k A h x b hb c]
  ring

private theorem archInsertion_commutes_finite
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  apply RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite F ζ hζ a
    ⟨c.val, ?_⟩
  change c.val ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ
  rw [finiteSubgroup_eq_finitePart F ζ hζ]
  exact c.property

theorem seedFibre_arch_finite_at_finite_torus
    (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (he : e.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    seedFibre F ζ hζ t k A (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) e =
      sphericalProduct F a * ∑ ν, A ν * fibreValue F ζ hζ t
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val) e := by
  let ef : KPGlobalTorusFunctionData.finitePart F ζ hζ := ⟨e.val, he⟩
  have ha := archInsertion_commutes_finite F ζ hζ
    (fun w => Matrix.ProjGenLinGroup.mk (a w)) ef
  unfold seedFibre
  rw [← mul_assoc, ha.eq.symm, mul_assoc]
  change _ * scalarSeed F ζ hζ t k A
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * (ef * c).val) = _
  rw [scalarSeed_arch_finite]
  unfold evalCoefficient fibreValue
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  have hk := archInsertion_commutes_finite F ζ hζ (k ν).val ef
  change _ * (_ * (A ν * t.val.val
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * (e.val * c.val)))) = _
  have hk' : e.val * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * e.val := hk.eq.symm
  have heq : e.val * (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * (e.val * c.val) := by
    rw [← mul_assoc, hk', mul_assoc]
  rw [heq]
  ring

theorem scalarSeed_arch_diagonal_covariance
    (z : InfinitePlace F → ℂˣ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    scalarSeed F ζ hζ t k A
      ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (z w : ℂ))).val * g) =
      (((∏ w : InfinitePlace F, ‖(z w : ℂ)‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        scalarSeed F ζ hζ t k A g := by
  let e := archFiniteEquiv F ζ hζ
  let a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => (e.symm g).1 w |>.out
  let c := (e.symm g).2
  have ha : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = (e.symm g).1 := by
    funext w
    exact Quotient.out_eq _
  have hg : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val = g := by
    rw [ha, ← archFiniteEquiv_apply]
    exact e.apply_symm_apply g
  have hd := KPContinuation.ChamberFlatCasimir.arch_diagonal_insertion F ζ hζ
    (fun w => (z w : ℂ)) (fun w => Units.ne_zero (z w))
  change scalarSeed F ζ hζ t k A
    (KPGlobalTorusFunctionData.archDiagonalLift F ζ hζ (fun w => (z w : ℂ)) * g) = _
  rw [← hg, ← hd]
  change scalarSeed F ζ hζ t k A
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (z w) 1)) *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val)) = _
  rw [← mul_assoc, ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
  have hm : ((fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (z w) 1)) *
      (fun w => Matrix.ProjGenLinGroup.mk (a w))) =
      fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (z w) 1 * a w) := by
    funext w
    exact (map_mul (Matrix.ProjGenLinGroup.mk : KPCplxCharacterHaar.ComplexGL2 →*
      Matrix.ProjGenLinGroup (Fin 2) ℂ) _ _).symm
  rw [hm, scalarSeed_arch_finite, scalarSeed_arch_finite,
    sphericalProduct_diagonal_covariance]
  ring

theorem seedFibre_arch_finite_all_torus
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    seedFibre F ζ hζ t k A (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) e =
      sphericalProduct F a * ∑ ν, A ν * fibreValue F ζ hζ t
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val) e := by
  obtain ⟨z, ef, hef, he⟩ := full_torus_split F ζ hζ e
  let d := KPGlobalTorusFunctionData.torusArchChart F ζ hζ (fun w => (z w : ℂ))
  let M : ℂ := (((∏ w : InfinitePlace F, ‖(z w : ℂ)‖ ^ 2) ^ (2 / 3 : ℝ) : ℝ) : ℂ)
  have ht (g : KPGlobalTorusFunctionData.G F ζ hζ) : t.val.val (d.val * g) = M * t.val.val g := by
    have hh := ActualRaisingGeometry.source_arch_borel_covariance F ζ hζ t
      (fun w => (z w : ℂ)) (fun w => Units.ne_zero (z w)) 0 g
    have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    simpa only [hn, mul_one] using hh
  have hs (g : KPGlobalTorusFunctionData.G F ζ hζ) :
      scalarSeed F ζ hζ t k A (d.val * g) = M * scalarSeed F ζ hζ t k A g :=
    scalarSeed_arch_diagonal_covariance F ζ hζ t k A z g
  have hf := seedFibre_arch_finite_at_finite_torus F ζ hζ t k A a c ef hef
  unfold seedFibre fibreValue at hf ⊢
  have he' : e.val = d.val * ef.val := congrArg Subtype.val he
  have hte (ν : Fin m) : t.val.val (e.val *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val)) =
      M * t.val.val (ef.val *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val)) := by
    rw [he', mul_assoc, ht]
  simp_rw [hte]
  rw [he', mul_assoc, hs]
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ ef ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    have hn : (((KPGlobalTorusFunctionData.delta F ζ hζ ef : ℝ≥0) : ℝ)) ≠ 0 :=
      NNReal.coe_ne_zero.mpr (Units.ne_zero _)
    have hp := Real.sqrt_pos.mpr (lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hn))
    exact Complex.ofReal_ne_zero.mpr hp.ne'
  have hh := congrArg (fun x : ℂ => KPGlobalTorusFunctionData.deltaHalf F ζ hζ ef * x) hf
  have hclear : scalarSeed F ζ hζ t k A (ef.val *
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val)) =
      sphericalProduct F a * ∑ ν, A ν * t.val.val (ef.val *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val)) := by
    calc
      _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ ef *
          ((KPGlobalTorusFunctionData.deltaHalf F ζ hζ ef)⁻¹ *
            scalarSeed F ζ hζ t k A (ef.val *
              (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
                (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val))) := by
            exact (mul_inv_cancel_left₀ hd _).symm
      _ = _ := by
        rw [hf]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ν _
        field_simp
  rw [hclear]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

def smoothSeedFibre
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    KPGlobalTorusBorelTwistCompatibility.Smooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) :=
  sphericalPGL F ((archFiniteEquiv F ζ hζ).symm g).1 •
    ∑ ν, A ν • T.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val *
      ((archFiniteEquiv F ζ hζ).symm g).2.val)

theorem smoothSeedFibre_value
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    (smoothSeedFibre F ζ hζ k A T g).val.val e = seedFibre F ζ hζ t k A g e := by
  let E := archFiniteEquiv F ζ hζ
  let a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => (E.symm g).1 w |>.out
  let c := (E.symm g).2
  have ha : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = (E.symm g).1 := by
    funext w
    exact Quotient.out_eq _
  have hg : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val = g := by
    rw [ha, ← archFiniteEquiv_apply]
    exact E.apply_symm_apply g
  have hf := seedFibre_arch_finite_all_torus F ζ hζ t k A a c e
  rw [hg] at hf
  rw [hf]
  unfold smoothSeedFibre
  change sphericalPGL F (E.symm g).1 *
      (∑ ν, A ν • T.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val)).val.val e = _
  rw [← ha, sphericalPGL_mk]
  congr 1
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ν _
  rw [← fibreValue_eq_owned_lift F ζ hζ t T hT]

theorem smoothSeedFibre_torus_covariance
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val)
    (b : KPGlobalTorusFunctionData.E F ζ hζ) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    smoothSeedFibre F ζ hζ k A T (b.val * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b •
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
          (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) b
          (smoothSeedFibre F ζ hζ k A T g) := by
  apply Subtype.ext
  apply Subtype.ext
  funext e
  change _ = KPGlobalTorusFunctionData.deltaHalf F ζ hζ b * _
  rw [KPGlobalTorusPeriodizationInverse.rightAction_formula]
  rw [smoothSeedFibre_value F ζ hζ t k A T hT,
    smoothSeedFibre_value F ζ hζ t k A T hT]
  unfold seedFibre
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ (e * b) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ e * KPGlobalTorusFunctionData.deltaHalf F ζ hζ b := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.sqrt_mul (NNReal.coe_nonneg _), Complex.ofReal_mul]
  rw [hd]
  have hb : KPGlobalTorusFunctionData.deltaHalf F ζ hζ b ≠ 0 := by
    unfold KPGlobalTorusFunctionData.deltaHalf
    have hn : (((KPGlobalTorusFunctionData.delta F ζ hζ b : ℝ≥0) : ℝ)) ≠ 0 :=
      NNReal.coe_ne_zero.mpr (Units.ne_zero _)
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr
      (lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hn))).ne'
  change _ * scalarSeed F ζ hζ t k A (e.val * (b.val * g)) =
    _ * (_ * scalarSeed F ζ hζ t k A ((e.val * b.val) * g))
  rw [mul_assoc e.val b.val g, mul_inv_rev]
  field_simp

theorem scalarSeed_upper_root_invariant
    (x : KPGlobalTorusFunctionData.Adeles F)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    scalarSeed F ζ hζ t k A (KPGlobalTorusFunctionData.N F ζ hζ x * g) =
      scalarSeed F ζ hζ t k A g := by
  let nf := KPGlobalTorusFunctionData.N F ζ hζ (0, x.2)
  have hnf : nf ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    refine ⟨KPGlobalTorusFunctionData.rootTuple F ζ hζ (0, x.2), ?_, rfl⟩
    apply Subgroup.mem_iInf.mpr
    intro w
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inl w) 0 = 1
    exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inl w)
  have hfinite (g : KPGlobalTorusFunctionData.G F ζ hζ) :
      scalarSeed F ζ hζ t k A (nf * g) = scalarSeed F ζ hζ t k A g := by
    have hh := scalarSeed_finite_borel_covariance F ζ hζ t k A 1 (0, x.2) ⟨nf, hnf⟩
      (by change nf = 1 * nf; simp) g
    simpa [KPGlobalTorusFunctionData.deltaHalf] using hh
  let E := archFiniteEquiv F ζ hζ
  let a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => (E.symm g).1 w |>.out
  let c := (E.symm g).2
  have ha : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = (E.symm g).1 := by
    funext w
    exact Quotient.out_eq _
  have hg : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val = g := by
    rw [ha, ← archFiniteEquiv_apply]
    exact E.apply_symm_apply g
  let z := KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.complexParameter F ζ hζ x.1
  have harch (g : KPGlobalTorusFunctionData.G F ζ hζ) :
      scalarSeed F ζ hζ t k A (KPGlobalTorusFunctionData.N F ζ hζ (x.1, 0) * g) =
        scalarSeed F ζ hζ t k A g := by
    let aa : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => (E.symm g).1 w |>.out
    let cc := (E.symm g).2
    have haa : (fun w => Matrix.ProjGenLinGroup.mk (aa w)) = (E.symm g).1 := by
      funext w; exact Quotient.out_eq _
    have hgg : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (aa w)) * cc.val = g := by
      rw [haa, ← archFiniteEquiv_apply]; exact E.apply_symm_apply g
    rw [KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.root_arch_insertion,
      ← hgg, ← mul_assoc, ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    have hm : (KPMsResidualTailRestoration.SharpConstantTerm.FiberStability.archRoot z *
        (fun w => Matrix.ProjGenLinGroup.mk (aa w))) =
        fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n ℂ (z w) * aa w) := by
      funext w
      exact (map_mul (Matrix.ProjGenLinGroup.mk : KPCplxCharacterHaar.ComplexGL2 →*
        Matrix.ProjGenLinGroup (Fin 2) ℂ) _ _).symm
    rw [hm, scalarSeed_arch_finite, scalarSeed_arch_finite]
    congr 1
    unfold sphericalProduct
    apply Finset.prod_congr rfl
    intro w _
    have hu : KubotaRankTwo.n ℂ (z w) = KPCplxPrincipalSeriesCharts.upperTriangular 1 1 (z w) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.n, KPCplxPrincipalSeriesCharts.upperTriangular]
    change (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter)
      (KubotaRankTwo.n ℂ (z w) * aa w) = _
    rw [hu]
    simpa [KPCplxPrincipalSeriesCharts.inductionWeight, KPCplxPrincipalSeriesCharts.complexAbs] using
      (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter).property.1
        1 1 (z w) (aa w)
  have hx : x = ((x.1, 0) : KPGlobalTorusFunctionData.Adeles F) +
      ((0, x.2) : KPGlobalTorusFunctionData.Adeles F) := by
    apply Prod.ext <;> simp
  have hN := KPGlobalTorusFunctionData.N_add F ζ hζ
    ((x.1, 0) : KPGlobalTorusFunctionData.Adeles F) ((0, x.2) : KPGlobalTorusFunctionData.Adeles F)
  have hN' : KPGlobalTorusFunctionData.N F ζ hζ x =
      KPGlobalTorusFunctionData.N F ζ hζ (x.1, 0) * KPGlobalTorusFunctionData.N F ζ hζ (0, x.2) := by
    calc
      _ = KPGlobalTorusFunctionData.N F ζ hζ
          (((x.1, 0) : KPGlobalTorusFunctionData.Adeles F) + ((0, x.2) : KPGlobalTorusFunctionData.Adeles F)) :=
        congrArg (KPGlobalTorusFunctionData.N F ζ hζ) hx
      _ = _ := hN
  rw [hN', mul_assoc, harch, hfinite]

theorem smoothSeedFibre_borel_covariance
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val)
    (b : KPGlobalTorusFunctionData.E F ζ hζ) (x : KPGlobalTorusFunctionData.Adeles F)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    smoothSeedFibre F ζ hζ k A T ((b.val * KPGlobalTorusFunctionData.N F ζ hζ x) * g) =
      KPGlobalTorusFunctionData.deltaHalf F ζ hζ b •
        KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ
          (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) b
          (smoothSeedFibre F ζ hζ k A T g) := by
  rw [mul_assoc, smoothSeedFibre_torus_covariance F ζ hζ t k A T hT]
  congr 2
  apply Subtype.ext
  apply Subtype.ext
  funext e
  rw [smoothSeedFibre_value F ζ hζ t k A T hT, smoothSeedFibre_value F ζ hζ t k A T hT]
  unfold seedFibre
  congr 1
  have hh := ActualBorelRetraction.torus_conjugates_root F ζ hζ e x
  have hr : e.val * KPGlobalTorusFunctionData.N F ζ hζ x =
      KPGlobalTorusFunctionData.N F ζ hζ ((KPGlobalTorusFunctionData.p F ζ hζ e : KPGlobalTorusFunctionData.Adeles F) * x) * e.val := by
    rw [← hh]
    group
  rw [← mul_assoc, hr, mul_assoc, scalarSeed_upper_root_invariant F ζ hζ t k A]

def seededInducedFunctions
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val) :
    KPGlobalTorusBorelTwistCompatibility.InducedFunctions F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) :=
  ⟨smoothSeedFibre F ζ hζ k A T,
    smoothSeedFibre_borel_covariance F ζ hζ t k A T hT⟩

open scoped Matrix.Norms.Elementwise in
private theorem sphericalProduct_left_chart_smooth
    (a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : KPGlobalTorusBorelTwistCompatibility.GroupArch F =>
        sphericalProduct F (fun w => KPLiteralChamber.leftMatrix (z w) * a w))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  unfold sphericalProduct
  apply contDiffOn_prod
  intro w _
  let P := fun z : KPGlobalTorusBorelTwistCompatibility.GroupArch F =>
    (!![z w 1, z w 1*z w 2; z w 0*z w 1, 1+z w 0*z w 1*z w 2]) * (a w).val
  have hP : ContDiff ℝ (⊤ : ℕ∞) P := by
    unfold P
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> fun_prop
  have he (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F)
      (hz : z ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) :
      P z = (KPLiteralChamber.leftMatrix (z w) * a w).val := by
    simp only [P, Units.val_mul, KPLiteralChamber.leftMatrix_val _ (hz w)]
  have hs := (KPCplxPrincipalSeriesCharts.principalSeries_mem_iff _ _).mp
    (KPCplxPrincipalSeriesCharts.sphericalSection KPCplxPrincipalSeriesCharts.positiveParameter).property
  have hm := hs.2.comp hP.contDiffOn (fun z hz => by
    rw [he z hz]
    exact Matrix.GeneralLinearGroup.det_ne_zero _)
  apply hm.congr
  intro z hz
  dsimp only [Function.comp_apply]
  rw [he z hz]
  unfold KPCplxPrincipalSeriesCharts.matrixFunction
  rw [dite_eq_left (Matrix.GeneralLinearGroup.det_ne_zero _)]
  congr 1

theorem scalarSeed_group_chart_smooth
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => scalarSeed F ζ hζ t k A
        (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  let E := archFiniteEquiv F ζ hζ
  let a : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 := fun w => (E.symm g).1 w |>.out
  let c := (E.symm g).2
  have ha : (fun w => Matrix.ProjGenLinGroup.mk (a w)) = (E.symm g).1 := by
    funext w; exact Quotient.out_eq _
  have hg : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val = g := by
    rw [ha, ← archFiniteEquiv_apply]; exact E.apply_symm_apply g
  have he (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F) :
      scalarSeed F ζ hζ t k A (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) =
      sphericalProduct F (fun w => KPLiteralChamber.leftMatrix (z w) * a w) *
        evalCoefficient F ζ hζ t k A c := by
    rw [KPLiteralChamber.left_insertion, ← hg, ← mul_assoc,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    have hh : ((fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.leftMatrix (z w))) *
        (fun w => Matrix.ProjGenLinGroup.mk (a w))) =
        fun w => Matrix.ProjGenLinGroup.mk (KPLiteralChamber.leftMatrix (z w) * a w) := by
      funext w
      exact (map_mul (Matrix.ProjGenLinGroup.mk : KPCplxCharacterHaar.ComplexGL2 →*
        Matrix.ProjGenLinGroup (Fin 2) ℂ) _ _).symm
    rw [hh, scalarSeed_arch_finite]
  simpa only [he] using (sphericalProduct_left_chart_smooth F a).mul contDiffOn_const

def seededInducedLevel
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (htU : t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U) :
    KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) U := by
  refine ⟨seededInducedFunctions F ζ hζ t k A T hT, ?_, ?_⟩
  · intro g
    have hv (z : KPGlobalTorusBorelTwistCompatibility.GroupArch F) :
        ((seededInducedFunctions F ζ hζ t k A T hT).val
          (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1 =
        scalarSeed F ζ hζ t k A (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g) := by
      change (smoothSeedFibre F ζ hζ k A T _).val.val 1 = _
      rw [smoothSeedFibre_value F ζ hζ t k A T hT]
      simp [seedFibre, KPGlobalTorusFunctionData.deltaHalf]
    simpa only [hv] using scalarSeed_group_chart_smooth F ζ hζ t k A g
  · intro g u
    apply Subtype.ext
    apply Subtype.ext
    funext e
    change (smoothSeedFibre F ζ hζ k A T (g * u.val)).val.val e =
      (smoothSeedFibre F ζ hζ k A T g).val.val e
    rw [smoothSeedFibre_value F ζ hζ t k A T hT, smoothSeedFibre_value F ζ hζ t k A T hT]
    unfold seedFibre
    rw [← mul_assoc]
    congr 1
    obtain ⟨v, hv, he⟩ := u.property
    let v' : U.toOpenSubgroup := ⟨v, hv⟩
    have hh := scalarSeed_right_level F ζ hζ t k A U htU (e.val * g) v'
    have hvu : v.val = u.val := he
    simpa only [v', hvu] using hh

theorem seededInducedLevel_value
    (T : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (hT : KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) T = t.val)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (htU : t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) (e : KPGlobalTorusFunctionData.E F ζ hζ) :
    ((seededInducedLevel F ζ hζ t k A T hT U htU).val.val g).val.val e =
      seedFibre F ζ hζ t k A g e :=
  smoothSeedFibre_value F ζ hζ t k A T hT g e

include ζ hζ in

theorem sphericalPGL_right_KInfinity
    (a : KPSmoothActualFlowData.GInfinity F)
    (q : KPContSectorArchSphericalFibers.KInfinity F) :
    sphericalPGL F (a * q.val) = sphericalPGL F a := by
  obtain ⟨r, hr⟩ := KPContinuation.ArchCompact.KInfinity_has_su2 F ζ hζ q
  unfold sphericalPGL
  apply Finset.prod_congr rfl
  intro w _
  have hmem : q.val w ∈ KPCplxPrincipalSeriesCharts.compactSubgroup := by
    exact ⟨r w, hr w⟩
  change (KPCplxPrincipalSeriesCharts.pi _ (a w * q.val w) _) 1 = _
  rw [KPCplxPrincipalSeriesCharts.pi_mul,
    KPCplxPrincipalSeriesCharts.sphericalSection_fixed _ ⟨q.val w, hmem⟩]

theorem scalarSeed_right_KInfinity
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ)
    (q : KPContSectorArchSphericalFibers.KInfinity F) :
    scalarSeed F ζ hζ t k A (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ q.val) =
      scalarSeed F ζ hζ t k A g := by
  let E := archFiniteEquiv F ζ hζ
  let a := (E.symm g).1
  let c := (E.symm g).2
  have hg : g = E (a, c) := (E.apply_symm_apply g).symm
  have hq : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ q.val = E (q.val, 1) := by
    simp [E, archFiniteEquiv_apply]
  rw [hg, hq, ← map_mul]
  change sphericalPGL F (E.symm (E (a * q.val, c * 1))).1 *
    evalCoefficient F ζ hζ t k A (E.symm (E (a * q.val, c * 1))).2 =
    sphericalPGL F (E.symm (E (a, c))).1 *
    evalCoefficient F ζ hζ t k A (E.symm (E (a, c))).2
  simp only [E.symm_apply_apply, mul_one]
  rw [sphericalPGL_right_KInfinity F ζ hζ]

def scalarReset {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
    (A : Fin m → ℂ) :
    (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) →ₗ[ℂ]
      (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) where
  toFun f g := sphericalPGL F ((archFiniteEquiv F ζ hζ).symm g).1 *
    ∑ ν, A ν * f (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val *
      ((archFiniteEquiv F ζ hζ).symm g).2.val)
  map_add' f h := by
    funext g
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z f := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ν _
    ring

@[simp] theorem scalarReset_source
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ) :
    scalarReset F ζ hζ k A t.val.val = scalarSeed F ζ hζ t k A := rfl

theorem scalarReset_finite_equivariant
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ)
    (f : KPGlobalTorusFunctionData.G F ζ hζ → ℂ)
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    scalarReset F ζ hζ k A (fun x => f (x * b.val)) g =
      scalarReset F ζ hζ k A f (g * b.val) := by
  let E := archFiniteEquiv F ζ hζ
  let a := (E.symm g).1
  let c := (E.symm g).2
  have hg : g = E (a, c) := (E.apply_symm_apply g).symm
  have hb : b.val = E (1, b) := by
    dsimp only [E]
    rw [archFiniteEquiv_apply,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul]
  rw [hg, hb, ← map_mul]
  change sphericalPGL F (E.symm (E (a, c))).1 *
    (∑ ν, A ν * f ((KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val *
      (E.symm (E (a, c))).2.val) * E (1, b))) =
    sphericalPGL F (E.symm (E (a * 1, c * b))).1 *
      (∑ ν, A ν * f (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val *
        (E.symm (E (a * 1, c * b))).2.val))
  simp only [E.symm_apply_apply, mul_one]
  rw [← hb]
  simp only [Subgroup.coe_mul, mul_assoc]

private theorem archProjection_compact
    (q : (KPContFlatSourceRecipe.D F ζ hζ).K) (w : InfinitePlace F) :
    PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ q.val w ∈
      KPCplxPrincipalSeriesCharts.compactSubgroup := by
  have hq : q.val ∈ PrincipalOfKP.iwasawaCompactSubgroupMax F ζ hζ := q.property
  obtain ⟨x, hx, he⟩ := Subgroup.mem_map.mp hq
  rw [← he]
  rw [MonoidHom.comp_apply, PGLComplex.AdelicSlicesRaw.archProjection_restricted_eval]
  let p : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) →*
      Matrix.ProjGenLinGroup (Fin 2) ℂ :=
    Matrix.ProjGenLinGroup.mk.comp ((Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivComplexOfIsComplex
        (KPHilbert.infinite_isComplex F ζ hζ w)).toRingHom).comp
      (KPLocalCover.projection F ζ hζ (Sum.inl w)))
  have hp : PrincipalOfKP.archimedeanLocalCompact F ζ hζ w ≤
      KPCplxPrincipalSeriesCharts.compactSubgroup.comap p := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨r, rfl⟩
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)
    change Matrix.ProjGenLinGroup.mk ((Matrix.GeneralLinearGroup.map e.toRingHom)
      ((Matrix.GeneralLinearGroup.map e.symm.toRingHom)
        (KPCplxCharacterHaar.complexSU2Embedding r))) ∈ KPCplxPrincipalSeriesCharts.compactSubgroup
    have hi : (Matrix.GeneralLinearGroup.map e.toRingHom)
        ((Matrix.GeneralLinearGroup.map e.symm.toRingHom)
          (KPCplxCharacterHaar.complexSU2Embedding r)) =
        KPCplxCharacterHaar.complexSU2Embedding r := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      simp [Matrix.GeneralLinearGroup.map_apply]
    rw [hi]
    exact ⟨r, rfl⟩
  exact hp (hx (Sum.inl w))

private theorem split_archProjection (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ((archFiniteEquiv F ζ hζ).symm g).1 =
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ g := by
  obtain ⟨⟨a, c⟩, hg⟩ := (archFiniteEquiv F ζ hζ).surjective g
  rw [← hg, (archFiniteEquiv F ζ hζ).symm_apply_apply, archFiniteEquiv_apply, map_mul]
  have hc : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ c.val = 1 := by
    have hk := (PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ).choose_spec.2.2.2.1
    have hle : KPGlobalTorusFunctionData.finitePart F ζ hζ ≤
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ).ker := by
      rw [hk, finiteSubgroup_eq_finitePart F ζ hζ]
    exact hle c.property
  have ha : PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) = a :=
    PGLComplex.AdelicSlicesRaw.archProjection_archimedeanInsertion F ζ hζ a
  rw [ha, hc, mul_one]

theorem full_compact_arch_finite_factor
    (q : (KPContFlatSourceRecipe.D F ζ hζ).K) :
    ∃ (a : KPSmoothActualFlowData.GInfinity F)
      (b : KPGlobalTorusFunctionData.finitePart F ζ hζ),
      (∀ w, a w ∈ KPCplxPrincipalSeriesCharts.compactSubgroup) ∧
      b.val ∈ (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      q.val = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * b.val := by
  let E := archFiniteEquiv F ζ hζ
  let a := (E.symm q.val).1
  let b := (E.symm q.val).2
  have ha (w : InfinitePlace F) : a w ∈ KPCplxPrincipalSeriesCharts.compactSubgroup := by
    dsimp only [a, E]
    rw [split_archProjection F ζ hζ]
    exact archProjection_compact F ζ hζ q w
  have hrep (w : InfinitePlace F) : ∃ r : KPCplxCharacterHaar.ComplexSU2,
      Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding r) = a w := ha w
  choose r hr using hrep
  have hae : a = fun w => Matrix.ProjGenLinGroup.mk
      (KPCplxCharacterHaar.complexSU2Embedding (r w)) := by
    funext w
    exact (hr w).symm
  have hak : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a ∈
      (KPContFlatSourceRecipe.D F ζ hζ).K := by
    rw [hae, (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hg
    exact KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ w (r w)
  have he : q.val = KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * b.val :=
    (E.apply_symm_apply q.val).symm.trans (archFiniteEquiv_apply F ζ hζ a b)
  refine ⟨a, b, ha, ?_, he⟩
  have hb : b.val = (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a)⁻¹ * q.val := by
    rw [he, inv_mul_cancel_left]
  rw [hb]
  exact (KPContFlatSourceRecipe.D F ζ hζ).K.mul_mem
    ((KPContFlatSourceRecipe.D F ζ hζ).K.inv_mem hak) q.property

theorem scalarSeed_raw_compact_orbit_finiteDimensional
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    {m : ℕ} (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F) (A : Fin m → ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun q : (KPContFlatSourceRecipe.D F ζ hζ).K =>
        fun g => scalarSeed F ζ hζ t k A (g * q.val)))) := by
  let W := Submodule.span ℂ (Set.range
    (fun q : (KPContFlatSourceRecipe.D F ζ hζ).K => fun g => t.val.val (g * q.val)))
  let L := scalarReset F ζ hζ k A
  haveI : FiniteDimensional ℂ W :=
    KPGlobalResidualKernel.ScatteringResidue.source_raw_compact_orbit_finiteDimensional_public t
  haveI : FiniteDimensional ℂ (W.map L) := inferInstance
  apply Submodule.finiteDimensional_of_le (S₂ := W.map L)
  apply Submodule.span_le.mpr
  rintro f ⟨q, rfl⟩
  obtain ⟨a, b, ha, hb, hq⟩ := full_compact_arch_finite_factor F ζ hζ q
  let qf : (KPContFlatSourceRecipe.D F ζ hζ).K := ⟨b.val, hb⟩
  refine Submodule.mem_map.mpr ⟨(fun g => t.val.val (g * qf.val)),
    Submodule.subset_span ⟨qf, rfl⟩, ?_⟩
  funext g
  rw [scalarReset_finite_equivariant F ζ hζ, scalarReset_source]
  change scalarSeed F ζ hζ t k A (g * b.val) = scalarSeed F ζ hζ t k A (g * q.val)
  rw [hq]
  let E := archFiniteEquiv F ζ hζ
  have he : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a * b.val = E (a, b) :=
    (archFiniteEquiv_apply F ζ hζ a b).symm
  rw [he]
  have hg : g = E (E.symm g) := (E.apply_symm_apply g).symm
  have heb : b.val = E (1, b) := by
    dsimp only [E]
    rw [archFiniteEquiv_apply,
      (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).1, one_mul]
  rw [hg, heb, ← map_mul, ← map_mul]
  change sphericalPGL F (E.symm (E (E.symm g * (1, b)))).1 *
    evalCoefficient F ζ hζ t k A (E.symm (E (E.symm g * (1, b)))).2 =
    sphericalPGL F (E.symm (E (E.symm g * (a, b)))).1 *
    evalCoefficient F ζ hζ t k A (E.symm (E (E.symm g * (a, b)))).2
  simp only [E.symm_apply_apply, Prod.fst_mul, Prod.snd_mul, mul_one]
  congr 1
  unfold sphericalPGL
  apply Finset.prod_congr rfl
  intro w _
  change (KPCplxPrincipalSeriesCharts.pi _ ((E.symm g).1 w) _) 1 =
    (KPCplxPrincipalSeriesCharts.pi _ ((E.symm g).1 w * a w) _) 1
  rw [KPCplxPrincipalSeriesCharts.pi_mul,
    KPCplxPrincipalSeriesCharts.sphericalSection_fixed _ ⟨a w, ha w⟩]

set_option backward.isDefEq.respectTransparency false in
private theorem seed_sourceCore_mem_of_raw_compact_orbit
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (v : KPMsRationalCompactCrossPairing.Source F ζ hζ 0)
    (hv : v ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0))
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (hU : ∀ g (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U),
      v.val (g * u.val) = v.val g)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun k : D.K => fun g => v.val (g * k.val))))) :
    v ∈ KPMsRationalCompactCrossPairing.sourceCore F ζ hζ D := by
  let ρ := (KPGlobalTorusFunctionData.borelRightTranslation F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).comp D.K.subtype
  let W := Submodule.span ℂ (Set.range (fun k : D.K => ρ k v))
  let i := (KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)).subtype
  have himage : W.map i = Submodule.span ℂ (Set.range
      (fun k : D.K => fun g => v.val (g * k.val))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  haveI : FiniteDimensional ℂ (W.map i) := by rw [himage]; exact hfin
  haveI : FiniteDimensional ℂ W :=
    FiniteDimensional.of_injective
      ((i.comp W.subtype).codRestrict (W.map i) (fun w =>
        Submodule.mem_map.mpr ⟨w.val, w.property, rfl⟩))
      (by
        intro x y h
        apply Subtype.ext
        apply Subtype.ext
        simpa only [LinearMap.codRestrict_apply, LinearMap.comp_apply,
          Submodule.subtype_apply, i] using congrArg (fun z : W.map i => z.val) h)
  have hstable : CompactProjectors.IsStable ρ W := by
    intro k w hw
    apply Submodule.span_induction (p := fun w _ => ρ k w ∈ W) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨l, rfl⟩
      have heq : ρ k (ρ l v) = ρ (k * l) v := by
        rw [map_mul]; rfl
      rw [heq]
      exact Submodule.subset_span ⟨k * l, rfl⟩
    · simpa using W.zero_mem
    · intro x y hx hy hxm hym
      simpa only [map_add] using W.add_mem hxm hym
    · intro c x hx hxm
      simpa only [map_smul] using W.smul_mem c hxm
  let τ : KPGlobalEisensteinData.CompactTypeStage ρ := ⟨W, inferInstance, hstable⟩
  apply Submodule.mem_iSup_of_mem U
  apply Submodule.mem_iSup_of_mem τ
  refine ⟨⟨hv, ?_⟩, ?_⟩
  · intro u
    ext g
    exact hU g ⟨u.val.val, Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩⟩
  · have heq : ρ 1 v = v := by rw [map_one]; rfl
    rw [← heq]
    exact Submodule.subset_span ⟨1, rfl⟩

theorem actual_source_finite_evaluation_spherical_reseeding
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ))
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    (htU : t ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U)
    (hUK : KPGlobalTorusFunctionData.globalLevel F ζ hζ U ≤
      (KPContFlatSourceRecipe.D F ζ hζ).K)
    (m : ℕ) (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
    (A : Fin m → ℂ) :
    ∃ (U' : KPMsRationalCompactCrossPairing.Level F ζ hζ)
      (v : KPContActualSphericalFlatStage.Stage F ζ hζ U'),
      U'.toOpenSubgroup ≤ U.toOpenSubgroup ∧
      KPGlobalTorusFunctionData.globalLevel F ζ hζ U' ≤
        (KPContFlatSourceRecipe.D F ζ hζ).K ∧
      (∀ (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        v.val.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
          sphericalProduct F a * evalCoefficient F ζ hζ t k A c) ∧
      (∀ (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
        (e : KPGlobalTorusFunctionData.E F ζ hζ),
        fibreValue F ζ hζ v.val
          (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
            (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) e =
          sphericalProduct F a * ∑ ν, A ν * fibreValue F ζ hζ t
            (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k ν).val * c.val) e) := by
  have ht : t.val ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
    have hle : KPMsRationalCompactCrossPairing.sourceCore F ζ hζ
        (KPContFlatSourceRecipe.D F ζ hζ) ≤
        KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
          (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
      unfold KPMsRationalCompactCrossPairing.sourceCore KPGlobalEisensteinData.hcHeckeCore
      exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left
    exact hle t.property
  obtain ⟨T, hT⟩ := ht
  let R := seededInducedLevel F ζ hζ t k A T hT U htU
  let RI : KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) :=
    ⟨R.val, Submodule.mem_iSup_of_mem U R.property⟩
  let r := KPGlobalTorusBorelTwistCompatibility.scalarSection F ζ hζ
    (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) RI
  have hr (g : KPGlobalTorusFunctionData.G F ζ hζ) : r.val g = scalarSeed F ζ hζ t k A g := by
    change (R.val.val g).val.val 1 = _
    rw [seededInducedLevel_value F ζ hζ t k A T hT U htU]
    simp [seedFibre, KPGlobalTorusFunctionData.deltaHalf]
  have hsmooth : r ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := ⟨RI, rfl⟩
  have hright (g : KPGlobalTorusFunctionData.G F ζ hζ)
      (u : KPGlobalTorusFunctionData.globalLevel F ζ hζ U) : r.val (g * u.val) = r.val g := by
    rw [hr, hr]
    obtain ⟨v, hv, he⟩ := u.property
    let v' : U.toOpenSubgroup := ⟨v, hv⟩
    have hvu : v.val = u.val := he
    simpa only [v', hvu] using scalarSeed_right_level F ζ hζ t k A U htU g v'
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      (fun q : (KPContFlatSourceRecipe.D F ζ hζ).K => fun g => r.val (g * q.val)))) := by
    have hre : r.val = scalarSeed F ζ hζ t k A := funext hr
    rw [hre]
    exact scalarSeed_raw_compact_orbit_finiteDimensional F ζ hζ t k A
  let v : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ) :=
    ⟨r, seed_sourceCore_mem_of_raw_compact_orbit F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ) r hsmooth U hright hfin⟩
  have hvU : v ∈ KPContFlatCommonLevelKernel.CommonLevel F ζ hζ U := by
    rw [KPContFlatCommonLevelKernel.commonLevel_eq_fixedPlus_of_le F ζ hζ U hUK]
    exact hright
  have hvK : v ∈ KPContFlatCommonLevelKernel.rightKInfinityFixed F ζ hζ := by
    intro g q
    change r.val _ = r.val g
    rw [hr, hr]
    exact scalarSeed_right_KInfinity F ζ hζ t k A g q
  let vs : KPContActualSphericalFlatStage.Stage F ζ hζ U := ⟨v, hvU, hvK⟩
  refine ⟨U, vs, le_rfl, hUK, ?_, ?_⟩
  · intro a c
    change r.val _ = _
    rw [hr, scalarSeed_arch_finite]
  · intro a c e
    change (KPGlobalTorusFunctionData.deltaHalf F ζ hζ e)⁻¹ * r.val _ = _
    rw [hr]
    exact seedFibre_arch_finite_all_torus F ζ hζ t k A a c e

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

end
