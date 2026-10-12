module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ClosedCellEvaluation

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPLocalInductionJacquetReciprocity

open scoped NumberField NNReal
open NumberField IsDedekindDomain
open KPLocalSmoothRepresentation

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F)) (m : ℕ)
  (hm : KPLocalChartTopology.MatrixChartDepth F w m)

def torusToBorel : Torus F ζ hζ w →* Borel F ζ hζ w := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact Subgroup.inclusion
    (KPRankOneInduction.coveredTorus_le_Borel F w (projection F ζ hζ w))

theorem upperRoot_mem_borel (x : Multiplicative (KPRankOneInduction.LocalField F w)) :
    upperRoot F ζ hζ w x ∈ Borel F ζ hζ w := by
  exact KPJacquetClosedCellBump.upperRoot_mem_borel F ζ hζ w x

private theorem ordinaryPGLMap_injective : Function.Injective (ordinaryPGLMap F w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro a b
  induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
      intro h
      change Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B at h
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
      apply (QuotientGroup.mk'_eq_mk' _).mpr
      exact ⟨KPScalarSplitCentral.scalarMatrix F (Sum.inr w) u, ⟨u, rfl⟩, hu⟩

private theorem projection_kernel_central :
    (projection F ζ hζ w).ker ≤ Subgroup.center (FiniteCover F ζ hζ w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro g hg
  have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g = 1 := by
    apply ordinaryPGLMap_injective F w
    exact hg
  apply KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr w)
  rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
  exact he

private theorem projection_kernel_finite : Finite (projection F ζ hζ w).ker := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  have hex (g : (projection F ζ hζ w).ker) :
      ∃ z, KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) z = g.val := by
    have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g.val = 1 := by
      apply ordinaryPGLMap_injective F w
      exact g.property
    have hr := KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr w)
    rw [← MonoidHom.mem_ker, ← hr] at he
    exact he
  let e : (projection F ζ hζ w).ker → rootsOfUnity 3 F := fun g => Classical.choose (hex g)
  have he (g : (projection F ζ hζ w).ker) :
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) (e g) = g.val :=
    Classical.choose_spec (hex g)
  exact Finite.of_injective e (fun a b h => Subtype.ext (by rw [← he a, ← he b, h]))

private theorem projection_surjective : Function.Surjective (projection F ζ hζ w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro g
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨b, hb⟩ := KPPGLLocalCover.projection_surjective F ζ hζ (Sum.inr w)
    (KPPGLLocalCover.baseQuotient F (Sum.inr w) A)
  exact ⟨b, congrArg (ordinaryPGLMap F w) hb⟩

private theorem upperRoot_projection (x : Multiplicative (KPRankOneInduction.LocalField F w)) :
    projection F ζ hζ w (upperRoot F ζ hζ w x) = KPRankOneInduction.ordinaryUpperRootHom F w x := by
  change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n _ _) =
    Matrix.ProjGenLinGroup.mk (KPRankOneInduction.upperRootMatrix F w _)
  rfl

private theorem upperRoot_injective : Function.Injective (upperRoot F ζ hζ w) := by
  intro x y h
  have he := congrArg (projection F ζ hζ w) h
  rw [upperRoot_projection, upperRoot_projection] at he
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
  have h11 := congrArg (fun A : KPRankOneInduction.GL2 F w => A 1 1) hu
  have h01 := congrArg (fun A : KPRankOneInduction.GL2 F w => A 0 1) hu
  simp [KPRankOneInduction.ordinaryUpperRootHom, KPRankOneInduction.upperRootElement,
    KPRankOneInduction.upperRootMatrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar] at h11 h01
  apply Multiplicative.toAdd.injective
  simpa [h11] using h01

 theorem exists_root_retraction :
    ∃ q : Borel F ζ hζ w →* Torus F ζ hζ w,
      (∀ h : Torus F ζ hζ w, q ⟨h.val, by
        obtain ⟨A, hA, h10, h01⟩ := h.property
        exact ⟨A, hA, h10⟩⟩ = h) ∧
      (∀ x, q ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩ = 1) ∧
      (∀ b : Borel F ζ hζ w, b.val * (q b : FiniteCover F ζ hζ w)⁻¹ ∈
        (upperRoot F ζ hζ w).range) := by
  letI : TopologicalSpace (FiniteCover F ζ hζ w) := ⊥
  letI : DiscreteTopology (FiniteCover F ζ hζ w) := ⟨rfl⟩
  letI : IsTopologicalGroup (FiniteCover F ζ hζ w) := inferInstance
  letI := projection_kernel_finite F ζ hζ w
  exact KPRankOneInduction.exists_canonicalBorelRetraction F w (projection F ζ hζ w)
    (projection_kernel_central F ζ hζ w) (projection_surjective F ζ hζ w)
    (upperRoot F ζ hζ w) (upperRoot_projection F ζ hζ w)

theorem borel_factorization (b : Borel F ζ hζ w) :
    ∃! p : Torus F ζ hζ w × Multiplicative (KPRankOneInduction.LocalField F w),
      (b : FiniteCover F ζ hζ w) = (p.1 : FiniteCover F ζ hζ w) * upperRoot F ζ hζ w p.2 := by
  classical
  obtain ⟨q, hqt, hqn, hqd⟩ := exists_root_retraction F ζ hζ w
  let hb (h : Torus F ζ hζ w) : Borel F ζ hζ w := ⟨h.val, by
    obtain ⟨A, hA, h10, h01⟩ := h.property
    exact ⟨A, hA, h10⟩⟩
  have hk : q ((hb (q b))⁻¹ * b) = 1 := by simp [hb, hqt]
  have hd := hqd ((hb (q b))⁻¹ * b)
  rw [hk] at hd
  change (q b).val⁻¹ * b.val * (1 : FiniteCover F ζ hζ w)⁻¹ ∈ _ at hd
  simp only [inv_one, mul_one] at hd
  obtain ⟨x, hx⟩ := hd
  have he : b.val = (q b).val * upperRoot F ζ hζ w x := by rw [hx]; group
  refine ⟨(q b, x), he, ?_⟩
  rintro ⟨h, y⟩ hy
  have hby : b = hb h * ⟨upperRoot F ζ hζ w y, upperRoot_mem_borel F ζ hζ w y⟩ :=
    Subtype.ext hy
  have hh : q b = h := by rw [hby, map_mul, hqn, mul_one]; exact hqt h
  apply Prod.ext
  · exact hh.symm
  · apply upperRoot_injective F ζ hζ w
    apply mul_left_cancel (a := h.val)
    rw [← hy, ← hh]
    exact he

 theorem chosen_retraction_eq (b : Borel F ζ hζ w)
    (q : Borel F ζ hζ w →* Torus F ζ hζ w)
    (hqt : ∀ h : Torus F ζ hζ w, q ⟨h.val, by
      obtain ⟨A, hA, h10, h01⟩ := h.property
      exact ⟨A, hA, h10⟩⟩ = h)
    (hqn : ∀ x, q ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩ = 1) :
    (Classical.choose (ExistsUnique.exists (borel_factorization F ζ hζ w b))).1 = q b := by
  let p := Classical.choose (ExistsUnique.exists (borel_factorization F ζ hζ w b))
  have hp := Classical.choose_spec (ExistsUnique.exists (borel_factorization F ζ hζ w b))
  have he : b = (⟨p.1.val, by
    obtain ⟨A, hA, h10, h01⟩ := p.1.property
    exact ⟨A, hA, h10⟩⟩ : Borel F ζ hζ w) *
    ⟨upperRoot F ζ hζ w p.2, upperRoot_mem_borel F ζ hζ w p.2⟩ := Subtype.ext hp
  change p.1 = q b
  rw [he, map_mul, hqt, hqn, mul_one]

def borelRetraction : Borel F ζ hζ w →* Torus F ζ hζ w where
  toFun b := (Classical.choose (ExistsUnique.exists
    (borel_factorization F ζ hζ w b))).1
  map_one' := by
    obtain ⟨q, hqt, hqn, hqd⟩ := exists_root_retraction F ζ hζ w
    rw [chosen_retraction_eq F ζ hζ w 1 q hqt hqn, map_one]
  map_mul' := by
    intro a b
    obtain ⟨q, hqt, hqn, hqd⟩ := exists_root_retraction F ζ hζ w
    rw [chosen_retraction_eq F ζ hζ w (a * b) q hqt hqn,
      chosen_retraction_eq F ζ hζ w a q hqt hqn,
      chosen_retraction_eq F ζ hζ w b q hqt hqn, map_mul]

set_option maxHeartbeats 1000000 in
@[simp] theorem borelRetraction_torus (h : Torus F ζ hζ w) :
    borelRetraction F ζ hζ w (torusToBorel F ζ hζ w m hm h) = h := by
  have hf := borel_factorization F ζ hζ w (torusToBorel F ζ hζ w m hm h)
  have hc := Classical.choose_spec (ExistsUnique.exists hf)
  have hp : (torusToBorel F ζ hζ w m hm h : FiniteCover F ζ hζ w) =
      (h : FiniteCover F ζ hζ w) * upperRoot F ζ hζ w 1 := by
    change h.val = h.val * upperRoot F ζ hζ w 1
    rw [map_one, mul_one]
  have he : Classical.choose (ExistsUnique.exists hf) = (h, 1) :=
    hf.unique hc hp
  exact congrArg Prod.fst he

set_option maxHeartbeats 1000000 in
@[simp] theorem borelRetraction_upperRoot
    (x : Multiplicative (KPRankOneInduction.LocalField F w)) :
    borelRetraction F ζ hζ w
      ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩ = 1 := by
  let b : Borel F ζ hζ w := ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩
  have hf := borel_factorization F ζ hζ w b
  have hc := Classical.choose_spec (ExistsUnique.exists hf)
  have hp : b.val = ((1 : Torus F ζ hζ w) : FiniteCover F ζ hζ w) * upperRoot F ζ hζ w x := by simp [b]
  have he : Classical.choose (ExistsUnique.exists hf) = (1, x) :=
    hf.unique hc hp
  exact congrArg Prod.fst he

theorem borelRetraction_decomposition (b : Borel F ζ hζ w) :
    ∃ x : Multiplicative (KPRankOneInduction.LocalField F w),
      (b : FiniteCover F ζ hζ w) =
        (borelRetraction F ζ hζ w b : FiniteCover F ζ hζ w) * upperRoot F ζ hζ w x := by
  exact ⟨(Classical.choose (ExistsUnique.exists (borel_factorization F ζ hζ w b))).2,
    Classical.choose_spec (ExistsUnique.exists (borel_factorization F ζ hζ w b))⟩

theorem borelRetraction_kernel (b : Borel F ζ hζ w) :
    borelRetraction F ζ hζ w b = 1 ↔
      ∃ x : Multiplicative (KPRankOneInduction.LocalField F w),
        (b : FiniteCover F ζ hζ w) = upperRoot F ζ hζ w x := by
  constructor
  · intro hb
    obtain ⟨x, hx⟩ := borelRetraction_decomposition F ζ hζ w b
    exact ⟨x, by simpa [hb] using hx⟩
  · rintro ⟨x, hx⟩
    have hb : b = ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩ :=
      Subtype.ext hx
    rw [hb, borelRetraction_upperRoot]

private theorem upper_entry_ratio_eq (A B : KPRankOneInduction.GL2 F w)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    A 0 1 / A 0 0 = B 0 1 / B 0 0 := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply,
    mul_div_mul_right _ _ (Units.ne_zero u)]

 def upperCoordinate (b : KPRankOneInduction.upperBorel F w) :
    KPRankOneInduction.LocalField F w :=
  let A := Classical.choose b.property
  A 0 1 / A 0 0

private theorem upperCoordinate_eq (b : KPRankOneInduction.upperBorel F w)
    (A : KPRankOneInduction.GL2 F w) (hA : Matrix.ProjGenLinGroup.mk A = b.val) :
    upperCoordinate F w b = A 0 1 / A 0 0 :=
  upper_entry_ratio_eq F w _ A ((Classical.choose_spec b.property).1.trans hA.symm)

private theorem upperCoordinate_continuous : Continuous (upperCoordinate F w) := by
  have hq : IsOpenQuotientMap
      (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F w → KPRankOneInduction.PGL2 F w) :=
    QuotientGroup.isOpenQuotientMap_mk
  apply ((hq.restrictPreimage (KPRankOneInduction.upperBorel F w)).continuous_comp_iff).mp
  have he : (fun A : {A : KPRankOneInduction.GL2 F w |
      Matrix.ProjGenLinGroup.mk A ∈ KPRankOneInduction.upperBorel F w} =>
      upperCoordinate F w ⟨Matrix.ProjGenLinGroup.mk A.val, A.property⟩) =
      (fun A => A.val 0 1 / A.val 0 0) := by
    funext A
    exact upperCoordinate_eq F w _ A.val rfl
  change Continuous (fun A : {A : KPRankOneInduction.GL2 F w |
    Matrix.ProjGenLinGroup.mk A ∈ KPRankOneInduction.upperBorel F w} =>
    upperCoordinate F w ⟨Matrix.ProjGenLinGroup.mk A.val, A.property⟩)
  rw [he]
  apply Continuous.div
  · exact (continuous_apply 1).comp ((continuous_apply 0).comp
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPRankOneInduction.LocalField F w))).comp continuous_subtype_val))
  · exact (continuous_apply 0).comp ((continuous_apply 0).comp
      ((Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (KPRankOneInduction.LocalField F w))).comp continuous_subtype_val))
  · intro A hz
    obtain ⟨B, hB, h10⟩ := A.property
    have hr := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
    obtain ⟨u, hu⟩ := hr
    have hb00 : B 0 0 = 0 := by
      have he := congrArg (fun M : KPRankOneInduction.GL2 F w => M 0 0) hu
      simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply, hz] using he
    have hd := Units.ne_zero (Matrix.GeneralLinearGroup.det B)
    apply hd
    change (B.val).det = 0
    simp [Matrix.det_fin_two, h10, hb00]

private theorem borelRetraction_formula (b : Borel F ζ hζ w) :
    (borelRetraction F ζ hζ w b).val = b.val * upperRoot F ζ hζ w
      (Multiplicative.ofAdd (-upperCoordinate F w
        (KPRankOneInduction.borelProjection F w (projection F ζ hζ w) b))) := by
  obtain ⟨x, hx⟩ := borelRetraction_decomposition F ζ hζ w b
  obtain ⟨A, hA, h10, h01⟩ := (borelRetraction F ζ hζ w b).property
  have ha00 : A 0 0 ≠ 0 := by
    intro hz
    have hd := Units.ne_zero (Matrix.GeneralLinearGroup.det A)
    apply hd
    change (A.val).det = 0
    simp [Matrix.det_fin_two, h10, hz]
  have hc : upperCoordinate F w
      (KPRankOneInduction.borelProjection F w (projection F ζ hζ w) b) =
      Multiplicative.toAdd x := by
    rw [upperCoordinate_eq F w _ (A * KubotaRankTwo.n _ (Multiplicative.toAdd x)) (by
      change Matrix.ProjGenLinGroup.mk _ = projection F ζ hζ w b.val
      rw [hx]
      rw [(projection F ζ hζ w).map_mul, upperRoot_projection]
      change Matrix.ProjGenLinGroup.mk _ = _ * Matrix.ProjGenLinGroup.mk _
      rw [map_mul, hA]
      rfl)]
    simp [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, KubotaRankTwo.n,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, h01, ha00]
  rw [hc]
  have he : Multiplicative.ofAdd (-Multiplicative.toAdd x) = x⁻¹ := rfl
  rw [he, map_inv, hx]
  group

private theorem borelRetraction_continuous_admissible
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    Continuous (borelRetraction F ζ hζ w) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hmap : Continuous (ordinaryPGLMap F w) := by
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
    apply (QuotientGroup.isQuotientMap_mk
      (KPPGLLocalCover.scalarSubgroup F (Sum.inr w))).continuous_iff.mpr
    exact QuotientGroup.continuous_mk
  have hp : Continuous (projection F ζ hζ w) := hmap.comp
    (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.2.1.continuous
  have hbp : Continuous (KPRankOneInduction.borelProjection F w (projection F ζ hζ w)) :=
    (hp.comp continuous_subtype_val).subtype_mk _
  have hc := (upperCoordinate_continuous F w).comp hbp
  have hN := (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).1
  have hformula : Continuous (fun b : Borel F ζ hζ w => b.val * upperRoot F ζ hζ w
      (Multiplicative.ofAdd (-upperCoordinate F w
        (KPRankOneInduction.borelProjection F w (projection F ζ hζ w) b)))) :=
    continuous_subtype_val.mul (hN.comp hc.neg)
  apply Continuous.subtype_mk _ _
  exact hformula.congr (fun b => (borelRetraction_formula F ζ hζ w b).symm)

theorem borelRetraction_continuous
    (hm : KPLocalChartTopology.MatrixChartDepth F w m) :
    letI := finiteCoverTopology F ζ hζ w m
    Continuous (borelRetraction F ζ hζ w) := by
  exact borelRetraction_continuous_admissible F ζ hζ w m hm

theorem dB_retraction (b : Borel F ζ hζ w) :
    dB F ζ hζ w (torusToBorel F ζ hζ w m hm (borelRetraction F ζ hζ w b)) =
      dB F ζ hζ w b := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  obtain ⟨x, hx⟩ := borelRetraction_decomposition F ζ hζ w b
  let n : Borel F ζ hζ w := ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩
  have hb : b = torusToBorel F ζ hζ w m hm (borelRetraction F ζ hζ w b) * n :=
    Subtype.ext hx
  have hd : deltaB F ζ hζ w n = 1 :=
    KPRankOneInduction.deltaB_upperRoot F w (projection F ζ hζ w) _ n
      (upperRoot_projection F ζ hζ w x)
  have hn : dB F ζ hζ w n = 1 := by
    apply Units.ext
    change NNReal.sqrt (deltaB F ζ hζ w n : ℝ≥0) = 1
    rw [hd]
    simp
  conv_rhs => rw [hb, map_mul, hn, mul_one]

def torusHalfModulus : Torus F ζ hζ w →* (ℝ≥0)ˣ :=
  (dB F ζ hζ w).comp (torusToBorel F ζ hζ w m hm)

variable {V E : Type*} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup E] [Module ℂ E]

theorem jacquet_relations_stable
    (ρ : Representation ℂ (FiniteCover F ζ hζ w) V)
    (h : Torus F ζ hζ w) :
    Representation.Coinvariants.ker
      (rootTwistedRepresentation ρ (upperRoot F ζ hζ w) 1) ≤
    (Representation.Coinvariants.ker
      (rootTwistedRepresentation ρ (upperRoot F ζ hζ w) 1)).comap
        (ρ (h : FiniteCover F ζ hζ w)) := by
  classical
  rw [rootTwistedRepresentation_ker]
  apply Submodule.span_le.mpr
  rintro z ⟨⟨x, v⟩, rfl⟩
  change ρ h.val (ρ (upperRoot F ζ hζ w x) v - (1 : ℂ) • v) ∈
    rootRelationSpan ρ (upperRoot F ζ hζ w) 1
  let hb : Borel F ζ hζ w := ⟨h.val, by
    change ∃ A : KPRankOneInduction.GL2 F w,
      Matrix.ProjGenLinGroup.mk A = projection F ζ hζ w h.val ∧ A 1 0 = 0
    obtain ⟨A, hA, h10, h01⟩ := h.property
    exact ⟨A, hA, h10⟩⟩
  let nb : Borel F ζ hζ w := ⟨upperRoot F ζ hζ w x, upperRoot_mem_borel F ζ hζ w x⟩
  have hk : borelRetraction F ζ hζ w (hb * nb * hb⁻¹) = 1 := by
    simp [nb]
  obtain ⟨y, hy⟩ := (borelRetraction_kernel F ζ hζ w (hb * nb * hb⁻¹)).mp hk
  change h.val * upperRoot F ζ hζ w x * h.val⁻¹ = upperRoot F ζ hζ w y at hy
  have heq : h.val * upperRoot F ζ hζ w x = upperRoot F ζ hζ w y * h.val := by
    rw [← hy]; group
  have hv : ρ h.val (ρ (upperRoot F ζ hζ w x) v) =
      ρ (upperRoot F ζ hζ w y) (ρ h.val v) := by
    rw [← Module.End.mul_apply, ← map_mul, heq, map_mul, Module.End.mul_apply]
  simp only [map_sub, one_smul, hv]
  exact Submodule.subset_span ⟨(y, ρ h.val v), by simp⟩

def jacquetAction (ρ : Representation ℂ (FiniteCover F ζ hζ w) V) :
    Representation ℂ (Torus F ζ hζ w) (OrdinaryCoinvariants F ζ hζ w ρ) :=
  Representation.quotient (ρ.comp (Torus F ζ hζ w).subtype)
    (Representation.Coinvariants.ker
      (rootTwistedRepresentation ρ (upperRoot F ζ hζ w) 1))
    (jacquet_relations_stable F ζ hζ w ρ)

def inducedAction (τ : Representation ℂ (Torus F ζ hζ w) E) :
    Representation ℂ (FiniteCover F ζ hζ w)
      (PrincipalSeries F ζ hζ w m (borelRetraction F ζ hζ w) τ) := by
  letI := finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact smoothIndRepresentation (Borel F ζ hζ w)
    (inflatedRepresentation F ζ hζ w (borelRetraction F ζ hζ w) τ) (dB F ζ hζ w)

end DedekindZetaZeroFree.KPLocalInductionJacquetReciprocity

end
