module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.ClosedCellEvaluation
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CovariantFunctionsWithCompactRepresentatives
public import DedekindZetaZeroFree.Metaplectic.Kubota.PGLCentralTransitions

import all Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

namespace DedekindZetaZeroFree.KPKirillovGenuineSectionCharts

open scoped Topology NumberField TensorProduct Classical

open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F))

abbrev K := KPRankOneInduction.LocalField F w

abbrev G := KPLocalSmoothRepresentation.FiniteCover F ζ hζ w

abbrev P := KPLocalSmoothRepresentation.Borel F ζ hζ w

def slope : P F ζ hζ w →* (K F w)ˣ :=
  (KPRankOneInduction.borelRatio F w).comp
    (KPRankOneInduction.borelProjection F w
      (KPLocalSmoothRepresentation.projection F ζ hζ w))

def H : Subgroup (P F ζ hζ w) := (slope F ζ hζ w).ker

def n (b : K F w) : P F ζ hζ w :=
  ⟨KPLocalSmoothRepresentation.upperRoot F ζ hζ w (Multiplicative.ofAdd b),
    KPJacquetClosedCellBump.upperRoot_mem_borel F ζ hζ w _⟩

def z : rootsOfUnity 3 F →* P F ζ hζ w :=
  (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w)).codRestrict
    (P F ζ hζ w) (by
      intro e
      letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
      change KPLocalSmoothRepresentation.projection F ζ hζ w _ ∈
        KPRankOneInduction.upperBorel F w
      have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
          (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e) = 1 := by
        apply (KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr w)).le
        exact ⟨e, rfl⟩
      change KPLocalSmoothRepresentation.ordinaryPGLMap F w
        (KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
          (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e)) ∈
          KPRankOneInduction.upperBorel F w
      rw [he, map_one]
      exact Subgroup.one_mem _)

private theorem n_projection (b : K F w) :
    KPLocalSmoothRepresentation.projection F ζ hζ w (n F ζ hζ w b).val =
      KPRankOneInduction.upperRootElement F w b := rfl

private theorem z_projection (e : rootsOfUnity 3 F) :
    KPLocalSmoothRepresentation.projection F ζ hζ w (z F ζ hζ w e).val = 1 := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e) = 1 := by
    apply (KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr w)).le
    exact ⟨e, rfl⟩
  change KPLocalSmoothRepresentation.ordinaryPGLMap F w
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e)) = 1
  rw [he, map_one]

private theorem ordinaryPGL_injective :
    Function.Injective (KPLocalSmoothRepresentation.ordinaryPGLMap F w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro a b
  induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
      intro h
      change Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B at h
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
      apply (QuotientGroup.mk'_eq_mk' _).mpr
      exact ⟨KPScalarSplitCentral.scalarMatrix F (Sum.inr w) u, ⟨u, rfl⟩, hu⟩

private theorem nz_unique (a b : K F w) (e d : rootsOfUnity 3 F)
    (he : n F ζ hζ w a * z F ζ hζ w e = n F ζ hζ w b * z F ζ hζ w d) :
    a = b ∧ e = d := by
  have hp := congrArg (fun p : P F ζ hζ w =>
    KPLocalSmoothRepresentation.projection F ζ hζ w p.val) he
  simp only [Subgroup.coe_mul, map_mul, n_projection, z_projection, mul_one] at hp
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have h11 := congrArg (fun A : KPRankOneInduction.GL2 F w => A 1 1) hu
  have h01 := congrArg (fun A : KPRankOneInduction.GL2 F w => A 0 1) hu
  simp [KPRankOneInduction.upperRootElement, KPRankOneInduction.upperRootMatrix,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar] at h11 h01
  have hab : a = b := by simpa [h11] using h01
  refine ⟨hab, ?_⟩
  rw [hab] at he
  have hz := mul_left_cancel he
  exact KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr w)
    (congrArg Subtype.val hz)

theorem H_decomposition (h : H F ζ hζ w) :
    ∃! p : K F w × rootsOfUnity 3 F,
      h.val = n F ζ hζ w p.1 * z F ζ hζ w p.2 := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  obtain ⟨a, t, ht, hfac, _, hproj, _⟩ :=
    FiniteCentralBorel.exists_unique_lifted_factorization F w
      (KPLocalSmoothRepresentation.projection F ζ hζ w)
      (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) (fun _ => rfl)
      h.val.val h.val.property
  have hs : KPRankOneInductionRaw.borelRatio F w
      ⟨KPLocalSmoothRepresentation.projection F ζ hζ w h.val.val, h.val.property⟩ = 1 :=
    h.property
  rw [hs] at hproj
  have hd : KPRankOneInductionRaw.diagonalElement F w 1 = 1 := by
    have hmat : KPRankOneInductionRaw.diagonalMatrix F w 1 = 1 := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [KPRankOneInductionRaw.diagonalMatrix]
    unfold KPRankOneInductionRaw.diagonalElement
    rw [hmat, map_one]
  rw [hd] at hproj
  have hk : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) t = 1 := by
    apply ordinaryPGL_injective F w
    exact hproj
  have hr : t ∈ (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w)).range := by
    rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
    exact hk
  obtain ⟨e, he⟩ := hr
  have hf : h.val = n F ζ hζ w a * z F ζ hζ w e := by
    apply Subtype.ext
    change h.val.val = KPLocalSmoothRepresentation.upperRoot F ζ hζ w _ *
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e
    rw [he]
    exact hfac
  refine ⟨(a, e), hf, ?_⟩
  rintro ⟨b, d⟩ hb
  obtain ⟨hab, hed⟩ := nz_unique F ζ hζ w b a d e (hb.symm.trans hf)
  exact Prod.ext hab hed

def iota : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

def hCoordinates (h : H F ζ hζ w) : K F w × rootsOfUnity 3 F :=
  Classical.choose (ExistsUnique.exists (H_decomposition F ζ hζ w h))

private theorem hCoordinates_spec (h : H F ζ hζ w) :
    h.val = n F ζ hζ w (hCoordinates F ζ hζ w h).1 *
      z F ζ hζ w (hCoordinates F ζ hζ w h).2 :=
  Classical.choose_spec (ExistsUnique.exists (H_decomposition F ζ hζ w h))

private theorem hCoordinates_eq (h : H F ζ hζ w) (b : K F w)
    (e : rootsOfUnity 3 F) (hh : h.val = n F ζ hζ w b * z F ζ hζ w e) :
    hCoordinates F ζ hζ w h = (b, e) := by
  obtain ⟨hb, he⟩ := nz_unique F ζ hζ w _ b _ e
    ((hCoordinates_spec F ζ hζ w h).symm.trans hh)
  exact Prod.ext hb he

private theorem n_add (a b : K F w) :
    n F ζ hζ w (a + b) = n F ζ hζ w a * n F ζ hζ w b :=
  Subtype.ext ((KPLocalSmoothRepresentation.upperRoot F ζ hζ w).map_mul _ _)

private theorem n_zero : n F ζ hζ w 0 = 1 :=
  Subtype.ext ((KPLocalSmoothRepresentation.upperRoot F ζ hζ w).map_one)

private theorem z_comm (e : rootsOfUnity 3 F) (p : P F ζ hζ w) :
    z F ζ hζ w e * p = p * z F ζ hζ w e := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr w) ⟨e, rfl⟩)
      p.val).symm

theorem hCoordinates_one : hCoordinates F ζ hζ w 1 = (0, 1) := by
  apply hCoordinates_eq
  simp [n_zero]

theorem hCoordinates_mul (h k : H F ζ hζ w) :
    hCoordinates F ζ hζ w (h * k) =
      ((hCoordinates F ζ hζ w h).1 + (hCoordinates F ζ hζ w k).1,
        (hCoordinates F ζ hζ w h).2 * (hCoordinates F ζ hζ w k).2) := by
  apply hCoordinates_eq
  rw [Subgroup.coe_mul, hCoordinates_spec F ζ hζ w h,
    hCoordinates_spec F ζ hζ w k, n_add, map_mul]
  rw [mul_assoc, ← mul_assoc (z F ζ hζ w _) (n F ζ hζ w _) _, z_comm]
  group

def inducingCharacter (ψ : Multiplicative (K F w) →* ℂˣ) :
    H F ζ hζ w →* ℂˣ where
  toFun h := ψ (Multiplicative.ofAdd (hCoordinates F ζ hζ w h).1) *
    iota F ζ hζ (hCoordinates F ζ hζ w h).2
  map_one' := by simp [hCoordinates_one]
  map_mul' h k := by
    simp only [hCoordinates_mul, map_mul]
    change ψ (Multiplicative.ofAdd (_ + _)) * _ = _
    rw [show Multiplicative.ofAdd ((hCoordinates F ζ hζ w h).1 +
        (hCoordinates F ζ hζ w k).1) =
      Multiplicative.ofAdd (hCoordinates F ζ hζ w h).1 *
        Multiplicative.ofAdd (hCoordinates F ζ hζ w k).1 from rfl, map_mul]
    ac_rfl

section Topology

variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)

local notation "coverTopology" => KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m

private lemma chart_borelRatio_continuous : Continuous (KPRankOneInduction.borelRatio F w) := by
  let f := (KPRankOneInduction.upperBorel F w : Set (KPRankOneInduction.PGL2 F w)).restrictPreimage
    (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F w → KPRankOneInduction.PGL2 F w)
  have hq : Topology.IsQuotientMap f :=
    (QuotientGroup.isOpenQuotientMap_mk.restrictPreimage _).isQuotientMap
  apply hq.continuous_iff.mpr
  have hupper (a : {a : KPRankOneInduction.GL2 F w | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F w}) :
      (a : KPRankOneInduction.GL2 F w) 1 0 = 0 := by
    obtain ⟨B, hB, h10⟩ := a.property
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
    have hh := congrArg (fun g : KPRankOneInduction.GL2 F w => g 1 0) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] at hh
    simp at hh
    rw [← hh, h10, zero_mul]
  have hdiag (a : {a : KPRankOneInduction.GL2 F w | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F w}) :
      (a : KPRankOneInduction.GL2 F w) 0 0 ≠ 0 ∧ (a : KPRankOneInduction.GL2 F w) 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero (a : KPRankOneInduction.GL2 F w)
    rw [Matrix.det_fin_two] at hd
    simp only [hupper a, mul_zero, sub_zero] at hd
    exact mul_ne_zero_iff.mp hd
  have hval : ∀ a, ((KPRankOneInduction.borelRatio F w) (f a) : K F w) =
      (a : KPRankOneInduction.GL2 F w) 0 0 / (a : KPRankOneInduction.GL2 F w) 1 1 := by
    intro a
    exact KPRankOneInduction.borelRatio_eq F w (f a) a rfl (hupper a)
  have hentry (i j : Fin 2) : Continuous (fun a : {a : KPRankOneInduction.GL2 F w | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F w} =>
      (a : KPRankOneInduction.GL2 F w) i j) :=
    (continuous_apply_apply i j).comp
      ((Units.continuous_val : Continuous (fun A : KPRankOneInduction.GL2 F w => (A : Matrix (Fin 2) (Fin 2) (K F w)))).comp continuous_subtype_val)
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun a => ((KPRankOneInduction.borelRatio F w) (f a) : K F w))
    simp_rw [hval]
    exact (hentry 0 0).div (hentry 1 1) (fun a => (hdiag a).2)
  · change Continuous (fun a => (((KPRankOneInduction.borelRatio F w) (f a))⁻¹ : K F w))
    simp_rw [hval, inv_div]
    exact (hentry 1 1).div (hentry 0 0) (fun a => (hdiag a).1)

def diagonalLift (y : (K F w)ˣ) : P F ζ hζ w :=
  ⟨KPPGLLocalCover.A F ζ hζ (Sum.inr w) y,
    KPRankOneInduction.diagonalElement_mem F w y⟩

private lemma diagonalLift_projects (y : (K F w)ˣ) :
    KPLocalSmoothRepresentation.projection F ζ hζ w (diagonalLift F ζ hζ w y).val =
      KPRankOneInduction.diagonalElement F w y := rfl

lemma diagonalLift_slope (y : (K F w)ˣ) :
    slope F ζ hζ w (diagonalLift F ζ hζ w y) = y := by
  apply Units.ext
  change (KPRankOneInduction.borelRatio F w _ : K F w) = y
  rw [KPRankOneInduction.borelRatio_eq F w _ (KPRankOneInduction.diagonalMatrix F w y)
    rfl (by simp [KPRankOneInduction.diagonalMatrix, KubotaRankTwo.d])]
  simp [KPRankOneInduction.diagonalMatrix, KubotaRankTwo.d]

include hm in
 lemma diagonalLift_continuous :
    letI := coverTopology
    Continuous (diagonalLift F ζ hζ w) := by
  letI := coverTopology
  exact (KPPGLLocalCover.finite_lifts_continuous F ζ hζ w m hm).2.2.subtype_mk _

include hm in
private lemma chart_projection_continuous :
    letI := coverTopology
    Continuous (KPLocalSmoothRepresentation.projection F ζ hζ w) := by
  letI := coverTopology
  have hmap : Continuous (KPLocalSmoothRepresentation.ordinaryPGLMap F w) := by
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
    apply (QuotientGroup.isQuotientMap_mk
      (KPPGLLocalCover.scalarSubgroup F (Sum.inr w))).continuous_iff.mpr
    exact QuotientGroup.continuous_mk
  exact hmap.comp (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.2.1.continuous

include hm in
 lemma chart_slope_continuous :
    letI := coverTopology
    Continuous (slope F ζ hζ w) := by
  letI := coverTopology
  apply (chart_borelRatio_continuous F w).comp
  exact ((chart_projection_continuous F ζ hζ w m hm).comp continuous_subtype_val).subtype_mk _

lemma chart_rel_of_slope_eq (p q : P F ζ hζ w)
    (h : slope F ζ hζ w p = slope F ζ hζ w q) :
    QuotientGroup.rightRel (H F ζ hζ w) p q := by
  rw [QuotientGroup.rightRel_apply]
  change slope F ζ hζ w (q * p⁻¹) = 1
  rw [map_mul, map_inv, h, mul_inv_cancel]

lemma chart_slope_eq_of_rel (p q : P F ζ hζ w)
    (h : QuotientGroup.rightRel (H F ζ hζ w) p q) :
    slope F ζ hζ w p = slope F ζ hζ w q := by
  rw [QuotientGroup.rightRel_apply] at h
  change slope F ζ hζ w (q * p⁻¹) = 1 at h
  rw [map_mul, map_inv] at h
  exact (mul_inv_eq_one.mp h).symm

def chartQuotHomeomorph :
    letI := coverTopology
    SectionCosetSpace (H F ζ hζ w) ≃ₜ (K F w)ˣ := by
  letI := coverTopology
  exact {
    toFun := Quotient.lift (slope F ζ hζ w) (chart_slope_eq_of_rel F ζ hζ w)
    invFun := fun t => Quotient.mk _ (diagonalLift F ζ hζ w t)
    left_inv := by
      intro q
      induction q using Quotient.inductionOn with
      | h p =>
        apply Quotient.sound
        exact chart_rel_of_slope_eq F ζ hζ w _ _ (diagonalLift_slope F ζ hζ w _)
    right_inv := diagonalLift_slope F ζ hζ w
    continuous_toFun := by
      apply isQuotientMap_quotient_mk'.continuous_iff.mpr
      exact chart_slope_continuous F ζ hζ w m hm
    continuous_invFun := continuous_quotient_mk'.comp
      (diagonalLift_continuous F ζ hζ w m hm) }

def quotientHomeomorph :
    letI := coverTopology
    SectionCosetSpace (H F ζ hζ w) ≃ₜ (K F w)ˣ := by
  exact chartQuotHomeomorph F ζ hζ w m hm

include hm in
theorem quotientHomeomorph_mk (p : P F ζ hζ w) :
    letI := coverTopology
    quotientHomeomorph F ζ hζ w m hm
      (Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w)) p) = slope F ζ hζ w p := by
  rfl

variable (ψ : Multiplicative (K F w) →* ℂˣ)

def coefficientRepresentation (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Representation ℂ (H F ζ hζ w) J where
  toFun h := (inducingCharacter F ζ hζ w ψ h : ℂ) • LinearMap.id
  map_one' := by ext v; simp
  map_mul' h k := by
    ext v
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply,
      LinearMap.id_apply, Module.End.mul_apply, smul_smul]

def CompactLCSections (J : Type*) [AddCommGroup J] [Module ℂ J] :
    letI := coverTopology
    Submodule ℂ (P F ζ hζ w → J) := by
  letI := coverTopology
  exact {
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupportModH (H F ζ hζ w) f ∧
    ∀ (h : H F ζ hζ w) (p : P F ζ hζ w),
      f (h.val * p) = (inducingCharacter F ζ hζ w ψ h : ℂ) • f p}
  zero_mem' := by
    refine ⟨IsLocallyConstant.zero, ?_, ?_⟩
    · simp [HasCompactSupportModH]
    · intro h p; simp
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_, ?_⟩
    · have hs : Function.support (f + g) ⊆ Function.support f ∪ Function.support g :=
        Function.support_add f g
      have hi := (Set.image_mono hs).trans
        (le_of_eq (Set.image_union (Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w))) _ _))
      exact (hf.2.1.union hg.2.1).of_isClosed_subset isClosed_closure
        ((closure_mono hi).trans (le_of_eq closure_union))
    · intro h p
      change f _ + g _ = _ • (f p + g p)
      rw [hf.2.2, hg.2.2, smul_add]
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.comp (fun v => c • v), ?_, ?_⟩
    · have hs : Function.support (c • f) ⊆ Function.support f := by
        intro p hp
        contrapose! hp
        have hz : f p = 0 := by simpa [Function.mem_support] using hp
        simp [Pi.smul_apply, hz]
      exact hf.2.1.of_isClosed_subset isClosed_closure
        (closure_mono (Set.image_mono hs))
    · intro h p
      change c • f _ = _ • (c • f p)
      rw [hf.2.2, smul_comm] }

abbrev Sections (J : Type*) [AddCommGroup J] [Module ℂ J] :=
  letI := coverTopology
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  CompactSmoothInd (H F ζ hζ w) (coefficientRepresentation F ζ hζ w ψ J) 1

def sectionValue {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ J) : P F ζ hζ w → J := f.val.val.val

structure CompactOpenBall where
  domain : Set (K F w)ˣ
  center : (K F w)ˣ
  radius : ℝ
  radius_pos : 0 < radius
  ball_eq : domain = {t : (K F w)ˣ | ‖(t : K F w) - (center : K F w)‖ ≤ radius}
  open_domain : IsOpen domain
  compact_domain : IsCompact domain

structure LocalChart where
  ball : CompactOpenBall F w
  lift : ball.domain → P F ζ hζ w
  continuous_lift : letI := coverTopology; Continuous lift
  projects : ∀ t, KPLocalSmoothRepresentation.projection F ζ hζ w (lift t).val =
    KPRankOneInduction.diagonalElement F w t.val
  slope_lift : ∀ t, slope F ζ hζ w (lift t) = t.val

include hm in

theorem exists_localChart (t : (K F w)ˣ) (U : Set (K F w)ˣ)
    (hU : IsOpen U) (ht : t ∈ U) :
    ∃ c : LocalChart F ζ hζ w m, t ∈ c.ball.domain ∧ c.ball.domain ⊆ U := by
  letI := coverTopology
  have hopen : IsOpen ((Units.val : (K F w)ˣ → K F w) '' U) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen t.val ⟨t, ht, rfl⟩
  let r : ℝ := min (ε / 2) (‖(t : K F w)‖ / 2)
  have htpos : 0 < ‖(t : K F w)‖ := norm_pos_iff.mpr t.ne_zero
  have hr : 0 < r := lt_min (half_pos hε) (half_pos htpos)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrt : r < ‖(t : K F w)‖ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  let D : Set (K F w)ˣ := {y | ‖(y : K F w) - (t : K F w)‖ ≤ r}
  have hD : IsOpen D :=
    (IsUltrametricDist.isOpen_closedBall (t : K F w) hr.ne').preimage Units.continuous_val
  have himage : (Units.val : (K F w)ˣ → K F w) '' D = Metric.closedBall (t : K F w) r := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hx0 : x ≠ 0 := by
        intro hz
        have hnorm : ‖(t : K F w)‖ ≤ r := by simpa [hz, dist_eq_norm] using hx
        exact (not_le_of_gt hrt) hnorm
      exact ⟨Units.mk0 x hx0, hx, rfl⟩
  have hc : IsCompact D :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isEmbedding.isCompact_iff.mpr
      (by rw [himage]; exact isCompact_closedBall _ _)
  let ball : CompactOpenBall F w :=
    ⟨D, t, r, hr, rfl, hD, hc⟩
  let c : LocalChart F ζ hζ w m := {
    ball := ball
    lift := fun y => diagonalLift F ζ hζ w y.val
    continuous_lift := (diagonalLift_continuous F ζ hζ w m hm).comp continuous_subtype_val
    projects := fun y => diagonalLift_projects F ζ hζ w y.val
    slope_lift := fun y => diagonalLift_slope F ζ hζ w y.val }
  refine ⟨c, ?_, ?_⟩
  · change ‖(t : K F w) - t‖ ≤ r
    simpa using hr.le
  · intro y hy
    have hx : (y : K F w) ∈ Metric.ball (t : K F w) ε := by
      change ‖(y : K F w) - t‖ < ε
      exact lt_of_le_of_lt hy hrε
    obtain ⟨z, hz, heq⟩ := hball hx
    exact (Units.val_injective heq) ▸ hz

include hm in
 theorem compactLC_smooth {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : CompactLCSections F ζ hζ w m ψ J) :
    letI := coverTopology
    SmoothVector KPLocalPrincipalSeries.vectorRightTranslation f.val := by
  classical
  letI := coverTopology
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  let e := quotientHomeomorph F ζ hζ w m hm
  let T := e '' closure ((Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w))) ''
    Function.support f.val)
  have hT : IsCompact T := f.property.2.1.image e.continuous
  have hcover : T ⊆ ⋃ c : LocalChart F ζ hζ w m, c.ball.domain := by
    intro t ht
    obtain ⟨c, hc, _⟩ := exists_localChart F ζ hζ w m hm t Set.univ isOpen_univ (Set.mem_univ t)
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  obtain ⟨cs, hcs⟩ := hT.elim_finite_subcover _ (fun c => c.ball.open_domain) hcover
  let C : Set (P F ζ hζ w) := ⋃ c ∈ cs, Set.range c.lift
  have hC : IsCompact C := cs.isCompact_biUnion fun c hc => by
    letI : CompactSpace c.ball.domain := isCompact_iff_compactSpace.mp c.ball.compact_domain
    exact isCompact_range c.continuous_lift
  apply KPRankOneBruhatKernelTransport.OpenCellSmoothnessSteps.covariant_smooth_of_compact_representatives
    (H F ζ hζ w) (coefficientRepresentation F ζ hζ w ψ J) f.val
    (fun h p => f.property.2.2 h p) f.property.1 C hC
  intro p hp
  have ht : slope F ζ hζ w p ∈ T := by
    rw [← quotientHomeomorph_mk F ζ hζ w m hm p]
    exact ⟨_, subset_closure ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨c, hc, hct⟩ := Set.mem_iUnion₂.mp (hcs ht)
  let t : c.ball.domain := ⟨slope F ζ hζ w p, hct⟩
  let b : H F ζ hζ w := ⟨p * (c.lift t)⁻¹, by
    change slope F ζ hζ w (p * (c.lift t)⁻¹) = 1
    rw [map_mul, map_inv, c.slope_lift]
    exact mul_inv_cancel _⟩
  refine ⟨b, c.lift t, Set.mem_iUnion₂.mpr ⟨c, hc, ⟨t, rfl⟩⟩, ?_⟩
  change p = (p * (c.lift t)⁻¹) * c.lift t
  group

def compactLCEquiv (hψ : IsLocallyConstant ψ)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Sections F ζ hζ w m ψ J ≃ₗ[ℂ] CompactLCSections F ζ hζ w m ψ J := by
  letI := coverTopology
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  let τ := coefficientRepresentation F ζ hζ w ψ J
  let toLC : Sections F ζ hζ w m ψ J → CompactLCSections F ζ hζ w m ψ J := fun f =>
    ⟨sectionValue F ζ hζ w m ψ f,
      (SmoothInd_le_LCSections (H F ζ hζ w) τ 1 f.val.property),
      f.property, by
        intro h p
        have hc := f.val.val.property h p
        simpa [sectionValue, normalizedSectionRepresentation, τ, coefficientRepresentation] using hc⟩
  let toSm : CompactLCSections F ζ hζ w m ψ J → Sections F ζ hζ w m ψ J := fun f =>
    ⟨⟨⟨f.val, by
      intro h p
      simpa [normalizedSectionRepresentation, τ, coefficientRepresentation] using f.property.2.2 h p⟩,
      by
        obtain ⟨U, hU⟩ := compactLC_smooth F ζ hζ w m hm ψ f
        rw [SmoothInd, mem_smoothSubmodule]
        refine ⟨U, fun u hu => ?_⟩
        apply Subtype.ext
        exact hU u hu⟩, f.property.2.1⟩
  exact {
    toFun := toLC
    invFun := toSm
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

theorem compactLCEquiv_value (hψ : IsLocallyConstant ψ)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ J) (p : P F ζ hζ w) :
    (compactLCEquiv F ζ hζ w m hm ψ hψ J f).val p =
      sectionValue F ζ hζ w m ψ f p := by rfl

def CompactFunctions (X J : Type*) [TopologicalSpace X]
    [AddCommGroup J] [Module ℂ J] : Submodule ℂ (X → J) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c x hx =>
    ⟨hx.1.comp₂ (IsLocallyConstant.const c) (fun a b => b • a), hx.2.smul_left⟩

end Topology

end DedekindZetaZeroFree.KPKirillovGenuineSectionCharts

end

section

noncomputable section

set_option maxHeartbeats 2000000

namespace DedekindZetaZeroFree.KPKirillovGenuineSectionCharts

open scoped Topology NumberField TensorProduct Classical
open NumberField IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F))

theorem n_mem_H (b : K F w) : n F ζ hζ w b ∈ H F ζ hζ w := by
  change slope F ζ hζ w (n F ζ hζ w b) = 1
  apply Units.ext
  have he := KPRankOneInduction.borelRatio_eq F w
    (KPRankOneInduction.borelProjection F w (KPLocalSmoothRepresentation.projection F ζ hζ w)
      (n F ζ hζ w b)) (KPRankOneInduction.upperRootMatrix F w b) rfl (by rfl)
  simpa [slope, KPRankOneInduction.upperRootMatrix] using he

theorem z_mem_H (e : rootsOfUnity 3 F) : z F ζ hζ w e ∈ H F ζ hζ w := by
  change slope F ζ hζ w (z F ζ hζ w e) = 1
  have he : KPRankOneInduction.borelProjection F w
      (KPLocalSmoothRepresentation.projection F ζ hζ w) (z F ζ hζ w e) = 1 :=
    Subtype.ext (z_projection F ζ hζ w e)
  change KPRankOneInduction.borelRatio F w _ = 1
  rw [he, map_one]

theorem inducingCharacter_formula (ψ : Multiplicative (K F w) →* ℂˣ)
    (b : K F w) (e : rootsOfUnity 3 F) (h : H F ζ hζ w)
    (hh : h.val = n F ζ hζ w b * z F ζ hζ w e) :
    inducingCharacter F ζ hζ w ψ h = ψ (Multiplicative.ofAdd b) * iota F ζ hζ e := by
  change ψ (Multiplicative.ofAdd (hCoordinates F ζ hζ w h).1) *
    iota F ζ hζ (hCoordinates F ζ hζ w h).2 = _
  rw [hCoordinates_eq F ζ hζ w h b e hh]

section Topology
variable (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)

local notation "coverTopology" => KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m

variable (ψ : Multiplicative (K F w) →* ℂˣ)

def rightAction (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Representation ℂ (P F ζ hζ w) (Sections F ζ hζ w m ψ J) :=
  letI := coverTopology
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  compactSmoothIndRepresentation (H F ζ hζ w)
    (coefficientRepresentation F ζ hζ w ψ J) 1

theorem rightAction_apply {J : Type*} [AddCommGroup J] [Module ℂ J]
    (a p : P F ζ hζ w) (f : Sections F ζ hζ w m ψ J) :
    sectionValue F ζ hζ w m ψ (rightAction F ζ hζ w m hm ψ J a f) p =
      sectionValue F ζ hζ w m ψ f (p * a) := by rfl

theorem sections_covariance {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ J) (b : K F w) (e : rootsOfUnity 3 F)
    (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m ψ f ((n F ζ hζ w b * z F ζ hζ w e) * p) =
      ((ψ (Multiplicative.ofAdd b) * iota F ζ hζ e : ℂˣ) : ℂ) •
        sectionValue F ζ hζ w m ψ f p := by
  letI := coverTopology
  let h : H F ζ hζ w := ⟨n F ζ hζ w b * z F ζ hζ w e,
    (H F ζ hζ w).mul_mem (n_mem_H F ζ hζ w b) (z_mem_H F ζ hζ w e)⟩
  have hc := f.val.val.property h p
  change sectionValue F ζ hζ w m ψ f (h.val * p) =
    normalizedSectionRepresentation (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ J) 1 h
        (sectionValue F ζ hζ w m ψ f p) at hc
  simpa [normalizedSectionRepresentation, coefficientRepresentation,
    inducingCharacter_formula F ζ hζ w ψ b e h rfl] using hc

def chartValue {J : Type*} [AddCommGroup J] [Module ℂ J]
    (c : LocalChart F ζ hζ w m) (f : Sections F ζ hζ w m ψ J) : c.ball.domain → J :=
  fun t => sectionValue F ζ hζ w m ψ f (c.lift t)

private theorem chart_kernel_central (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) :
    (KPLocalSmoothRepresentation.projection F ζ hζ w).ker ≤ Subgroup.center (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  intro g hg
  have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g = 1 := by
    apply KPWildCompactProjectorKirillov.ClopenGluing.ordinaryPGLMap_injective F w
    exact hg
  apply KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr w)
  rw [KPPGLLocalCover.range_centralInjection_eq_ker_projection]
  exact he

private theorem chart_kernel_finite (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : HeightOneSpectrum (RingOfIntegers F)) : Finite (KPLocalSmoothRepresentation.projection F ζ hζ w).ker := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  have hex (g : (KPLocalSmoothRepresentation.projection F ζ hζ w).ker) :
      ∃ z, KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) z = g.val := by
    have he : KPPGLLocalCover.projection F ζ hζ (Sum.inr w) g.val = 1 := by
      apply KPWildCompactProjectorKirillov.ClopenGluing.ordinaryPGLMap_injective F w
      exact g.property
    have hr := KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr w)
    rw [← MonoidHom.mem_ker, ← hr] at he
    exact he
  let e : (KPLocalSmoothRepresentation.projection F ζ hζ w).ker → rootsOfUnity 3 F := fun g => Classical.choose (hex g)
  have he (g : (KPLocalSmoothRepresentation.projection F ζ hζ w).ker) :
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) (e g) = g.val :=
    Classical.choose_spec (hex g)
  exact Finite.of_injective e (fun a b h => Subtype.ext (by rw [← he a, ← he b, h]))

include hm in

theorem chart_root_identity (c : LocalChart F ζ hζ w m)
    (t : c.ball.domain) (b : K F w) :
    c.lift t * n F ζ hζ w b = n F ζ hζ w ((t.val : K F w) * b) * c.lift t := by
  letI := chart_kernel_finite F ζ hζ w
  have hn (x : Multiplicative (K F w)) :
      KPLocalSmoothRepresentation.projection F ζ hζ w
        (KPLocalSmoothRepresentation.upperRoot F ζ hζ w x) =
          KPRankOneInductionRaw.ordinaryUpperRootHom F w x := rfl
  have htD : KPLocalSmoothRepresentation.projection F ζ hζ w (c.lift t).val ∈
      KPRankOneInductionRaw.diagonalTorus F w := by
    rw [c.projects t]
    exact ⟨KPRankOneInduction.diagonalMatrix F w t.val, rfl,
      by simp [KPRankOneInduction.diagonalMatrix, KubotaRankTwo.d],
      by simp [KPRankOneInduction.diagonalMatrix, KubotaRankTwo.d]⟩
  have h := FiniteCentralBorel.torusLift_conjugates_root F w
    (KPLocalSmoothRepresentation.projection F ζ hζ w) (chart_kernel_central F ζ hζ w)
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) hn (c.lift t).val htD
    (c.lift t).property b
  have hs : (KPRankOneInductionRaw.borelRatio F w
      ⟨KPLocalSmoothRepresentation.projection F ζ hζ w (c.lift t).val, (c.lift t).property⟩ :
      K F w) = t.val := congrArg Units.val (c.slope_lift t)
  rw [hs] at h
  apply Subtype.ext
  exact (mul_inv_eq_iff_eq_mul).mp h

include hm in
theorem chartValue_right_root {J : Type*} [AddCommGroup J] [Module ℂ J]
    (c : LocalChart F ζ hζ w m) (t : c.ball.domain) (b : K F w)
    (f : Sections F ζ hζ w m ψ J) :
    chartValue F ζ hζ w m ψ c
        (rightAction F ζ hζ w m hm ψ J (n F ζ hζ w b) f) t =
      (ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ) •
        chartValue F ζ hζ w m ψ c f t := by
  unfold chartValue
  rw [rightAction_apply, chart_root_identity F ζ hζ w m hm c t b]
  have h := sections_covariance F ζ hζ w m ψ f ((t.val : K F w) * b) 1 (c.lift t)
  simpa using h

include hm in

def PatchSections (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Submodule ℂ (Sections F ζ hζ w m ψ J) where
  carrier := {f | ∀ p, slope F ζ hζ w p ∉ c.ball.domain →
    sectionValue F ζ hζ w m ψ f p = 0}
  zero_mem' := by
    intro p hp
    simp [sectionValue]
  add_mem' := by
    intro f g hf hg p hp
    have h1 : sectionValue F ζ hζ w m ψ (f + g) p =
        sectionValue F ζ hζ w m ψ f p + sectionValue F ζ hζ w m ψ g p := rfl
    rw [h1, hf p hp, hg p hp, add_zero]
  smul_mem' := by
    intro a f hf p hp
    have h1 : sectionValue F ζ hζ w m ψ (a • f) p =
        a • sectionValue F ζ hζ w m ψ f p := rfl
    rw [h1, hf p hp, smul_zero]

include hm in
private theorem slope_continuous :
    letI := coverTopology
    Continuous (slope F ζ hζ w) := by
  letI := coverTopology
  have he : (fun p : P F ζ hζ w =>
      quotientHomeomorph F ζ hζ w m hm
        (Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w)) p)) = slope F ζ hζ w := by
    funext p
    exact quotientHomeomorph_mk F ζ hζ w m hm p
  rw [← he]
  exact (quotientHomeomorph F ζ hζ w m hm).continuous.comp continuous_quot_mk

private def cutSection (hψ : IsLocallyConstant ψ)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (U : TopologicalSpace.Clopens (K F w)ˣ) (f : Sections F ζ hζ w m ψ J) :
    Sections F ζ hζ w m ψ J := by
  classical
  letI := coverTopology
  let fLC := compactLCEquiv F ζ hζ w m hm ψ hψ J f
  let S : Set (P F ζ hζ w) := (slope F ζ hζ w) ⁻¹' U
  have hS : IsClopen S := U.isClopen.preimage (slope_continuous F ζ hζ w m hm)
  let v : CompactLCSections F ζ hζ w m ψ J := ⟨S.indicator fLC.val, by
    refine ⟨?_, ?_, ?_⟩
    · exact (LocallyConstant.indicator ⟨fLC.val, fLC.property.1⟩ hS).isLocallyConstant
    · have hs : Function.support (S.indicator fLC.val) ⊆ Function.support fLC.val :=
        fun p hp => by
          by_contra hz
          have he : fLC.val p = 0 := by simpa [Function.mem_support] using hz
          exact hp (by simp [Set.indicator, he])
      exact fLC.property.2.1.of_isClosed_subset isClosed_closure
        (closure_mono (Set.image_mono hs))
    · intro h p
      have hs : slope F ζ hζ w h.val = 1 := h.property
      by_cases hp : p ∈ S
      · have hh : h.val * p ∈ S := by
          change slope F ζ hζ w (h.val * p) ∈ U
          simpa [S, map_mul, hs] using hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hh]
        exact fLC.property.2.2 h p
      · have hh : h.val * p ∉ S := by
          change slope F ζ hζ w (h.val * p) ∉ U
          simpa [S, map_mul, hs] using hp
        rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hh, smul_zero]⟩
  exact (compactLCEquiv F ζ hζ w m hm ψ hψ J).symm v

private theorem cutSection_value (hψ : IsLocallyConstant ψ)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (U : TopologicalSpace.Clopens (K F w)ˣ) (f : Sections F ζ hζ w m ψ J)
    (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m ψ (cutSection F ζ hζ w m hm ψ hψ U f) p =
      if slope F ζ hζ w p ∈ U then sectionValue F ζ hζ w m ψ f p else 0 := by
  classical
  rfl

def patchRestriction (hψ : IsLocallyConstant ψ) (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    PatchSections F ζ hζ w m ψ c J →ₗ[ℂ] CompactFunctions c.ball.domain J := by
  letI := coverTopology
  letI : CompactSpace c.ball.domain := isCompact_iff_compactSpace.mp c.ball.compact_domain
  exact {
    toFun := fun f => ⟨chartValue F ζ hζ w m ψ c f.val, by
      refine ⟨?_, HasCompactSupport.of_compactSpace _⟩
      exact ((compactLCEquiv F ζ hζ w m hm ψ hψ J f.val).property.1).comp_continuous
        c.continuous_lift⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

set_option maxHeartbeats 1800000 in
theorem patchRestriction_injective (hψ : IsLocallyConstant ψ)
    (c : LocalChart F ζ hζ w m) (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Function.Injective (patchRestriction F ζ hζ w m hm ψ hψ c J) := by
  intro f g he
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext p
  change sectionValue F ζ hζ w m ψ f.val p = sectionValue F ζ hζ w m ψ g.val p
  by_cases hp : slope F ζ hζ w p ∈ c.ball.domain
  · let t : c.ball.domain := ⟨slope F ζ hζ w p, hp⟩
    let h : H F ζ hζ w := ⟨p * (c.lift t)⁻¹, by
      change slope F ζ hζ w (p * (c.lift t)⁻¹) = 1
      rw [map_mul, map_inv, c.slope_lift]
      exact mul_inv_cancel _⟩
    have hv : chartValue F ζ hζ w m ψ c f.val t =
        chartValue F ζ hζ w m ψ c g.val t := congrFun (congrArg Subtype.val he) t
    have hmul : h.val * c.lift t = p := by dsimp [h]; group
    have hf := f.val.val.val.property h (c.lift t)
    have hg := g.val.val.val.property h (c.lift t)
    change _ = normalizedSectionRepresentation (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ J) 1 h
        (chartValue F ζ hζ w m ψ c f.val t) at hf
    change _ = normalizedSectionRepresentation (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ J) 1 h
        (chartValue F ζ hζ w m ψ c g.val t) at hg
    rw [hv] at hf
    exact (hmul ▸ hf).trans (hmul ▸ hg).symm
  · rw [f.property p hp, g.property p hp]

include hm in
theorem patchRestriction_surjective_of_lcCharacter
    (hψ : IsLocallyConstant ψ)
    (hχ : letI := coverTopology; IsLocallyConstant (inducingCharacter F ζ hζ w ψ))
    (c : LocalChart F ζ hζ w m) (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Function.Surjective (patchRestriction F ζ hζ w m hm ψ hψ c J) := by
  classical
  letI := coverTopology
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  intro v
  let S : Set (P F ζ hζ w) := (slope F ζ hζ w) ⁻¹' c.ball.domain
  have hS : IsClopen S :=
    (show IsClopen c.ball.domain from ⟨c.ball.compact_domain.isClosed, c.ball.open_domain⟩).preimage
      (slope_continuous F ζ hζ w m hm)
  let t : S → c.ball.domain := fun p => ⟨slope F ζ hζ w p.val, p.property⟩
  have ht : Continuous t := ((slope_continuous F ζ hζ w m hm).comp continuous_subtype_val).subtype_mk _
  let d : S → H F ζ hζ w := fun p => ⟨p.val * (c.lift (t p))⁻¹, by
    change slope F ζ hζ w (p.val * (c.lift (t p))⁻¹) = 1
    rw [map_mul, map_inv, c.slope_lift]
    exact mul_inv_cancel _⟩
  have hd : Continuous d :=
    (continuous_subtype_val.mul (c.continuous_lift.comp ht).inv).subtype_mk _
  let a : LocallyConstant S J := ⟨fun p => (inducingCharacter F ζ hζ w ψ (d p) : ℂ) • v.val (t p),
    (hχ.comp_continuous hd).comp₂ (v.property.1.comp_continuous ht) (fun x y => (x : ℂ) • y)⟩
  let f : LocallyConstant (P F ζ hζ w) J := LocallyConstant.piecewise hS.isClosed
    hS.compl.isClosed (Set.union_compl_self S) a (LocallyConstant.const _ 0) (by
      intro p hp; exact (hp.2 hp.1).elim)
  have f_in (p : P F ζ hζ w) (hp : p ∈ S) : f p =
      (inducingCharacter F ζ hζ w ψ (d ⟨p, hp⟩) : ℂ) • v.val (t ⟨p, hp⟩) := by
    exact LocallyConstant.piecewise_apply_left _ _ _ _ _ _ p hp
  have f_out (p : P F ζ hζ w) (hp : p ∉ S) : f p = 0 := by
    exact LocallyConstant.piecewise_apply_right _ _ _ _ _ _ p hp
  let e := quotientHomeomorph F ζ hζ w m hm
  have hsupport : (Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w))) '' Function.support f ⊆
      e.symm '' c.ball.domain := by
    rintro q ⟨p, hp, rfl⟩
    have hpS : p ∈ S := by by_contra hn; exact hp (f_out p hn)
    refine ⟨slope F ζ hζ w p, hpS, ?_⟩
    apply e.injective
    rw [e.apply_symm_apply]
    exact (quotientHomeomorph_mk F ζ hζ w m hm p).symm
  letI : T2Space (SectionCosetSpace (H F ζ hζ w)) := e.symm.t2Space
  have hc : HasCompactSupportModH (H F ζ hζ w) f :=
    (c.ball.compact_domain.image e.symm.continuous).of_isClosed_subset isClosed_closure
      (closure_minimal hsupport (c.ball.compact_domain.image e.symm.continuous).isClosed)
  have hcov (h : H F ζ hζ w) (p : P F ζ hζ w) :
      f (h.val * p) = (inducingCharacter F ζ hζ w ψ h : ℂ) • f p := by
    have hs : slope F ζ hζ w h.val = 1 := h.property
    have htp : slope F ζ hζ w (h.val * p) = slope F ζ hζ w p := by simp [map_mul, hs]
    by_cases hp : p ∈ S
    · have hp' : h.val * p ∈ S := by simpa [S, htp] using hp
      rw [f_in p hp, f_in (h.val * p) hp']
      have htd : t ⟨h.val * p, hp'⟩ = t ⟨p, hp⟩ := Subtype.ext htp
      have hdd : d ⟨h.val * p, hp'⟩ = h * d ⟨p, hp⟩ := by
        apply Subtype.ext
        change (h.val * p) * (c.lift (t ⟨h.val * p, hp'⟩))⁻¹ = _
        rw [htd]
        exact mul_assoc _ _ _
      rw [htd, hdd, map_mul, Units.val_mul, mul_smul]
    · have hp' : h.val * p ∉ S := by simpa [S, htp] using hp
      rw [f_out p hp, f_out (h.val * p) hp', smul_zero]
  let fLC : CompactLCSections F ζ hζ w m ψ J := ⟨f, f.isLocallyConstant, hc, hcov⟩
  let fs := (compactLCEquiv F ζ hζ w m hm ψ hψ J).symm fLC
  let fp : PatchSections F ζ hζ w m ψ c J := ⟨fs, fun p hp => f_out p hp⟩
  refine ⟨fp, ?_⟩
  apply Subtype.ext
  funext x
  change f (c.lift x) = v.val x
  have hx : c.lift x ∈ S := by change slope F ζ hζ w (c.lift x) ∈ c.ball.domain; rw [c.slope_lift]; exact x.property
  rw [f_in _ hx]
  have htx : t ⟨c.lift x, hx⟩ = x := Subtype.ext (c.slope_lift x)
  have hdx : d ⟨c.lift x, hx⟩ = 1 := by
    apply Subtype.ext
    change c.lift x * (c.lift (t ⟨c.lift x, hx⟩))⁻¹ = 1
    rw [htx, mul_inv_cancel]
  simp [htx, hdx]

section PatchCharacterLC
set_option maxHeartbeats 800000
open scoped Matrix
private def patchLC_translation (b : KPRankOneInduction.upperBorel F w) : K F w :=
  let A := Classical.choose b.property
  A 0 1 / A 1 1

private lemma patchLC_translation_formula (b : KPRankOneInduction.upperBorel F w)
    (A : KPRankOneInduction.GL2 F w) (hA : Matrix.ProjGenLinGroup.mk A = b.val)
    (_hupper : A 1 0 = 0) : patchLC_translation F w b = A 0 1 / A 1 1 := by
  let B := Classical.choose b.property
  have hB : Matrix.ProjGenLinGroup.mk B = b.val := (Classical.choose_spec b.property).1
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp (hB.trans hA.symm)
  have hh (i j : Fin 2) := congrArg (fun g : KPRankOneInduction.GL2 F w => g i j) hu
  have h01 : A 0 1 = B 0 1 * (u : K F w) := by
    simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] using (hh 0 1).symm
  have h11 : A 1 1 = B 1 1 * (u : K F w) := by
    simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] using (hh 1 1).symm
  change B 0 1 / B 1 1 = _
  rw [h01, h11, mul_div_mul_right _ _ (Units.ne_zero u)]

private lemma patchLC_translation_continuous : Continuous (patchLC_translation F w) := by
  let f := (KPRankOneInduction.upperBorel F w : Set (KPRankOneInduction.PGL2 F w)).restrictPreimage
    (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F w → KPRankOneInduction.PGL2 F w)
  have hq : Topology.IsQuotientMap f :=
    (QuotientGroup.isOpenQuotientMap_mk.restrictPreimage _).isQuotientMap
  apply hq.continuous_iff.mpr
  have hupper (a : {a : KPRankOneInduction.GL2 F w | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F w}) :
      (a : KPRankOneInduction.GL2 F w) 1 0 = 0 := by
    obtain ⟨B, hB, h10⟩ := a.property
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
    have hh := congrArg (fun g : KPRankOneInduction.GL2 F w => g 1 0) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] at hh
    simp at hh
    rw [← hh, h10, zero_mul]
  have h11 (a : {a : KPRankOneInduction.GL2 F w | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F w}) :
      (a : KPRankOneInduction.GL2 F w) 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero (a : KPRankOneInduction.GL2 F w)
    rw [Matrix.det_fin_two] at hd
    simp only [hupper a, mul_zero, sub_zero] at hd
    exact (mul_ne_zero_iff.mp hd).2
  have hval : ∀ a, patchLC_translation F w (f a) =
      (a : KPRankOneInduction.GL2 F w) 0 1 / (a : KPRankOneInduction.GL2 F w) 1 1 := by
    intro a
    exact patchLC_translation_formula F w (f a) a rfl (hupper a)
  have hentry (i j : Fin 2) : Continuous (fun a : {a : KPRankOneInduction.GL2 F w | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F w} =>
      (a : KPRankOneInduction.GL2 F w) i j) :=
    (continuous_apply_apply i j).comp
      ((Units.continuous_val : Continuous (fun A : KPRankOneInduction.GL2 F w => (A : Matrix (Fin 2) (Fin 2) (K F w)))).comp continuous_subtype_val)
  change Continuous (fun a => patchLC_translation F w (f a))
  simp_rw [hval]
  exact (hentry 0 1).div (hentry 1 1) h11

private lemma patchLC_coordinates_word (h : H F ζ hζ w) :
    h.val = n F ζ hζ w (hCoordinates F ζ hζ w h).1 *
      z F ζ hζ w (hCoordinates F ζ hζ w h).2 :=
  Classical.choose_spec (ExistsUnique.exists (H_decomposition F ζ hζ w h))

private lemma patchLC_projection_z (e : rootsOfUnity 3 F) :
    KPLocalSmoothRepresentation.projection F ζ hζ w (z F ζ hζ w e).val = 1 := by
  change KPLocalSmoothRepresentation.ordinaryPGLMap F w
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e)) = 1
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  have hz : KPPGLLocalCover.projection F ζ hζ (Sum.inr w)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) e) = 1 := by
    apply (KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr w)).le
    exact ⟨e, rfl⟩
  rw [hz, map_one]

private lemma patchLC_coordinates_fst_eq (h : H F ζ hζ w) :
    (hCoordinates F ζ hζ w h).1 = patchLC_translation F w
      ⟨KPLocalSmoothRepresentation.projection F ζ hζ w h.val.val, h.val.property⟩ := by
  have hp : KPLocalSmoothRepresentation.projection F ζ hζ w h.val.val =
      KPRankOneInduction.upperRootElement F w (hCoordinates F ζ hζ w h).1 := by
    have hw := congrArg (fun p : P F ζ hζ w => KPLocalSmoothRepresentation.projection F ζ hζ w p.val)
      (patchLC_coordinates_word F ζ hζ w h)
    simp only [Subgroup.coe_mul, map_mul, patchLC_projection_z, mul_one] at hw
    exact hw
  rw [patchLC_translation_formula F w
    ⟨KPLocalSmoothRepresentation.projection F ζ hζ w h.val.val, h.val.property⟩
    (KPRankOneInduction.upperRootMatrix F w (hCoordinates F ζ hζ w h).1)
    hp.symm (by simp [KPRankOneInduction.upperRootMatrix])]
  simp [KPRankOneInduction.upperRootMatrix]

local notation "topology" => KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
include hm
private lemma patchLC_actual_projection_continuous :
    letI := topology
    Continuous (KPLocalSmoothRepresentation.projection F ζ hζ w) := by
  letI := topology
  have hmap : Continuous (KPLocalSmoothRepresentation.ordinaryPGLMap F w) := by
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
    apply (QuotientGroup.isQuotientMap_mk
      (KPPGLLocalCover.scalarSubgroup F (Sum.inr w))).continuous_iff.mpr
    exact QuotientGroup.continuous_mk
  exact hmap.comp (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.2.1.continuous

private lemma patchLC_coordinates_fst_continuous :
    letI := topology
    Continuous (fun h : H F ζ hζ w => (hCoordinates F ζ hζ w h).1) := by
  letI := topology
  simp_rw [patchLC_coordinates_fst_eq]
  exact (patchLC_translation_continuous F w).comp
    (((patchLC_actual_projection_continuous F ζ hζ w m hm).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)

private def patchLC_centralDefect (h : H F ζ hζ w) :
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
    (KPPGLLocalCover.projection F ζ hζ (Sum.inr w)).ker := by
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  refine ⟨(n F ζ hζ w (hCoordinates F ζ hζ w h).1).val⁻¹ * h.val.val, ?_⟩
  have he : (n F ζ hζ w (hCoordinates F ζ hζ w h).1).val⁻¹ * h.val.val =
      (z F ζ hζ w (hCoordinates F ζ hζ w h).2).val := by
    rw [patchLC_coordinates_word F ζ hζ w h]
    simp
  rw [he, ← KPPGLLocalCover.range_centralInjection_eq_ker_projection]
  exact ⟨(hCoordinates F ζ hζ w h).2, rfl⟩

private lemma patchLC_centralDefect_value (h : H F ζ hζ w) :
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
    (patchLC_centralDefect F ζ hζ w h).val =
      KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr w) (hCoordinates F ζ hζ w h).2 := by
  change (n F ζ hζ w (hCoordinates F ζ hζ w h).1).val⁻¹ * h.val.val = _
  rw [patchLC_coordinates_word F ζ hζ w h]
  simp only [Subgroup.coe_mul, inv_mul_cancel_left]
  rfl

private lemma patchLC_centralDefect_continuous :
    letI := topology
    letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
    Continuous (patchLC_centralDefect F ζ hζ w) := by
  letI := topology
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  have hn : Continuous (fun h : H F ζ hζ w =>
      (n F ζ hζ w (hCoordinates F ζ hζ w h).1).val) :=
    (KPLocalSmoothRepresentation.continuousUpperRoot F ζ hζ w m hm).continuous.comp
      (continuous_ofAdd.comp (patchLC_coordinates_fst_continuous F ζ hζ w m hm))
  exact (hn.inv.mul (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

private lemma patchLC_coordinates_snd_locallyConstant :
    letI := topology
    IsLocallyConstant (fun h : H F ζ hζ w => (hCoordinates F ζ hζ w h).2) := by
  letI := topology
  letI := KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr w)
  letI : TopologicalSpace (rootsOfUnity 3 F) := ⊥
  obtain ⟨hd, e, he⟩ := KPPGLLocalCover.finite_discrete_kernel F ζ hζ w m hm
  letI := hd
  have hc := (IsLocallyConstant.of_discrete e.symm).comp_continuous
    (patchLC_centralDefect_continuous F ζ hζ w m hm)
  have hv (h : H F ζ hζ w) : e.symm (patchLC_centralDefect F ζ hζ w h) =
      (hCoordinates F ζ hζ w h).2 := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [patchLC_centralDefect_value F ζ hζ w m hm h, he]
  simpa only [Function.comp_def, hv] using hc

theorem patchLC_actual_inducingCharacter_locallyConstant
    (ψ : Multiplicative (K F w) →* ℂˣ) (hψ : IsLocallyConstant ψ) :
    letI := topology
    IsLocallyConstant (inducingCharacter F ζ hζ w ψ) := by
  letI := topology
  have hb := hψ.comp_continuous
    (continuous_ofAdd.comp (patchLC_coordinates_fst_continuous F ζ hζ w m hm))
  have he := (patchLC_coordinates_snd_locallyConstant F ζ hζ w m hm).comp
    (iota F ζ hζ)
  exact hb.mul he

end PatchCharacterLC

def patchEquiv (hψ : IsLocallyConstant ψ) (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    PatchSections F ζ hζ w m ψ c J ≃ₗ[ℂ] CompactFunctions c.ball.domain J := by
  exact LinearEquiv.ofBijective (patchRestriction F ζ hζ w m hm ψ hψ c J)
    ⟨patchRestriction_injective F ζ hζ w m hm ψ hψ c J,
      patchRestriction_surjective_of_lcCharacter F ζ hζ w m hm ψ hψ
        (patchLC_actual_inducingCharacter_locallyConstant F ζ hζ w m hm ψ hψ) c J⟩

theorem patchEquiv_value (hψ : IsLocallyConstant ψ)
    (c : LocalChart F ζ hζ w m) {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : PatchSections F ζ hζ w m ψ c J) (t : c.ball.domain) :
    (patchEquiv F ζ hζ w m hm ψ hψ c J f).val t =
      chartValue F ζ hζ w m ψ c f.val t := by rfl

set_option maxHeartbeats 1800000 in
include hm in

theorem finite_patch_decomposition (hψ : IsLocallyConstant ψ)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ J) :
    ∃ r : ℕ, ∃ c : Fin r → LocalChart F ζ hζ w m,
      ∃ v : (i : Fin r) → PatchSections F ζ hζ w m ψ (c i) J,
        f = ∑ i, (v i).val := by
  classical
  letI := coverTopology
  let e := quotientHomeomorph F ζ hζ w m hm
  let T := e '' closure ((Quotient.mk (QuotientGroup.rightRel (H F ζ hζ w))) ''
    Function.support (sectionValue F ζ hζ w m ψ f))
  have hT : IsCompact T := f.property.image e.continuous
  have hcover : T ⊆ ⋃ c : LocalChart F ζ hζ w m, c.ball.domain := by
    intro t ht
    obtain ⟨c, hc, _⟩ := exists_localChart F ζ hζ w m hm t Set.univ isOpen_univ (Set.mem_univ t)
    exact Set.mem_iUnion.mpr ⟨c, hc⟩
  obtain ⟨cs, hcs⟩ := hT.elim_finite_subcover _ (fun c => c.ball.open_domain) hcover
  let c : Fin cs.card → LocalChart F ζ hζ w m := fun i => cs.equivFin.symm i
  let U : Fin cs.card → TopologicalSpace.Clopens (K F w)ˣ := fun i =>
    ⟨(c i).ball.domain, (c i).ball.compact_domain.isClosed, (c i).ball.open_domain⟩
  obtain ⟨W, hWU, hWeq, hWd⟩ := Fintype.exists_disjointed_le U
  have hUnion : (⋃ i, (W i : Set (K F w)ˣ)) = ⋃ i, (U i : Set (K F w)ˣ) := by
    have hh := congrArg (fun A : TopologicalSpace.Clopens (K F w)ˣ => (A : Set (K F w)ˣ)) hWeq
    simpa only [TopologicalSpace.Clopens.coe_finset_sup, Finset.mem_univ,
      Set.iUnion_true] using hh
  let v : (i : Fin cs.card) → PatchSections F ζ hζ w m ψ (c i) J := fun i =>
    ⟨cutSection F ζ hζ w m hm ψ hψ (W i) f, by
      intro p hp
      rw [cutSection_value]
      have hn : slope F ζ hζ w p ∉ W i := fun hw => hp (hWU i hw)
      simp [hn]⟩
  refine ⟨cs.card, c, v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext p
  change sectionValue F ζ hζ w m ψ f p =
    sectionValue F ζ hζ w m ψ (∑ i, (v i).val) p
  have hs : sectionValue F ζ hζ w m ψ (∑ i, (v i).val) p =
      ∑ i, sectionValue F ζ hζ w m ψ (v i).val p := by
    simp [sectionValue]
  rw [hs]
  by_cases hp : sectionValue F ζ hζ w m ψ f p = 0
  · simp [v, cutSection_value, hp]
  · have ht : slope F ζ hζ w p ∈ T := by
      rw [← quotientHomeomorph_mk F ζ hζ w m hm p]
      exact ⟨_, subset_closure ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨d, hd, hpd⟩ := Set.mem_iUnion₂.mp (hcs ht)
    have hpu : slope F ζ hζ w p ∈ ⋃ i, (U i : Set (K F w)ˣ) := by
      refine Set.mem_iUnion.mpr ⟨cs.equivFin ⟨d, hd⟩, ?_⟩
      simpa [U, c] using hpd
    rw [← hUnion] at hpu
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hpu
    change slope F ζ hζ w p ∈ W i at hi
    have hother (j : Fin cs.card) (hji : j ≠ i) : slope F ζ hζ w p ∉ W j := by
      intro hj
      have hdis := TopologicalSpace.Clopens.coe_disjoint.mpr (hWd hji)
      exact Set.disjoint_left.mp hdis hj hi
    rw [Finset.sum_eq_single i]
    · simp [v, cutSection_value, hi]
    · intro j hj hji
      simp [v, cutSection_value, hother j hji]
    · simp

section CompactFunctionTensorHelpers
variable {X : Type*} [TopologicalSpace X]
variable (J : Type*) [AddCommGroup J] [Module ℂ J]
def compactFunctionTensorMap : CompactFunctions X ℂ ⊗[ℂ] J →ₗ[ℂ] CompactFunctions X J :=
  TensorProduct.lift {
    toFun := fun f => {
      toFun := fun v => ⟨fun x => f.val x • v, by
        constructor
        · exact f.property.1.comp (fun c : ℂ => c • v)
        · exact f.property.2.smul_right (f' := fun _ => v)⟩
      map_add' := by intro a b; ext x; simp [smul_add]
      map_smul' := by intro c v; ext x; simp [smul_smul, mul_comm] }
    map_add' := by intro f g; ext v x; simp [add_smul]
    map_smul' := by intro c f; ext v x; simp [smul_smul] }
private theorem compactFunctionTensorMap_tmul (f : CompactFunctions X ℂ) (v : J) (x : X) :
    (compactFunctionTensorMap J (f ⊗ₜ[ℂ] v)).val x = f.val x • v := rfl
theorem compactFunctionTensorMap_injective : Function.Injective (compactFunctionTensorMap (X := X) J) := by
  classical
  let b := Module.Free.chooseBasis ℂ J
  let e := TensorProduct.equivFinsuppOfBasisRight (M := CompactFunctions X ℂ) b
  have hker : ∀ z, compactFunctionTensorMap (X := X) J z = 0 → z = 0 := by
    intro z hz
    suffices he : e z = 0 from e.injective (he.trans e.map_zero.symm)
    apply Finsupp.ext
    intro i
    apply Subtype.ext
    funext x
    have hcoord : (e z i).val x = b.coord i ((compactFunctionTensorMap J z).val x) := by
      clear hz
      induction z using TensorProduct.induction_on with
      | zero =>
        rw [e.map_zero, (compactFunctionTensorMap J).map_zero]
        exact (b.coord i).map_zero.symm
      | add a c ha hc => simp only [map_add, Finsupp.add_apply, Submodule.coe_add, Pi.add_apply, ha, hc]
      | tmul f v => simp [e, compactFunctionTensorMap_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
          Module.Basis.coord_apply, mul_comm]
    rw [hcoord, hz]
    simp
  intro a c hac
  have hz : compactFunctionTensorMap J (a - c) = 0 := by rw [map_sub, hac, sub_self]
  exact sub_eq_zero.mp (hker _ hz)
private theorem compactFunctionFiniteRange (f : CompactFunctions X J) : (Set.range f.val).Finite := by
  classical
  let S := tsupport f.val
  have hc : IsCompact S := f.property.2
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hc
  have hf : (Set.range (fun x : S => f.val x)).Finite :=
    (f.property.1.comp_continuous continuous_subtype_val).range_finite
  apply (hf.union (Set.finite_singleton 0)).subset
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · exact Or.inl ⟨⟨x, hx⟩, rfl⟩
  · exact Or.inr (by
      apply Classical.byContradiction
      intro h
      exact hx (subset_tsupport f.val h))
private theorem compactFunctionIndicatorMem (f : CompactFunctions X J) (v : J) (hv : v ≠ 0) :
    (f.val ⁻¹' {v}).indicator (fun _ => (1 : ℂ)) ∈ CompactFunctions X ℂ := by
  constructor
  · exact (LocallyConstant.charFn ℂ (f.property.1.isClopen_fiber v)).isLocallyConstant
  · have hsub : f.val ⁻¹' {v} ⊆ tsupport f.val := by
      intro x hx
      apply subset_tsupport
      change f.val x ≠ 0
      rw [show f.val x = v from hx]
      exact hv
    have hc := f.property.2.of_isClosed_subset (f.property.1.isClopen_fiber v).isClosed hsub
    exact HasCompactSupport.intro' hc (f.property.1.isClopen_fiber v).isClosed
      (by intro x hx; exact Set.indicator_of_notMem hx _)
theorem compactFunctionTensorMap_surjective : Function.Surjective (compactFunctionTensorMap (X := X) J) := by
  classical
  intro f
  let s := (compactFunctionFiniteRange J f).toFinset.erase 0
  let I : s → CompactFunctions X ℂ := fun v => ⟨(f.val ⁻¹' {v.val}).indicator (fun _ => 1),
    compactFunctionIndicatorMem J f v.val (Finset.ne_of_mem_erase v.property)⟩
  refine ⟨∑ v : s, I v ⊗ₜ[ℂ] v.val, ?_⟩
  apply Subtype.ext
  funext x
  simp only [map_sum, Submodule.coe_sum, Finset.sum_apply, compactFunctionTensorMap_tmul]
  by_cases hx : f.val x = 0
  · rw [hx]
    apply Finset.sum_eq_zero
    intro v _
    have hv : f.val x ≠ v.val := by rw [hx]; exact (Finset.ne_of_mem_erase v.property).symm
    simp [I, Set.indicator_of_notMem, hv]
  · have hmem : f.val x ∈ s := Finset.mem_erase.mpr ⟨hx, (compactFunctionFiniteRange J f).mem_toFinset.mpr ⟨x, rfl⟩⟩
    let v : s := ⟨f.val x, hmem⟩
    rw [Finset.sum_eq_single v]
    · simp [I, v]
    · intro b _ hb
      have hne : f.val x ≠ b.val := fun h => hb (Subtype.ext h.symm)
      simp [I, Set.indicator_of_notMem, hne]
    · simp
end CompactFunctionTensorHelpers

def patchTensorEquiv (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    (CompactFunctions c.ball.domain ℂ ⊗[ℂ] J) ≃ₗ[ℂ] CompactFunctions c.ball.domain J :=
  LinearEquiv.ofBijective (compactFunctionTensorMap J)
    ⟨compactFunctionTensorMap_injective J, compactFunctionTensorMap_surjective J⟩
theorem patchTensorEquiv_tmul (c : LocalChart F ζ hζ w m)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : CompactFunctions c.ball.domain ℂ) (v : J) (t : c.ball.domain) :
    (patchTensorEquiv F ζ hζ w m c J (f ⊗ₜ[ℂ] v)).val t = f.val t • v := rfl

section FunctionSubmoduleTensorHelpers
variable {X : Type*} {J : Type*} [AddCommGroup J] [Module ℂ J]
  (A : Submodule ℂ (X → ℂ)) (B : Submodule ℂ (X → J))
  (h : ∀ f : A, ∀ v : J, (fun x => f.val x • v) ∈ B)
def functionSubmoduleTensorMap : A ⊗[ℂ] J →ₗ[ℂ] B := TensorProduct.lift {
  toFun := fun f => {
    toFun := fun v => ⟨fun x => f.val x • v, h f v⟩
    map_add' := by intros; ext x; simp [smul_add]
    map_smul' := by intros; ext x; simp [smul_smul, mul_comm] }
  map_add' := by intros; ext v x; simp [add_smul]
  map_smul' := by intros; ext v x; simp [smul_smul] }
private theorem functionSubmoduleTensorMap_tmul (f : A) (v : J) (x : X) :
    (functionSubmoduleTensorMap A B h (f ⊗ₜ[ℂ] v)).val x = f.val x • v := rfl
theorem functionSubmoduleTensorMap_injective : Function.Injective (functionSubmoduleTensorMap A B h) := by
  classical
  let b := Module.Free.chooseBasis ℂ J
  let e := TensorProduct.equivFinsuppOfBasisRight (M := A) b
  have hker : ∀ z, functionSubmoduleTensorMap A B h z = 0 → z = 0 := by
    intro z hz
    suffices he : e z = 0 from e.injective (he.trans e.map_zero.symm)
    apply Finsupp.ext
    intro i
    apply Subtype.ext
    funext x
    have hcoord : (e z i).val x = b.coord i ((functionSubmoduleTensorMap A B h z).val x) := by
      clear hz
      induction z using TensorProduct.induction_on with
      | zero =>
        rw [e.map_zero, (functionSubmoduleTensorMap A B h).map_zero]
        exact (b.coord i).map_zero.symm
      | add a c ha hc => simp only [map_add, Finsupp.add_apply, Submodule.coe_add, Pi.add_apply, ha, hc]
      | tmul f v => simp [e, functionSubmoduleTensorMap_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
          Module.Basis.coord_apply, mul_comm]
    rw [hcoord, hz]
    exact (b.coord i).map_zero
  intro a c hac
  have hz : functionSubmoduleTensorMap A B h (a - c) = 0 := by rw [map_sub, hac, sub_self]
  exact sub_eq_zero.mp (hker _ hz)
end FunctionSubmoduleTensorHelpers

section SectionTensorHelpers
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
variable (hψ : IsLocallyConstant ψ)
private theorem value_injective {J : Type*} [AddCommGroup J] [Module ℂ J] :
    Function.Injective (sectionValue F ζ hζ w m ψ (J := J)) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  exact Subtype.ext hab
theorem lcCoeffMem (J : Type*) [AddCommGroup J] [Module ℂ J]
    (f : CompactLCSections F ζ hζ w m ψ ℂ) (v : J) :
    (fun p => f.val p • v) ∈ CompactLCSections F ζ hζ w m ψ J := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  refine ⟨f.property.1.comp (fun c : ℂ => c • v), ?_, ?_⟩
  · have hsub : Function.support (fun p => f.val p • v) ⊆ Function.support f.val := by
      intro p hp hz
      exact hp (show f.val p • v = 0 by rw [hz, zero_smul])
    exact f.property.2.1.of_isClosed_subset isClosed_closure (closure_mono (Set.image_mono hsub))
  · intro h p
    change (f.val (h.val * p)) • v = _
    rw [f.property.2.2 h p]
    exact smul_assoc _ _ _
def sectionTensorMap (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Sections F ζ hζ w m ψ ℂ ⊗[ℂ] J →ₗ[ℂ] Sections F ζ hζ w m ψ J :=
  (compactLCEquiv F ζ hζ w m hm ψ hψ J).symm.toLinearMap.comp
    ((functionSubmoduleTensorMap (CompactLCSections F ζ hζ w m ψ ℂ)
      (CompactLCSections F ζ hζ w m ψ J) (lcCoeffMem F ζ hζ w m ψ J)).comp
        (TensorProduct.map (compactLCEquiv F ζ hζ w m hm ψ hψ ℂ).toLinearMap LinearMap.id))
theorem sectionTensorMap_tmul {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ ℂ) (v : J) (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m ψ (sectionTensorMap F ζ hζ w m hm ψ hψ J (f ⊗ₜ[ℂ] v)) p =
      sectionValue F ζ hζ w m ψ f p • v := by
  let T := compactLCEquiv F ζ hζ w m hm ψ hψ J
  have he : T (sectionTensorMap F ζ hζ w m hm ψ hψ J (f ⊗ₜ[ℂ] v)) =
      ⟨fun p => (compactLCEquiv F ζ hζ w m hm ψ hψ ℂ f).val p • v,
        lcCoeffMem F ζ hζ w m ψ J _ v⟩ := by
    change T (T.symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  calc
    _ = (T (sectionTensorMap F ζ hζ w m hm ψ hψ J (f ⊗ₜ[ℂ] v))).val p :=
      (compactLCEquiv_value F ζ hζ w m hm ψ hψ _ p).symm
    _ = (compactLCEquiv F ζ hζ w m hm ψ hψ ℂ f).val p • v := congrArg (fun g => g.val p) he
    _ = _ := congrArg (fun c : ℂ => c • v) (compactLCEquiv_value F ζ hζ w m hm ψ hψ f p)
theorem sectionTensorMap_injective (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Function.Injective (sectionTensorMap F ζ hζ w m hm ψ hψ J) := by
  let T := compactLCEquiv F ζ hζ w m hm ψ hψ J
  let S := compactLCEquiv F ζ hζ w m hm ψ hψ ℂ
  exact T.symm.injective.comp
    ((functionSubmoduleTensorMap_injective (CompactLCSections F ζ hζ w m ψ ℂ)
      (CompactLCSections F ζ hζ w m ψ J) (lcCoeffMem F ζ hζ w m ψ J)).comp
        (TensorProduct.congr S (LinearEquiv.refl ℂ J)).injective)
include hm hψ in
private theorem sectionValue_H_covariance {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ J) (h : H F ζ hζ w) (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m ψ f (h.val * p) =
      (inducingCharacter F ζ hζ w ψ h : ℂ) • sectionValue F ζ hζ w m ψ f p := by
  let T := compactLCEquiv F ζ hζ w m hm ψ hψ J
  have hc := (T f).property.2.2 h p
  exact (compactLCEquiv_value F ζ hζ w m hm ψ hψ f _).symm.trans
    (hc.trans (congrArg (fun x : J => (inducingCharacter F ζ hζ w ψ h : ℂ) • x)
      (compactLCEquiv_value F ζ hζ w m hm ψ hψ f p)))
include hm hψ in
private theorem patchValues_injective (c : LocalChart F ζ hζ w m)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f g : PatchSections F ζ hζ w m ψ c J)
    (he : ∀ t : c.ball.domain, chartValue F ζ hζ w m ψ c f.val t =
      chartValue F ζ hζ w m ψ c g.val t) : f = g := by
  apply Subtype.ext
  apply value_injective F ζ hζ w m ψ
  funext p
  by_cases hp : slope F ζ hζ w p ∈ c.ball.domain
  · let t : c.ball.domain := ⟨slope F ζ hζ w p, hp⟩
    let h : H F ζ hζ w := ⟨p * (c.lift t)⁻¹, by
      change slope F ζ hζ w (p * (c.lift t)⁻¹) = 1
      rw [map_mul, map_inv, c.slope_lift]
      exact mul_inv_cancel _⟩
    have hp' : h.val * c.lift t = p := by dsimp [h]; group
    have hf := sectionValue_H_covariance F ζ hζ w m hm ψ hψ f.val h (c.lift t)
    have hg := sectionValue_H_covariance F ζ hζ w m hm ψ hψ g.val h (c.lift t)
    have hc : sectionValue F ζ hζ w m ψ f.val (c.lift t) =
        sectionValue F ζ hζ w m ψ g.val (c.lift t) := he t
    exact ((congrArg (sectionValue F ζ hζ w m ψ f.val) hp').symm.trans hf).trans
      ((congrArg (fun x : J => (inducingCharacter F ζ hζ w ψ h : ℂ) • x) hc).trans
        (hg.symm.trans (congrArg (sectionValue F ζ hζ w m ψ g.val) hp')))
  · exact (f.property p hp).trans (g.property p hp).symm
private def patchToSection (c : LocalChart F ζ hζ w m) :
    CompactFunctions c.ball.domain ℂ →ₗ[ℂ] Sections F ζ hζ w m ψ ℂ :=
  (PatchSections F ζ hζ w m ψ c ℂ).subtype.comp
    (patchEquiv F ζ hζ w m hm ψ hψ c ℂ).symm.toLinearMap
private def sectionValues (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Sections F ζ hζ w m ψ J →ₗ[ℂ] (P F ζ hζ w → J) where
  toFun := sectionValue F ζ hζ w m ψ
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
private def patchTensorIntoSections (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    CompactFunctions c.ball.domain ℂ ⊗[ℂ] J →ₗ[ℂ] Sections F ζ hζ w m ψ J :=
  (sectionTensorMap F ζ hζ w m hm ψ hψ J).comp
    (TensorProduct.map (patchToSection F ζ hζ w m hm ψ hψ c) LinearMap.id)
private theorem patchTensorIntoSections_tmul (c : LocalChart F ζ hζ w m)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : CompactFunctions c.ball.domain ℂ) (v : J) (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m ψ (patchTensorIntoSections F ζ hζ w m hm ψ hψ c J (f ⊗ₜ[ℂ] v)) p =
      sectionValue F ζ hζ w m ψ (patchToSection F ζ hζ w m hm ψ hψ c f) p • v :=
  sectionTensorMap_tmul F ζ hζ w m hm ψ hψ _ v p
private theorem sectionTensorMap_patch_mem (c : LocalChart F ζ hζ w m)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (z : CompactFunctions c.ball.domain ℂ ⊗[ℂ] J) :
    sectionTensorMap F ζ hζ w m hm ψ hψ J
      (TensorProduct.map (patchToSection F ζ hζ w m hm ψ hψ c) LinearMap.id z) ∈
        PatchSections F ζ hζ w m ψ c J := by
  let L := patchTensorIntoSections F ζ hζ w m hm ψ hψ c J
  change L z ∈ PatchSections F ζ hζ w m ψ c J
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [L.map_zero]
    exact Submodule.zero_mem _
  | add a b ha hb =>
    rw [L.map_add]
    exact Submodule.add_mem _ ha hb
  | tmul f v =>
    intro p hp
    have he := patchTensorIntoSections_tmul F ζ hζ w m hm ψ hψ c f v p
    have hz := ((patchEquiv F ζ hζ w m hm ψ hψ c ℂ).symm f).property p hp
    exact he.trans ((congrArg (fun c : ℂ => c • v) hz).trans (zero_smul _ _))
private def sectionTensorPatchMap (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    CompactFunctions c.ball.domain ℂ ⊗[ℂ] J →ₗ[ℂ] PatchSections F ζ hζ w m ψ c J :=
  (patchTensorIntoSections F ζ hζ w m hm ψ hψ c J).codRestrict
      (PatchSections F ζ hζ w m ψ c J) (sectionTensorMap_patch_mem F ζ hζ w m hm ψ hψ c)
private theorem patchTensorIntoSections_chart (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J]
    (z : CompactFunctions c.ball.domain ℂ ⊗[ℂ] J) (t : c.ball.domain) :
    sectionValue F ζ hζ w m ψ (patchTensorIntoSections F ζ hζ w m hm ψ hψ c J z) (c.lift t) =
      (patchTensorEquiv F ζ hζ w m c J z).val t := by
  let evalSection : Sections F ζ hζ w m ψ J →ₗ[ℂ] J :=
    (LinearMap.proj (c.lift t)).comp (sectionValues F ζ hζ w m ψ J)
  let evalFunc : CompactFunctions c.ball.domain J →ₗ[ℂ] J :=
    (LinearMap.proj t).comp (CompactFunctions c.ball.domain J).subtype
  have he : evalSection.comp (patchTensorIntoSections F ζ hζ w m hm ψ hψ c J) =
      evalFunc.comp (patchTensorEquiv F ζ hζ w m c J).toLinearMap := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    have ht := patchTensorIntoSections_tmul F ζ hζ w m hm ψ hψ c f v (c.lift t)
    have he := patchEquiv_value F ζ hζ w m hm ψ hψ c
      ((patchEquiv F ζ hζ w m hm ψ hψ c ℂ).symm f) t
    have hc : sectionValue F ζ hζ w m ψ
        (patchToSection F ζ hζ w m hm ψ hψ c f) (c.lift t) = f.val t :=
      he.symm.trans (congrArg (fun g => g.val t)
        ((patchEquiv F ζ hζ w m hm ψ hψ c ℂ).apply_symm_apply f))
    exact ht.trans ((congrArg (fun c : ℂ => c • v) hc).trans
      (patchTensorEquiv_tmul F ζ hζ w m c f v t).symm)
  exact congrArg (fun L => L z) he
private theorem sectionTensorPatchMap_surjective (c : LocalChart F ζ hζ w m)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Function.Surjective (sectionTensorPatchMap F ζ hζ w m hm ψ hψ c J) := by
  intro f
  let z := (patchTensorEquiv F ζ hζ w m c J).symm (patchEquiv F ζ hζ w m hm ψ hψ c J f)
  refine ⟨z, ?_⟩
  apply patchValues_injective F ζ hζ w m hm ψ hψ c
  intro t
  have hpoint := patchTensorIntoSections_chart F ζ hζ w m hm ψ hψ c J z t
  exact hpoint.trans ((congrArg (fun g => g.val t)
    ((patchTensorEquiv F ζ hζ w m c J).apply_symm_apply _)).trans
      (patchEquiv_value F ζ hζ w m hm ψ hψ c f t))
theorem sectionTensorMap_surjective (J : Type*) [AddCommGroup J] [Module ℂ J] :
    Function.Surjective (sectionTensorMap F ζ hζ w m hm ψ hψ J) := by
  intro f
  obtain ⟨r, c, v, hf⟩ := finite_patch_decomposition F ζ hζ w m hm ψ hψ f
  choose z hz using fun i => sectionTensorPatchMap_surjective F ζ hζ w m hm ψ hψ (c i) J (v i)
  refine ⟨∑ i, TensorProduct.map (patchToSection F ζ hζ w m hm ψ hψ (c i)) LinearMap.id (z i), ?_⟩
  rw [map_sum, hf]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg Subtype.val (hz i)
end SectionTensorHelpers

def sectionsTensorEquiv (hψ : IsLocallyConstant ψ)
    (J : Type*) [AddCommGroup J] [Module ℂ J] :
    (Sections F ζ hζ w m ψ ℂ ⊗[ℂ] J) ≃ₗ[ℂ] Sections F ζ hζ w m ψ J :=
  LinearEquiv.ofBijective (sectionTensorMap F ζ hζ w m hm ψ hψ J)
    ⟨sectionTensorMap_injective F ζ hζ w m hm ψ hψ J,
      sectionTensorMap_surjective F ζ hζ w m hm ψ hψ J⟩
include hm in
theorem sectionsTensorEquiv_tmul (hψ : IsLocallyConstant ψ)
    {J : Type*} [AddCommGroup J] [Module ℂ J]
    (f : Sections F ζ hζ w m ψ ℂ) (v : J) (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m ψ
      (sectionsTensorEquiv F ζ hζ w m hm ψ hψ J (f ⊗ₜ[ℂ] v)) p =
        sectionValue F ζ hζ w m ψ f p • v :=
  sectionTensorMap_tmul F ζ hζ w m hm ψ hψ f v p

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 200000 in
include hm in

theorem sectionsTensorEquiv_equivariant (hψ : IsLocallyConstant ψ)
    {J : Type*} [AddCommGroup J] [Module ℂ J] (p : P F ζ hζ w)
    (v : Sections F ζ hζ w m ψ ℂ ⊗[ℂ] J) :
    sectionsTensorEquiv F ζ hζ w m hm ψ hψ J
        (TensorProduct.map (rightAction F ζ hζ w m hm ψ ℂ p) LinearMap.id v) =
      rightAction F ζ hζ w m hm ψ J p
        (sectionsTensorEquiv F ζ hζ w m hm ψ hψ J v) := by
  let e := sectionsTensorEquiv F ζ hζ w m hm ψ hψ J
  let a := TensorProduct.map (rightAction F ζ hζ w m hm ψ ℂ p)
    (LinearMap.id : J →ₗ[ℂ] J)
  let b := rightAction F ζ hζ w m hm ψ J p
  change e (a v) = b (e v)
  induction v using TensorProduct.induction_on with
  | zero => rw [a.map_zero, e.map_zero, b.map_zero]
  | tmul f j =>
    change e (a (f ⊗ₜ[ℂ] j)) = b (e (f ⊗ₜ[ℂ] j))
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext q
    change sectionValue F ζ hζ w m ψ
      (sectionsTensorEquiv F ζ hζ w m hm ψ hψ J
        (TensorProduct.map (rightAction F ζ hζ w m hm ψ ℂ p) LinearMap.id
          (f ⊗ₜ[ℂ] j))) q = _
    rw [TensorProduct.map_tmul, LinearMap.id_apply, sectionsTensorEquiv_tmul]
    change sectionValue F ζ hζ w m ψ
      (rightAction F ζ hζ w m hm ψ ℂ p f) q • j =
      sectionValue F ζ hζ w m ψ
        (rightAction F ζ hζ w m hm ψ J p
          (sectionsTensorEquiv F ζ hζ w m hm ψ hψ J (f ⊗ₜ[ℂ] j))) q
    rw [rightAction_apply, rightAction_apply, sectionsTensorEquiv_tmul]
  | add x y hx hy =>
    calc
      e (a (x + y)) = e (a x + a y) := congrArg e (a.map_add x y)
      _ = e (a x) + e (a y) := e.map_add (a x) (a y)
      _ = b (e x) + b (e y) := congrArg₂ (· + ·) hx hy
      _ = b (e x + e y) := (b.map_add (e x) (e y)).symm
      _ = b (e (x + y)) := congrArg b (e.map_add x y).symm

end Topology
end DedekindZetaZeroFree.KPKirillovGenuineSectionCharts

end
end
