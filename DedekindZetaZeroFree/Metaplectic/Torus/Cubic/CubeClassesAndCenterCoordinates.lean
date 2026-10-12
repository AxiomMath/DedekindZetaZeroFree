module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.LocalPGLCoverModules
public import DedekindZetaZeroFree.Metaplectic.Kubota.AdelicCover.AdelicRestrictedProductTopology

@[expose] public section

open scoped NumberField Valued commutatorElement
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.ActualFiniteTorus

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))

abbrev K := q.adicCompletion F
abbrev Cover := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)

instance coverTopology : TopologicalSpace (Cover F ζ hζ q) :=
  KPPGLLocalCover.finiteTopology F ζ hζ q
    (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)

instance coverTopologicalGroup : IsTopologicalGroup (Cover F ζ hζ q) :=
  (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1

instance localValuativeRel : ValuativeRel (K F q) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
instance localNonarchimedean : IsNonarchimedeanLocalField (K F q) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q

abbrev H := KPLocalSmoothRepresentation.Torus F ζ hζ q

abbrev D := KPLocalTorus.CubeClasses (K F q)ˣ

def ordinaryIota : rootsOfUnity 3 F →* ℂˣ :=
  (KPLocalCover.coefficientEmbedding F ζ hζ).comp (KPLocalCover.threeToSix F)

def ordinaryMu3 : rootsOfUnity 3 F →* rootsOfUnity 3 ℂ :=
  (ordinaryIota F ζ hζ).codRestrict (rootsOfUnity 3 ℂ) (fun e => by
    change ordinaryIota F ζ hζ e ^ 3 = 1
    rw [← map_pow]
    have he : e ^ 3 = 1 := Subtype.ext e.property
    rw [he, map_one])

def coordinate : H F ζ hζ q →* (K F q)ˣ :=
  (KPRankOneInduction.borelRatio F q).comp
    ((KPRankOneInduction.borelProjection F q
      (KPLocalSmoothRepresentation.projection F ζ hζ q)).comp
      (Subgroup.inclusion (KPRankOneInduction.coveredTorus_le_Borel F q
        (KPLocalSmoothRepresentation.projection F ζ hζ q))))

def normalWord (e : rootsOfUnity 3 F) (y : (K F q)ˣ) : Cover F ζ hζ q :=
  KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e *
    KPPGLLocalCover.A F ζ hζ (Sum.inr q) y

def sheet (h : H F ζ hζ q) : rootsOfUnity 3 F :=
  @dite _ (∃ e, (h : Cover F ζ hζ q) = normalWord F ζ hζ q e (coordinate F ζ hζ q h))
    (Classical.propDecidable _) (fun he => Classical.choose he) (fun _ => 1)

local instance : (KPPGLLocalCover.scalarSubgroup F (Sum.inr q)).Normal :=
  KPPGLLocalCover.scalarSubgroup_normal F (Sum.inr q)
private lemma normalWord_projection (e : rootsOfUnity 3 F) (y : (K F q)ˣ) :
  KPLocalSmoothRepresentation.projection F ζ hζ q (normalWord F ζ hζ q e y) =
    Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (K F q) y 1) := by
  rw [normalWord, map_mul]
  have hz : KPLocalSmoothRepresentation.projection F ζ hζ q
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) = 1 := by
    change KPLocalSmoothRepresentation.ordinaryPGLMap F q
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e)) = 1
    have hk := KPPGLLocalCover.range_centralInjection_eq_ker_projection F ζ hζ (Sum.inr q)
    have hh : KPPGLLocalCover.projection F ζ hζ (Sum.inr q)
      (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) = 1 := by
      have hh : KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e ∈
        (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).ker := by rw [← hk]; exact ⟨e, rfl⟩
      exact hh
    rw [hh, map_one]
  rw [hz, one_mul]
  rfl
private lemma normalWord_mem (e : rootsOfUnity 3 F) (y : (K F q)ˣ) :
  normalWord F ζ hζ q e y ∈ H F ζ hζ q := by
  change KPLocalSmoothRepresentation.projection F ζ hζ q _ ∈ KPRankOneInduction.diagonalTorus F q
  refine ⟨KubotaRankTwo.d (K F q) y 1, (normalWord_projection F ζ hζ q e y).symm, ?_, ?_⟩ <;>
    simp [KubotaRankTwo.d]
private lemma normalWord_coordinate (e : rootsOfUnity 3 F) (y : (K F q)ˣ) (h : H F ζ hζ q)
  (hh : (h : Cover F ζ hζ q) = normalWord F ζ hζ q e y) : coordinate F ζ hζ q h = y := by
  apply Units.ext
  change (KPRankOneInduction.borelRatio F q _ : K F q) = (y : K F q)
  rw [KPRankOneInduction.borelRatio_eq _ _ _ (KubotaRankTwo.d (K F q) y 1)]
  · simp [KubotaRankTwo.d]
  · change Matrix.ProjGenLinGroup.mk _ = KPLocalSmoothRepresentation.projection F ζ hζ q h
    rw [hh, normalWord_projection]
  · simp [KubotaRankTwo.d]
private lemma ordinaryPGLMap_injective : Function.Injective (KPLocalSmoothRepresentation.ordinaryPGLMap F q) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  induction x using QuotientGroup.induction_on with | _ g =>
    change Matrix.ProjGenLinGroup.mk g = 1 at hx
    apply (QuotientGroup.eq_one_iff g).mpr
    have hg := Matrix.ProjGenLinGroup.mk_eq_one.mp hx
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    exact hg
private lemma normalWord_exists (h : H F ζ hζ q) :
    ∃ e, (h : Cover F ζ hζ q) = normalWord F ζ hζ q e (coordinate F ζ hζ q h) := by
  obtain ⟨A, hA, h10, h01⟩ := h.property
  have h11 : A 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [Matrix.det_fin_two] at hd
    simp only [h10, mul_zero, sub_zero] at hd
    exact (mul_ne_zero_iff.mp hd).2
  have hy : (coordinate F ζ hζ q h : K F q) = A 0 0 / A 1 1 := by
    apply KPRankOneInduction.borelRatio_eq F q _ A hA h10
  have hmat : KubotaRankTwo.d (K F q) (coordinate F ζ hζ q h) 1 *
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (A 1 1) h11) = A := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
        Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply, h10, h01, hy, h11]
  have hp : KPLocalSmoothRepresentation.projection F ζ hζ q
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (coordinate F ζ hζ q h)) =
      KPLocalSmoothRepresentation.projection F ζ hζ q h := by
    change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d (K F q) (coordinate F ζ hζ q h) 1) = _
    rw [← hA]
    exact (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr ⟨Units.mk0 (A 1 1) h11, hmat⟩
  have hk : (h : Cover F ζ hζ q) *
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) (coordinate F ζ hζ q h))⁻¹ ∈
      (KPPGLLocalCover.projection F ζ hζ (Sum.inr q)).ker := by
    apply ordinaryPGLMap_injective F q
    change KPLocalSmoothRepresentation.projection F ζ hζ q _ =
      KPLocalSmoothRepresentation.ordinaryPGLMap F q 1
    rw [map_mul, map_inv, hp, mul_inv_cancel, map_one]
  rw [← KPPGLLocalCover.range_centralInjection_eq_ker_projection] at hk
  obtain ⟨e, he⟩ := hk
  refine ⟨e, ?_⟩
  rw [normalWord, he]
  simp
private lemma borelRatio_continuous : Continuous (KPRankOneInduction.borelRatio F q) := by
  let f := (KPRankOneInduction.upperBorel F q : Set (KPRankOneInduction.PGL2 F q)).restrictPreimage
    (Matrix.ProjGenLinGroup.mk : KPRankOneInduction.GL2 F q → KPRankOneInduction.PGL2 F q)
  have hq : Topology.IsQuotientMap f :=
    (QuotientGroup.isOpenQuotientMap_mk.restrictPreimage _).isQuotientMap
  apply hq.continuous_iff.mpr
  have hupper (a : {a : KPRankOneInduction.GL2 F q | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F q}) :
      (a : KPRankOneInduction.GL2 F q) 1 0 = 0 := by
    obtain ⟨B, hB, h10⟩ := a.property
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
    have hh := congrArg (fun g : KPRankOneInduction.GL2 F q => g 1 0) hu
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar_apply, Matrix.diagonal_apply] at hh
    simp at hh
    rw [← hh, h10, zero_mul]
  have hdiag (a : {a : KPRankOneInduction.GL2 F q | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F q}) :
      (a : KPRankOneInduction.GL2 F q) 0 0 ≠ 0 ∧ (a : KPRankOneInduction.GL2 F q) 1 1 ≠ 0 := by
    have hd := Matrix.GeneralLinearGroup.det_ne_zero (a : KPRankOneInduction.GL2 F q)
    rw [Matrix.det_fin_two] at hd
    simp only [hupper a, mul_zero, sub_zero] at hd
    exact mul_ne_zero_iff.mp hd
  have hval : ∀ a, ((KPRankOneInduction.borelRatio F q) (f a) : K F q) =
      (a : KPRankOneInduction.GL2 F q) 0 0 / (a : KPRankOneInduction.GL2 F q) 1 1 := by
    intro a
    exact KPRankOneInduction.borelRatio_eq F q (f a) a rfl (hupper a)
  have hentry (i j : Fin 2) : Continuous (fun a : {a : KPRankOneInduction.GL2 F q | Matrix.ProjGenLinGroup.mk a ∈ KPRankOneInduction.upperBorel F q} =>
      (a : KPRankOneInduction.GL2 F q) i j) :=
    (continuous_apply_apply i j).comp
      ((Units.continuous_val : Continuous (fun A : KPRankOneInduction.GL2 F q => (A : Matrix (Fin 2) (Fin 2) (K F q)))).comp continuous_subtype_val)
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun a => ((KPRankOneInduction.borelRatio F q) (f a) : K F q))
    simp_rw [hval]
    exact (hentry 0 0).div (hentry 1 1) (fun a => (hdiag a).2)
  · change Continuous (fun a => (((KPRankOneInduction.borelRatio F q) (f a))⁻¹ : K F q))
    simp_rw [hval, inv_div]
    exact (hentry 1 1).div (hentry 0 0) (fun a => (hdiag a).1)
private lemma normalWord_coordinateinate_cont : Continuous (coordinate F ζ hζ q) := by
  have hpgl : Continuous (KPLocalSmoothRepresentation.ordinaryPGLMap F q) := by
    apply (QuotientGroup.isQuotientMap_mk (KPPGLLocalCover.scalarSubgroup F (Sum.inr q))).continuous_iff.mpr
    exact QuotientGroup.continuous_mk
  have hp : Continuous (KPLocalSmoothRepresentation.projection F ζ hζ q) :=
    hpgl.comp (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
      (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.2.1.continuous
  apply (borelRatio_continuous F q).comp
  exact (hp.comp continuous_subtype_val).subtype_mk _

theorem actual_torus_normal_form :
    (∀ e y, normalWord F ζ hζ q e y ∈ H F ζ hζ q) ∧
    (∀ h : H F ζ hζ q, ∃! p : rootsOfUnity 3 F × (K F q)ˣ,
      (h : Cover F ζ hζ q) = normalWord F ζ hζ q p.1 p.2) ∧
    (∀ h : H F ζ hζ q,
      (h : Cover F ζ hζ q) =
        normalWord F ζ hζ q (sheet F ζ hζ q h) (coordinate F ζ hζ q h)) ∧
    Continuous (coordinate F ζ hζ q) ∧
    Function.Surjective (coordinate F ζ hζ q) ∧
    (∀ h : H F ζ hζ q, coordinate F ζ hζ q h = 1 ↔
      ∃ e, (h : Cover F ζ hζ q) = KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) ∧
    (∀ (e : rootsOfUnity 3 F) (y : (K F q)ˣ) (h : H F ζ hζ q),
      (h : Cover F ζ hζ q) = normalWord F ζ hζ q e y →
      coordinate F ζ hζ q h = y ∧ sheet F ζ hζ q h = e) := by
  classical
  have hsheet (h : H F ζ hζ q) : (h : Cover F ζ hζ q) =
      normalWord F ζ hζ q (sheet F ζ hζ q h) (coordinate F ζ hζ q h) := by
    unfold sheet
    rw [dif_pos (normalWord_exists F ζ hζ q h)]
    exact Classical.choose_spec (normalWord_exists F ζ hζ q h)
  have hcoeff (e f : rootsOfUnity 3 F) (y : (K F q)ˣ) :
      normalWord F ζ hζ q e y = normalWord F ζ hζ q f y → e = f := by
    intro hh
    apply KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q)
    exact mul_right_cancel hh
  refine ⟨normalWord_mem F ζ hζ q, ?_, hsheet, normalWord_coordinateinate_cont F ζ hζ q, ?_, ?_, ?_⟩
  · intro h
    refine ⟨(sheet F ζ hζ q h, coordinate F ζ hζ q h), hsheet h, ?_⟩
    intro p hp
    have hy := normalWord_coordinate F ζ hζ q p.1 p.2 h hp
    apply Prod.ext
    · apply hcoeff p.1 (sheet F ζ hζ q h) p.2
      exact hp.symm.trans (by simpa [hy] using hsheet h)
    · exact hy.symm
  · intro y
    exact ⟨⟨normalWord F ζ hζ q 1 y, normalWord_mem F ζ hζ q 1 y⟩,
      normalWord_coordinate F ζ hζ q 1 y _ rfl⟩
  · intro h
    constructor
    · intro hy
      refine ⟨sheet F ζ hζ q h, ?_⟩
      simpa [normalWord, hy, KPPGLLocalCover.A, KPStandardLocalRootLifts.A_one] using hsheet h
    · rintro ⟨e, he⟩
      apply normalWord_coordinate F ζ hζ q e 1 h
      simpa [normalWord, KPPGLLocalCover.A, KPStandardLocalRootLifts.A_one] using he
  · intro e y h hh
    have hy := normalWord_coordinate F ζ hζ q e y h hh
    refine ⟨hy, ?_⟩
    apply hcoeff (sheet F ζ hζ q h) e y
    exact (by simpa [hy] using (hsheet h).symm.trans hh)

def torusLift (y : (K F q)ˣ) : H F ζ hζ q :=
  ⟨normalWord F ζ hζ q 1 y, (actual_torus_normal_form F ζ hζ q).1 1 y⟩

def central : rootsOfUnity 3 F →* H F ζ hζ q :=
  (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q)).codRestrict (H F ζ hζ q)
    (fun e => by
      have hm := (actual_torus_normal_form F ζ hζ q).1 e 1
      simpa [normalWord, KPPGLLocalCover.A, KPStandardLocalRootLifts.A_one] using hm)

def π : H F ζ hζ q →* D F q :=
  (QuotientGroup.mk' (CubicCharacters.cubes (K F q)ˣ)).comp (coordinate F ζ hζ q)

def arithmeticPairing : D F q →* (D F q →* rootsOfUnity 3 F) := by
  exact KPHilbert.finiteThreePairing F ζ hζ q

def pairing : D F q →* (D F q →* rootsOfUnity 3 ℂ) where
  toFun d := (ordinaryMu3 F ζ hζ).comp (arithmeticPairing F ζ hζ q d)
  map_one' := by
    apply MonoidHom.ext
    intro d
    change ordinaryMu3 F ζ hζ (arithmeticPairing F ζ hζ q 1 d) = 1
    rw [map_one]
    change ordinaryMu3 F ζ hζ 1 = 1
    exact map_one _
  map_mul' x y := by
    apply MonoidHom.ext
    intro d
    change ordinaryMu3 F ζ hζ (arithmeticPairing F ζ hζ q (x * y) d) =
      ordinaryMu3 F ζ hζ (arithmeticPairing F ζ hζ q x d) *
      ordinaryMu3 F ζ hζ (arithmeticPairing F ζ hζ q y d)
    rw [map_mul]
    change ordinaryMu3 F ζ hζ (arithmeticPairing F ζ hζ q x d * arithmeticPairing F ζ hζ q y d) = _
    exact map_mul _ _ _

private lemma z_comm (e : rootsOfUnity 3 F) (g : Cover F ζ hζ q) :
    Commute (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) g := by
  exact (Subgroup.mem_center_iff.mp (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e, rfl⟩) g).symm
private lemma A_commutator (x y : (K F q)ˣ) :
    ⁅KPPGLLocalCover.A F ζ hζ (Sum.inr q) x, KPPGLLocalCover.A F ζ hζ (Sum.inr q) y⁆ =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (KPHilbert.B3 F ζ hζ (Sum.inr q) x y) := by
  let b := KPHilbert.B3 F ζ hζ (Sum.inr q) x y
  have hb : b ^ 3 = 1 := Subtype.ext b.property
  have hrev : KPHilbert.B3 F ζ hζ (Sum.inr q) y x = b⁻¹ :=
    (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.1 y x
  have hh : b * (b⁻¹)^2 = b^2 := by
    have hh' : b^2 = b⁻¹ := (eq_inv_iff_mul_eq_one.mpr (by simpa [pow_succ] using hb))
    calc
      b * (b⁻¹)^2 = b * (b^2)⁻¹ := by rw [inv_pow]
      _ = b * b := by rw [hh', inv_inv]
      _ = b^2 := (pow_two b).symm
  have hab : KPPGLLocalCover.A F ζ hζ (Sum.inr q) x * KPPGLLocalCover.A F ζ hζ (Sum.inr q) y =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) b *
      (KPPGLLocalCover.A F ζ hζ (Sum.inr q) y * KPPGLLocalCover.A F ζ hζ (Sum.inr q) x) := by
    rw [KPPGLLocalCover.A_mul, KPPGLLocalCover.A_mul, hrev, ← mul_assoc, ← map_mul, hh, mul_comm x y]
  rw [commutatorElement_def, hab]
  group
  rfl
private lemma word_commutator (e f : rootsOfUnity 3 F) (x y : (K F q)ˣ) :
    ⁅normalWord F ζ hζ q e x, normalWord F ζ hζ q f y⁆ =
    KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) (KPHilbert.B3 F ζ hζ (Sum.inr q) x y) := by
  let a := KPPGLLocalCover.A F ζ hζ (Sum.inr q) x
  let b := KPPGLLocalCover.A F ζ hζ (Sum.inr q) y
  let z := KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e
  let w := KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) f
  have hza : Commute z a := z_comm F ζ hζ q e a
  have hzb : Commute z b := z_comm F ζ hζ q e b
  have hwa : Commute w a := z_comm F ζ hζ q f a
  have hwz : Commute w z := z_comm F ζ hζ q f z
  change ⁅z * a, w * b⁆ = _
  rw [commutatorElement_mul_left_eq_conj_mul, ((z_comm F ζ hζ q e w).mul_right hzb).commutator_eq]
  rw [commutatorElement_mul_right_eq_mul_conj, hwa.symm.commutator_eq, one_mul,
    A_commutator F ζ hζ q]
  change z * (w * _ * w⁻¹) * z⁻¹ * 1 = _
  rw [(z_comm F ζ hζ q f _).eq]
  change z * (_ * w * w⁻¹) * z⁻¹ * 1 = _
  simp only [mul_inv_cancel_right, mul_one]
  rw [(z_comm F ζ hζ q e _).eq]
  change _ * z * z⁻¹ = _
  simp

private lemma ordinary_inj : Function.Injective (ordinaryMu3 F ζ hζ) := by
  intro a b hab
  apply Subtype.ext
  have he := KPLocalCover.coefficientEmbedding_injective F ζ hζ (congrArg (fun z : rootsOfUnity 3 ℂ => (z : ℂˣ)) hab)
  exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) he
private lemma ordinary_bij : Function.Bijective (ordinaryMu3 F ζ hζ) := by
  apply (Nat.bijective_iff_injective_and_card _).2
  refine ⟨ordinary_inj F ζ hζ, ?_⟩
  obtain ⟨z, hz⟩ := KPHilbert.rootsThree F ζ hζ
  have hf : IsPrimitiveRoot z 3 := (mem_primitiveRoots (by decide)).mp hz
  rw [hf.card_rootsOfUnity]
  symm
  exact (Complex.isPrimitiveRoot_exp 3 (by decide)).card_rootsOfUnity
private lemma pairing_bijective : Function.Bijective (pairing F ζ hζ q) := by
  letI : Finite (ClassFieldTheory.PowerClassGroup (K F q) 3) := ClassFieldTheory.powerClassGroup_finite (K F q) 3 (by norm_num)
  let B := ClassFieldTheory.finitePlaceAdicHilbertPairingFamily F 3 (KPHilbert.rootsThree F ζ hζ) q
  have hmu : (primitiveRoots 3 (K F q)).Nonempty := by
    obtain ⟨z, hz⟩ := KPHilbert.rootsThree F ζ hζ
    exact ⟨algebraMap F (K F q) z, (mem_primitiveRoots (by decide)).2 (((mem_primitiveRoots (by decide)).1 hz).map_of_injective (algebraMap F (K F q)).injective)⟩
  have hB := (ClassFieldTheory.finitePlaceAdicHilbertPairingFamily_isLocallyHilbert F 3 (KPHilbert.rootsThree F ζ hζ) q).2.2.1.bijective
    hmu
  let e := MulEquiv.ofBijective (ordinaryMu3 F ζ hζ) (ordinary_bij F ζ hζ)
  let f := (KPHilbert.finiteRootsThree F ζ hζ q).symm.trans e
  let g := (MulEquiv.inv (rootsOfUnity 3 (K F q))).trans f
  have hp : ∀ d, pairing F ζ hζ q d = g.toMonoidHom.comp (B d) := by
    intro d
    apply MonoidHom.ext
    intro d'
    rfl
  constructor
  · intro a b hab
    apply hB.1
    apply MonoidHom.ext
    intro d
    apply g.injective
    exact congrArg (fun h : D F q →* rootsOfUnity 3 ℂ => h d) hab
  · intro h
    obtain ⟨d, hd⟩ := hB.2 (g.symm.toMonoidHom.comp h)
    refine ⟨d, ?_⟩
    apply (hp d).trans
    apply MonoidHom.ext
    intro d'
    change g (B d d') = h d'
    have hd' := congrArg (fun k : ClassFieldTheory.PowerClassGroup (K F q) 3 →* rootsOfUnity 3 (K F q) => k d') hd
    change B d d' = g.symm (h d') at hd'
    rw [hd']
    exact g.apply_symm_apply (h d')

theorem actual_cube_quotient_pairing :
    Finite (D F q) ∧ Function.Surjective (π F ζ hζ q) ∧
    (∀ d : D F q, pairing F ζ hζ q d d = 1) ∧
    Function.Bijective (pairing F ζ hζ q) ∧
    (∀ x y : (K F q)ˣ,
      ⁅torusLift F ζ hζ q x, torusLift F ζ hζ q y⁆ =
        central F ζ hζ q (KPHilbert.B3 F ζ hζ (Sum.inr q) x y)) ∧
    (∀ x y : H F ζ hζ q,
      ⁅x, y⁆ = central F ζ hζ q (KPHilbert.B3 F ζ hζ (Sum.inr q)
        (coordinate F ζ hζ q x) (coordinate F ζ hζ q y))) ∧
    (∀ x y : H F ζ hζ q, Commute x y ↔
      pairing F ζ hζ q (π F ζ hζ q x) (π F ζ hζ q y) = 1) ∧
    (∀ x y : H F ζ hζ q,
      (pairing F ζ hζ q (π F ζ hζ q x) (π F ζ hζ q y) : ℂˣ) =
        ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q)
          (coordinate F ζ hζ q x) (coordinate F ζ hζ q y))) := by
  classical
  have hs : Function.Surjective (π F ζ hζ q) := by
    intro d
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (CubicCharacters.cubes (K F q)ˣ) d
    refine ⟨torusLift F ζ hζ q y, ?_⟩
    have hc := (actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 1 y (torusLift F ζ hζ q y) rfl
    change QuotientGroup.mk' _ (coordinate F ζ hζ q (torusLift F ζ hζ q y)) = d
    rw [hc.1]
    exact hy
  have hv (x y : H F ζ hζ q) :
      (pairing F ζ hζ q (π F ζ hζ q x) (π F ζ hζ q y) : ℂˣ) =
        ordinaryIota F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q)
          (coordinate F ζ hζ q x) (coordinate F ζ hζ q y)) := by
    rw [KPHilbert.B3_canonical]
    rfl
  have hcomm (x y : H F ζ hζ q) : ⁅x, y⁆ = central F ζ hζ q
      (KPHilbert.B3 F ζ hζ (Sum.inr q) (coordinate F ζ hζ q x) (coordinate F ζ hζ q y)) := by
    apply Subtype.ext
    change ⁅(x : Cover F ζ hζ q), (y : Cover F ζ hζ q)⁆ = _
    rw [(actual_torus_normal_form F ζ hζ q).2.2.1 x,
      (actual_torus_normal_form F ζ hζ q).2.2.1 y]
    exact word_commutator F ζ hζ q _ _ _ _
  refine ⟨ClassFieldTheory.powerClassGroup_finite (K F q) 3 (by norm_num), hs, ?_,
    pairing_bijective F ζ hζ q, ?_, hcomm, ?_, hv⟩
  · intro d
    obtain ⟨x, rfl⟩ := hs d
    apply Subtype.ext
    rw [hv, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.2 _ |>.1, map_one]
    rfl
  · intro x y
    have hx := (actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 1 x (torusLift F ζ hζ q x) rfl
    have hy := (actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 1 y (torusLift F ζ hζ q y) rfl
    simpa [hx.1, hy.1] using hcomm (torusLift F ζ hζ q x) (torusLift F ζ hζ q y)
  · intro x y
    rw [← commutatorElement_eq_one_iff_commute, hcomm]
    have hi : Function.Injective (central F ζ hζ q) := by
      intro a b hab
      exact KPPGLLocalCover.centralInjection_injective F ζ hζ (Sum.inr q) (congrArg Subtype.val hab)
    have hz (b : rootsOfUnity 3 F) : central F ζ hζ q b = 1 ↔ b = 1 :=
      ⟨fun h => hi (h.trans (map_one _).symm), fun h => h ▸ map_one _⟩
    rw [hz]
    have hp : pairing F ζ hζ q (π F ζ hζ q x) (π F ζ hζ q y) =
        ordinaryMu3 F ζ hζ (KPHilbert.B3 F ζ hζ (Sum.inr q)
          (coordinate F ζ hζ q x) (coordinate F ζ hζ q y)) := by
      apply Subtype.ext
      exact hv x y
    rw [hp]
    exact ⟨fun h => h ▸ map_one _, fun h => (ordinary_inj F ζ hζ) (h.trans (map_one _).symm)⟩

def finiteCubeClasses : Finite (D F q) :=
  (actual_cube_quotient_pairing F ζ hζ q).1

abbrev C := Subgroup.center (H F ζ hζ q)

theorem actual_center_cube_normal_form :
    (π F ζ hζ q).ker = C F ζ hζ q ∧
    IsOpen (C F ζ hζ q : Set (H F ζ hζ q)) ∧
    (∀ e, central F ζ hζ q e ∈ C F ζ hζ q) ∧
    (∀ y : (K F q)ˣ, torusLift F ζ hζ q (y ^ 3) ∈ C F ζ hζ q) ∧
    (∀ c : C F ζ hζ q, ∃! p : rootsOfUnity 3 F × CubicCharacters.cubes (K F q)ˣ,
      (c : H F ζ hζ q) = central F ζ hζ q p.1 * torusLift F ζ hζ q p.2) ∧
    (torusLift F ζ hζ q (1 ^ 3) = 1 ∧
      ∀ x y : (K F q)ˣ, torusLift F ζ hζ q ((x * y) ^ 3) =
        torusLift F ζ hζ q (x ^ 3) * torusLift F ζ hζ q (y ^ 3)) := by
  classical
  have hc := actual_cube_quotient_pairing F ζ hζ q
  have hn := actual_torus_normal_form F ζ hζ q
  have hker : (π F ζ hζ q).ker = C F ζ hζ q := by
    apply Subgroup.ext
    intro x
    change π F ζ hζ q x = 1 ↔ x ∈ Subgroup.center (H F ζ hζ q)
    rw [Subgroup.mem_center_iff]
    constructor
    · intro hx y
      exact ((hc.2.2.2.2.2.2.1 x y).2 (by rw [hx, map_one]; rfl)).eq.symm
    · intro hx
      apply hc.2.2.2.1.1
      apply MonoidHom.ext
      intro d
      obtain ⟨y, rfl⟩ := hc.2.1 d
      have hcomm : Commute x y := (hx y).symm
      have hp1 : pairing F ζ hζ q 1 (π F ζ hζ q y) = 1 := by
        rw [map_one]; rfl
      exact ((hc.2.2.2.2.2.2.1 x y).1 hcomm).trans hp1.symm
  have hcoord (e : rootsOfUnity 3 F) (y : (K F q)ˣ) :
      coordinate F ζ hζ q (central F ζ hζ q e * torusLift F ζ hζ q y) = y := by
    apply (hn.2.2.2.2.2.2 e y _ ?_).1
    simp [central, torusLift, normalWord]
  have hcube (y : (K F q)ˣ) : torusLift F ζ hζ q (y ^ 3) ∈ C F ζ hζ q := by
    rw [← hker]
    change QuotientGroup.mk' _ (coordinate F ζ hζ q (torusLift F ζ hζ q (y^3))) = 1
    have hy := (hn.2.2.2.2.2.2 1 (y^3) (torusLift F ζ hζ q (y^3)) rfl).1
    rw [hy]
    exact (QuotientGroup.eq_one_iff (y^3)).mpr ⟨y, rfl⟩
  have hcen (e : rootsOfUnity 3 F) : central F ζ hζ q e ∈ C F ζ hζ q := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (z_comm F ζ hζ q e g).eq.symm
  refine ⟨hker, ?_, hcen, hcube, ?_, ?_, ?_⟩
  · obtain ⟨E, hE⟩ := LocalClassFieldTheory.exists_finiteGalois_normSubgroup_le_powMonoidHom_range
        (K F q) 3 (by norm_num)
    letI : FiniteDimensional (K F q) (E : IntermediateField (K F q) (SeparableClosure (K F q))) := E.finiteDimensional
    letI : IsGalois (K F q) (E : IntermediateField (K F q) (SeparableClosure (K F q))) := E.isGalois
    have hopen : IsOpen (CubicCharacters.cubes (K F q)ˣ : Set (K F q)ˣ) :=
      Subgroup.isOpen_mono hE (LocalClassFieldTheory.localNormSubgroup_isOpen (K F q)
        (E : IntermediateField (K F q) (SeparableClosure (K F q))))
    rw [← hker]
    have heq : ((π F ζ hζ q).ker : Set (H F ζ hζ q)) =
        coordinate F ζ hζ q ⁻¹' (CubicCharacters.cubes (K F q)ˣ : Set (K F q)ˣ) := by
      ext x
      exact QuotientGroup.eq_one_iff (coordinate F ζ hζ q x)
    rw [heq]
    exact hopen.preimage hn.2.2.2.1
  · intro c
    let y := coordinate F ζ hζ q (c : H F ζ hζ q)
    have hy : y ∈ CubicCharacters.cubes (K F q)ˣ := by
      have hk : (c : H F ζ hζ q) ∈ (π F ζ hζ q).ker := by rw [hker]; exact c.property
      exact (QuotientGroup.eq_one_iff y).mp hk
    let e := sheet F ζ hζ q (c : H F ζ hζ q)
    have hword : (c : H F ζ hζ q) = central F ζ hζ q e * torusLift F ζ hζ q y := by
      apply Subtype.ext
      simpa [central, torusLift, normalWord, e, y] using hn.2.2.1 (c : H F ζ hζ q)
    refine ⟨(e, ⟨y, hy⟩), hword, ?_⟩
    intro p hp
    have hpy : (p.2 : (K F q)ˣ) = y := by
      have hh := congrArg (coordinate F ζ hζ q) hp
      rw [hcoord] at hh
      exact hh.symm
    apply Prod.ext
    · have hn1 := (hn.2.2.2.2.2.2 p.1 p.2 (c : H F ζ hζ q) ?_).2
      · exact hn1.symm
      · simpa [central, torusLift, normalWord] using congrArg Subtype.val hp
    · exact Subtype.ext hpy
  · apply Subtype.ext
    simp [torusLift, normalWord, KPPGLLocalCover.A, KPStandardLocalRootLifts.A_one]
  · intro x y
    apply Subtype.ext
    change normalWord F ζ hζ q 1 ((x*y)^3) =
      normalWord F ζ hζ q 1 (x^3) * normalWord F ζ hζ q 1 (y^3)
    simp only [normalWord, map_one, one_mul]
    rw [KPPGLLocalCover.A_mul, (KPHilbert.B3_laws F ζ hζ (Sum.inr q)).2.2.2.2.1 x (y^3) |>.1,
      one_pow, map_one, one_mul, mul_pow]

def centerInjection : rootsOfUnity 3 F →* C F ζ hζ q :=
  (central F ζ hζ q).codRestrict (C F ζ hζ q)
    (actual_center_cube_normal_form F ζ hζ q).2.2.1

def cubeLift : (K F q)ˣ →* C F ζ hζ q where
  toFun y := ⟨torusLift F ζ hζ q (y ^ 3),
    (actual_center_cube_normal_form F ζ hζ q).2.2.2.1 y⟩
  map_one' := Subtype.ext (actual_center_cube_normal_form F ζ hζ q).2.2.2.2.2.1
  map_mul' x y := Subtype.ext ((actual_center_cube_normal_form F ζ hζ q).2.2.2.2.2.2 x y)

end
end DedekindZetaZeroFree.ActualFiniteTorus
