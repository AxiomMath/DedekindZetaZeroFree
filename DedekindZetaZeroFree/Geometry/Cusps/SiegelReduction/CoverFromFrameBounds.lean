module

public import DedekindZetaZeroFree.Adeles.Lattices.MinkowskiCuspHeight
public import DedekindZetaZeroFree.Geometry.Cusps.SiegelReduction.CrossSectionRepresentatives

@[expose] public section

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

theorem exists_openEmbedding_cuspQuotient
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (U : Set (KPArch.Space (KPCuspLogShape.dimension F))) (hU : IsOpen U)
    (hident : ∀ (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F)),
      z ∈ U → action F (γ : KPCuspArithmetic.PGL2 F) z ∈ U →
      (γ : KPCuspArithmetic.PGL2 F) ∈ parabolic F Γ q) :
    ∃ e : CuspQuotient F Γ q U → OrbitQuotient F Γ,
      Topology.IsOpenEmbedding e ∧
      (∀ z : U, e (Quotient.mk _ z) = projection F Γ z) := by
  have hrel (x y : U)
      (h : (Setoid.comap (Subtype.val : U → KPArch.Space (KPCuspLogShape.dimension F))
        (MulAction.orbitRel (parabolic F Γ q) (KPArch.Space (KPCuspLogShape.dimension F)))) x y) :
      projection F Γ x = projection F Γ y := by
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    exact ⟨⟨g, g.property.1⟩, hg⟩
  let e : CuspQuotient F Γ q U → OrbitQuotient F Γ :=
    Quotient.lift (fun z : U => projection F Γ z) hrel
  have he (z : U) : e (Quotient.mk _ z) = projection F Γ z := rfl
  refine ⟨e, Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_, he⟩
  · exact ((continuous_projection F Γ).comp continuous_subtype_val).quotient_lift hrel
  · intro x y hxy
    induction x using Quotient.inductionOn with | h x =>
      induction y using Quotient.inductionOn with | h y =>
        change projection F Γ x = projection F Γ y at hxy
        obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
          (MulAction.orbitRel_apply.mp (Quotient.exact hxy))
        apply Quotient.sound
        apply MulAction.orbitRel_apply.mpr
        apply MulAction.mem_orbit_iff.mpr
        have hm : (γ : KPCuspArithmetic.PGL2 F) ∈ parabolic F Γ q :=
          hident γ y y.property (by simpa only [show action F (γ : KPCuspArithmetic.PGL2 F) y = x from hγ] using x.property)
        exact ⟨⟨γ, hm⟩, hγ⟩
  · intro V hV
    let W : Set U := (Quotient.mk _) ⁻¹' V
    have hW : IsOpen W := continuous_quotient_mk'.isOpen_preimage V hV
    have hWV : e '' V = projection F Γ '' (Subtype.val '' W) := by
      ext p
      constructor
      · rintro ⟨v, hv, rfl⟩
        obtain ⟨z, rfl⟩ := Quotient.mk_surjective v
        exact ⟨z, ⟨z, hv, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨Quotient.mk _ w, hw, rfl⟩
    rw [hWV]
    exact isOpenMap_projection F Γ _ (hU.isOpenEmbedding_subtypeVal.isOpenMap W hW)

theorem exists_embedding_highCusp
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (hident : ∀ (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F)),
      z ∈ highCusp F σ T → action F (γ : KPCuspArithmetic.PGL2 F) z ∈ highCusp F σ T →
      (γ : KPCuspArithmetic.PGL2 F) ∈ parabolic F Γ q) :
    ∃ e : CuspQuotient F Γ q (highCusp F σ T) → OrbitQuotient F Γ,
      Topology.IsEmbedding e ∧
      (∀ z : highCusp F σ T, e (Quotient.mk _ z) = projection F Γ z) := by
  obtain ⟨e, he, hrep⟩ := exists_openEmbedding_cuspQuotient F Γ q _
    (isOpen_highCusp F σ T) hident
  exact ⟨e, he.isEmbedding, hrep⟩

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

theorem meanHeight_conjugated_parabolic
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q)
    (g : parabolic F Γ q) (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
      (action F (σ⁻¹ * (g : KPCuspArithmetic.PGL2 F) * σ) z) =
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z := by
  obtain ⟨hupper, J, L, E, ι, ρ, hJ, hL, hLindex, hhor, hE, hindex,
    hinj, hsurj, hexact, hiota, hratio⟩ :=
    kp_cusp_arithmetic_parabolic_stabilizers F M hM Γ hΓ hcomm q σ hσ
  let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
  let u : S := ⟨σ⁻¹ * (g : KPCuspArithmetic.PGL2 F) * σ,
    Subgroup.mem_map.mpr ⟨g, g.property, by simp [MulAut.conj_apply]⟩⟩
  obtain ⟨A, hA, hzero⟩ := hupper u u.property
  have hr := hratio u A hA hzero
  change KPCuspLogShape.meanHeight _ (action F (u : KPCuspArithmetic.PGL2 F) z) = _
  rw [← hA, action_mk]
  exact (KPCuspLogShape.actual_upper_height_shape F hF E hE (ρ u) A hzero hr z).1

theorem parabolic_mapsTo_highCusp
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q)
    (T : ℝ) (g : parabolic F Γ q) :
    Set.MapsTo (action F (g : KPCuspArithmetic.PGL2 F))
      (highCusp F σ T) (highCusp F σ T) := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨action F (σ⁻¹ * (g : KPCuspArithmetic.PGL2 F) * σ) z, ?_, ?_⟩
  · change T < KPCuspLogShape.meanHeight _ _
    rw [meanHeight_conjugated_parabolic F hF M hM Γ hΓ hcomm q σ hσ]
    exact hz
  · change σ • ((σ⁻¹ * (g : KPCuspArithmetic.PGL2 F) * σ) • z) =
      (g : KPCuspArithmetic.PGL2 F) • (σ • z)
    simp only [mul_smul, smul_inv_smul]

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

def frameLowerRow (A : Matrix.GeneralLinearGroup (Fin 2) F) : KPCusp.Row F :=
  ⟨(A 1 0, A 1 1), by
    intro h
    have hc : A 1 0 = 0 := congrArg Prod.fst h
    have hd : A 1 1 = 0 := congrArg Prod.snd h
    apply A.det_ne_zero
    simp [Matrix.det_fin_two, hc, hd]⟩

theorem prod_height_eq_exp_meanHeight
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    (∏ i, KPArch.height (z i)) =
      Real.exp ((KPCuspLogShape.dimension F : ℝ) *
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z) := by
  by_cases hd : KPCuspLogShape.dimension F = 0
  · haveI : IsEmpty (Fin (KPCuspLogShape.dimension F)) :=
      ⟨fun i => by have := i.isLt; omega⟩
    simp [KPCuspLogShape.meanHeight, hd]
  · simp only [KPArch.height, ← Real.exp_sum, KPCuspLogShape.meanHeight]
    rw [mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hd)]

theorem normalizedHeight_frame_lower_row
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPCusp.normalizedHeight F J (frameLowerRow F A) z =
      (FractionalIdeal.absNorm (KPCusp.content F J (frameLowerRow F A)) : ℝ) /
        (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
          Matrix (Fin 2) (Fin 2) ℂ).det‖) *
        Real.exp ((KPCuspLogShape.dimension F : ℝ) *
          KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (glAction F A z)) := by
  rw [← prod_height_eq_exp_meanHeight]
  have hden (i : Fin (KPCuspLogShape.dimension F)) :
      KPCusp.rowDenominator F (frameLowerRow F A) i (z i) =
        KPArch.actionDenominator
          (Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A) (z i) := rfl
  have hdet : (∏ i, ‖(Matrix.GeneralLinearGroup.map
      (KPCusp.complexPlace F i).embedding A : Matrix (Fin 2) (Fin 2) ℂ).det‖) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.map _ A).det_ne_zero
  simp only [glAction, KPArch.productAction, KPArch.action_height,
    Finset.prod_div_distrib, Finset.prod_mul_distrib]
  simp only [KPCusp.normalizedHeight, hden]
  field_simp
  rfl

def frameHeightConstant
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) : ℝ :=
  (FractionalIdeal.absNorm (KPCusp.content F J (frameLowerRow F A)) : ℝ) /
    (∏ i, ‖(Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding A :
      Matrix (Fin 2) (Fin 2) ℂ).det‖)

theorem frameHeightConstant_pos
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) : 0 < frameHeightConstant F J A := by
  have h := KPCusp.normalizedHeight_pos F J hJ (frameLowerRow F A)
    (fun _ => (0, 0))
  rw [normalizedHeight_frame_lower_row F] at h
  change 0 < frameHeightConstant F J A * _ at h
  exact (mul_pos_iff_of_pos_right (Real.exp_pos _)).mp h

theorem highCusp_eq_normalized_horoball
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (T : ℝ)
    (hd : 0 < KPCuspLogShape.dimension F) :
    highCusp F (Matrix.ProjGenLinGroup.mk A⁻¹) T =
      KPCusp.horoball F J (frameLowerRow F A)
        (frameHeightConstant F J A * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T)) := by
  have hc := frameHeightConstant_pos F J hJ A
  have hdR : (0 : ℝ) < KPCuspLogShape.dimension F := by exact_mod_cast hd
  have hh (z : KPArch.Space (KPCuspLogShape.dimension F)) :
      T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (glAction F A z) ↔
      frameHeightConstant F J A * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T) <
        KPCusp.normalizedHeight F J (frameLowerRow F A) z := by
    rw [normalizedHeight_frame_lower_row F]
    change _ ↔ frameHeightConstant F J A * _ < frameHeightConstant F J A * _
    rw [mul_lt_mul_iff_right₀ hc, Real.exp_lt_exp, mul_lt_mul_iff_right₀ hdR]
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    apply (hh _).mp
    have he : glAction F A (action F (Matrix.ProjGenLinGroup.mk A⁻¹) w) = w := by
      rw [← action_mk]
      change Matrix.ProjGenLinGroup.mk A • (Matrix.ProjGenLinGroup.mk A⁻¹ • w) = w
      rw [map_inv]
      exact smul_inv_smul _ _
    rw [he]
    exact hw
  · intro hz
    refine ⟨glAction F A z, (hh z).mpr hz, ?_⟩
    rw [← action_mk]
    change Matrix.ProjGenLinGroup.mk A⁻¹ • (Matrix.ProjGenLinGroup.mk A • z) = z
    rw [map_inv]
    exact inv_smul_smul _ _

theorem normalized_horoballs_disjoint_of_threshold_product
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (r s : KPCusp.Row F) (hflags : KPCusp.flag F r ≠ KPCusp.flag F s)
    (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (hUV : (FractionalIdeal.absNorm J : ℝ) ≤ U * V) :
    Disjoint (KPCusp.horoball F J r U) (KPCusp.horoball F J s V) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  change U < KPCusp.normalizedHeight F J r z at hz
  change V < KPCusp.normalizedHeight F J s z at hz'
  have h := KPCusp.normalizedHeight_product_le_norm_twist F hF J hJ r s hflags z
  have hp : U * V < KPCusp.normalizedHeight F J r z * KPCusp.normalizedHeight F J s z :=
    mul_lt_mul hz hz'.le hV (KPCusp.normalizedHeight_pos F J hJ r z).le
  exact (not_lt_of_ge (h.trans hUV)) hp

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix

namespace DedekindZetaZeroFree.KPCuspSiegel

variable (F : Type*) [Field F] [NumberField F]

def rowCusp (r : KPCusp.Row F) : KPCuspArithmetic.Cusp F :=
  Projectivization.mk F ![-r.val.2, r.val.1] (by
    intro h
    have h0 : r.val.2 = 0 := by simpa using congrFun h 0
    have h1 : r.val.1 = 0 := by simpa using congrFun h 1
    exact r.property (Prod.ext h1 h0))

theorem rowCusp_eq_of_flag_eq (r s : KPCusp.Row F)
    (h : KPCusp.flag F r = KPCusp.flag F s) : rowCusp F r = rowCusp F s := by
  have hv : (-r.val.2, r.val.1) ∈ KPCusp.flag F r := by
    change r.val.1 * (-r.val.2) + r.val.2 * r.val.1 = 0
    ring
  rw [h] at hv
  change s.val.1 * (-r.val.2) + s.val.2 * r.val.1 = 0 at hv
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  by_cases hc : r.val.1 = 0
  · have hd : r.val.2 ≠ 0 := by
      intro hd
      exact r.property (Prod.ext hc hd)
    have hs : s.val.1 = 0 := by simpa [hc, hd] using hv
    have hd' : s.val.2 ≠ 0 := by
      intro hd'
      exact s.property (Prod.ext hs hd')
    refine ⟨Units.mk0 (r.val.2 / s.val.2) (div_ne_zero hd hd'), ?_⟩
    ext i
    fin_cases i <;> simp [hc, hs, div_mul_cancel₀ _ hd', mul_neg]
  · have hc' : s.val.1 ≠ 0 := by
      intro hs
      have hd' : s.val.2 = 0 := by simpa [hs, hc] using hv
      exact s.property (Prod.ext hs hd')
    refine ⟨Units.mk0 (r.val.1 / s.val.1) (div_ne_zero hc hc'), ?_⟩
    ext i
    fin_cases i
    · change (r.val.1 / s.val.1) * (-s.val.2) = -(r.val.2)
      field_simp
      linear_combination -hv
    · simp [div_mul_cancel₀ _ hc']

theorem flag_eq_of_rowCusp_eq (r s : KPCusp.Row F)
    (h : rowCusp F r = rowCusp F s) : KPCusp.flag F r = KPCusp.flag F s := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have hc : r.val.1 = (a : F) * s.val.1 := by
    change r.val.1 = a • s.val.1
    exact (congrFun ha 1).symm
  have hd : r.val.2 = (a : F) * s.val.2 := by
    change r.val.2 = a • s.val.2
    have := congrFun ha 0
    simpa using congrArg Neg.neg this.symm
  ext v
  change r.val.1 * v.1 + r.val.2 * v.2 = 0 ↔ s.val.1 * v.1 + s.val.2 * v.2 = 0
  rw [hc, hd, mul_assoc, mul_assoc, ← mul_add]
  exact mul_eq_zero.trans (or_iff_right a.ne_zero)

theorem rowCusp_eq_iff_flag_eq (r s : KPCusp.Row F) :
    rowCusp F r = rowCusp F s ↔ KPCusp.flag F r = KPCusp.flag F s :=
  ⟨flag_eq_of_rowCusp_eq F r s, rowCusp_eq_of_flag_eq F r s⟩

theorem rowCusp_frameLowerRow (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    rowCusp F (frameLowerRow F A) =
      Matrix.ProjGenLinGroup.mk A⁻¹ • KPCuspArithmetic.infinity F := by
  have he : Matrix.ProjGenLinGroup.mk A • rowCusp F (frameLowerRow F A) =
      KPCuspArithmetic.infinity F := by
    rw [rowCusp, Projectivization.PGL.mk_smul_mk, KPCuspArithmetic.infinity]
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    refine ⟨Units.mk0 (-(A : Matrix (Fin 2) (Fin 2) F).det) (neg_ne_zero.mpr A.det_ne_zero), ?_⟩
    ext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, frameLowerRow, Matrix.det_fin_two] <;>
      ring
  rw [map_inv]
  rw [← he, inv_smul_smul]

theorem exists_frameLowerRow (r : KPCusp.Row F) :
    ∃ A : Matrix.GeneralLinearGroup (Fin 2) F, frameLowerRow F A = r := by
  by_cases hc : r.val.1 = 0
  · have hd : r.val.2 ≠ 0 := by
      intro hd
      exact r.property (Prod.ext hc hd)
    let A := Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; r.val.1, r.val.2]
      (by simpa [Matrix.det_fin_two] using hd)
    exact ⟨A, Subtype.ext (by rfl)⟩
  · let A := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; r.val.1, r.val.2]
      (by simpa [Matrix.det_fin_two] using hc)
    exact ⟨A, Subtype.ext (by rfl)⟩

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspSiegel
variable (F : Type*) [Field F] [NumberField F]

theorem exists_height_cover_of_frame_upper_bound {n : ℕ}
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : Fin n → KPCuspArithmetic.Cusp F)
    (A : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ a, Matrix.ProjGenLinGroup.mk (A a)⁻¹ • KPCuspArithmetic.infinity F = q a)
    (hcusps : ∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ (a : Fin n) (G : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk G ∈ Γ → frameHeightConstant F 1 (A a * G⁻¹) ≤ C) :
    ∃ t₀ : ℝ, ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
      ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
        t₀ ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) w ∧
        z = action F (γ : KPCuspArithmetic.PGL2 F)
          (action F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) w) := by
  obtain ⟨c, hc, hshort⟩ := kp_cusp_minkowski_normalized_height F hF 1 (by simp)
  have hd : (0 : ℝ) < KPCuspLogShape.dimension F := by
    exact_mod_cast KPCuspLogShape.dimension_pos F hF
  refine ⟨Real.log (c / C) / (KPCuspLogShape.dimension F : ℝ), ?_⟩
  intro z
  obtain ⟨r, hr⟩ := hshort z
  obtain ⟨a, γ, hγ⟩ := hcusps (rowCusp F r)
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective (γ : KPCuspArithmetic.PGL2 F)
  change (γ : KPCuspArithmetic.PGL2 F) • q a = rowCusp F r at hγ
  have he : rowCusp F (frameLowerRow F (A a * G⁻¹)) = rowCusp F r := by
    rw [rowCusp_frameLowerRow]
    simpa only [mul_inv_rev, inv_inv, map_mul, mul_smul, hG, hA] using hγ
  have hh := KPCusp.normalizedHeight_eq_of_flag_eq F hF 1 _ _
    (flag_eq_of_rowCusp_eq F _ _ he) z
  have hl : c ≤ frameHeightConstant F 1 (A a * G⁻¹) *
      Real.exp ((KPCuspLogShape.dimension F : ℝ) *
        KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (glAction F (A a * G⁻¹) z)) := by
    rw [← hh, normalizedHeight_frame_lower_row F] at hr
    exact hr
  have hl' : c ≤ C * Real.exp ((KPCuspLogShape.dimension F : ℝ) *
      KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) (glAction F (A a * G⁻¹) z)) :=
    hl.trans (mul_le_mul_of_nonneg_right (hbound a G (by rw [hG]; exact γ.property)) (Real.exp_pos _).le)
  refine ⟨γ, a, glAction F (A a * G⁻¹) z, ?_, ?_⟩
  · apply (div_le_iff₀ hd).mpr
    rw [mul_comm]
    have hle := (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using hl')
    have hh' := Real.log_le_log (div_pos hc hC) hle
    rwa [Real.log_exp] at hh'
  · rw [← action_mk]
    change z = (γ : KPCuspArithmetic.PGL2 F) •
      (Matrix.ProjGenLinGroup.mk (A a)⁻¹ • (Matrix.ProjGenLinGroup.mk (A a * G⁻¹) • z))
    simp [map_mul, map_inv, hG, mul_smul]

theorem box_cover_of_height_cover {n : ℕ}
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : Fin n → KPCuspArithmetic.Cusp F)
    (σ : Fin n → KPCuspArithmetic.PGL2 F)
    (P : Fin n → Set (Fin (KPCuspLogShape.dimension F) → ℂ))
    (B : Fin n → Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F)))
    (hrep : ∀ (a : Fin n) (z : KPArch.Space (KPCuspLogShape.dimension F)),
      ∃ g : KPCuspArithmetic.conjugatedStabilizer F Γ (q a) (σ a),
        ∃ x ∈ P a, ∃ b ∈ B a,
          action F (g : KPCuspArithmetic.PGL2 F) z =
            fun i => (x i, KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) z +
              (b : Fin (KPCuspLogShape.dimension F) → ℝ) i))
    (t₀ : ℝ)
    (hcover : ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
      ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
        t₀ ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) w ∧
        z = action F (γ : KPCuspArithmetic.PGL2 F) (action F (σ a) w)) :
    ∀ z : KPArch.Space (KPCuspLogShape.dimension F),
      ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
        w ∈ box F (P a) (B a) (Set.Ici t₀) ∧
        z = action F (γ : KPCuspArithmetic.PGL2 F) (action F (σ a) w) := by
  intro z
  obtain ⟨γ, a, w, hw, hz⟩ := hcover z
  obtain ⟨g, x, hx, b, hb, he⟩ := hrep a w
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp g.property
  have hg : (σ a)⁻¹ * k * σ a = (g : KPCuspArithmetic.PGL2 F) := by
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, inv_inv] using hkg
  let δ : Γ := γ * (⟨k, hk.1⟩ : Γ)⁻¹
  refine ⟨δ, a, action F (g : KPCuspArithmetic.PGL2 F) w, ?_, ?_⟩
  · exact ⟨x, hx, b, hb, KPCuspLogShape.meanHeight _ w, hw, he⟩
  · rw [hz]
    change (γ : KPCuspArithmetic.PGL2 F) • (σ a • w) =
      ((γ : KPCuspArithmetic.PGL2 F) * k⁻¹) • (σ a • ((g : KPCuspArithmetic.PGL2 F) • w))
    rw [← hg]
    simp only [mul_smul, smul_inv_smul, inv_smul_smul]

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspSiegel
variable (F : Type*) [Field F] [NumberField F]

theorem action_image_highCusp (g σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    action F g '' highCusp F σ T = highCusp F (g * σ) T := by
  rw [highCusp, highCusp, Set.image_image]
  congr 1
  funext z
  exact (mul_smul g σ z).symm

theorem uniform_high_cusp_intersection_of_frame_bound {n : ℕ}
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : Fin n → KPCuspArithmetic.Cusp F)
    (A : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ a, Matrix.ProjGenLinGroup.mk (A a)⁻¹ • KPCuspArithmetic.infinity F = q a)
    (hirr : ∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ (a : Fin n) (G : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk G ∈ Γ → c ≤ frameHeightConstant F 1 (A a * G⁻¹))
    (t₀ : ℝ) :
    ∃ T₁ : ℝ, t₀ < T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
      ∀ (a b : Fin n) (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F)),
        z ∈ highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T →
        action F (γ : KPCuspArithmetic.PGL2 F) z ∈
          highCusp F (Matrix.ProjGenLinGroup.mk (A b)⁻¹) T →
        a = b ∧ (γ : KPCuspArithmetic.PGL2 F) ∈ parabolic F Γ (q a) := by
  have hd : (0 : ℝ) < KPCuspLogShape.dimension F := by
    exact_mod_cast KPCuspLogShape.dimension_pos F hF
  let R : ℝ := Real.log (1 / c) / (KPCuspLogShape.dimension F : ℝ)
  refine ⟨max (t₀ + 1) R, lt_of_lt_of_le (by linarith) (le_max_left _ _), ?_⟩
  intro T hT a b γ z hz hγz
  have hRT : R ≤ T := (le_max_right _ _).trans hT
  have hexp : 1 ≤ c * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T) := by
    have hl : Real.log (1 / c) ≤ (KPCuspLogShape.dimension F : ℝ) * T := by
      exact (div_le_iff₀ hd).mp hRT |>.trans_eq (mul_comm _ _)
    have he := Real.exp_le_exp.mpr hl
    rw [Real.exp_log (div_pos zero_lt_one hc)] at he
    calc
      1 = c * (1 / c) := by field_simp
      _ ≤ c * Real.exp _ := mul_le_mul_of_nonneg_left he hc.le
  obtain ⟨G, hG⟩ := Matrix.ProjGenLinGroup.mk_surjective (γ : KPCuspArithmetic.PGL2 F)
  have hGa : c ≤ frameHeightConstant F 1 (A a * G⁻¹) :=
    hbound a G (by rw [hG]; exact γ.property)
  have hGb : c ≤ frameHeightConstant F 1 (A b) := by
    simpa using hbound b 1 (by simp)
  have hcusp : highCusp F (Matrix.ProjGenLinGroup.mk (A a * G⁻¹)⁻¹) T =
      action F (γ : KPCuspArithmetic.PGL2 F) ''
        highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T := by
    rw [action_image_highCusp]
    congr 1
    simp [map_mul, map_inv, hG]
  have hflag : KPCusp.flag F (frameLowerRow F (A a * G⁻¹)) =
      KPCusp.flag F (frameLowerRow F (A b)) := by
    by_contra hn
    have hdis := normalized_horoballs_disjoint_of_threshold_product F hF 1 (by simp)
      _ _ hn
      (frameHeightConstant F 1 (A a * G⁻¹) * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T))
      (frameHeightConstant F 1 (A b) * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T))
      (mul_pos (frameHeightConstant_pos F 1 (by simp) _) (Real.exp_pos _))
      (mul_pos (frameHeightConstant_pos F 1 (by simp) _) (Real.exp_pos _))
    have hU : 1 ≤ frameHeightConstant F 1 (A a * G⁻¹) * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T) :=
      hexp.trans (mul_le_mul_of_nonneg_right hGa (Real.exp_pos _).le)
    have hV : 1 ≤ frameHeightConstant F 1 (A b) * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T) :=
      hexp.trans (mul_le_mul_of_nonneg_right hGb (Real.exp_pos _).le)
    have hp : (FractionalIdeal.absNorm (1 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) : ℝ) ≤
        (frameHeightConstant F 1 (A a * G⁻¹) * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T)) *
        (frameHeightConstant F 1 (A b) * Real.exp ((KPCuspLogShape.dimension F : ℝ) * T)) := by
      simpa using mul_le_mul hU hV (by norm_num) (le_trans (by norm_num) hU)
    have hz' : action F (γ : KPCuspArithmetic.PGL2 F) z ∈
        highCusp F (Matrix.ProjGenLinGroup.mk (A a * G⁻¹)⁻¹) T := by
      rw [hcusp]
      exact ⟨z, hz, rfl⟩
    rw [highCusp_eq_normalized_horoball F 1 (by simp) _ T
      (KPCuspLogShape.dimension_pos F hF)] at hz' hγz
    exact Set.disjoint_left.mp (hdis hp) hz' hγz
  have hq : γ • q a = q b := by
    change (γ : KPCuspArithmetic.PGL2 F) • q a = q b
    have he := rowCusp_eq_of_flag_eq F _ _ hflag
    rw [rowCusp_frameLowerRow, rowCusp_frameLowerRow] at he
    simpa only [mul_inv_rev, inv_inv, map_mul, mul_smul, hG, hA] using he
  have hab : a = b := by
    by_contra hn
    exact hirr a b hn γ hq
  refine ⟨hab, γ.property, ?_⟩
  change (γ : KPCuspArithmetic.PGL2 F) • q a = q a
  change (γ : KPCuspArithmetic.PGL2 F) • q a = q b at hq
  simpa only [hab] using hq

theorem pairwise_disjoint_projected_highCusps_of_intersection {n : ℕ}
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : Fin n → KPCuspArithmetic.PGL2 F) (T : ℝ)
    (hident : ∀ (a b : Fin n) (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F)),
      z ∈ highCusp F (σ a) T → action F (γ : KPCuspArithmetic.PGL2 F) z ∈ highCusp F (σ b) T → a = b) :
    Pairwise fun a b : Fin n =>
      Disjoint (projection F Γ '' highCusp F (σ a) T)
        (projection F Γ '' highCusp F (σ b) T) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx, hxp⟩ ⟨y, hy, hyp⟩
  have he : projection F Γ y = projection F Γ x := hyp.trans hxp.symm
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact he))
  exact hab (hident a b γ x hx (by simpa only [show action F (γ : KPCuspArithmetic.PGL2 F) x = y from hγ] using hy))

end DedekindZetaZeroFree.KPCuspSiegel

end

end

section

noncomputable section
open scoped Classical Matrix nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspSiegel
variable (F : Type*) [Field F] [NumberField F]

theorem siegel_cover_of_uniform_frame_bounds {n : ℕ}
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : Fin n → KPCuspArithmetic.Cusp F)
    (A : Fin n → Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ a, Matrix.ProjGenLinGroup.mk (A a)⁻¹ • KPCuspArithmetic.infinity F = q a)
    (hcusps : ∀ r : KPCuspArithmetic.Cusp F, ∃ (a : Fin n) (γ : Γ), γ • q a = r)
    (hirr : ∀ (a b : Fin n), a ≠ b → ∀ γ : Γ, γ • q a ≠ q b)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlower : ∀ (a : Fin n) (G : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk G ∈ Γ → c ≤ frameHeightConstant F 1 (A a * G⁻¹))
    (hupper : ∀ (a : Fin n) (G : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk G ∈ Γ → frameHeightConstant F 1 (A a * G⁻¹) ≤ C) :
    ∃ (t₀ : ℝ)
      (P : Fin n → Set (Fin (KPCuspLogShape.dimension F) → ℂ))
      (B : Fin n → Set (KPCuspLogShape.hyperplane (KPCuspLogShape.dimension F))),
      (∀ a, IsCompact (P a) ∧ (P a).Nonempty ∧ IsCompact (B a) ∧ (B a).Nonempty) ∧
      (∀ z : KPArch.Space (KPCuspLogShape.dimension F),
        ∃ (γ : Γ) (a : Fin n) (w : KPArch.Space (KPCuspLogShape.dimension F)),
          w ∈ box F (P a) (B a) (Set.Ici t₀) ∧
          z = action F (γ : KPCuspArithmetic.PGL2 F)
            (action F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) w)) ∧
      (∀ (a : Fin n) (T : ℝ),
        projection F Γ '' highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T =
          projection F Γ '' (action F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) ''
            box F (P a) (B a) (Set.Ioi T))) ∧
      (∀ T : ℝ, t₀ < T →
        IsCompact (projection F Γ '' (⋃ a : Fin n,
          action F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) ''
            box F (P a) (B a) (Set.Icc t₀ T))) ∧
        IsCompact ((Set.univ : Set (OrbitQuotient F Γ)) \
          (⋃ a : Fin n, projection F Γ '' highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T))) ∧
      ∃ T₁ : ℝ, t₀ < T₁ ∧ ∀ T : ℝ, T₁ ≤ T →
        (Pairwise fun a b : Fin n =>
          Disjoint (projection F Γ '' highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T)
            (projection F Γ '' highCusp F (Matrix.ProjGenLinGroup.mk (A b)⁻¹) T)) ∧
        (∀ (a b : Fin n) (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F)),
          z ∈ highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T →
          action F (γ : KPCuspArithmetic.PGL2 F) z ∈
            highCusp F (Matrix.ProjGenLinGroup.mk (A b)⁻¹) T →
          a = b ∧ (γ : KPCuspArithmetic.PGL2 F) ∈ parabolic F Γ (q a)) ∧
        (∀ (a : Fin n) (g : parabolic F Γ (q a)),
          Set.MapsTo (action F (g : KPCuspArithmetic.PGL2 F))
            (highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T)
            (highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T)) ∧
        (∀ a : Fin n, ∃ e : CuspQuotient F Γ (q a)
            (highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T) → OrbitQuotient F Γ,
          Topology.IsEmbedding e ∧
          (∀ z : highCusp F (Matrix.ProjGenLinGroup.mk (A a)⁻¹) T,
            e (Quotient.mk _ z) = projection F Γ z)) := by
  choose P B hP hPne hB hBne hrep hhigh using fun a =>
    exists_arithmetic_high_box_representatives F hF M hM Γ hΓ hcomm (q a)
      (Matrix.ProjGenLinGroup.mk (A a)⁻¹) (hA a)
  obtain ⟨t₀, hheight⟩ := exists_height_cover_of_frame_upper_bound F hF Γ q A hA hcusps C hC hupper
  have hcover := box_cover_of_height_cover F Γ q (fun a => Matrix.ProjGenLinGroup.mk (A a)⁻¹)
    P B hrep t₀ hheight
  refine ⟨t₀, P, B, fun a => ⟨hP a, hPne a, hB a, hBne a⟩, hcover, hhigh, ?_, ?_⟩
  · intro T _
    exact ⟨isCompact_projected_truncated_boxes F Γ _ P B hP hB t₀ T,
      isCompact_complement_of_cover F (KPCuspLogShape.dimension_pos F hF) Γ _ P B hP hB t₀ T hcover⟩
  · obtain ⟨T₁, ht, hident⟩ := uniform_high_cusp_intersection_of_frame_bound F hF Γ q A hA hirr c hc hlower t₀
    refine ⟨T₁, ht, ?_⟩
    intro T hT
    have hi := hident T hT
    refine ⟨pairwise_disjoint_projected_highCusps_of_intersection F Γ _ T
      (fun a b γ z hz hγz => (hi a b γ z hz hγz).1), hi, ?_, ?_⟩
    · intro a g
      exact parabolic_mapsTo_highCusp F hF M hM Γ hΓ hcomm (q a) _ (hA a) T g
    · intro a
      exact exists_embedding_highCusp F Γ (q a) _ T
        (fun γ z hz hγz => (hi a a γ z hz hγz).2)

end DedekindZetaZeroFree.KPCuspSiegel

end

end
