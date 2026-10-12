module

public import DedekindZetaZeroFree.Adeles.Quotients.PGL2CuspParabolicStabilizers
public import DedekindZetaZeroFree.Adeles.Lattices.PGL.SteinitzClassObstruction

@[expose] public section

noncomputable section
open scoped Matrix Pointwise
namespace DedekindZetaZeroFree.FiniteAdelicParabolicExtension

 def ratioIdealModule (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Submodule (NumberField.RingOfIntegers F) (Fin 2 → F) :=
  ((1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) : Submodule _ F).comap (LinearMap.proj 0) ⊓
  (I : Submodule _ F).comap (LinearMap.proj 1)
private theorem ratioIdealModule_mem (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) (v : Fin 2 → F) :
    v ∈ ratioIdealModule F I ↔ (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I := by
  simp [ratioIdealModule, FractionalIdeal.mem_one_iff]
 def pairVec (F : Type*) [Field F] [NumberField F] :
    (F × F) ≃ₗ[NumberField.RingOfIntegers F] (Fin 2 → F) where
  toFun x := ![x.1,x.2]
  invFun x := (x 0,x 1)
  left_inv x := rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl
private theorem ratioIdealModule_full (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) (hI : I ≠ 0) :
    KPCuspArithmetic.IsRankTwoLattice F (ratioIdealModule F I) := by
  have hfg : (ratioIdealModule F I).FG := by
    have hmap : ratioIdealModule F I = (coordinateLattice (NumberField.RingOfIntegers F) F 1 I).map (pairVec F).toLinearMap := by
      ext v
      constructor
      · intro hv
        exact ⟨(v 0, v 1), hv, by ext i; fin_cases i <;> rfl⟩
      · rintro ⟨v, hv, rfl⟩; exact hv
    rw [hmap]
    exact ((FractionalIdeal.fg_of_isNoetherianRing le_rfl (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)).prod
      (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)).map _
  refine ⟨Module.Finite.of_fg hfg, ?_⟩
  obtain ⟨b, hb, hb0⟩ := (I : Submodule (NumberField.RingOfIntegers F) F).ne_bot_iff.mp
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  apply top_unique
  intro x _
  have h1 : ![1,0] ∈ ratioIdealModule F I := by simp [ratioIdealModule]
  have h2 : ![0,b] ∈ ratioIdealModule F I := by simp [ratioIdealModule, hb]
  have hh := (Submodule.span F (ratioIdealModule F I : Set (Fin 2 → F))).add_mem
    (Submodule.smul_mem _ (x 0) (Submodule.subset_span h1))
    (Submodule.smul_mem _ (x 1 / b) (Submodule.subset_span h2))
  convert hh using 1
  ext i
  fin_cases i <;> simp [div_mul_cancel₀, hb0]
private theorem ideal_stabilizer_iff (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    A ∈ MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F) (KPFiniteAdelicLatticeStabilizers.idealVectors F I) ↔
    ∀ v : Fin 2 → F, v ∈ ratioIdealModule F I ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ ratioIdealModule F I := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  simp only [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h v
    let V : Matrix (Fin 2) (Fin 1) F := fun i _ => v i
    have hh := h (A • V)
    simp only [inv_smul_smul] at hh
    change (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I ↔ _ at hh
    rw [ratioIdealModule_mem, ratioIdealModule_mem]
    change ((∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I ↔
      (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = ((A : Matrix (Fin 2) (Fin 2) F) * V) 0 0) ∧
        ((A : Matrix (Fin 2) (Fin 2) F) * V) 1 0 ∈ I) at hh
    have he : ∀ i : Fin 2, ((A : Matrix (Fin 2) (Fin 2) F) * V) i 0 =
        ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) i := by
      intro i
      change (∑ j : Fin 2, A i j * V j 0) = ∑ j : Fin 2, A i j * v j
      rfl
    rw [he 0, he 1] at hh
    exact hh
  · intro h V
    have hh := (h (fun i => (A⁻¹ • V) i 0)).symm
    rw [ratioIdealModule_mem, ratioIdealModule_mem] at hh
    have he : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => (A⁻¹ • V) i 0) = fun i => V i 0 := by
      have hx := congrArg (fun M : Matrix (Fin 2) (Fin 1) F => fun i => M i 0) (smul_inv_smul A V)
      ext i
      simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hx i
    rw [he] at hh
    exact hh.symm
private theorem ratioIdealAut_eq (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I = KPCuspArithmetic.projectiveAutomorphisms F (ratioIdealModule F I) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    apply Subgroup.subset_closure
    exact ⟨A, rfl, (ideal_stabilizer_iff F I A).mp hA⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨A, hA, hp⟩
    exact ⟨A, (ideal_stabilizer_iff F I A).mpr hp, hA⟩

theorem ideal_cusp_ratio_commensurable
    (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (hI : I ≠ 0) (a : KPFiniteAdelicLatticeStabilizers.RationalPG F)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q)
    (ρ : KPCuspArithmetic.conjugatedStabilizer F
      ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
        (MulAut.conj a).toMonoidHom) q σ →* Fˣ)
    (hρ : ∀ (g : KPCuspArithmetic.conjugatedStabilizer F
        ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
          (MulAut.conj a).toMonoidHom) q σ)
      (A : Matrix.GeneralLinearGroup (Fin 2) F),
      Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
      A 1 0 = 0 → A 0 0 = (ρ g : F) * A 1 1) :
    ρ.range.Commensurable (KPCuspArithmetic.rationalUnits F) := by
  classical
  let Δ := KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I
  let Γ := Δ.map (MulAut.conj a).toMonoidHom
  let q' := a⁻¹ • q
  let τ := a⁻¹ * σ
  have hτ : τ • KPCuspArithmetic.infinity F = q' := by
    dsimp [τ, q']
    rw [mul_smul, hσ]
  have heq : KPCuspArithmetic.conjugatedStabilizer F Γ q σ =
      KPCuspArithmetic.conjugatedStabilizer F Δ q' τ := by
    ext g
    simp only [KPCuspArithmetic.conjugatedStabilizer, Subgroup.mem_map,
      Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
    constructor
    · rintro ⟨k, ⟨hk, hkq⟩, hg⟩
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hk
      refine ⟨l, ⟨hl, ?_⟩, ?_⟩
      · change l • (a⁻¹ • q) = a⁻¹ • q
        apply (MulAction.injective a).eq_iff.mp
        simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
          MulAut.conj_apply, mul_smul, smul_inv_smul] using hkq
      · simpa [τ, MulAut.conj_apply, mul_assoc] using hg
    · rintro ⟨l, ⟨hl, hlq⟩, hg⟩
      refine ⟨a * l * a⁻¹, ⟨?_, ?_⟩, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
      · change (a * l * a⁻¹) • q = q
        rw [mul_smul, mul_smul, hlq, smul_inv_smul]
      · simpa [τ, MulAut.conj_apply, mul_assoc] using hg
  have hΔ : ∀ g ∈ Δ,
      KPCuspArithmetic.PreservesUpToHomothety F (ratioIdealModule F I) g := by
    intro g hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨A, 1, rfl, ?_⟩
    simp only [Units.val_one, one_smul, Set.image_id']
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (ideal_stabilizer_iff F I A).mp hA w |>.mp hw
    · intro hv
      refine ⟨(A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) *ᵥ v, ?_, ?_⟩
      · have hi : (A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) ∈
            MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F)
              (KPFiniteAdelicLatticeStabilizers.idealVectors F I) := inv_mem hA
        exact ((ideal_stabilizer_iff F I A⁻¹).mp hi v).mp hv
      · change (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ((A⁻¹ : Matrix.GeneralLinearGroup (Fin 2) F) *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul]
        simp only [mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  obtain ⟨hu, J, L, E, ι, r, hJ, hL, hLi, hdisc, hE, hEi,
      hι, hr, hex, hιf, hrf⟩ :=
    DedekindZetaZeroFree.kp_cusp_arithmetic_parabolic_stabilizers F
      (ratioIdealModule F I) (ratioIdealModule_full F I hI) Δ hΔ
      (by rw [← ratioIdealAut_eq]) q' τ hτ
  let e := MulEquiv.subgroupCongr heq
  have hagree : ∀ g, ρ g = (r (e g) : Fˣ) := by
    intro g
    obtain ⟨A, hA, hAu⟩ := hu (e g) (e g).property
    apply Units.ext
    have hf := hρ g A hA hAu
    have hf' := hrf (e g) A hA hAu
    have hA11 : A 1 1 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hz, hAu])
    exact mul_right_cancel₀ hA11 (hf.symm.trans hf')
  have hrange : ρ.range = E := by
    ext u
    constructor
    · rintro ⟨g, rfl⟩
      rw [hagree]
      exact (r (e g)).property
    · intro huE
      obtain ⟨g, hg⟩ := hr ⟨u, huE⟩
      refine ⟨e.symm g, ?_⟩
      rw [hagree, e.apply_symm_apply, hg]
  rw [hrange]
  have hi : E.IsFiniteRelIndex (KPCuspArithmetic.rationalUnits F) :=
    Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr hEi
  have hi' : (KPCuspArithmetic.rationalUnits F).IsFiniteRelIndex E := by
    exact Subgroup.isFiniteRelIndex_of_le_left E hE
  exact ⟨hi, hi'⟩

end DedekindZetaZeroFree.FiniteAdelicParabolicExtension

end
