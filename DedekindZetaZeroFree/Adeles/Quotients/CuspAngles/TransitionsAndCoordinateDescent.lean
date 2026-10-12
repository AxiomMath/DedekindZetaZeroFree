module

public import DedekindZetaZeroFree.Adeles.Quotients.CuspAngles.FullCuspDomains
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction
public import DedekindZetaZeroFree.MeasureTheory.Quotients.FiberInvariantSections

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped Classical NumberField Topology NNReal Matrix MatrixGroups LinearAlgebra.Projectivization
namespace DedekindZetaZeroFree.KPMsActualAngularTransitionSource
open KPMsActualAngularSource KPMsActualCuspSource
open KPMsResidualTailRestoration.SharpConstantTerm KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (S : SourceRecipe F ζ hζ R P H) (U : KPMsActualAngularSource.Level F ζ hζ)

theorem finiteProjection_centre (ε : rootsOfUnity 3 F) :
    KPCuspGenuineMonodromy.finiteProjection F ζ hζ
      (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε) = 1 := by
  change Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map (RingHom.snd _ _)
    (projection F ζ hζ (centralInjection F ζ hζ ε))) = 1
  have hm : centralInjection F ζ hζ ε ∈ (projection F ζ hζ).ker := by
    rw [← range_centralInjection_eq_ker]
    exact ⟨ε, rfl⟩
  rw [MonoidHom.mem_ker.mp hm, map_one, map_one]

section Rational
variable (F ζ hζ)

theorem rationalLift_mul (g h : KPCuspArithmetic.PGL2 F) :
    rationalLift F ζ hζ (g * h) = rationalLift F ζ hζ g * rationalLift F ζ hζ h := by
  obtain ⟨a, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  obtain ⟨b, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective h
  rw [← map_mul, rationalLift_mk, rationalLift_mk, rationalLift_mk, map_mul, map_mul]

@[simp] theorem rationalLift_one : rationalLift F ζ hζ 1 = 1 := by
  rw [← map_one Matrix.ProjGenLinGroup.mk, rationalLift_mk, map_one, map_one]

@[simp] theorem rationalLift_inv (g : KPCuspArithmetic.PGL2 F) :
    rationalLift F ζ hζ g⁻¹ = (rationalLift F ζ hζ g)⁻¹ := by
  apply mul_eq_one_iff_eq_inv.mp
  rw [← rationalLift_mul, inv_mul_cancel, rationalLift_one]

theorem cusp_fixing_upper (q : KPCuspArithmetic.Cusp F) (σ γ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) (hγ : γ • q = q) :
    KPCuspArithmetic.IsUpperTriangular F (σ⁻¹ * γ * σ) := by
  have hinf : (σ⁻¹ * γ * σ) • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F := by
    rw [mul_smul, mul_smul, hσ, hγ, ← hσ, inv_smul_smul]
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (σ⁻¹ * γ * σ)
  refine ⟨A, hA, ?_⟩
  rw [← hA] at hinf
  unfold KPCuspArithmetic.infinity at hinf
  rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hinf
  obtain ⟨a, ha⟩ := hinf
  have h := congrFun ha 1
  have hzero : (a • ![1, 0]) 1 = (0 : F) := by simp
  rw [hzero] at h
  change 0 = ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) 1 at h
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm

theorem rationalSubgroup_exists_lift (g : KPMsActualAngularSource.G F ζ hζ)
    (hg : g ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ) :
    ∃ γ : KPCuspArithmetic.PGL2 F, rationalLift F ζ hζ γ = g := by
  obtain ⟨q, hq⟩ := hg
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨Matrix.ProjGenLinGroup.mk A, ?_⟩
  rw [rationalLift_mk]
  rw [← hq]
  exact (KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ A).symm
end Rational

end DedekindZetaZeroFree.KPMsActualAngularTransitionSource

end

end

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open scoped Classical NumberField Topology NNReal ENNReal
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsActualAngularDescentSource
open KPMsActualAngularSource KPMsActualAngularDomainSource KPMsActualAngularTransitionSource
open KPMsResidualTailRestoration.OutgoingTailL2.CoordinateDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

section Radial
variable (F ζ hζ)
theorem radialSection_eq_diagonalLift (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius) :
    KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r =
      KPGlobalCenterRationalCharacter.diagonalLift F ζ hζ (B.ell r) := by
  unfold KPMsFixedHaarDisintegration.radialSection KPGlobalTorusFunctionData.archDiagonalLift
    KPGlobalCenterRationalCharacter.diagonalLift
  congr 2
  apply Subtype.ext
  funext v
  cases v with
  | inl w =>
    simp only [KPGlobalTorusFunctionData.archDiagonalTuple,
      KPGlobalCenterRationalCharacter.diagonalTuple]
    have hz : KPMsFixedHaarDisintegration.positiveSlots F B.slot r w ≠ 0 := by
      unfold KPMsFixedHaarDisintegration.positiveSlots
      split_ifs
      · exact_mod_cast (Real.sqrt_pos.2 r.property).ne'
      · exact one_ne_zero
    simp only [dif_neg hz]
    congr 1
    apply Units.ext
    change _ = KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inl w) (B.ell r : KPAdeles F)
    rw [B.ell_slots]
    rfl
  | inr q =>
    simp only [KPGlobalTorusFunctionData.archDiagonalTuple,
      KPGlobalCenterRationalCharacter.diagonalTuple]
    have he : KPGlobalCubicIdelePairing.ideleEval F (Sum.inr q) (B.ell r) = 1 := by
      apply Units.ext
      exact B.ell_finite r q
    rw [he]
    simp

theorem radialSection_mem_center (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (r : KPMsFixedHaarDisintegration.Radius) :
    ∃ t : KPGlobalTorusFunctionData.Z F ζ hζ,
      t.val.val = KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r := by
  let y : CubicCharacters.cubes (KPGlobalTorusFunctionData.Ideles F) :=
    ⟨B.ell r, B.ell_cube r⟩
  refine ⟨KPGlobalCenterRationalCharacter.cubeLift F ζ hζ y, ?_⟩
  rw [KPGlobalCenterRationalCharacter.cubeLift_formula, radialSection_eq_diagonalLift F ζ hζ]

def framedNormOne (D : Iwasawa F ζ hζ) (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ g : G F ζ hζ) : NormOne F ζ hζ D :=
  ⟨framedNormalization F ζ hζ D B σ g,
    (framedNormalization_normOne_continuous F ζ hζ D B σ).1 g⟩
def framedFullAngular (D : Iwasawa F ζ hζ) (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ g : G F ζ hζ) : FullOmega F ζ hζ D := Quotient.mk _ (framedNormOne F ζ hζ D B σ g)

theorem framedFullAngular_continuous (D : Iwasawa F ζ hζ)
    (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ) (σ : G F ζ hζ) :
    Continuous (framedFullAngular F ζ hζ D B σ) :=
  continuous_quotient_mk'.comp
    ((framedNormalization_normOne_continuous F ζ hζ D B σ).2.subtype_mk _)

theorem framedFullAngular_upper_transition (D : Iwasawa F ζ hζ) (B : KPMsFixedHaarDisintegration.RadialData F ζ hζ)
    (σ : G F ζ hζ) (g h : KPMsActualAngularSource.G F ζ hζ)
    (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F)
    (hh : σ⁻¹ * h = (KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x * (σ⁻¹ * g)) :
    framedFullAngular F ζ hζ D B σ h = framedFullAngular F ζ hζ D B σ g := by
  have hr : framedRadius F ζ hζ D σ h = framedRadius F ζ hζ D σ g := by
    apply Subtype.ext
    exact congrArg (fun r : (ℝ≥0)ˣ => ((r : ℝ≥0) : ℝ))
        (by
          rw [hh]
          have hm := KPGlobalTorusBorelTwistCompatibility.iwasawaNorm_borel_mul
            F ζ hζ D (KPGlobalTorusFunctionData.s F ζ hζ y) x (σ⁻¹ * g)
          simpa only [KPGlobalTorusBorelNormTwistTransport.delta_rational, one_mul] using hm)
  let r := framedRadius F ζ hζ D σ g
  let t := KPGlobalTorusFunctionData.torusArchChart F ζ hζ
    (KPMsFixedHaarDisintegration.positiveSlots F B.slot r)
  have ht : t.val = KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot r := rfl
  obtain ⟨z,hz⟩ := radialSection_mem_center F ζ hζ B r
  have hzt : z.val = t := Subtype.ext (hz.trans ht.symm)
  have hc : Commute t (KPGlobalTorusFunctionData.s F ζ hζ y) := by
    rw [← hzt]
    exact (Subgroup.mem_center_iff.mp z.property _).symm
  have hcc : t.val⁻¹ * (KPGlobalTorusFunctionData.s F ζ hζ y).val =
      (KPGlobalTorusFunctionData.s F ζ hζ y).val * t.val⁻¹ := by
    exact congrArg (fun u : KPGlobalTorusFunctionData.E F ζ hζ => u.val) hc.inv_left.eq
  have hn := ActualBorelRetraction.torus_conjugates_root F ζ hζ t⁻¹ x
  apply Eq.symm
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨y, (KPGlobalTorusFunctionData.p F ζ hζ t⁻¹ : KPGlobalTorusFunctionData.Adeles F) * x, ?_⟩
  change (KPMsFixedHaarDisintegration.radialSection F ζ hζ B.slot
    (framedRadius F ζ hζ D σ h))⁻¹ * (σ⁻¹ * h) = _
  rw [hr, hh]
  change t.val⁻¹ * ((KPGlobalTorusFunctionData.s F ζ hζ y).val *
    KPGlobalTorusFunctionData.N F ζ hζ x * (σ⁻¹ * g)) =
    ((KPGlobalTorusFunctionData.s F ζ hζ y).val * _) * (t.val⁻¹ * (σ⁻¹ * g))
  rw [← hn]
  simp only [Subgroup.coe_inv, inv_inv]
  simp only [← mul_assoc]
  rw [hcc]
  group
theorem rational_upper_literal_factorization (g : KPCuspArithmetic.PGL2 F)
    (hg : KPCuspArithmetic.IsUpperTriangular F g) :
    ∃ (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F),
      KPMsActualCuspSource.rationalLift F ζ hζ g =
        (KPGlobalTorusFunctionData.s F ζ hζ y).val * KPGlobalTorusFunctionData.N F ζ hζ x := by
  obtain ⟨M, rfl, hM⟩ := hg
  have hdet := Matrix.GeneralLinearGroup.det_ne_zero M
  rw [Matrix.det_fin_two, hM, mul_zero, sub_zero] at hdet
  obtain ⟨ha, hd⟩ := mul_ne_zero_iff.mp hdet
  let a : Fˣ := Units.mk0 ((M : Matrix (Fin 2) (Fin 2) F) 0 0) ha
  let d : Fˣ := Units.mk0 ((M : Matrix (Fin 2) (Fin 2) F) 1 1) hd
  let y : Fˣ := a / d
  let b : F := (M : Matrix (Fin 2) (Fin 2) F) 0 1 / (a : F)
  have heq : M = Matrix.GeneralLinearGroup.scalar (Fin 2) d *
      KubotaRankTwo.d F y 1 * KubotaRankTwo.n F b := by
    apply Units.ext
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [KubotaRankTwo.d, KubotaRankTwo.n, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, a, d, y, b, hM]
    all_goals field_simp [ha, hd] <;> ring
  have hs : KPMsActualCuspSource.rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk M) =
      KPMsActualCuspSource.rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d F y 1)) *
        KPMsActualCuspSource.rationalLift F ζ hζ (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n F b)) := by
    rw [heq, map_mul, map_mul, rationalLift_mul, rationalLift_mul]
    have hz : KPMsActualCuspSource.rationalLift F ζ hζ
        (Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) = 1 := by
      rw [KPMsActualCuspSource.rationalLift_mk]
      exact KPRationalAdelicSplitting.rationalScalars_le_ker F ζ hζ ⟨d, rfl⟩
    rw [hz, one_mul]
  refine ⟨y, algebraMap F (KPGlobalTorusFunctionData.Adeles F) b, ?_⟩
  rw [hs, KPMsActualCuspSource.rationalLift_mk, KPMsActualCuspSource.rationalLift_mk]
  congr 1
  exact congrArg (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ)
    (KPRationalAdelicSplitting.N_rational F ζ hζ b).symm

end Radial

section CuspDescent
local instance : MulAction (KPCuspArithmetic.PGL2 F) (KPArch.Space (KPCuspLogShape.dimension F)) :=
  KPCuspSiegel.instMulActionPGL2SpaceDimension F
variable (S : SourceRecipe F ζ hζ R P H) (U : Level F ζ hζ)

theorem full_quotient_eq_iff_rational_left (g h : G F ζ hζ) :
    KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g =
      KPSmoothLocalQuotientCharts.quotientMap F ζ hζ h ↔
    ∃ γ : KPCuspArithmetic.PGL2 F, h = KPMsActualCuspSource.rationalLift F ζ hζ γ * g := by
  constructor
  · intro he
    have hm : h * g⁻¹ ∈ KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ :=
      QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    obtain ⟨γ, hγ⟩ := rationalSubgroup_exists_lift F ζ hζ _ hm
    refine ⟨γ, ?_⟩
    rw [hγ]
    group
  · rintro ⟨γ, rfl⟩
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    have hm : KPMsActualCuspSource.rationalLift F ζ hζ γ ∈
        KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ := by
      obtain ⟨m,rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
      exact ⟨KPRationalAdelicSplitting.rationalPGLQuotient F m,
        (KPRationalAdelicSplitting.rationalPGLHom_mk F ζ hζ m).trans
          (KPMsActualCuspSource.rationalLift_mk F ζ hζ m).symm⟩
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hm

end CuspDescent
end DedekindZetaZeroFree.KPMsActualAngularDescentSource

end

end
