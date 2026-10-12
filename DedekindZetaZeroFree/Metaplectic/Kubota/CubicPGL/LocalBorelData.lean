module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicBorel.TorusRetraction
public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.WeylAction

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

abbrev chartDepth : ℕ := KPAdelicCoverRestrictedProduct.depth F ζ hζ q

theorem chartDepth_admissible :
    KPLocalChartTopology.MatrixChartDepth F q (chartDepth F ζ hζ q) :=
  KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q

local instance : TopologicalSpace (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :=
  KPPGLLocalCover.finiteTopology F ζ hζ q (KPAdelicCoverRestrictedProduct.depth F ζ hζ q)

local instance : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :=
  (KPPGLLocalCover.finite_topological_cover F ζ hζ q _
    (KPAdelicCoverRestrictedProduct.depth_admissible F ζ hζ q)).2.2.1

abbrev actualBorel := KPLocalSmoothRepresentation.Borel F ζ hζ q

theorem actual_openCell_binding :
    letI := ActualFiniteTorus.finiteCubeClasses F ζ hζ q
    ∃ A : LocalBorelData (K := q.adicCompletion F)
        (G := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))
        (ActualFiniteTorus.actualHeisenberg F ζ hζ q),
      A.B = actualBorel F ζ hζ q ∧
      A.coordinate = ActualFiniteTorus.coordinate F ζ hζ q ∧
      A.cubeLift = ActualFiniteTorus.cubeLift F ζ hζ q ∧
      (∀ t, (A.torus t : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) = t.val) ∧
      (∀ b : A.B, ∀ hb : (b : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) ∈
          actualBorel F ζ hζ q,
        A.coordinate (A.retract b) = KPRankOneInduction.borelRatio F q
          ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b.val, hb⟩) ∧
      A.liftedW = KPRankOneOpenCellKernel.signedWeyl F ζ hζ q ∧
      (∀ x : q.adicCompletion F,
        (A.upperRoot (Multiplicative.ofAdd x) :
          KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) =
          KPPGLLocalCover.N F ζ hζ (Sum.inr q) x) ∧
      (∀ g : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q),
        A.projection (KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) g) =
          Matrix.ProjGenLinGroup.mk g.g) ∧
      (∀ P : Polarization (ActualFiniteTorus.actualHeisenberg F ζ hζ q),
        ∃ B : KPRankOneOpenCellKernel.Binding F ζ hζ q A P,
          B.eta = ActualFiniteTorus.ordinaryIota F ζ hζ ∧
          B.rootTorus = (fun v => ActualFiniteTorus.torusLift F ζ hζ q (v ^ 2)) ∧
          B.centralTorus = ActualFiniteTorus.central F ζ hζ q) := by
  letI := ActualFiniteTorus.finiteCubeClasses F ζ hζ q
  let root := (KPLocalSmoothRepresentation.upperRoot F ζ hζ q).codRestrict
    (actualBorel F ζ hζ q) (KPLocalInductionJacquetReciprocity.upperRoot_mem_borel F ζ hζ q)
  let torus := KPLocalInductionJacquetReciprocity.torusToBorel F ζ hζ q
    (chartDepth F ζ hζ q) (chartDepth_admissible F ζ hζ q)
  have coord (e : rootsOfUnity 3 F) (y : (q.adicCompletion F)ˣ)
      (t : ActualFiniteTorus.H F ζ hζ q)
      (ht : t.val = ActualFiniteTorus.normalWord F ζ hζ q e y) :
      ActualFiniteTorus.coordinate F ζ hζ q t = y :=
    ((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 e y t ht).1
  have cube_value (y : (q.adicCompletion F)ˣ) :
      ((ActualFiniteTorus.actualHeisenberg F ζ hζ q).ω
        (ActualFiniteTorus.cubeLift F ζ hζ q y) : ℂ) =
      normPower (q.adicCompletion F) (y ^ 3) (1 / 6) := by
    have hv := (ActualFiniteTorus.prescribed_center_character F ζ hζ q).2.2.2.2.1 1 y
    change (ActualFiniteTorus.rawCenterValue F ζ hζ q
      (ActualFiniteTorus.cubeLift F ζ hζ q y) : ℂ) = _
    simpa using hv
  let A : LocalBorelData (K := q.adicCompletion F)
      (G := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q))
      (ActualFiniteTorus.actualHeisenberg F ζ hζ q) := {
    B := actualBorel F ζ hζ q
    projection := KPLocalSmoothRepresentation.projection F ζ hζ q
    torus := torus
    torus_injective := by
      intro x y h
      exact Subtype.ext (congrArg (fun b : actualBorel F ζ hζ q => b.val) h)
    torus_continuous := continuous_subtype_val.subtype_mk _
    retract := KPLocalInductionJacquetReciprocity.borelRetraction F ζ hζ q
    retract_continuous := KPLocalInductionJacquetReciprocity.borelRetraction_continuous
      F ζ hζ q (chartDepth F ζ hζ q) (chartDepth_admissible F ζ hζ q)
    retract_torus := KPLocalInductionJacquetReciprocity.borelRetraction_torus
      F ζ hζ q (chartDepth F ζ hζ q) (chartDepth_admissible F ζ hζ q)
    upperRoot := root
    upperRoot_continuous := ((KPPGLLocalCover.finite_lifts_continuous F ζ hζ q
      (chartDepth F ζ hζ q) (chartDepth_admissible F ζ hζ q)).1.comp continuous_toAdd).subtype_mk _
    upperRoot_injective := by
      intro x y h
      have he := congrArg (fun b : actualBorel F ζ hζ q =>
        KPLocalSmoothRepresentation.projection F ζ hζ q b.val) h
      change Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n _ x.toAdd) =
        Matrix.ProjGenLinGroup.mk (KubotaRankTwo.n _ y.toAdd) at he
      obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
      have h11 := congrArg (fun B => B 1 1) hu
      have h01 := congrArg (fun B => B 0 1) hu
      simp [KubotaRankTwo.n, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar] at h11 h01
      apply Multiplicative.toAdd.injective
      simpa [h11] using h01
    upperRoot_projection := fun _ => rfl
    retract_upperRoot := KPLocalInductionJacquetReciprocity.borelRetraction_upperRoot F ζ hζ q
    borel_decomposition := by
      intro b
      obtain ⟨x, hx⟩ := KPLocalInductionJacquetReciprocity.borelRetraction_decomposition F ζ hζ q b
      exact ⟨x, Subtype.ext hx⟩
    coordinate := ActualFiniteTorus.coordinate F ζ hζ q
    coordinate_continuous := (ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.1
    torus_projection := Geometry.torus_projection F ζ hζ q
    cubeLift := ActualFiniteTorus.cubeLift F ζ hζ q
    cube_coordinate := fun y => coord 1 (y ^ 3) _ rfl
    exceptional_cube := cube_value
    liftedW := KPPGLLocalCover.signedW F ζ hζ (Sum.inr q)
    liftedW_projection := rfl
    weyl := Geometry.weyl F ζ hζ q
    weyl_from_lift := fun _ => rfl
    weylCenter := Geometry.weylCenter F ζ hζ q
    weylCenter_coe := fun _ => rfl
    weyl_cube := Geometry.weyl_cube F ζ hζ q }
  refine ⟨A, rfl, rfl, rfl, (fun _ => rfl), ?_, ?_, (fun _ => rfl), (fun _ => rfl), ?_⟩
  · intro b hb
    exact Geometry.retract_coordinate F ζ hζ q b
  · change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPStandardLocalRootLifts.signedW F ζ hζ (Sum.inr q)) = _
    rw [KPRankOneOpenCellKernel.signedWeyl, KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed]
  · intro P
    let B : KPRankOneOpenCellKernel.Binding F ζ hζ q A P := {
      projection_eq := fun _ => rfl
      weyl_eq := by
        change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          (KPStandardLocalRootLifts.signedW F ζ hζ (Sum.inr q)) = _
        rw [KPRankOneOpenCellKernel.signedWeyl, KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed]
      upper_eq := fun _ => rfl
      rootTorus := fun v => ActualFiniteTorus.torusLift F ζ hζ q (v ^ 2)
      torus_eq := by
        intro v
        simp [A, torus, ActualFiniteTorus.torusLift, ActualFiniteTorus.normalWord,
          KPRankOneOpenCellKernel.hLift, KPLocalInductionJacquetReciprocity.torusToBorel]
      coordinate_eq := fun v => coord 1 (v ^ 2) _ rfl
      centralTorus := ActualFiniteTorus.central F ζ hζ q
      central_eq := fun _ => rfl
      central_coordinate := by
        intro e
        apply coord e 1
        simp [ActualFiniteTorus.central, ActualFiniteTorus.normalWord, KPPGLLocalCover.A,
          KPStandardLocalRootLifts.A_one]
      eta := ActualFiniteTorus.ordinaryIota F ζ hζ
      eta_injective := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ))
          (KPLocalCover.coefficientEmbedding_injective F ζ hζ h)
      genuine := by
        intro ε e V
        have hv : ((ActualFiniteTorus.actualHeisenberg F ζ hζ q).ω
            (ActualFiniteTorus.centerInjection F ζ hζ q e) : ℂ) =
            (ActualFiniteTorus.ordinaryIota F ζ hζ e : ℂ) := by
          have hh := (ActualFiniteTorus.prescribed_center_character F ζ hζ q).2.2.2.2.1 e 1
          change (ActualFiniteTorus.rawCenterValue F ζ hζ q
            (ActualFiniteTorus.centerInjection F ζ hζ q e) : ℂ) = _
          simpa [normPower, localAbs_one] using hh
        cases ε
        · change tau P (A.retract (A.torus (ActualFiniteTorus.central F ζ hζ q e))) V = _
          rw [A.retract_torus]
          have ht := tau_hasCentralCharacter (ActualFiniteTorus.actualHeisenberg F ζ hζ q) P
            (ActualFiniteTorus.centerInjection F ζ hζ q e) V
          change tau P (ActualFiniteTorus.central F ζ hζ q e) V =
            ((ActualFiniteTorus.actualHeisenberg F ζ hζ q).ω
              (ActualFiniteTorus.centerInjection F ζ hζ q e) : ℂ) • V at ht
          rw [hv] at ht
          exact ht
        · change tau P (A.weyl (A.retract (A.torus (ActualFiniteTorus.central F ζ hζ q e)))) V = _
          rw [A.retract_torus]
          change tau P (Geometry.weyl F ζ hζ q (ActualFiniteTorus.central F ζ hζ q e)) V = _
          rw [Geometry.weyl_central]
          have ht := tau_hasCentralCharacter (ActualFiniteTorus.actualHeisenberg F ζ hζ q) P
            (ActualFiniteTorus.centerInjection F ζ hζ q e) V
          change tau P (ActualFiniteTorus.central F ζ hζ q e) V =
            ((ActualFiniteTorus.actualHeisenberg F ζ hζ q).ω
              (ActualFiniteTorus.centerInjection F ζ hζ q e) : ℂ) • V at ht
          rw [hv] at ht
          exact ht }
    exact ⟨B, rfl, rfl, rfl⟩

end
end DedekindZetaZeroFree.ActualFiniteBorel
