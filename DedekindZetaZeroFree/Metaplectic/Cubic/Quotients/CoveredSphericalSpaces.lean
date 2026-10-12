module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightInvariantDifferentialWords
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.ArchimedeanSphericalQuotients

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev FiniteCover := KPFiniteCuspAtlas.FiniteCover F ζ hζ
abbrev SymmetricSpace := KPFiniteCuspAtlas.SymmetricSpace F

def coveredRelation (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    Setoid (SymmetricSpace F × FiniteCover F ζ hζ) where
  r p p' := ∃ (γ : KPCuspArithmetic.PGL2 F) (u : U.toOpenSubgroup),
    p'.1 = γ • p.1 ∧ p'.2 =
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * p.2 * u
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨1, 1, by simp, by simp⟩
    · rintro p p' ⟨γ, u, hx, hc⟩
      refine ⟨γ⁻¹, u⁻¹, ?_, ?_⟩
      · rw [hx]
        simp
      · rw [hc]
        simp [map_inv, mul_assoc]
    · rintro p p' p'' ⟨γ, u, hx, hc⟩ ⟨δ, v, hy, hd⟩
      refine ⟨δ * γ, u * v, ?_, ?_⟩
      · rw [hy, hx, mul_smul]
      · rw [hd, hc]
        simp [map_mul, mul_assoc]

abbrev CoveredSpherical (U : CompactOpenLevel (FiniteCover F ζ hζ)) :=
  Quotient (coveredRelation F ζ hζ U)

instance instTopologicalSpaceCoveredSpherical
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    TopologicalSpace (CoveredSpherical F ζ hζ U) :=
  inferInstanceAs (TopologicalSpace (Quotient (coveredRelation F ζ hζ U)))

instance instMeasurableSpaceCoveredSpherical
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    MeasurableSpace (CoveredSpherical F ζ hζ U) := borel _

private theorem central_comm (ε : rootsOfUnity 3 F) (c : FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

 theorem central_translation_respects
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) (ε : rootsOfUnity 3 F)
    (p p' : SymmetricSpace F × FiniteCover F ζ hζ)
    (h : (coveredRelation F ζ hζ U).r p p') :
    Quotient.mk (coveredRelation F ζ hζ U)
      (p.1, KPCuspGenuineMonodromy.central F ζ hζ ε * p.2) =
    Quotient.mk (coveredRelation F ζ hζ U)
      (p'.1, KPCuspGenuineMonodromy.central F ζ hζ ε * p'.2) := by
  obtain ⟨γ, u, hx, hc⟩ := h
  apply Quotient.sound
  refine ⟨γ, u, hx, ?_⟩
  dsimp
  rw [hc, ← mul_assoc, ← mul_assoc,
    central_comm F ζ hζ ε (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)]
  simp only [mul_assoc]

def z (U : CompactOpenLevel (FiniteCover F ζ hζ)) (ε : rootsOfUnity 3 F) :
    CoveredSpherical F ζ hζ U ≃ₜ CoveredSpherical F ζ hζ U where
  toFun := Quotient.lift (fun p => Quotient.mk (coveredRelation F ζ hζ U)
    (p.1, KPCuspGenuineMonodromy.central F ζ hζ ε * p.2))
      (central_translation_respects F ζ hζ U ε)
  invFun := Quotient.lift (fun p => Quotient.mk (coveredRelation F ζ hζ U)
    (p.1, KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ * p.2))
      (central_translation_respects F ζ hζ U ε⁻¹)
  left_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | h p =>
      change Quotient.mk _ (p.1, KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
        (KPCuspGenuineMonodromy.central F ζ hζ ε * p.2)) = Quotient.mk _ p
      simp [map_inv]
  right_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | h p =>
      change Quotient.mk _ (p.1, KPCuspGenuineMonodromy.central F ζ hζ ε *
        (KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ * p.2)) = Quotient.mk _ p
      simp [map_inv]
  continuous_toFun := by
    letI := (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))
  continuous_invFun := by
    letI := (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
    apply continuous_quot_lift
    exact continuous_quotient_mk'.comp
      (continuous_fst.prodMk (continuous_const.mul continuous_snd))

theorem z_mk (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (ε : rootsOfUnity 3 F) (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) :
    z F ζ hζ U ε (Quotient.mk (coveredRelation F ζ hζ U) (x, c)) =
      Quotient.mk (coveredRelation F ζ hζ U)
        (x, KPCuspGenuineMonodromy.central F ζ hζ ε * c) := rfl

def centralAction (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    rootsOfUnity 3 F →* (CoveredSpherical F ζ hζ U ≃ₜ CoveredSpherical F ζ hζ U) where
  toFun := z F ζ hζ U
  map_one' := by
    ext a
    induction a using Quotient.inductionOn with
    | h p =>
      rcases p with ⟨x, c⟩
      simp [z_mk]
  map_mul' := by
    intro ε δ
    ext a
    induction a using Quotient.inductionOn with
    | h p =>
      rcases p with ⟨x, c⟩
      simp [z_mk, map_mul, mul_assoc]

instance instMulActionCoveredSpherical (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    MulAction (rootsOfUnity 3 F) (CoveredSpherical F ζ hζ U) where
  smul ε a := z F ζ hζ U ε a
  one_smul := by
    intro a
    exact congrArg (fun e : CoveredSpherical F ζ hζ U ≃ₜ CoveredSpherical F ζ hζ U => e a)
      (centralAction F ζ hζ U).map_one
  mul_smul := by
    intro ε δ a
    exact congrArg (fun e : CoveredSpherical F ζ hζ U ≃ₜ CoveredSpherical F ζ hζ U => e a)
      ((centralAction F ζ hζ U).map_mul ε δ)

def q (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    CoveredSpherical F ζ hζ U → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  Quotient.lift (fun p => Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) p)
    (by
      rintro p p' ⟨γ, u, hx, hc⟩
      apply Quotient.sound
      exact ⟨γ, 1, u, hx, by simpa using hc⟩)

theorem q_mk (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (x : SymmetricSpace F) (c : FiniteCover F ζ hζ) :
    q F ζ hζ U (Quotient.mk (coveredRelation F ζ hζ U) (x, c)) =
      Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (x, c) := rfl

theorem q_z (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (ε : rootsOfUnity 3 F) (a : CoveredSpherical F ζ hζ U) :
    q F ζ hζ U (z F ζ hζ U ε a) = q F ζ hζ U a := by
  induction a using Quotient.inductionOn with
  | h p =>
    rcases p with ⟨x, c⟩
    rw [z_mk, q_mk, q_mk]
    apply Eq.symm
    apply Quotient.sound
    exact ⟨1, ε, 1, by simp, by simp⟩

abbrev Gamma : Subgroup (ActualCover F ζ hζ) :=
  KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ

def K_U (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    Subgroup (ActualCover F ζ hζ) :=
  Subgroup.closure
    ((KPSmoothActualFlowData.archimedeanInsertion F ζ hζ) ''
        (KPContSectorArchSphericalFibers.KInfinity F : Set (KPSmoothActualFlowData.GInfinity F)) ∪
      (fun c : FiniteCover F ζ hζ => (c : ActualCover F ζ hζ)) ''
        (U.toOpenSubgroup : Set (FiniteCover F ζ hζ)))

abbrev CoveredActual (U : CompactOpenLevel (FiniteCover F ζ hζ)) :=
  DoubleCoset.Quotient (Gamma F ζ hζ : Set (ActualCover F ζ hζ))
    (K_U F ζ hζ U : Set (ActualCover F ζ hζ))

instance instTopologicalSpaceCoveredActual (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    TopologicalSpace (CoveredActual F ζ hζ U) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

instance instMeasurableSpaceCoveredActual (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    MeasurableSpace (CoveredActual F ζ hζ U) := borel _

def coveredActualMap (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    KPSmoothLocalQuotientCharts.X F ζ hζ → CoveredActual F ζ hζ U :=
  Quotient.lift (DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U)) (by
    intro a b hab
    apply Quotient.sound
    obtain ⟨γ, hγ, hγeq⟩ : ∃ γ ∈ Gamma F ζ hζ, b = γ * a := by
      refine ⟨b * a⁻¹, ?_, by simp⟩
      exact QuotientGroup.rightRel_apply.mp hab
    exact DoubleCoset.rel_iff.mpr
      ⟨γ, hγ, 1, (K_U F ζ hζ U).one_mem, by simpa using hγeq⟩)

theorem coveredActualMap_mk (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : ActualCover F ζ hζ) :
    coveredActualMap F ζ hζ U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) =
      DoubleCoset.mk (Gamma F ζ hζ) (K_U F ζ hζ U) g := rfl

theorem chi_norm (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 := by
  exact KPSmoothLocalQuotientCharts.ordinary_genuine_norm F ζ hζ ε

def chi : rootsOfUnity 3 F →* Circle where
  toFun ε := ⟨(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ), by
    simpa [Submonoid.unitSphere] using chi_norm F ζ hζ ε⟩
  map_one' := by
    apply Subtype.ext
    change (KPCuspGenuineMonodromy.chi F ζ hζ 1 : ℂ) = 1
    simp
  map_mul' := by
    intro ε δ
    apply Subtype.ext
    change (KPCuspGenuineMonodromy.chi F ζ hζ (ε * δ) : ℂ) =
      (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) *
        (KPCuspGenuineMonodromy.chi F ζ hζ δ : ℂ)
    simp

theorem chi_coe (ε : rootsOfUnity 3 F) :
    (chi F ζ hζ ε : ℂ) = (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) := rfl

end DedekindZetaZeroFree.KPContSectorCoveredQuotientVocabulary

end
