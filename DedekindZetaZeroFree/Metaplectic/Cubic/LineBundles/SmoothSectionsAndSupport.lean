module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Quotients.PhaseComponentCharts

@[expose] public section

noncomputable section
open scoped Classical NumberField
open Topology

namespace DedekindZetaZeroFree.KPContSectorSmoothFramesSupport

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)

def IsSmoothCovered (f : GenuineCoveredScalars F ζ hζ U) : Prop :=
  ∀ c : FiniteCover F ζ hζ,
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => (J F ζ hζ U f).val (x, c))

def smoothCovered : Submodule ℂ (GenuineCoveredScalars F ζ hζ U) where
  carrier := {f | IsSmoothCovered F ζ hζ U f}
  zero_mem' := by
    intro c
    have h : (fun x : SymmetricSpace F => (J F ζ hζ U 0).val (x, c)) = fun _ => (0 : ℂ) := by
      funext x; simp
    rw [h]; exact contDiff_const
  add_mem' := by
    intro f g hf hg c
    have h : (fun x : SymmetricSpace F => (J F ζ hζ U (f + g)).val (x, c))
        = fun x => (J F ζ hζ U f).val (x, c) + (J F ζ hζ U g).val (x, c) := by
      funext x; simp [map_add]
    rw [h]; exact (hf c).add (hg c)
  smul_mem' := by
    intro a f hf c
    have h : (fun x : SymmetricSpace F => (J F ζ hζ U (a • f)).val (x, c))
        = fun x => a • (J F ζ hζ U f).val (x, c) := by
      funext x; simp [map_smul]
    rw [h]; exact (hf c).const_smul a

variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

abbrev Sections := ∀ i : Fin (H.atlas U).componentCount,
  KPCuspGenuineMonodromy.sections F ζ hζ U
    ((H.atlas U).representative i) ((H.atlas U).line i).rho

def IsSmoothSections (s : Sections F ζ hζ U R P H) : Prop :=
  ∀ i, ContDiff ℝ (⊤ : ℕ∞) (s i).val

def smoothSections : Submodule ℂ (Sections F ζ hζ U R P H) where
  carrier := {s | IsSmoothSections F ζ hζ U R P H s}
  zero_mem' := by
    intro i
    have h : ((0 : Sections F ζ hζ U R P H) i).val = fun _ => (0 : ℂ) := by
      funext x; simp
    rw [h]; exact contDiff_const
  add_mem' := by
    intro s t hs ht i
    have h : ((s + t) i).val = fun x => (s i).val x + (t i).val x := by
      funext x; simp
    rw [h]; exact (hs i).add (ht i)
  smul_mem' := by
    intro a s hs i
    have h : ((a • s) i).val = fun x => a • (s i).val x := by
      funext x; simp
    rw [h]; exact (hs i).const_smul a

theorem smooth_iff (f : GenuineCoveredScalars F ζ hζ U) :
    IsSmoothCovered F ζ hζ U f ↔
      IsSmoothSections F ζ hζ U R P H (S F ζ hζ U R P H f) := by
  constructor
  · intro hf i
    have h := hf ((H.atlas U).representative i)
    have heq : ((S F ζ hζ U R P H) f i).val =
        fun x => (J F ζ hζ U f).val (x, (H.atlas U).representative i) := by
      funext x; rw [S_apply, J_apply]
    rwa [heq]
  · intro hs c
    classical
    set x0 : SymmetricSpace F := Classical.arbitrary _
    obtain ⟨w, hw⟩ := (H.atlas U).components.surjective
      (Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (x0, c))
    obtain ⟨i, y⟩ := w
    obtain ⟨x', hx'⟩ : ∃ x' : SymmetricSpace F,
        Quotient.mk (MulAction.orbitRel
          (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
          (SymmetricSpace F)) x' = y := ⟨Quotient.out y, Quotient.out_eq y⟩
    have hc_eq : Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (x0, c) =
        Quotient.mk (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U)
          (x', (H.atlas U).representative i) := by
      rw [← hw, ← hx', (H.atlas U).components_formula]
      rfl
    obtain ⟨γ, ε, u, hx, hrep⟩ := Quotient.exact hc_eq
    have hcentral : ∀ (a : rootsOfUnity 3 F) (b : FiniteCover F ζ hζ),
        KPCuspGenuineMonodromy.central F ζ hζ a * b =
          b * KPCuspGenuineMonodromy.central F ζ hζ a := by
      intro a b
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.mp
        (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨a, rfl⟩) b).symm
    have hrep' : (H.atlas U).representative i =
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
          KPCuspGenuineMonodromy.central F ζ hζ ε * c * u := hrep
    have hc : c = (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε)⁻¹ *
        (H.atlas U).representative i * u⁻¹ := by
      rw [hrep']
      rw [show (↑(u⁻¹) : FiniteCover F ζ hζ) = (↑u : FiniteCover F ζ hζ)⁻¹ from by simp]
      group
    have hc' : c = KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ⁻¹ *
        KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
        (H.atlas U).representative i * u⁻¹ := by
      rw [hc, mul_inv_rev,
        ← map_inv (KPCuspGenuineMonodromy.central F ζ hζ) ε,
        ← map_inv (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ) γ,
        hcentral ε⁻¹ (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ⁻¹)]
    have hfun : (fun x : SymmetricSpace F => (J F ζ hζ U f).val (x, c)) =
        fun x => (chi F ζ hζ ε⁻¹ : ℂ) * (S F ζ hζ U R P H f i).val (γ • x) := by
      funext x
      rw [J_apply, S_apply]
      have hrel : Quotient.mk (coveredRelation F ζ hζ U) (x, c) =
          Quotient.mk (coveredRelation F ζ hζ U)
            (γ • x, KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ *
              (H.atlas U).representative i) :=
        (Quotient.sound (show coveredRelation F ζ hζ U
            (γ • x, KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹ * (H.atlas U).representative i)
            (x, c) from ⟨γ⁻¹, u⁻¹, by simp, by rw [hc']; group⟩)).symm
      rw [hrel, ← z_mk F ζ hζ U ε⁻¹ (γ • x) ((H.atlas U).representative i)]
      exact f.property ε⁻¹ _
    rw [hfun]
    have hact : ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => γ • x) := by
      obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
      have he : (fun x : SymmetricSpace F =>
          (Matrix.ProjGenLinGroup.mk B : KPCuspArithmetic.PGL2 F) • x) =
          KPCuspSiegel.glAction F B := by
        funext x; exact KPCuspSiegel.action_mk F B x
      rw [he]
      exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
        (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B)).of_le le_top
    exact ContDiff.const_smul (chi F ζ hζ ε⁻¹ : ℂ) ((hs i).comp hact)

def smoothS : smoothCovered F ζ hζ U ≃ₗ[ℂ] smoothSections F ζ hζ U R P H where
  toFun f := ⟨S F ζ hζ U R P H f.val, (smooth_iff F ζ hζ U R P H f.val).mp f.property⟩
  invFun s := ⟨(S F ζ hζ U R P H).symm s.val,
    (smooth_iff F ζ hζ U R P H ((S F ζ hζ U R P H).symm s.val)).mpr (by
      rw [LinearEquiv.apply_symm_apply]
      exact s.property)⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv s := by apply Subtype.ext; simp
  map_add' f g := by apply Subtype.ext; simp
  map_smul' a f := by apply Subtype.ext; simp

theorem smoothS_apply (f : smoothCovered F ζ hζ U) :
    (smoothS F ζ hζ U R P H f).val = S F ζ hζ U R P H f.val := rfl

abbrev Coefficient := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U

def phaseTransport (ε : rootsOfUnity 3 F) :
    Coefficient F ζ hζ U ≃ₗᵢ[ℂ] Coefficient F ζ hζ U where
  toFun v := ⟨(chi F ζ hζ ε : ℂ) * (v : ℂ), by
    intro δ hδ
    show (chi F ζ hζ δ : ℂ) * ((chi F ζ hζ ε : ℂ) * (v : ℂ)) =
      (chi F ζ hζ ε : ℂ) * (v : ℂ)
    have hv : (chi F ζ hζ δ : ℂ) * (v : ℂ) = (v : ℂ) := by
      rw [chi_coe F ζ hζ δ]; exact v.property δ hδ
    calc (chi F ζ hζ δ : ℂ) * ((chi F ζ hζ ε : ℂ) * (v : ℂ))
        = ((chi F ζ hζ δ : ℂ) * (chi F ζ hζ ε : ℂ)) * (v : ℂ) := by ring
      _ = ((chi F ζ hζ ε : ℂ) * (chi F ζ hζ δ : ℂ)) * (v : ℂ) := by ring
      _ = (chi F ζ hζ ε : ℂ) * ((chi F ζ hζ δ : ℂ) * (v : ℂ)) := by ring
      _ = (chi F ζ hζ ε : ℂ) * (v : ℂ) := by rw [hv]⟩
  invFun v := ⟨(chi F ζ hζ ε⁻¹ : ℂ) * (v : ℂ), by
    intro δ hδ
    show (chi F ζ hζ δ : ℂ) * ((chi F ζ hζ ε⁻¹ : ℂ) * (v : ℂ)) =
      (chi F ζ hζ ε⁻¹ : ℂ) * (v : ℂ)
    have hv : (chi F ζ hζ δ : ℂ) * (v : ℂ) = (v : ℂ) := by
      rw [chi_coe F ζ hζ δ]; exact v.property δ hδ
    calc (chi F ζ hζ δ : ℂ) * ((chi F ζ hζ ε⁻¹ : ℂ) * (v : ℂ))
        = ((chi F ζ hζ δ : ℂ) * (chi F ζ hζ ε⁻¹ : ℂ)) * (v : ℂ) := by ring
      _ = ((chi F ζ hζ ε⁻¹ : ℂ) * (chi F ζ hζ δ : ℂ)) * (v : ℂ) := by ring
      _ = (chi F ζ hζ ε⁻¹ : ℂ) * ((chi F ζ hζ δ : ℂ) * (v : ℂ)) := by ring
      _ = (chi F ζ hζ ε⁻¹ : ℂ) * (v : ℂ) := by rw [hv]⟩
  left_inv v := by
    apply Subtype.ext
    show (chi F ζ hζ ε⁻¹ : ℂ) * ((chi F ζ hζ ε : ℂ) * (v : ℂ)) = (v : ℂ)
    have h1 : (chi F ζ hζ ε⁻¹ : ℂ) * (chi F ζ hζ ε : ℂ) = 1 := by
      rw [← Circle.coe_mul, map_inv, inv_mul_cancel, Circle.coe_one]
    rw [← mul_assoc, h1, one_mul]
  right_inv v := by
    apply Subtype.ext
    show (chi F ζ hζ ε : ℂ) * ((chi F ζ hζ ε⁻¹ : ℂ) * (v : ℂ)) = (v : ℂ)
    have h1 : (chi F ζ hζ ε : ℂ) * (chi F ζ hζ ε⁻¹ : ℂ) = 1 := by
      rw [← Circle.coe_mul, map_inv, mul_inv_cancel, Circle.coe_one]
    rw [← mul_assoc, h1, one_mul]
  map_add' v w := by
    apply Subtype.ext
    show (chi F ζ hζ ε : ℂ) * ((v : ℂ) + (w : ℂ)) =
      (chi F ζ hζ ε : ℂ) * (v : ℂ) + (chi F ζ hζ ε : ℂ) * (w : ℂ)
    ring
  map_smul' a v := by
    apply Subtype.ext
    show (chi F ζ hζ ε : ℂ) * (a * (v : ℂ)) = a * ((chi F ζ hζ ε : ℂ) * (v : ℂ))
    ring
  norm_map' v := by
    show ‖(chi F ζ hζ ε : ℂ) * (v : ℂ)‖ = ‖(v : ℂ)‖
    rw [norm_mul, chi_coe F ζ hζ ε, chi_norm F ζ hζ ε, one_mul]

theorem phaseTransport_apply (ε : rootsOfUnity 3 F) (v : Coefficient F ζ hζ U) :
    (phaseTransport F ζ hζ U ε v : ℂ) = (chi F ζ hζ ε : ℂ) * (v : ℂ) := rfl

theorem phaseTransport_level_ambiguity (ε η : rootsOfUnity 3 F)
    (h : KPCuspGenuineMonodromy.central F ζ hζ (η⁻¹ * ε) ∈ U.toOpenSubgroup)
    (v : Coefficient F ζ hζ U) :
    phaseTransport F ζ hζ U ε v = phaseTransport F ζ hζ U η v := by
  apply Subtype.ext
  show (chi F ζ hζ ε : ℂ) * (v : ℂ) = (chi F ζ hζ η : ℂ) * (v : ℂ)
  have hmul : (chi F ζ hζ ε : ℂ) =
      (chi F ζ hζ η : ℂ) * (chi F ζ hζ (η⁻¹ * ε) : ℂ) := by
    conv_lhs => rw [← mul_inv_cancel_left η ε]
    rw [map_mul, Circle.coe_mul]
  have hv : (chi F ζ hζ (η⁻¹ * ε) : ℂ) * (v : ℂ) = (v : ℂ) := by
    rw [chi_coe F ζ hζ (η⁻¹ * ε)]; exact v.property (η⁻¹ * ε) h
  rw [hmul, mul_assoc, hv]

theorem phase_lift_formula (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F)
    (x : SymmetricSpace F) :
    f.val (Quotient.mk (coveredRelation F ζ hζ U)
      (x, KPCuspGenuineMonodromy.central F ζ hζ ε * (H.atlas U).representative i)) =
      (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H f i).val x := by
  rw [S_apply]
  rw [← z_mk F ζ hζ U ε x ((H.atlas U).representative i)]
  exact f.property ε _

def liftFrame (x : SymmetricSpace F) :
    Coefficient F ζ hζ U ≃ₗᵢ[ℂ] Coefficient F ζ hζ U :=
  LinearIsometryEquiv.refl ℂ _

theorem liftFrame_unitary (x : SymmetricSpace F) (v : Coefficient F ζ hζ U) :
    ‖liftFrame F ζ hζ U x v‖ = ‖v‖ := by
  simp [liftFrame]

theorem liftFrame_equivariant (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : SymmetricSpace F) (v : Coefficient F ζ hζ U) :
    liftFrame F ζ hζ U ((γ : KPCuspArithmetic.PGL2 F) • x)
      (phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ) v) =
    phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)
      (liftFrame F ζ hζ U x v) := by
  simp [liftFrame]

def liftCoefficient (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    Coefficient F ζ hζ U := ⟨(s i).val x, (s i).property.1 x⟩

theorem liftCoefficient_transition (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : SymmetricSpace F) :
    liftCoefficient F ζ hζ U R P H s i ((γ : KPCuspArithmetic.PGL2 F) • x) =
      phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)
        (liftCoefficient F ζ hζ U R P H s i x) ∧
    ‖liftCoefficient F ζ hζ U R P H s i ((γ : KPCuspArithmetic.PGL2 F) • x)‖ =
      ‖liftCoefficient F ζ hζ U R P H s i x‖ := by
  have h1 : liftCoefficient F ζ hζ U R P H s i ((γ : KPCuspArithmetic.PGL2 F) • x) =
      phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)
        (liftCoefficient F ζ hζ U R P H s i x) := by
    apply Subtype.ext
    rw [phaseTransport_apply]
    exact (s i).property.2 γ x
  refine ⟨h1, ?_⟩
  rw [h1]
  exact (phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)).norm_map
    (liftCoefficient F ζ hζ U R P H s i x)

def phaseCoefficient (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U)
    (x : SymmetricSpace F) : Coefficient F ζ hζ U :=
  Quotient.lift (fun ε => phaseTransport F ζ hζ U ε
    (liftCoefficient F ζ hζ U R P H s i x)) (by
    intro a b hab
    have hmem : KPCuspGenuineMonodromy.central F ζ hζ (a⁻¹ * b) ∈ U.toOpenSubgroup := by
      have h1 := QuotientGroup.leftRel_apply.mp hab
      simpa [KPContSectorPhaseComponentCharts.centralLevel] using h1
    have hmem' : KPCuspGenuineMonodromy.central F ζ hζ (b⁻¹ * a) ∈ U.toOpenSubgroup := by
      have hconj : KPCuspGenuineMonodromy.central F ζ hζ (b⁻¹ * a) =
          (KPCuspGenuineMonodromy.central F ζ hζ (a⁻¹ * b))⁻¹ := by
        simp only [map_inv, map_mul]
        group
      rw [hconj]; exact U.toOpenSubgroup.inv_mem hmem
    exact phaseTransport_level_ambiguity F ζ hζ U a b hmem'
      (liftCoefficient F ζ hζ U R P H s i x)) m

theorem phaseCoefficient_class (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F)
    (x : SymmetricSpace F) :
    (phaseCoefficient F ζ hζ U R P H s i
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε) x : ℂ) =
      (chi F ζ hζ ε : ℂ) * (s i).val x := by
  rw [phaseCoefficient, KPContSectorPhaseComponentCharts.phaseClass,
    QuotientGroup.mk'_apply, Quotient.lift_mk, phaseTransport_apply]
  rfl

theorem phase_component_restriction (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount)
    (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U)
    (x : SymmetricSpace F) :
    f.val (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H
      ⟨i, Quotient.mk _ (m,x)⟩) =
      (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i m x : ℂ) := by
  refine Quotient.inductionOn m ?_
  intro ε
  have hm : KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε =
      (Quotient.mk _ ε : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) := rfl
  rw [← hm]
  rw [KPContSectorPhaseComponentCharts.componentHomeomorph_mk, phaseCoefficient_class,
    S_apply]
  rw [← z_mk F ζ hζ U ε x ((H.atlas U).representative i)]
  exact f.property ε _

theorem orbifold_restriction_commutes (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
    (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) (y : O.neighborhood) :
    f.val (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
      (Quotient.mk _ (m,y))).val =
      (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i m y.val : ℂ) := by
  refine Quotient.inductionOn m ?_
  intro ε
  have hm : KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε =
      (Quotient.mk _ ε : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U) := rfl
  rw [← hm]
  rw [KPContSectorPhaseComponentCharts.coveredChart_mk, phaseCoefficient_class, S_apply]
  rw [← z_mk F ζ hζ U ε y.val ((H.atlas U).representative i)]
  exact f.property ε _

theorem orbifold_frame_equivariant (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer
      (KPContSectorPhaseComponentCharts.Component F ζ hζ U R P H i) x)
    (y : O.neighborhood) (v : Coefficient F ζ hζ U) :
    liftFrame F ζ hζ U ((σ.val : KPCuspArithmetic.PGL2 F) • y.val)
      (phaseTransport F ζ hζ U (((H.atlas U).line i).rho σ.val) v) =
      phaseTransport F ζ hζ U (((H.atlas U).line i).rho σ.val)
        (liftFrame F ζ hζ U y.val v) := by
  simp [liftFrame]

theorem lift_restriction_commutes (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount) (V : Set (SymmetricSpace F)) :
    (fun x : V => (liftCoefficient F ζ hζ U R P H
      (S F ζ hζ U R P H f) i x.val : ℂ)) =
    (fun x : V => (J F ζ hζ U f).val (x.val, (H.atlas U).representative i)) := by
  funext x
  show ((S F ζ hζ U R P H f) i).val x.val =
    (J F ζ hζ U f).val (x.val, (H.atlas U).representative i)
  rw [S_apply, J_apply]

def cuspPoint (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) (p : KPCuspCharts.Coordinates F) :
    SymmetricSpace F :=
  ((H.atlas U).cuspAtlas i).representative j • KPCuspCharts.toArch F p

def cuspCoefficient (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) (p : KPCuspCharts.Coordinates F) :
    Coefficient F ζ hζ U :=
  liftCoefficient F ζ hζ U R P H s i (cuspPoint F ζ hζ U R P H i j p)

private theorem rationalAction_smooth (γ : KPCuspArithmetic.PGL2 F) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : SymmetricSpace F => γ • x) := by
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective γ
  have he : (fun x : SymmetricSpace F =>
      (Matrix.ProjGenLinGroup.mk B : KPCuspArithmetic.PGL2 F) • x) =
      KPCuspSiegel.glAction F B := by
    funext x
    exact KPCuspSiegel.action_mk F B x
  rw [he]
  exact (KPArch.productAction_contDiff (KPCuspLogShape.dimension F)
    (fun i => Matrix.GeneralLinearGroup.map (KPCusp.complexPlace F i).embedding B)).of_le le_top

theorem cuspCoefficient_smooth (s : Sections F ζ hζ U R P H)
    (hs : IsSmoothSections F ζ hζ U R P H s)
    (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
      (cuspCoefficient F ζ hζ U R P H s i j p : ℂ)) := by
  exact (hs i).comp ((rationalAction_smooth F
    (((H.atlas U).cuspAtlas i).representative j)).comp
      ((KPCuspCharts.toArch_contDiff F).of_le le_top))

theorem cuspCoefficient_transition (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount)
    (g : KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j))
    (p : KPCuspCharts.Cross F) (t : ℝ) :
    let γ := KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j) g
    cuspCoefficient F ζ hζ U R P H s i j
      ((((H.atlas U).cuspAtlas i).geometry j).crossAction g p, t) =
      phaseTransport F ζ hζ U (((H.atlas U).line i).rho γ)
        (cuspCoefficient F ζ hζ U R P H s i j (p,t)) ∧
    ‖cuspCoefficient F ζ hζ U R P H s i j
      ((((H.atlas U).cuspAtlas i).geometry j).crossAction g p, t)‖ =
      ‖cuspCoefficient F ζ hζ U R P H s i j (p,t)‖ := by
  dsimp only
  let D := ((H.atlas U).cuspAtlas i).parabolic j
  let G := ((H.atlas U).cuspAtlas i).geometry j
  let γ := KPCuspGenuineMonodromy.cuspInclusion F
    (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j) g
  have ha : (g : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F (p,t) =
      KPCuspCharts.toArch F (G.crossAction g p,t) := by
    obtain ⟨A, hA, hc⟩ := D.upper g g.property
    change KPCuspSiegel.action F _ _ = _
    rw [G.actual_action g A hA hc, G.crossAction_formula g A hA hc p]
    rfl
  have hp : cuspPoint F ζ hζ U R P H i j (G.crossAction g p,t) =
      (γ : KPCuspArithmetic.PGL2 F) • cuspPoint F ζ hζ U R P H i j (p,t) := by
    unfold cuspPoint
    rw [← ha]
    dsimp only [γ]
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula]
    simp only [mul_smul, inv_smul_smul]
  dsimp only [cuspCoefficient]
  change liftCoefficient F ζ hζ U R P H s i
      (cuspPoint F ζ hζ U R P H i j (G.crossAction g p,t)) = _ ∧
    ‖liftCoefficient F ζ hζ U R P H s i
      (cuspPoint F ζ hζ U R P H i j (G.crossAction g p,t))‖ = _
  rw [hp]
  exact liftCoefficient_transition F ζ hζ U R P H s i γ
    (cuspPoint F ζ hζ U R P H i j (p,t))

theorem actual_cusp_atlas_overlap (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) :
    let D := ((H.atlas U).cuspAtlas i).parabolic j
    let G := ((H.atlas U).cuspAtlas i).geometry j
    ∀ (a b : Fin G.atlas.chartCount)
      (u : G.atlas.shapeLift a) (v : G.atlas.shapeLift b),
      (QuotientAddGroup.mk u.val : KPCuspCharts.Base F H.totallyComplex
        D.E D.integralUnits) = QuotientAddGroup.mk v.val →
      ∃ g : KPCuspArithmetic.conjugatedStabilizer F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
        (((H.atlas U).cuspAtlas i).cusp j) (((H.atlas U).cuspAtlas i).representative j),
        v.val = u.val + KPCuspLogShape.logarithm F H.totallyComplex D.E
          D.integralUnits (Additive.ofMul (D.ratio g)) ∧
        (∀ z : KPCuspCharts.Torus F D.L,
          G.atlas.lift (z,u.val) = G.atlas.lift (G.torusAction (D.ratio g) z,v.val)) ∧
        (∀ (p : KPCuspCharts.Cross F) (t : ℝ),
          ‖cuspCoefficient F ζ hζ U R P H s i j (G.crossAction g p,t)‖ =
            ‖cuspCoefficient F ζ hζ U R P H s i j (p,t)‖) := by
  dsimp only
  intro a b u v huv
  obtain ⟨g, hv, hg⟩ := (((H.atlas U).cuspAtlas i).geometry j).atlas.transitions
    a b u v huv
  exact ⟨g, hv, hg, fun p t =>
    (cuspCoefficient_transition F ζ hζ U R P H s i j g p t).2⟩

def IsSmoothOrbifoldCuspSections (s : Sections F ζ hζ U R P H) : Prop :=
  (∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x),
      ContDiffOn ℝ (⊤ : ℕ∞) (s i).val O.neighborhood) ∧
  (∀ (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount),
      ContDiff ℝ (⊤ : ℕ∞) (fun p : KPCuspCharts.Coordinates F =>
        (cuspCoefficient F ζ hζ U R P H s i j p : ℂ)))

theorem smooth_sections_iff_lifts (s : Sections F ζ hζ U R P H) :
    IsSmoothSections F ζ hζ U R P H s ↔
      IsSmoothOrbifoldCuspSections F ζ hζ U R P H s := by
  constructor
  · intro hs
    exact ⟨fun i _ _ => (hs i).contDiffOn,
      fun i j => cuspCoefficient_smooth F ζ hζ U R P H s hs i j⟩
  · intro hs i
    apply contDiff_iff_contDiffAt.mpr
    intro x
    obtain ⟨O⟩ := KPContSectorPhaseComponentCharts.orbifoldChart_exists F ζ hζ U R P H i x
    exact (hs.1 i x O).contDiffAt (O.isOpen.mem_nhds O.center_mem)

theorem actual_cusp_shape_lift_smooth (s : Sections F ζ hζ U R P H)
    (hs : IsSmoothSections F ζ hζ U R P H s)
    (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount)
    (a : Fin (((H.atlas U).cuspAtlas i).geometry j).atlas.chartCount) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : KPCuspCharts.Coordinates F =>
        (cuspCoefficient F ζ hζ U R P H s i j p : ℂ))
      {p | p.1.2 ∈ (((H.atlas U).cuspAtlas i).geometry j).atlas.shapeLift a ∧
        ((H.atlas U).cuspAtlas i).threshold < p.2} := by
  exact (cuspCoefficient_smooth F ζ hζ U R P H s hs i j).contDiffOn

theorem cusp_restriction_commutes (f : GenuineCoveredScalars F ζ hζ U)
    (i : Fin (H.atlas U).componentCount)
    (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) (p : KPCuspCharts.Cross F) (t : ℝ) :
    (cuspCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i j (p,t) : ℂ) =
      (J F ζ hζ U f).val
        (((H.atlas U).cuspAtlas i).representative j • KPCuspCharts.toArch F (p,t),
          (H.atlas U).representative i) := by
  show ((S F ζ hζ U R P H f) i).val (cuspPoint F ζ hζ U R P H i j (p,t)) =
    (J F ζ hζ U f).val (cuspPoint F ζ hζ U R P H i j (p,t),
      (H.atlas U).representative i)
  rw [S_apply, J_apply]

def componentNorm (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) :
    KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) → ℝ :=
  Quotient.lift (fun x => ‖(s i).val x‖) (by
    intro x y hxy
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
    have hγy : (s i).val (γ • y) =
        (chi F ζ hζ (((H.atlas U).line i).rho γ) : ℂ) * (s i).val y :=
      (s i).property.2 γ y
    rw [← hγ, hγy, norm_mul, chi_coe F ζ hζ (((H.atlas U).line i).rho γ),
      chi_norm F ζ hζ (((H.atlas U).line i).rho γ), one_mul])

def sectionNorm (s : Sections F ζ hζ U R P H) :
    KPMsFixedHaarDisintegration.Spherical F ζ hζ U → ℝ :=
  fun b => let p := (H.atlas U).components.symm b; componentNorm F ζ hζ U R P H s p.1 p.2

theorem sectionNorm_component (s : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F) :
    sectionNorm F ζ hζ U R P H s
      ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) = ‖(s i).val x‖ := by
  simp only [sectionNorm, componentNorm]
  rw [Homeomorph.symm_apply_apply, Quotient.lift_mk]

theorem sectionNorm_pullback (f : GenuineCoveredScalars F ζ hζ U)
    (v : CoveredSpherical F ζ hζ U) :
    sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f) (q F ζ hζ U v) = ‖f.val v‖ := by
  obtain ⟨⟨i, w⟩, rfl⟩ :=
    (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H).surjective v
  refine Quotient.inductionOn w ?_
  rintro ⟨m, x⟩
  refine Quotient.inductionOn m ?_
  intro ε
  rw [KPContSectorPhaseComponentCharts.componentHomeomorph_forget]
  change sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)
    ((H.atlas U).components ⟨i, Quotient.mk _ x⟩) = _
  rw [sectionNorm_component, phase_component_restriction]
  change ‖((S F ζ hζ U R P H f) i).val x‖ =
    ‖(phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f) i
      (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε) x : ℂ)‖
  rw [phaseCoefficient_class, norm_mul, chi_coe, chi_norm, one_mul]

theorem q_closed_and_proper :
    IsClosedMap (q F ζ hζ U) ∧
    ∀ K : Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U),
      IsCompact K → IsCompact ((q F ζ hζ U) ⁻¹' K) := by
  have hcont := KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U
  have hsurj := KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U
  have hquot := (KPContSectorQuotientRelationsComparison.q_isOpenMap F ζ hζ U).isQuotientMap
    hcont hsurj
  have hclosed : IsClosedMap (q F ζ hζ U) := by
    intro C hC
    apply hquot.isCoinducing.isClosed_preimage.mp
    have hsat : (q F ζ hζ U) ⁻¹' ((q F ζ hζ U) '' C) =
        ⋃ ε : rootsOfUnity 3 F, (z F ζ hζ U ε) '' C := by
      ext v
      constructor
      · rintro ⟨w, hw, hq⟩
        obtain ⟨ε, hε⟩ := (KPContSectorQuotientRelationsComparison.q_eq_iff
          F ζ hζ U w v).mp hq
        exact Set.mem_iUnion.mpr ⟨ε, w, hw, hε.symm⟩
      · intro hv
        obtain ⟨ε, w, hw, rfl⟩ := Set.mem_iUnion.mp hv
        exact ⟨w, hw, (q_z F ζ hζ U ε w).symm⟩
    rw [hsat]
    exact isClosed_iUnion_of_finite (fun ε => (z F ζ hζ U ε).isClosedMap _ hC)
  have hfib : ∀ y, IsCompact ((q F ζ hζ U) ⁻¹' {y}) := by
    intro y
    obtain ⟨v, rfl⟩ := hsurj y
    have heq : (q F ζ hζ U) ⁻¹' {q F ζ hζ U v} =
        Set.range (fun ε : rootsOfUnity 3 F => z F ζ hζ U ε v) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
      rw [eq_comm, KPContSectorQuotientRelationsComparison.q_eq_iff]
      exact ⟨fun ⟨ε, hε⟩ => ⟨ε, hε.symm⟩, fun ⟨ε, hε⟩ => ⟨ε, hε.symm⟩⟩
    rw [heq]
    exact (Set.finite_range _).isCompact
  exact ⟨hclosed, fun K hK =>
    (isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨hcont, hclosed, hfib⟩).isCompact_preimage hK⟩

private theorem sectionNorm_support_preimage (f : GenuineCoveredScalars F ζ hζ U) :
    (q F ζ hζ U) ⁻¹' Function.support
      (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)) = Function.support f.val := by
  ext v
  simp only [Set.mem_preimage, Function.mem_support, sectionNorm_pullback, norm_ne_zero_iff]

theorem tsupport_sectionNorm (f : GenuineCoveredScalars F ζ hζ U) :
    tsupport (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)) =
      q F ζ hζ U '' tsupport f.val := by
  have hs : Function.support (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)) =
      q F ζ hζ U '' Function.support f.val := by
    rw [← sectionNorm_support_preimage F ζ hζ U R P H f]
    exact (Set.image_preimage_eq _
      (KPContSectorQuotientRelationsComparison.q_surjective F ζ hζ U)).symm
  change closure _ = _
  rw [hs]
  exact (q_closed_and_proper F ζ hζ U).1.closure_image_eq_of_continuous
    (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U) _

theorem hasCompactSupport_iff (f : GenuineCoveredScalars F ζ hζ U) :
    HasCompactSupport f.val ↔
      HasCompactSupport (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)) := by
  change IsCompact (tsupport f.val) ↔ IsCompact (tsupport
    (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)))
  rw [tsupport_sectionNorm F ζ hζ U R P H f]
  constructor
  · intro hf
    exact hf.image (KPContSectorQuotientRelationsComparison.q_continuous F ζ hζ U)
  · intro hs
    exact ((q_closed_and_proper F ζ hζ U).2 _ hs).of_isClosed_subset
      isClosed_closure (fun v hv => ⟨v, hv, rfl⟩)

end DedekindZetaZeroFree.KPContSectorSmoothFramesSupport

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorScalarLineAlgebra
open KPContSectorSmoothFramesSupport

theorem kp_cont_sector_smooth_frames_support
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) :
    (∃ E : smoothCovered F ζ hζ U ≃ₗ[ℂ] smoothSections F ζ hζ U R P H,
      ∀ f, (E f).val = S F ζ hζ U R P H f.val) ∧
    (∀ s : Sections F ζ hζ U R P H,
      IsSmoothSections F ζ hζ U R P H s ↔
        IsSmoothOrbifoldCuspSections F ζ hζ U R P H s) ∧
    (∀ (f : GenuineCoveredScalars F ζ hζ U)
      (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F)
      (x : SymmetricSpace F),
      f.val (KPContSectorPhaseComponentCharts.componentHomeomorph F ζ hζ U R P H
        ⟨i, Quotient.mk _ (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε,x)⟩) =
        (chi F ζ hζ ε : ℂ) * (S F ζ hζ U R P H f i).val x) ∧
    (∀ f : GenuineCoveredScalars F ζ hζ U,
      tsupport (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f)) =
        q F ζ hζ U '' tsupport f.val) ∧
    (∀ f : GenuineCoveredScalars F ζ hζ U,
      HasCompactSupport f.val ↔
        HasCompactSupport (sectionNorm F ζ hζ U R P H (S F ζ hζ U R P H f))) := by
  refine ⟨⟨smoothS F ζ hζ U R P H, fun f => smoothS_apply F ζ hζ U R P H f⟩, ?_, ?_, ?_, ?_⟩
  · intro s; exact smooth_sections_iff_lifts F ζ hζ U R P H s
  · intro f i ε x
    rw [phase_component_restriction F ζ hζ U R P H f i
        (KPContSectorPhaseComponentCharts.phaseClass F ζ hζ U ε) x,
      phaseCoefficient_class F ζ hζ U R P H (S F ζ hζ U R P H f) i ε x]
  · intro f; exact tsupport_sectionNorm F ζ hζ U R P H f
  · intro f; exact hasCompactSupport_iff F ζ hζ U R P H f

end DedekindZetaZeroFree

end
