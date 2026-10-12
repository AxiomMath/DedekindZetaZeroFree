module

public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.BorelCoverRefinement
public import DedekindZetaZeroFree.Adeles.Quotients.Cotangent.MeasurableFamilies
public import DedekindZetaZeroFree.Analysis.EquivariantSections.L2.MeasurableFixedFibers

@[expose] public section

noncomputable section
open scoped NumberField BigOperators
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContActualCotangentPieceHilbertSum
open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable (a : ShrunkChart F ζ hζ U R P H)

def actualAction (γ : Gamma a) (y : a.domain) : a.domain := a.action γ.val.1 y

theorem action_continuous (γ : Gamma a) : Continuous (actualAction a γ) :=
  ((KPCuspSiegel.continuous_action F (γ.val.1.val : KPCuspArithmetic.PGL2 F)).comp
    continuous_subtype_val).subtype_mk _

def actualActionEquiv (γ : Gamma a) : a.domain ≃ᵐ a.domain where
  toFun := actualAction a γ
  invFun := actualAction a γ⁻¹
  left_inv y := by
    apply Subtype.ext
    change (γ.val.1.val : KPCuspArithmetic.PGL2 F)⁻¹ •
      ((γ.val.1.val : KPCuspArithmetic.PGL2 F) • y.val) = y.val
    exact inv_smul_smul _ _
  right_inv y := by
    apply Subtype.ext
    change (γ.val.1.val : KPCuspArithmetic.PGL2 F) •
      ((γ.val.1.val : KPCuspArithmetic.PGL2 F)⁻¹ • y.val) = y.val
    exact smul_inv_smul _ _
  measurable_toFun := (action_continuous a γ).measurable
  measurable_invFun := (action_continuous a γ⁻¹).measurable

theorem action_preserving (γ : Gamma a) :
    MeasurePreserving (actualActionEquiv a γ) a.liftedMeasure a.liftedMeasure := by
  let g : KPCuspArithmetic.PGL2 F := γ.val.1.val
  let μ := KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)
  have he : (fun x : KPCuspGenuineMonodromy.SymmetricSpace F => g • x) ⁻¹' a.domain =
      a.domain := by
    ext x
    constructor
    · intro hx
      have hh := (actualAction a γ⁻¹ ⟨g • x, hx⟩).property
      simpa [actualAction, ShrunkChart.action, g] using hh
    · intro hx
      exact (actualAction a γ ⟨x, hx⟩).property
  have hp := (KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F g).restrict_preimage
    a.domain_open.measurableSet
  rw [he] at hp
  have hc := measurePreserving_subtype_coe (μa := μ.restrict a.domain)
    a.domain_open.measurableSet
  rw [Measure.restrict_restrict a.domain_open.measurableSet, Set.inter_self] at hc
  have hcomp := hp.comp hc
  have hmap : Measure.map (actualActionEquiv a γ)
      (Measure.comap (Subtype.val : a.domain → _) (μ.restrict a.domain)) =
      Measure.comap (Subtype.val : a.domain → _) (μ.restrict a.domain) := by
    apply (MeasurableEmbedding.subtype_coe a.domain_open.measurableSet).map_injective
    rw [Measure.map_map measurable_subtype_coe (actualActionEquiv a γ).measurable]
    exact hcomp.map_eq.trans hc.map_eq.symm
  exact (show MeasurePreserving (actualActionEquiv a γ)
    (Measure.comap (Subtype.val : a.domain → _) (μ.restrict a.domain))
    (Measure.comap (Subtype.val : a.domain → _) (μ.restrict a.domain)) from
      ⟨(actualActionEquiv a γ).measurable, hmap⟩).smul_measure _

def coordinates (y : a.domain) : omega a :=
  ⟨labeledAInv (placeEquiv F ζ hζ) y.val, by
    change labeledA (placeEquiv F ζ hζ)
      (labeledAInv (placeEquiv F ζ hζ) y.val) ∈ a.domain
    have hi : ∀ z : KPCuspGenuineMonodromy.SymmetricSpace F,
        labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) z) = z := by
      intro z; funext k; simp [labeledA, labeledAInv]
    rw [hi]
    exact y.property⟩

theorem coordinates_continuous : Continuous (coordinates a) := by
  apply Continuous.subtype_mk
  apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
  exact (continuous_pi fun k => continuous_apply _).comp continuous_subtype_val

def actualTensor (γ : Gamma a) (y : a.domain) : E F ≃ₗᵢ[ℂ] E F :=
  T (isotropyArrow a γ) (coordinates a y).val
    (KPContActualCotangentMeasurableFamilies.omega_subset_larger a (coordinates a y).property)

theorem tensor_measurable (γ : Gamma a) :
    Measurable (fun p : a.domain × E F => actualTensor a γ p.1 p.2) := by
  have hc : Continuous (fun y : omega a => twistedOperator (isotropyArrow a γ) y.val) :=
    ((smooth_operators (isotropyArrow a γ)).2.continuousOn.mono
      (KPContActualCotangentMeasurableFamilies.omega_subset_larger a)).restrict
  exact (((hc.comp (coordinates_continuous a)).comp continuous_fst).clm_apply
    continuous_snd).measurable

private theorem same_labels {i : Fin (H.atlas U).componentCount}
    {b c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ) (U := U) (R := R) (P := P) (H := H) i}
    (e f : Arrow b c) (hγ : e.gamma = f.gamma) (hr : e.root = f.root)
    (x : M F) (he : x ∈ e.domain) (hf : x ∈ f.domain) : T e x he = T f x hf := by
  apply LinearIsometryEquiv.ext
  intro v
  change twistedOperator e x v = twistedOperator f x v
  simp only [twistedOperator, Arrow.phase, Arrow.psi, Q, hγ, hr]

theorem tensor_one (y : a.domain) :
    actualTensor a 1 y = LinearIsometryEquiv.refl ℂ (E F) := by
  unfold actualTensor
  have hx := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    (coordinates a y).property
  exact (same_labels (isotropyArrow a 1) (identity (isotropyChart a)) rfl rfl
    (coordinates a y).val hx hx).trans (T_identity _ _ hx)

theorem coordinates_action (γ : Gamma a) (y : a.domain) :
    (coordinates a (actualActionEquiv a γ y)).val =
      (isotropyArrow a γ).psi (coordinates a y).val := by
  change labeledAInv (placeEquiv F ζ hζ) (γ.val.1.val • y.val) = _
  have hi : labeledA (placeEquiv F ζ hζ) (coordinates a y).val = y.val := by
    funext k; simp [coordinates, labeledA, labeledAInv]
  change labeledAInv (placeEquiv F ζ hζ) (γ.val.1.val • y.val) =
    labeledAInv (placeEquiv F ζ hζ)
      ((1⁻¹ * γ.val.1.val * 1) • labeledA (placeEquiv F ζ hζ) (coordinates a y).val)
  rw [hi]
  simp

theorem tensor_mul (γ δ : Gamma a) (y : a.domain) (v : E F) :
    actualTensor a (γ * δ) y v =
      actualTensor a γ (actualActionEquiv a δ y) (actualTensor a δ y v) := by
  have hx := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    (coordinates a y).property
  have ht := KPContActualCotangentMeasurableFamilies.omega_subset_larger a
    (coordinates a (actualActionEquiv a δ y)).property
  rw [coordinates_action a δ y] at ht
  have hc := T_comp (isotropyArrow a γ) (isotropyArrow a δ)
    (coordinates a y).val hx ht
  have hs := same_labels (isotropyArrow a (γ * δ))
    (comp (isotropyArrow a γ) (isotropyArrow a δ)) rfl rfl
    (coordinates a y).val hx ⟨hx, ht⟩
  unfold actualTensor
  rw [hs, hc]
  simp only [LinearIsometryEquiv.trans_apply]
  change twistedOperator (isotropyArrow a γ) ((isotropyArrow a δ).psi (coordinates a y).val)
    (twistedOperator (isotropyArrow a δ) (coordinates a y).val v) =
    twistedOperator (isotropyArrow a γ) (coordinates a (actualActionEquiv a δ y)).val
      (twistedOperator (isotropyArrow a δ) (coordinates a y).val v)
  rw [coordinates_action a δ y]

instance gammaFintype : Fintype (Gamma a) := by
  letI := finite_Gamma a
  exact Fintype.ofFinite _

def localData : KPMeasurableLocalL2.Data a.domain (E F) (Gamma a) where
  measure := a.liftedMeasure
  action := actualActionEquiv a
  action_one y := by
    apply Subtype.ext
    change (1 : KPCuspArithmetic.PGL2 F) • y.val = y.val
    exact one_smul _ _
  action_mul γ δ y := by
    apply Subtype.ext
    change (γ.val.1.val * δ.val.1.val : KPCuspArithmetic.PGL2 F) • y.val =
      γ.val.1.val • (δ.val.1.val • y.val)
    exact mul_smul _ _ _
  invariant_measure := action_preserving a
  tensor := actualTensor a
  measurable_tensor := tensor_measurable a
  tensor_one := tensor_one a
  tensor_mul := tensor_mul a

variable (cover : CountableCover F ζ hζ U R P H)

def supportedPiece (n : ℕ) : KPMeasurableLocalL2.Piece (localData (cover.chart n)) where
  set := KPContActualCotangentBorelRefinement.liftedPiece cover n
  measurableSet := (kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover).lifted_measurable n
  invariant γ y := by
    let hp := kp_cont_actual_cotangent_borel_refinement F ζ hζ U R P H cover
    constructor
    · intro hy
      have hinv := hp.lifted_invariant n γ⁻¹.val.1
      have hm := Set.mem_image_of_mem ((cover.chart n).action γ⁻¹.val.1) hy
      rw [hinv] at hm
      have he : (cover.chart n).action γ⁻¹.val.1
          ((cover.chart n).action γ.val.1 y) = y :=
        (actualActionEquiv (cover.chart n) γ).left_inv y
      change (cover.chart n).action γ⁻¹.val.1
        ((cover.chart n).action γ.val.1 y) ∈ _ at hm
      simpa only [he] using hm
    · intro hy
      have hm := Set.mem_image_of_mem ((cover.chart n).action γ.val.1) hy
      rw [hp.lifted_invariant n γ.val.1] at hm
      exact hm

def Q (n : ℕ) : Submodule ℂ (Lp (E F) 2 (cover.chart n).liftedMeasure) :=
  KPMeasurableLocalL2.Q (localData (cover.chart n)) (supportedPiece cover n)

instance qInnerProductSpace (n : ℕ) : InnerProductSpace ℂ (Q cover n) :=
  KPMeasurableLocalL2.Q_innerProductSpace (localData (cover.chart n)) (supportedPiece cover n)

instance qCompleteSpace (n : ℕ) : CompleteSpace (Q cover n) :=
  KPMeasurableLocalL2.Q_completeSpace (localData (cover.chart n)) (supportedPiece cover n)

abbrev PieceHilbert := lp (fun n : ℕ => ↥(Q cover n)) 2

instance pieceHilbertNormedAddCommGroup : NormedAddCommGroup (PieceHilbert cover) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun n : ℕ => ↥(Q cover n)) 2))

instance pieceHilbertNormedSpace : NormedSpace ℂ (PieceHilbert cover) :=
  inferInstanceAs (NormedSpace ℂ (lp (fun n : ℕ => ↥(Q cover n)) 2))

instance pieceHilbertInnerProductSpace : InnerProductSpace ℂ (PieceHilbert cover) :=
  inferInstanceAs (InnerProductSpace ℂ (lp (fun n : ℕ => ↥(Q cover n)) 2))

instance pieceHilbertCompleteSpace : CompleteSpace (PieceHilbert cover) :=
  inferInstanceAs (CompleteSpace (lp (fun n : ℕ => ↥(Q cover n)) 2))

theorem inner_eq_tsum (u w : PieceHilbert cover) :
    inner ℂ u w = ∑' n, inner ℂ (u n) (w n) :=
  lp.inner_eq_tsum u w

theorem norm_sq_eq_tsum (u : PieceHilbert cover) :
    ‖u‖ ^ 2 = ∑' n, ‖u n‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (E := fun n : ℕ => ↥(Q cover n))
    (p := 2) (by norm_num) u

end DedekindZetaZeroFree.KPContActualCotangentPieceHilbertSum

namespace DedekindZetaZeroFree

open KPContActualCotangentPieceHilbertSum

end DedekindZetaZeroFree

end
