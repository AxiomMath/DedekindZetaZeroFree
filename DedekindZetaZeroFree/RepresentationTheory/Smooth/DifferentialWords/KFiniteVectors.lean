module

public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Casimir.RightWordCommutation
public import DedekindZetaZeroFree.Theta.Periods.CompactKernelOrbitData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RawWordKFinite
open KPGlobalResidualConstruction KPLiteralChamber KPSmoothActualFlowData
open KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.CanonicalWholeCoreNative.SourceInverse.IncomingMatrixSmooth renaming invertibleProducts_open → invertibleProducts_open
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
local notation "G" => KPGlobalTorusFunctionData.G F ζ hζ

def NativeSmooth (f : G → ℂ) : Prop := ∀ g,
  ContDiffOn ℝ (⊤ : ℕ∞) (fun x => f (g * archChart F ζ hζ x)) (archDomain F)

def expLift (f : G → ℂ) (g : G) (a : LieCoordinates F) : ℂ :=
  f (g * archimedeanInsertion F ζ hζ (exponential F a))

open scoped Matrix.Norms.Operator in
private theorem matrixExpEntry_smooth (v : NumberField.InfinitePlace F) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : LieCoordinates F =>
      NormedSpace.exp (sl2Matrix (fun j => a (v,j))) i j) := by
  letI : NormedAddCommGroup (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  let L : LieCoordinates F →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
    { toFun := fun a => sl2Matrix (fun j => a (v,j))
      map_add' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2Matrix] <;> ring
      map_smul' := by intro x y; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2Matrix, Complex.real_smul] <;> ring }
  let ev : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hh : ContDiff ℝ (⊤ : ℕ∞) (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) :=
    (show AnalyticOnNhd ℝ (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → _) Set.univ from fun _ _ => NormedSpace.exp_analytic _).contDiff
  exact ev.toContinuousLinearMap.contDiff.comp (hh.comp L.toContinuousLinearMap.contDiff)

open scoped Matrix.Norms.Elementwise

theorem expLift_smooth (f : G → ℂ) (hf : NativeSmooth f) (g : G) :
    ContDiff ℝ (⊤ : ℕ∞) (expLift f g) := by
  let e : LieCoordinates F → MatrixProduct F := fun a v =>
    NormedSpace.exp (sl2Matrix (fun j => a (v,j)))
  have he : ContDiff ℝ (⊤ : ℕ∞) e := by
    exact contDiff_pi.mpr (fun v => contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => matrixExpEntry_smooth v i j)))
  have hi (a) : e a ∈ invertibleProducts := by
    intro v
    exact Matrix.GeneralLinearGroup.det_ne_zero (matrixExponential (sl2Matrix (fun j => a (v,j))))
  have h := (matrixPullback_smooth f hf g).comp (he.contDiffOn (s := Set.univ)) (fun a _ => hi a)
  rw [contDiffOn_univ] at h
  convert h using 1
  funext a
  change expLift f g a = matrixPullback f g (e a)
  rw [matrixPullback, dif_pos (hi a)]
  unfold expLift exponential
  congr 3
  funext v
  congr 1
  apply Units.ext
  rfl

open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming word → word
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming actual_eq_word → actual_eq_word
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.NativeWordAction renaming native_word_smooth → native_word_smooth
open KPContActualSphericalRightFieldIdentification
open KPSmoothAutomorphicEvaluation.AmbientApproximation.OrbitSmoothing.Reconstruction.LocalSobolev.Scalar.CoordinateSource

def sixWord (w : List (B F)) (f : G → ℂ) : G → ℂ := word F ζ hζ w f

theorem sixWord_smooth (f : G → ℂ) (hf : NativeSmooth f) (w : List (B F)) :
    NativeSmooth (sixWord w f) := by
  let e := (lieEnumeration F).trans (actualBasisReindex F)
  let v := w.map e.symm
  have h := native_word_smooth F ζ hζ f hf v
  rw [actual_eq_word] at h
  have he : v.map (fun b => actualBasisReindex F (lieEnumeration F b)) = w := by
    change (w.map e.symm).map e = w
    simp
  rw [he] at h
  exact h

def jet (a : LieCoordinates F) (f : G → ℂ) (g : G) : ℂ :=
  fderiv ℝ (expLift f g) 0 a

theorem direction_hasDerivAt (f : G → ℂ) (hf : NativeSmooth f) (g : G)
    (a : LieCoordinates F) :
    HasDerivAt (fun t : ℝ => expLift f g (t • a)) (jet a f g) 0 := by
  have hd := (hasDerivAt_id (0 : ℝ)).smul_const a
  have hs := ((expLift_smooth f hf g).differentiable (by simp) 0).hasFDerivAt
  have hs' : HasFDerivAt (expLift f g) (fderiv ℝ (expLift f g) 0) ((0 : ℝ) • a) := by simpa using hs
  convert hs'.comp_hasDerivAt 0 hd using 1 <;> simp [jet, Function.comp_def]

theorem derivative_eq_jet (f : G → ℂ) (hf : NativeSmooth f) (g : G) (b : B F) :
    KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f g = jet (Pi.single b 1) f g := by
  have h := direction_hasDerivAt f hf g (Pi.single b 1)
  have he : (fun t : ℝ => expLift f g (t • Pi.single b 1)) =
      (fun t : ℝ => f (g * archimedeanInsertion F ζ hζ (flow F b t))) := by
    funext t
    unfold expLift flow
    congr 4
    funext c
    by_cases hc : c = b <;> simp [Pi.single_apply, hc]
  rw [he] at h
  exact h.deriv

def translate (k : GInfinity F) (f : G → ℂ) (g : G) : ℂ :=
  f (g * archimedeanInsertion F ζ hζ k)

theorem translate_smooth (k : GInfinity F) (f : G → ℂ) (hf : NativeSmooth f) :
    NativeSmooth (translate k f) := by
  intro g
  let m : ArchCoordinates F → MatrixProduct F := fun x v =>
    (!![x v 1 + x v 0 * x v 2, x v 0; x v 2, 1]) * (k v).out.val
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := by
    apply contDiff_pi.mpr; intro v
    apply contDiff_pi.mpr; intro i
    apply contDiff_pi.mpr; intro j
    fin_cases i <;> fin_cases j <;> simp [m, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> fun_prop
  have hv (x) (hx : x ∈ archDomain F) (v) : m x v = (rightMatrix (x v) * (k v).out).val := by
    rw [Units.val_mul, rightMatrix_val _ (hx v)]
  have hi (x) (hx : x ∈ archDomain F) : m x ∈ invertibleProducts := by
    intro v
    rw [hv x hx v]
    exact Matrix.GeneralLinearGroup.det_ne_zero _
  have h := (matrixPullback_smooth f hf g).comp hm.contDiffOn hi
  apply h.congr
  intro x hx
  change translate k f (g * archChart F ζ hζ x) = matrixPullback f g (m x)
  rw [matrixPullback, dif_pos (hi x hx)]
  unfold translate
  rw [right_insertion, mul_assoc, ← (archimedean_insertion_properties F ζ hζ).2.1]
  congr 3
  funext v
  change Matrix.ProjGenLinGroup.mk (rightMatrix (x v)) * k v = _
  have hk : Matrix.ProjGenLinGroup.mk (k v).out = k v := Quotient.out_eq _
  rw [← hk, ← map_mul]
  congr 1
  apply Units.ext
  exact (hv x hx v).symm

theorem translate_derivative (k : GInfinity F) (f : G → ℂ) (hf : NativeSmooth f)
    (g : G) (b : B F) :
    translate k (KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f) g =
      jet (PGLComplex.productAdjointLinearEquiv (NumberField.InfinitePlace F) k (Pi.single b 1))
        (translate k f) g := by
  let a := PGLComplex.productAdjointLinearEquiv (NumberField.InfinitePlace F) k (Pi.single b 1)
  have h := direction_hasDerivAt (translate k f) (translate_smooth k f hf) g a
  have he (t : ℝ) : exponential F (t • a) * k = k * flow F b t := by
    have hex := PGLComplex.productExponential_adjoint (NumberField.InfinitePlace F) k (t • Pi.single b 1)
    have hflow : PGLComplex.productExponential (NumberField.InfinitePlace F) (t • Pi.single b 1) = flow F b t := by
      change exponential F (t • Pi.single b 1) = exponential F (fun c => if c = b then t else 0)
      congr 1
      funext c
      by_cases hc : c = b <;> simp [hc]
    rw [hflow, map_smul] at hex
    change k * flow F b t * k⁻¹ = exponential F (t • a) at hex
    rw [← hex]
    simp [mul_assoc]
  have hc : (fun t : ℝ => expLift (translate k f) g (t • a)) =
      (fun t : ℝ => f ((g * archimedeanInsertion F ζ hζ k) *
        archimedeanInsertion F ζ hζ (flow F b t))) := by
    funext t
    unfold expLift translate
    rw [mul_assoc, mul_assoc, ← (archimedean_insertion_properties F ζ hζ).2.1,
      ← (archimedean_insertion_properties F ζ hζ).2.1, he]
  rw [hc] at h
  exact h.deriv

def scalarSpace : Submodule ℂ (G → ℂ) where
  carrier := NativeSmooth
  zero_mem' := by intro g; exact contDiffOn_const
  add_mem' := by intro f h hf hh g; exact (hf g).add (hh g)
  smul_mem' := by
    intro c f hf g
    change ContDiffOn ℝ (⊤ : ℕ∞) (fun x => c * f (g * archChart F ζ hζ x)) (archDomain F)
    exact contDiffOn_const.mul (hf g)

open _root_.DedekindZetaZeroFree.KPMsClearedTruncationL2.NativeStageJets renaming rightWord_hasDerivAt_of_chart_smooth → rightWord_hasDerivAt_of_chart_smooth

def derivative (b : B F) : scalarSpace (F := F) (ζ := ζ) (hζ := hζ) →ₗ[ℂ] scalarSpace (F := F) (ζ := ζ) (hζ := hζ) where
  toFun f := ⟨KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f.val,
    sixWord_smooth f.val f.property [b]⟩
  map_add' f h := by
    apply Subtype.ext
    funext g
    exact ((rightWord_hasDerivAt_of_chart_smooth F ζ hζ f.val f.property [] b g).add
      (rightWord_hasDerivAt_of_chart_smooth F ζ hζ h.val h.property [] b g)).deriv
  map_smul' c f := by
    apply Subtype.ext
    funext g
    exact ((rightWord_hasDerivAt_of_chart_smooth F ζ hζ f.val f.property [] b g).const_smul c).deriv

def translation (k : GInfinity F) : scalarSpace (F := F) (ζ := ζ) (hζ := hζ) →ₗ[ℂ] scalarSpace (F := F) (ζ := ζ) (hζ := hζ) where
  toFun f := ⟨translate k f.val, translate_smooth k f.val f.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem jet_eq_sum (a : LieCoordinates F) (f : G → ℂ) (hf : NativeSmooth f) (g : G) :
    jet a f g = ∑ b : B F, (a b : ℂ) * KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f g := by
  have ha : a = ∑ b : B F, a b • Pi.single b 1 := by
    funext c
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  unfold jet
  conv_lhs => arg 2; rw [ha]
  simp only [map_sum, map_smul, Complex.real_smul, derivative_eq_jet f hf]
  rfl

theorem translation_derivative (k : GInfinity F) (b : B F)
    (f : scalarSpace (F := F) (ζ := ζ) (hζ := hζ)) :
    translation k (derivative b f) = ∑ a : B F,
      ((PGLComplex.productAdjointLinearEquiv (NumberField.InfinitePlace F) k (Pi.single b 1) a : ℝ) : ℂ) •
        derivative a (translation k f) := by
  apply Subtype.ext
  funext g
  change translate k (KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 f.val) g = _
  rw [translate_derivative k f.val f.property, jet_eq_sum _ _ (translate_smooth k f.val f.property)]
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl

def words : ℕ → Finset (List (B F))
  | 0 => {[]}
  | n+1 => Finset.univ.biUnion (fun b : B F => (words n).image (List.cons b))

def wordVector (w : List (B F)) (f : scalarSpace (F := F) (ζ := ζ) (hζ := hζ)) : scalarSpace (F := F) (ζ := ζ) (hζ := hζ) :=
  w.foldr (fun b h => derivative b h) f

def wordSpace (n : ℕ) (f : scalarSpace (F := F) (ζ := ζ) (hζ := hζ)) :
    Submodule ℂ (scalarSpace (F := F) (ζ := ζ) (hζ := hζ)) :=
  Submodule.span ℂ ((fun w => wordVector w f) '' (words (F := F) n : Set (List (B F))))

theorem derivative_mem_wordSpace (n : ℕ) (f : scalarSpace (F := F) (ζ := ζ) (hζ := hζ))
    (b : B F) {v : scalarSpace (F := F) (ζ := ζ) (hζ := hζ)} (hv : v ∈ wordSpace n f) :
    derivative b v ∈ wordSpace (n+1) f := by
  unfold wordSpace at hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨w, hw, rfl⟩ := hv
    apply Submodule.subset_span
    refine ⟨b :: w, ?_, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
  | zero => simpa using (wordSpace (n+1) f).zero_mem
  | add x y hx hy ix iy => simpa using (wordSpace (n+1) f).add_mem ix iy
  | smul c x hx ix => simpa using (wordSpace (n+1) f).smul_mem c ix

theorem translate_word_mem (f : scalarSpace (F := F) (ζ := ζ) (hζ := hζ))
    (k : GInfinity F) (hk : translation k f = f) (w : List (B F)) :
    translation k (wordVector w f) ∈ wordSpace w.length f := by
  induction w with
  | nil =>
    change translation k f ∈ _
    rw [hk]
    exact Submodule.subset_span ⟨[], by simp [words], rfl⟩
  | cons b w ih =>
    change translation k (derivative b (wordVector w f)) ∈ wordSpace (w.length+1) f
    rw [translation_derivative]
    apply Submodule.sum_mem
    intro a ha
    apply Submodule.smul_mem
    exact derivative_mem_wordSpace _ f a ih

theorem wordVector_val (w : List (B F)) (f : scalarSpace (F := F) (ζ := ζ) (hζ := hζ)) :
    (wordVector w f).val = sixWord w f.val := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change KPMsGreenFlux.rightDerivative F ζ hζ b.1 b.2 (wordVector w f).val = _
    rw [ih]
    rfl

theorem sixWord_kFinite (f : G → ℂ) (hf : NativeSmooth f)
    (hk : ∀ (k : KPMsGreenFlux.K F) g,
      f (g * KPMsGreenFlux.compactInsertion F ζ hζ k) = f g)
    (w : List (B F)) : KPMsGreenFlux.KFinite F ζ hζ (sixWord w f) := by
  let v : scalarSpace (F := F) (ζ := ζ) (hζ := hζ) := ⟨f, hf⟩
  let W := wordSpace w.length v
  let W' := W.map (scalarSpace (F := F) (ζ := ζ) (hζ := hζ)).subtype
  have hfg : W.FG := Submodule.fg_span ((words (F := F) w.length).finite_toSet.image _)
  letI : Module.Finite ℂ W' := Module.Finite.of_fg (hfg.map _)
  let S := Submodule.span ℂ (Set.range (fun k : KPMsGreenFlux.K F =>
    fun g => sixWord w f (g * KPMsGreenFlux.compactInsertion F ζ hζ k)))
  have hle : S ≤ W' := by
    apply Submodule.span_le.mpr
    rintro u ⟨k, rfl⟩
    have hkv : translation (fun a => (k a).val) v = v := by
      apply Subtype.ext
      funext g
      exact hk k g
    refine Submodule.mem_map.mpr ⟨translation (fun a => (k a).val) (wordVector w v),
      translate_word_mem v _ hkv w, ?_⟩
    funext g
    change (wordVector w v).val (g * KPMsGreenFlux.compactInsertion F ζ hζ k) = _
    rw [wordVector_val]
  exact Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem actualRightWord_kFinite (f : G → ℂ) (hf : NativeSmooth f)
    (hk : ∀ (k : KPMsGreenFlux.K F) g,
      f (g * KPMsGreenFlux.compactInsertion F ζ hζ k) = f g)
    (w : List (Fin (groupDimension F))) :
    KPMsGreenFlux.KFinite F ζ hζ (actualRightWord F ζ hζ w f) := by
  rw [actual_eq_word]
  exact sixWord_kFinite f hf hk _

end DedekindZetaZeroFree.RawWordKFinite

end
