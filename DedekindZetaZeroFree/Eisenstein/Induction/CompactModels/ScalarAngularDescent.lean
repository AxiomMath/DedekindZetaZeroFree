module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open DedekindZetaZeroFree.KPMsRationalCompactCrossPairing
namespace DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarAngularDescent
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem source_rational (s : ℂ) (f : Source F ζ hζ s)
    (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    f.val (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g) = f.val g := by
  let t : (sourcePolarization F ζ hζ s).H :=
    ⟨KPGlobalTorusFunctionData.s F ζ hζ y, Subgroup.mem_sup_left ⟨y, rfl⟩⟩
  have hc : ((sourcePolarization F ζ hζ s).character t : ℂ) = 1 := by
    change (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ t : ℂ) *
      KPGlobalTorusBorelTwistCompatibility.normPower F ζ hζ s t.val = 1
    rw [KPGlobalCenterRationalCharacter.lambdaR_rational F ζ hζ y t rfl]
    simp [t, KPGlobalTorusBorelTwistCompatibility.normPower,
      KPGlobalTorusBorelTwistCompatibility.delta_rational]
  have hd : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t.val = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf, t,
      KPGlobalTorusBorelTwistCompatibility.delta_rational]
  simpa only [hd, hc, one_mul] using f.property t x g

theorem target_rational (s : ℂ) (f : Target F ζ hζ s)
    (y : Fˣ) (x : KPGlobalTorusFunctionData.Adeles F) (g : G F ζ hζ) :
    f.val (((KPGlobalTorusFunctionData.s F ζ hζ y).val *
      KPGlobalTorusFunctionData.N F ζ hζ x) * g) = f.val g := by
  let f' : Source F ζ hζ (-1 / 3 - s) := ⟨f.val, by
    change f.val ∈ KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
      (sourcePolarization F ζ hζ (-1 / 3 - s))
    change f.val ∈ KPGlobalTorusFunctionData.BorelFunctions F ζ hζ
      (targetExponentPolarization F ζ hζ s)
    rw [← actual_weyl_fibre F ζ hζ s]
    exact f.property⟩
  exact source_rational (-1 / 3 - s) f' y x g

 def quotientLinear {V α : Type*} [AddCommMonoid V] [Module ℂ V]
    (S : Setoid α) (e : V →ₗ[ℂ] (α → ℂ))
    (he : ∀ f a b, S.r a b → e f a = e f b) : V →ₗ[ℂ] (Quotient S → ℂ) where
  toFun f := Quotient.lift (e f) (he f)
  map_add' f g := by
    funext q
    induction q using Quotient.inductionOn with
    | h a => exact congrFun (e.map_add f g) a
  map_smul' c f := by
    funext q
    induction q using Quotient.inductionOn with
    | h a => exact congrFun (e.map_smul c f) a

 theorem eqv_eval {α : Type*} {r : α → α → Prop} {v : α → ℂ}
    (h : ∀ a b, r a b → v a = v b) {a b : α} (hab : Relation.EqvGen r a b) :
    v a = v b := by
  induction hab with
  | rel a b hab => exact h a b hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ij => exact ih.trans ij

def fullSourceSection (D : Iwasawa F ζ hζ) (s : ℂ) :
    Source F ζ hζ s →ₗ[ℂ] (FullOmega F ζ hζ D → ℂ) :=
  quotientLinear (fullAngularSetoid F ζ hζ D)
    { toFun := fun f g => f.val g.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } (by
    intro f a b hab
    apply eqv_eval (v := fun g : NormOne F ζ hζ D => f.val g.val) ?_ hab
    rintro a b ⟨y, x, hb⟩
    rw [hb, source_rational])

def fullTargetSection (D : Iwasawa F ζ hζ) (s : ℂ) :
    Target F ζ hζ s →ₗ[ℂ] (FullOmega F ζ hζ D → ℂ) :=
  quotientLinear (fullAngularSetoid F ζ hζ D)
    { toFun := fun f g => f.val g.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } (by
    intro f a b hab
    apply eqv_eval (v := fun g : NormOne F ζ hζ D => f.val g.val) ?_ hab
    rintro a b ⟨y, x, hb⟩
    rw [hb, target_rational])

@[simp] theorem fullSourceSection_mk (D : Iwasawa F ζ hζ) (s : ℂ)
    (f : Source F ζ hζ s) (g : NormOne F ζ hζ D) :
    fullSourceSection D s f (Quotient.mk _ g) = f.val g.val := rfl

@[simp] theorem fullTargetSection_mk (D : Iwasawa F ζ hζ) (s : ℂ)
    (f : Target F ζ hζ s) (g : NormOne F ζ hζ D) :
    fullTargetSection D s f (Quotient.mk _ g) = f.val g.val := rfl

def sourceAngular (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    fixedPlus F ζ hζ D U →ₗ[ℂ] (Omega F ζ hζ D U → ℂ) :=
  quotientLinear (angularSetoid F ζ hζ D U)
    { toFun := fun f g => f.val.val.val g.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } (by
    intro f a b hab
    apply eqv_eval (v := fun g : NormOne F ζ hζ D => f.val.val.val g.val) ?_ hab
    rintro a b ⟨y, x, u, hb⟩
    rw [hb, f.property, source_rational])

def targetAngular (D : Iwasawa F ζ hζ) (U : Level F ζ hζ) :
    fixedMinus F ζ hζ D U →ₗ[ℂ] (Omega F ζ hζ D U → ℂ) :=
  quotientLinear (angularSetoid F ζ hζ D U)
    { toFun := fun f g => f.val.val.val g.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl } (by
    intro f a b hab
    apply eqv_eval (v := fun g : NormOne F ζ hζ D => f.val.val.val g.val) ?_ hab
    rintro a b ⟨y, x, u, hb⟩
    rw [hb, f.property, target_rational])

@[simp] theorem sourceAngular_mk (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (f : fixedPlus F ζ hζ D U) (g : NormOne F ζ hζ D) :
    sourceAngular D U f (Quotient.mk _ g) = f.val.val.val g.val := rfl

@[simp] theorem targetAngular_mk (D : Iwasawa F ζ hζ) (U : Level F ζ hζ)
    (f : fixedMinus F ζ hζ D U) (g : NormOne F ζ hζ D) :
    targetAngular D U f (Quotient.mk _ g) = f.val.val.val g.val := rfl

def fullSourceAngular (D : Iwasawa F ζ hζ) :
    Vplus F ζ hζ D →ₗ[ℂ] (FullOmega F ζ hζ D → ℂ) :=
  (fullSourceSection D 0).comp (sourceCore F ζ hζ D).subtype

def fullTargetAngular (D : Iwasawa F ζ hζ) :
    Vminus F ζ hζ D →ₗ[ℂ] (FullOmega F ζ hζ D → ℂ) :=
  (fullTargetSection D 0).comp (targetCore F ζ hζ D).subtype

@[simp] theorem fullSourceAngular_mk (D : Iwasawa F ζ hζ)
    (f : Vplus F ζ hζ D) (g : NormOne F ζ hζ D) :
    fullSourceAngular D f (Quotient.mk _ g) = f.val.val g.val := rfl

@[simp] theorem fullTargetAngular_mk (D : Iwasawa F ζ hζ)
    (f : Vminus F ζ hζ D) (g : NormOne F ζ hζ D) :
    fullTargetAngular D f (Quotient.mk _ g) = f.val.val g.val := rfl

end DedekindZetaZeroFree.KPMsRationalCompactCrossPairingProof.ScalarAngularDescent

end
