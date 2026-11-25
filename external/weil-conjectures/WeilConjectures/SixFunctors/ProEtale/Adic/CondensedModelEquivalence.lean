/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
public import WeilConjectures.CategoryTheory.Sites.ModuleLift
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-!
# The two models of `ℓ`-adic sheaves agree

Let `X` be a scheme. There are two models of the category of `ℚ̄_ℓ`-sheaves on `X_proét`:

- the sheaves of `ℚ̄_ℓ,X`-modules `AlgebraicGeometry.ProEtale.AdicSheaf ℓ X`, i.e. module objects
  over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` in sheaves of `ℚ̄_ℓ`-modules;
- module objects in abelian sheaves over the condensed coefficient ring
  `condensedRingObj (Profinite.padicAlgClRingObj ℓ) X = p_X^* ℚ̄_ℓ`.

The forgetful functor `AlgebraicGeometry.ProEtale.AdicSheaf.forgetAb` from the first to module
objects in abelian sheaves over `forgetAb ℚ̄_ℓ,X` is an equivalence: a module object `N` over
`forgetAb ℚ̄_ℓ,X` acquires a `ℚ̄_ℓ`-vector space structure through the constant sections
`ℚ̄_ℓ → ℚ̄_ℓ,X(U)` (`AlgebraicGeometry.ProEtale.AdicSheaf.toWeilSheaf`), for which the action of
`ℚ̄_ℓ,X(U)` on `N(U)` is `ℚ̄_ℓ`-bilinear, `ℚ̄_ℓ,X(U)` being a commutative `ℚ̄_ℓ`-algebra.
This gives a module object over the presheaf of rings `ℚ̄_ℓ,X`
(`AlgebraicGeometry.ProEtale.AdicSheaf.presheafMod`) whose sheafification is an `ℓ`-adic sheaf
with image `N` under `forgetAb`. Morphisms of module
objects over `forgetAb ℚ̄_ℓ,X` are automatically `ℚ̄_ℓ`-linear, since scalars act as constant
sections. Composing with the restriction of scalars along the isomorphism of ring objects
`p_X^* ℚ̄_ℓ ≅ forgetAb ℚ̄_ℓ,X` gives the comparison of the two models.

## Main results

- `AlgebraicGeometry.ProEtale.AdicSheaf.isEquivalence_forgetAb`: `forgetAb` is an equivalence.
- `AlgebraicGeometry.ProEtale.AdicSheaf.forgetAbEquivalence`: the equivalence
  `AdicSheaf ℓ X ≌ Mod (Sheaf (ProEt.topology X) Ab) (forgetAb ℚ̄_ℓ,X)`.
- `AlgebraicGeometry.ProEtale.condensedRingObjIsoForgetAb`: the isomorphism of ring objects
  `p_X^* ℚ̄_ℓ ≅ forgetAb ℚ̄_ℓ,X`.
- `AlgebraicGeometry.ProEtale.adicSheafEquivCondensedMod`: the equivalence
  `AdicSheaf ℓ X ≌ Mod (Sheaf (ProEt.topology X) Ab) (condensedRingObj (padicAlgClRingObj ℓ) X)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal
open scoped Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X : Scheme.{u}}

namespace AdicSheaf

/-- The action `a • m` of a locally finite function `a ∈ ℚ̄_ℓ,X(U)` on a section `m ∈ N(U)` of a
module object `N` over `forgetAb ℚ̄_ℓ,X` in abelian sheaves: the action
`forgetAb ℚ̄_ℓ,X ⊗ N ⟶ N` restricted along the comparison with the objectwise tensor product. -/
noncomputable def abSectionAct (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X))) {U : X.ProEtᵒᵖ}
    (a : (adicConstantSheaf l X).obj.obj U) (m : N.X.obj.obj U) : N.X.obj.obj U :=
  (Mod.act N.X).hom.app U
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X).app U
      ((a : ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)).obj.obj U) ⊗ₜ m))

variable (l X) in
/-- On underlying presheaves, the multiplication of the ring object `forgetAb ℚ̄_ℓ,X` is the
objectwise multiplication of `ℚ̄_ℓ,X`. -/
lemma μ_sheafToPresheaf_comp_map_mul_forgetAb :
    Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X))
        ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) ≫
      (sheafToPresheaf _ _).map μ[(weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)] =
    Functor.LaxMonoidal.μ ((Functor.whiskeringRight _ _ _).obj
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})) (adicConstantSheaf l X).obj
        (adicConstantSheaf l X).obj ≫
      ((Functor.whiskeringRight _ _ _).obj
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).map μ[(adicConstantSheaf l X).obj] := by
  rw [Functor.obj.μ_def, Functor.map_comp, ← Category.assoc,
    Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose, Category.assoc,
    ← adicConstantSheaf_μ_comp_map_mul' X, Functor.map_comp]
  rfl

variable (l X) in
/-- On underlying presheaves, the unit of the ring object `forgetAb ℚ̄_ℓ,X` is the objectwise
unit of `ℚ̄_ℓ,X`. -/
lemma ε_sheafToPresheaf_comp_map_one_forgetAb :
    Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
      (sheafToPresheaf _ _).map η[(weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)] =
    Functor.LaxMonoidal.ε ((Functor.whiskeringRight _ _ _).obj
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})) ≫
      ((Functor.whiskeringRight _ _ _).obj
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).map η[(adicConstantSheaf l X).obj] := by
  rw [Functor.obj.η_def, Functor.map_comp, ← Category.assoc,
    Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose, Category.assoc,
    ← adicConstantSheaf_ε_comp_map_one' X, Functor.map_comp]
  rfl

variable (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X))) {U : X.ProEtᵒᵖ}

/-- The action on sections is associative: `(a * b) • m = a • (b • m)`. -/
lemma abSectionAct_mul (a b : (adicConstantSheaf l X).obj.obj U) (m : N.X.obj.obj U) :
    abSectionAct N (ULift.up (a.down * b.down)) m = abSectionAct N a (abSectionAct N b m) := by
  let := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).modObjObj
    (A := (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X
  have h := congrArg (fun g ↦ g.app U ((a ⊗ₜ b) ⊗ₜ m))
    (Mod.mul_act (A := (sheafToPresheaf _ _).obj
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)))
      ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj N.X))
  rw [Functor.obj.μ_def, μ_sheafToPresheaf_comp_map_mul_forgetAb] at h
  exact h

/-- The constant function `1` acts trivially. -/
lemma abSectionAct_one (m : N.X.obj.obj U) :
    abSectionAct N (ULift.up 1) m = m := by
  let := (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).modObjObj
    (A := (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X
  have h := congrArg (fun g ↦ g.app U (ULift.up (1 : ℤ) ⊗ₜ m))
    (Mod.one_act (A := (sheafToPresheaf _ _).obj
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)))
      ((sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj N.X))
  rw [Functor.obj.η_def, ε_sheafToPresheaf_comp_map_one_forgetAb] at h
  refine Eq.trans ?_ (h.trans (one_zsmul m))
  refine (congrArg (abSectionAct N · m) (?_ : _ = η[(adicConstantSheaf l X).obj].app U
    ((Functor.LaxMonoidal.ε ((Functor.whiskeringRight _ _ _).obj
      (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}))).app U (ULift.up 1)))).trans rfl
  rw [adicConstantSheaf_one_app]
  refine ULift.ext ?_
  exact ((congrArg (algebraMap _ _) (one_zsmul (1 : PadicAlgCl l))).trans (map_one _)).symm

lemma abSectionAct_add (a : (adicConstantSheaf l X).obj.obj U) (x y : N.X.obj.obj U) :
    abSectionAct N a (x + y) = abSectionAct N a x + abSectionAct N a y := by
  simp only [abSectionAct, TensorProduct.tmul_add, map_add]

lemma add_abSectionAct (a b : (adicConstantSheaf l X).obj.obj U) (x : N.X.obj.obj U) :
    abSectionAct N (a + b) x = abSectionAct N a x + abSectionAct N b x := by
  simp only [abSectionAct, TensorProduct.add_tmul, map_add]

lemma zero_abSectionAct (x : N.X.obj.obj U) : abSectionAct N 0 x = 0 := by
  simp only [abSectionAct, TensorProduct.zero_tmul, map_zero]

/-- The action on sections is compatible with restriction. -/
lemma map_abSectionAct {V : X.ProEtᵒᵖ} (f : U ⟶ V)
    (a : (adicConstantSheaf l X).obj.obj U) (x : N.X.obj.obj U) :
    N.X.obj.map f (abSectionAct N a x) =
      abSectionAct N ((adicConstantSheaf l X).obj.map f a) (N.X.obj.map f x) := by
  have h1 := NatTrans.naturality_apply (Mod.act N.X).hom f
    ((Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X).app U
      ((a : ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)).obj.obj U) ⊗ₜ x))
  have h2 := NatTrans.naturality_apply
    (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X) f
    ((a : ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)).obj.obj U) ⊗ₜ x)
  rw [abSectionAct, ← h1]
  erw [← h2]
  rfl

/-- The action on sections is compatible with morphisms of module objects. -/
lemma hom_abSectionAct {N' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X))} (φ : N ⟶ N')
    (a : (adicConstantSheaf l X).obj.obj U) (x : N.X.obj.obj U) :
    φ.hom.hom.app U (abSectionAct N a x) = abSectionAct N' a (φ.hom.hom.app U x) := by
  have h := congrArg (fun g ↦ (Functor.LaxMonoidal.μ (sheafToPresheaf
    (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) N.X ≫
        (sheafToPresheaf _ _).map g).app U
      ((a : ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)).obj.obj U) ⊗ₜ x))
    (Mod.act_hom φ)
  simp only [Functor.map_comp, ← μ_natural_right_assoc] at h
  exact h

lemma abSectionAct_zero (a : (adicConstantSheaf l X).obj.obj U) : abSectionAct N a 0 = 0 := by
  simp only [abSectionAct, TensorProduct.tmul_zero, map_zero]

variable (U) in
/-- The constant function with value `c`, a section of `ℚ̄_ℓ,X` over `U`. -/
noncomputable abbrev constScalarSection (c : ULift.{u + 1} (PadicAlgCl l)) :
    (adicConstantSheaf l X).obj.obj U :=
  ULift.up (algebraMap _ _ c.down)

/-- Restrictions of constant sections are constant. -/
lemma map_constScalarSection {V : X.ProEtᵒᵖ} (f : U ⟶ V) (c : ULift.{u + 1} (PadicAlgCl l)) :
    (adicConstantSheaf l X).obj.map f (constScalarSection U c) = constScalarSection V c :=
  rfl

/-- The action of the constant section `c` on a module object over `forgetAb ℚ̄_ℓ,X`, as an
endomorphism of the underlying abelian sheaf. -/
noncomputable def constAct (c : ULift.{u + 1} (PadicAlgCl l)) : N.X ⟶ N.X :=
  { hom :=
    { app U := AddCommGrpCat.ofHom
        { toFun := abSectionAct N (constScalarSection U c)
          map_zero' := abSectionAct_zero N _
          map_add' := abSectionAct_add N _ }
      naturality _ _ f := AddCommGrpCat.ext fun x ↦
        ((map_abSectionAct N f _ x).trans
          (congrArg (abSectionAct N · _) (map_constScalarSection f c))).symm } }

lemma constAct_app (c : ULift.{u + 1} (PadicAlgCl l)) (x : N.X.obj.obj U) :
    (constAct N c).hom.app U x = abSectionAct N (constScalarSection U c) x :=
  rfl

/-- The constant sections act on a module object over `forgetAb ℚ̄_ℓ,X` through a ring
homomorphism `ℚ̄_ℓ →+* End N`. -/
noncomputable def constActRingHom : ULift.{u + 1} (PadicAlgCl l) →+* End N.X where
  toFun c := End.of (constAct N c)
  map_one' := End.ext (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ AddCommGrpCat.ext fun x ↦
    (congrArg (abSectionAct N · x) (congrArg ULift.up (map_one _))).trans
      (abSectionAct_one N x))))
  map_mul' _ _ := End.ext (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ AddCommGrpCat.ext fun x ↦
    (congrArg (abSectionAct N · x) (congrArg ULift.up (map_mul _ _ _))).trans
      (abSectionAct_mul N _ _ x))))
  map_zero' := End.ext (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ AddCommGrpCat.ext fun x ↦
    (congrArg (abSectionAct N · x) (congrArg ULift.up (map_zero _))).trans
      (zero_abSectionAct N x))))
  map_add' _ _ := End.ext (Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ AddCommGrpCat.ext fun x ↦
    (congrArg (abSectionAct N · x) (congrArg ULift.up (map_add _ _ _))).trans
      (add_abSectionAct N _ _ x))))

/-- Morphisms of module objects over `forgetAb ℚ̄_ℓ,X` commute with the action of the constant
sections. -/
lemma constAct_comp_hom {N' : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X))} (φ : N ⟶ N')
    (c : ULift.{u + 1} (PadicAlgCl l)) :
    (constActRingHom N c).asHom ≫ φ.hom = φ.hom ≫ (constActRingHom N' c).asHom :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ ↦ AddCommGrpCat.ext fun x ↦
    hom_abSectionAct N φ _ x))

variable (l X) in
/-- A module object over `forgetAb ℚ̄_ℓ,X` in abelian sheaves, regarded as a sheaf of
`ℚ̄_ℓ`-modules: `ℚ̄_ℓ` acts through the constant sections. -/
noncomputable def toWeilSheaf :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) ⥤
      Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l) :=
  Sheaf.moduleLift (Mod.forget _) constActRingHom (fun φ c ↦ constAct_comp_hom _ φ c)

/-- Scalars act on the sections of `toWeilSheaf N` as constant sections. -/
lemma toWeilSheaf_smul (c : ULift.{u + 1} (PadicAlgCl l))
    (x : ((toWeilSheaf l X).obj N).obj.obj U) :
    c • x = abSectionAct N (constScalarSection U c) x :=
  rfl

/-- The `ℚ̄_ℓ`-vector space structure of `ℚ̄_ℓ,X(U)` is multiplication by constant sections. -/
lemma smul_eq_constSection_mul (c : ULift.{u + 1} (PadicAlgCl l))
    (a : (adicConstantSheaf l X).obj.obj U) :
    c • a = ULift.up ((constScalarSection U c).down * a.down) :=
  ULift.ext (Algebra.smul_def c.down a.down)

variable (U) in
/-- The action of `ℚ̄_ℓ,X(U)` on the sections over `U` of a module object over
`forgetAb ℚ̄_ℓ,X`, as a map out of the tensor product of `ℚ̄_ℓ`-modules. -/
noncomputable def weilActApp :
    (adicConstantSheaf l X).obj.obj U ⊗ ((toWeilSheaf l X).obj N).obj.obj U ⟶
      ((toWeilSheaf l X).obj N).obj.obj U :=
  ModuleCat.MonoidalCategory.tensorLift (fun a x ↦ abSectionAct N a x)
    (fun a b x ↦ add_abSectionAct N a b x)
    (fun c a x ↦ by
      rw [smul_eq_constSection_mul, abSectionAct_mul]
      rfl)
    (fun a x y ↦ abSectionAct_add N a x y)
    (fun c a x ↦ by
      rw [toWeilSheaf_smul, toWeilSheaf_smul, ← abSectionAct_mul, ← abSectionAct_mul, mul_comm])

lemma weilActApp_tmul (a : (adicConstantSheaf l X).obj.obj U)
    (x : ((toWeilSheaf l X).obj N).obj.obj U) :
    (weilActApp N U).hom (a ⊗ₜ x) = abSectionAct N a x :=
  rfl

/-- The action of `ℚ̄_ℓ,X` on the underlying presheaf of `ℚ̄_ℓ`-modules. -/
noncomputable def weilAct :
    (adicConstantSheaf l X).obj ⊗ ((toWeilSheaf l X).obj N).obj ⟶
      ((toWeilSheaf l X).obj N).obj where
  app U := weilActApp N U
  naturality _ _ f := ModuleCat.MonoidalCategory.tensor_ext fun a x ↦
    (map_abSectionAct N f a x).symm

/-- A module object over `forgetAb ℚ̄_ℓ,X`, as a module object over the presheaf of rings
`ℚ̄_ℓ,X` in presheaves of `ℚ̄_ℓ`-modules. -/
noncomputable def presheafMod :
    Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj :=
  letI : ModObj (adicConstantSheaf l X).obj ((toWeilSheaf l X).obj N).obj :=
    ModObj.mk' _ (weilAct N)
      (NatTrans.ext (funext fun _ ↦ ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl))
      (NatTrans.ext (funext fun _ ↦ ModuleCat.MonoidalCategory.tensor_ext₃' fun a b x ↦
        abSectionAct_mul N a b x))
  ⟨((toWeilSheaf l X).obj N).obj⟩

variable (l X) in
/-- The comparison `sheafify ℚ̄_ℓ,X ⟶ ℚ̄_ℓ,X` is an isomorphism. -/
instance isIso_homEquiv_symm_adicConstantSheafObjMonHom :
    IsIso (((sheafificationAdjunction (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).homEquiv
      _ _).symm (adicConstantSheafObjMonHom X l).hom) := by
  rw [Adjunction.homEquiv_counit]
  exact IsIso.comp_isIso' (Functor.map_isIso _ (𝟙 _)) inferInstance

variable (l X) in
/-- Sheafification of module objects over the presheaf of rings `ℚ̄_ℓ,X`. -/
noncomputable abbrev sheafifyMod :
    Mod (X.ProEtᵒᵖ ⥤ WeilCoefficients.{u} l) (adicConstantSheaf l X).obj ⥤ AdicSheaf l X :=
  (sheafificationAdjunction (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).modLeft
    (adicConstantSheafObjMonHom X l).hom

/-- The unit of the sheafification adjunction of module objects at `presheafMod N`. -/
noncomputable def presheafModUnit :
    presheafMod N ⟶ ((sheafificationAdjunction _ _).modRight
      (adicConstantSheafObjMonHom X l).hom).obj ((sheafifyMod l X).obj (presheafMod N)) :=
  ((sheafificationAdjunction _ _).modAdjunction (adicConstantSheafObjMonHom X l).hom).unit.app _

lemma presheafModUnit_hom :
    (presheafModUnit N).hom = toSheafify _ ((toWeilSheaf l X).obj N).obj := by
  rw [presheafModUnit, ← Adjunction.homEquiv_id, Adjunction.modAdjunction_homEquiv_apply_hom,
    Adjunction.homEquiv_unit]
  exact Category.comp_id _

instance isIso_presheafModUnit_hom : IsIso (presheafModUnit N).hom := by
  rw [presheafModUnit_hom]
  exact isIso_toSheafify _ ((toWeilSheaf l X).obj N).property

/-- The underlying sheaf of the sheafification of `presheafMod N` is `toWeilSheaf N`. -/
noncomputable def sheafifyModXIso :
    ((sheafifyMod l X).obj (presheafMod N)).X ≅ (toWeilSheaf l X).obj N :=
  ((fullyFaithfulSheafToPresheaf _ _).preimageIso (asIso (presheafModUnit N).hom)).symm

/-- On underlying presheaves, `sheafifyModXIso N` is the inverse of the unit of sheafification. -/
lemma sheafToPresheaf_map_sheafifyModXIso_hom :
    (sheafToPresheaf _ _).map (sheafifyModXIso N).hom = inv (presheafModUnit N).hom :=
  (fullyFaithfulSheafToPresheaf _ _).map_preimage _

variable (l X) in
/-- The comparison of the two ring structures on the presheaf `ℚ̄_ℓ,X` is the identity. -/
lemma adicConstantSheafObjMonHom_hom : (adicConstantSheafObjMonHom X l).hom = 𝟙 _ :=
  rfl

/-- The action of the sheafification of `presheafMod N`, transported along `sheafifyModXIso N`,
restricts to the action `weilAct N` on the objectwise tensor product. -/
lemma μ_comp_map_act_comp_map_sheafifyModXIso_hom :
    Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l))
        (adicConstantSheaf l X) ((sheafifyMod l X).obj (presheafMod N)).X ≫
      (sheafToPresheaf _ _).map (Mod.act ((sheafifyMod l X).obj (presheafMod N)).X) ≫
      (sheafToPresheaf _ _).map (sheafifyModXIso N).hom =
    (adicConstantSheaf l X).obj ◁ (sheafToPresheaf _ _).map (sheafifyModXIso N).hom ≫
      weilAct N := by
  have h := Mod.act_hom (presheafModUnit N)
  have h' : Mod.act (((sheafificationAdjunction _ _).modRight
      (adicConstantSheafObjMonHom X l).hom).obj ((sheafifyMod l X).obj (presheafMod N))).X =
      𝟙 (adicConstantSheaf l X).obj ▷ _ ≫
        Functor.LaxMonoidal.μ (sheafToPresheaf _ _) (adicConstantSheaf l X)
          ((sheafifyMod l X).obj (presheafMod N)).X ≫
        (sheafToPresheaf _ _).map (Mod.act ((sheafifyMod l X).obj (presheafMod N)).X) :=
    rfl
  rw [h', id_whiskerRight, Category.id_comp] at h
  rw [sheafToPresheaf_map_sheafifyModXIso_hom,
    ← cancel_epi ((adicConstantSheaf l X).obj ◁ (presheafModUnit N).hom),
    ← whiskerLeft_comp_assoc, IsIso.hom_inv_id, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  have h2 := congrArg (· ≫ inv (presheafModUnit N).hom) h
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h2
  exact h2.symm

/-- A module object over `forgetAb ℚ̄_ℓ,X` is the image under `forgetAb` of the sheafification
of `presheafMod N`. -/
noncomputable def forgetAbObjSheafifyModIso :
    (forgetAb l X).obj ((sheafifyMod l X).obj (presheafMod N)) ≅ N :=
  Mod.isoMk ((weilCoefficientsForgetAb l X).mapIso (sheafifyModXIso N)) (by
    refine Sheaf.tensor_hom_ext ?_
    have key := (Functor.whiskeringRight _ _ _).obj (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})
      |>.congr_map (μ_comp_map_act_comp_map_sheafifyModXIso_hom N)
    have K := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
      (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}) (adicConstantSheaf l X)
      ((sheafifyMod l X).obj (presheafMod N)).X
    rw [Functor.act_mapMod_obj, Functor.map_comp, Functor.map_comp, Functor.map_comp,
      ← μ_natural_right_assoc, Category.assoc]
    erw [reassoc_of% K]
    have hF {P Q : Sheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)} (f : P ⟶ Q) :
        (sheafToPresheaf _ Ab.{u + 1}).map ((weilCoefficientsForgetAb l X).map f) =
          ((Functor.whiskeringRight _ _ _).obj (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).map
            ((sheafToPresheaf _ _).map f) :=
      rfl
    rw [Functor.mapIso_hom, hF, hF, ← Functor.map_comp, ← Functor.map_comp, key]
    refine NatTrans.ext (funext fun U ↦ AddCommGrpCat.hom_ext_toIntLinearMap
      (TensorProduct.ext' fun a x ↦ ?_))
    rfl)

variable (M : AdicSheaf l X)

/-- The action of `ℚ̄_ℓ,X` on the sections of `forgetAb M` is the action of `ℚ̄_ℓ,X` on
the sections of `M`. -/
lemma abSectionAct_forgetAb_obj (a : (adicConstantSheaf l X).obj.obj U) (x : M.X.obj.obj U) :
    abSectionAct ((forgetAb l X).obj M) a x =
      (Mod.act M.X).hom.app U ((Functor.LaxMonoidal.μ (sheafToPresheaf
        (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) (adicConstantSheaf l X) M.X).app U
          (a ⊗ₜ x)) := by
  have K := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose (Scheme.ProEt.topology X)
    (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}) (adicConstantSheaf l X) M.X
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (K =≫ (sheafToPresheaf _ Ab.{u + 1}).map ((weilCoefficientsForgetAb l X).map (Mod.act M.X)))
    U) ((a : ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)).obj.obj U) ⊗ₜ x)
  simp only [Category.assoc, ← Functor.map_comp] at h
  exact h

/-- The constant sections act on the sections of an `ℓ`-adic sheaf through its `ℚ̄_ℓ`-vector
space structure. -/
lemma act_μ_constSection_tmul (c : ULift.{u + 1} (PadicAlgCl l)) (x : M.X.obj.obj U) :
    (Mod.act M.X).hom.app U ((Functor.LaxMonoidal.μ (sheafToPresheaf
        (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)) (adicConstantSheaf l X) M.X).app U
          (constScalarSection U c ⊗ₜ x)) = c • x := by
  let := (sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).modObjObj
    (A := adicConstantSheaf l X) M.X
  have h := congrArg (fun g ↦ g.app U (c ⊗ₜ x))
    (Mod.one_act (A := (sheafToPresheaf _ _).obj (adicConstantSheaf l X))
      ((sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)).obj M.X))
  rw [Functor.obj.η_def, adicConstantSheaf_ε_comp_map_one'] at h
  exact h

/-- The action of a constant section on the sections of `forgetAb M` is scalar
multiplication. -/
lemma abSectionAct_forgetAb_obj_constSection (c : ULift.{u + 1} (PadicAlgCl l))
    (x : M.X.obj.obj U) :
    abSectionAct ((forgetAb l X).obj M) (constScalarSection U c) x = c • x :=
  (abSectionAct_forgetAb_obj M _ x).trans (act_μ_constSection_tmul M c x)

variable {M} {M' : AdicSheaf l X}

/-- A morphism of module objects `forgetAb M ⟶ forgetAb M'` is `ℚ̄_ℓ`-linear on sections. -/
noncomputable def sheafHomOfForgetAb (f : (forgetAb l X).obj M ⟶ (forgetAb l X).obj M') :
    M.X ⟶ M'.X :=
  { hom :=
    { app U := ModuleCat.ofHom
        { toFun := f.hom.hom.app U
          map_add' := map_add _
          map_smul' := fun c x ↦ by
            rw [← abSectionAct_forgetAb_obj_constSection, RingHom.id_apply,
              ← abSectionAct_forgetAb_obj_constSection]
            exact hom_abSectionAct _ f _ x }
      naturality _ _ φ := ModuleCat.hom_ext (LinearMap.ext fun x ↦
        ConcreteCategory.congr_hom (f.hom.hom.naturality φ) x) } }

/-- The components of `sheafHomOfForgetAb f` are those of `f`. -/
lemma sheafHomOfForgetAb_app (f : (forgetAb l X).obj M ⟶ (forgetAb l X).obj M')
    (x : M.X.obj.obj U) : (sheafHomOfForgetAb f).hom.app U x = f.hom.hom.app U x :=
  rfl

/-- A morphism of module objects `forgetAb M ⟶ forgetAb M'` is a morphism of `ℓ`-adic
sheaves. -/
noncomputable def homOfForgetAb (f : (forgetAb l X).obj M ⟶ (forgetAb l X).obj M') : M ⟶ M' :=
  Mod.homMk (sheafHomOfForgetAb f) (by
    refine Sheaf.tensor_hom_ext ?_
    rw [Functor.map_comp, Functor.map_comp, ← μ_natural_right_assoc]
    refine NatTrans.ext (funext fun U ↦ ModuleCat.MonoidalCategory.tensor_ext fun a x ↦ ?_)
    have h := hom_abSectionAct _ f a x
    rw [abSectionAct_forgetAb_obj, abSectionAct_forgetAb_obj] at h
    exact h)

/-- `forgetAb` is faithful, since forgetting to abelian groups is faithful. -/
instance faithful_forgetAb : (forgetAb l X).Faithful where
  map_injective {M M'} _ _ h := by
    refine Mod.hom_ext _ _ (Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
      ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_))))
    have h' := NatTrans.congr_app (congrArg
      (fun φ : (forgetAb l X).obj M ⟶ (forgetAb l X).obj M' ↦ φ.hom.hom) h) U
    exact ConcreteCategory.congr_hom h' x

/-- `forgetAb` is full: morphisms of module objects over `forgetAb ℚ̄_ℓ,X` are `ℚ̄_ℓ`-linear. -/
instance full_forgetAb : (forgetAb l X).Full where
  map_surjective f := ⟨homOfForgetAb f, Mod.hom_ext _ _ (Sheaf.hom_ext rfl)⟩

/-- `forgetAb` is essentially surjective: a module object `N` is the image of the sheafification
of `presheafMod N`. -/
instance essSurj_forgetAb : (forgetAb l X).EssSurj where
  mem_essImage N := ⟨(sheafifyMod l X).obj (presheafMod N), ⟨forgetAbObjSheafifyModIso N⟩⟩

/-- **The forgetful functor from `ℓ`-adic sheaves to module objects over `forgetAb ℚ̄_ℓ,X` in
abelian sheaves is an equivalence.** -/
instance isEquivalence_forgetAb : (forgetAb l X).IsEquivalence where

variable (l X) in
/-- The equivalence between `ℓ`-adic sheaves and module objects over `forgetAb ℚ̄_ℓ,X` in abelian
sheaves. -/
noncomputable abbrev forgetAbEquivalence :
    AdicSheaf l X ≌ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X)) :=
  (forgetAb l X).asEquivalence

end AdicSheaf
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- The isomorphism of ring objects between the condensed model `p_X^* ℚ̄_ℓ` of `ℚ̄_ℓ,X` and
the image `forgetAb ℚ̄_ℓ,X` of the constant `ℓ`-adic sheaf. -/
noncomputable def condensedRingObjIsoForgetAb :
    condensedRingObj (Profinite.padicAlgClRingObj l) X ≅
      (weilCoefficientsForgetAb l X).obj (adicConstantSheaf l X) :=
  (Mon.forget _).mapIso (CondensedQbarCoefficientRealization.globalCoefficientIso l X) ≪≫
    padicAlgClSheafIsoAdicConstantSheaf X l

instance isMonHom_condensedRingObjIsoForgetAb_hom :
    IsMonHom (condensedRingObjIsoForgetAb l X).hom :=
  inferInstanceAs (IsMonHom
    ((CondensedQbarCoefficientRealization.globalCoefficientIso l X).hom.hom ≫
      padicAlgClSheafToAdicConstantSheaf X l))

/-- **The two models of `ℓ`-adic sheaves agree**: `ℓ`-adic sheaves on `X`, i.e. module objects
over `ℚ̄_ℓ,X` in sheaves of `ℚ̄_ℓ`-modules on `X_proét`, are equivalent to module
objects over the condensed coefficient ring `p_X^* ℚ̄_ℓ` in abelian sheaves on `X_proét`. -/
noncomputable def adicSheafEquivCondensedMod :
    AdicSheaf l X ≌ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X) :=
  (AdicSheaf.forgetAbEquivalence l X).trans
    (Mod.comapEquivalenceOfIsIso (condensedRingObjIsoForgetAb l X).hom)

end AlgebraicGeometry.ProEtale
