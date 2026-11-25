/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.Monoidal.Mod.PointSMul
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.SixFunctors.ProEtale.Adic.Hom
public import WeilConjectures.SixFunctors.ProEtale.Adic.SectionAction

/-!
# Multiplication by a global section on `ℓ`-adic sheaves

A global section `f` of the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X` acts on every sheaf of
`ℚ̄_ℓ,X`-modules by `ℚ̄_ℓ,X`-linear endomorphisms, `ℚ̄_ℓ,X` being commutative: this is a natural
endomorphism of the identity functor (`AlgebraicGeometry.ProEtale.AdicSheaf.globalSMul`), acting on
sections over `U` by `x ↦ f|_U • x` (`AlgebraicGeometry.ProEtale.AdicSheaf.globalSMul_app_apply`).

For a morphism `g : Z ⟶ Y`, the pushforward `g_*` carries the multiplication by a global section
`f'` of `ℚ̄_ℓ,Z` lying over a global section `f` of `ℚ̄_ℓ,Y` to the multiplication by `f`
(`AlgebraicGeometry.ProEtale.AdicSheaf.adicLowerStar_map_globalSMul_app`), hence so do its right
derived functors
(`AlgebraicGeometry.ProEtale.AdicSheaf.rightDerived_adicLowerStar_map_globalSMul_app`). This
applies to `f' = f ∘ g` (`AlgebraicGeometry.ProEtale.AdicSheaf.pullbackGlobalSection`), giving
`Rⁱg_*(f ∘ g) = f` on `Rⁱg_*`
(`AdicSheaf.rightDerived_adicLowerStar_map_globalSMul_pullbackGlobalSection`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale.AdicSheaf

variable {l : ℕ} [Fact l.Prime]

section Point

variable {X : Scheme.{u}} (f : (adicConstantSheaf l X).obj.obj (op (proEtTop X)))

/-- The point `𝟙 ⟶ ℚ̄_ℓ,X` of the constant `ℓ`-adic sheaf attached to a global section `f`. -/
noncomputable def globalSectionPoint : 𝟙_ _ ⟶ adicConstantSheaf l X :=
  η[adicConstantSheaf l X] ≫ sectionSheafHom (unit l X) f

/-- **Multiplication by a global section** `f` of `ℚ̄_ℓ,X`, as a natural endomorphism of the
identity functor of sheaves of `ℚ̄_ℓ,X`-modules. -/
noncomputable def globalSMul : 𝟭 (AdicSheaf l X) ⟶ 𝟭 (AdicSheaf l X) :=
  Mod.pointSMul (globalSectionPoint f)

lemma globalSMul_app_hom (F : AdicSheaf l X) :
    ((globalSMul f).app F).hom = Mod.pointSMulHom (globalSectionPoint f) F.X :=
  rfl

end Point

section LowerStar

open scoped Obj

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) {f : (adicConstantSheaf l Y).obj.obj (op (proEtTop Y))}
  {f' : (adicConstantSheaf l Z).obj.obj (op (proEtTop Z))}
  (hf : sectionSheafHom (unit l Y) f ≫ adicConstantSheafToLowerStar l g =
    adicConstantSheafToLowerStar l g ≫
      (g)_*[WeilCoefficients.{u} l].map (sectionSheafHom (unit l Z) f'))

include hf in
lemma globalSectionPoint_comp_adicConstantSheafToLowerStar :
    globalSectionPoint f ≫ adicConstantSheafToLowerStar l g =
      ε (g)_*[WeilCoefficients.{u} l] ≫
        (g)_*[WeilCoefficients.{u} l].map (globalSectionPoint f') := by
  rw [globalSectionPoint, Category.assoc, hf]
  rw [IsMonHom.one_hom_assoc]
  rw [globalSectionPoint, Functor.map_comp]
  rfl

include hf in
/-- **The pushforward intertwines the multiplications by global sections** `f'` of `ℚ̄_ℓ,Z` and
`f` of `ℚ̄_ℓ,Y`, when `f'` lies over `f`. -/
lemma adicLowerStar_map_globalSMul_app (N : AdicSheaf l Z) :
    (g)_*ᵃ[l].map ((globalSMul f').app N) = (globalSMul f).app ((g)_*ᵃ[l].obj N) :=
  Mod.hom_ext _ _ (Mod.map_pointSMulHom (g)_*[WeilCoefficients.{u} l]
    (adicConstantSheafToLowerStar l g)
    (globalSectionPoint_comp_adicConstantSheafToLowerStar g hf) N).symm

include hf in
/-- **The right derived functors of the pushforward intertwine the multiplications by global
sections** `f'` of `ℚ̄_ℓ,Z` and `f` of `ℚ̄_ℓ,Y`, when `f'` lies over `f`. -/
lemma rightDerived_adicLowerStar_map_globalSMul_app (i : ℕ) (N : AdicSheaf l Z) :
    ((g)_*ᵃ[l].rightDerived i).map ((globalSMul f').app N) =
      (globalSMul f).app (((g)_*ᵃ[l].rightDerived i).obj N) :=
  Functor.rightDerived_map_app_eq _ _ _ (adicLowerStar_map_globalSMul_app g hf) i N

end LowerStar

section Sections

variable {X : Scheme.{u}} (f : (adicConstantSheaf l X).obj.obj (op (proEtTop X)))

/-- On sections over `U`, the multiplication by a global section `f` is `x ↦ f|_U • x`. -/
lemma globalSMul_app_apply (F : AdicSheaf l X) (U : X.ProEtᵒᵖ) (x : F.X.obj.obj U) :
    ((globalSMul f).app F).hom.hom.app U x = sectionAct F (restrictTop (unit l X) f U) x := by
  let P := sheafToPresheaf (Scheme.ProEt.topology X) (WeilCoefficients.{u} l)
  have h1 : P.map (Mod.pointSMulHom (globalSectionPoint f) F.X) =
      (λ_ (P.obj F.X)).inv ≫ (η[(adicConstantSheaf l X).obj] ≫
        P.map (sectionSheafHom (unit l X) f)) ▷ P.obj F.X ≫
        Functor.LaxMonoidal.μ P (adicConstantSheaf l X) F.X ≫ P.map (Mod.act F.X) := by
    rw [← adicConstantSheaf_ε_comp_map_one', Category.assoc, ← P.map_comp, ← globalSectionPoint,
      Mod.pointSMulHom, P.map_comp, P.map_comp, ← left_unitality_inv, comp_whiskerRight]
    simp only [Category.assoc]
    rw [← μ_natural_left_assoc]
  have h3 := congrArg (fun φ ↦ φ.app U x) h1
  dsimp only at h3
  refine h3.trans ?_
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  have e1 : (λ_ (P.obj F.X)).inv.app U x = (1 : ULift.{u + 1} (PadicAlgCl l)) ⊗ₜ x :=
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply x
  rw [e1]
  erw [ModuleCat.MonoidalCategory.whiskerRight_apply]
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply]
  have e2 : (P.map ((unit l X).sectionSheafHom f)).app U
      ((η[(adicConstantSheaf l X).obj]).app U (1 : ULift.{u + 1} (PadicAlgCl l))) =
        restrictTop (unit l X) f U :=
    (algebraMap_sectionAct (unit l X) (U := U) (ULift.up 1) (restrictTop (unit l X) f U)).trans
      (one_smul _ _)
  exact congrArg (fun r ↦ sectionAct F r x) e2

end Sections


section Unit

variable {X : Scheme.{u}} {U : X.ProEtᵒᵖ}

/-- The action of `ℚ̄_ℓ,X` on itself is the multiplication of functions. -/
lemma sectionAct_unit (a b : (adicConstantSheaf l X).obj.obj U) :
    sectionAct (unit l X) a b = ULift.up (a.down * b.down) :=
  congrArg (fun g ↦ g.app U (a ⊗ₜ b)) (adicConstantSheaf_μ_comp_map_mul' (l := l) X)

end Unit

section Pullback

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y) (f : (adicConstantSheaf l Y).obj.obj (op (proEtTop Y)))

/-- The pullback `f ∘ g` of a global section `f` of `ℚ̄_ℓ,Y` along `g : Z ⟶ Y`. -/
noncomputable def pullbackGlobalSection : (adicConstantSheaf l Z).obj.obj (op (proEtTop Z)) :=
  ULift.up (PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom f.down)

/-- The pullback `f ∘ g` of a global section `f` lies over `f`. -/
lemma sectionSheafHom_pullbackGlobalSection :
    sectionSheafHom (unit l Y) f ≫ adicConstantSheafToLowerStar l g =
      adicConstantSheafToLowerStar l g ≫
        (g)_*[WeilCoefficients.{u} l].map (sectionSheafHom (unit l Z)
          (pullbackGlobalSection g f)) := by
  ext V : 4
  refine LinearMap.ext fun a ↦ ?_
  change (adicConstantSheafToLowerStar l g).hom.app V (sectionAct (unit l Y) a _) =
    sectionAct (unit l Z) ((adicConstantSheafToLowerStar l g).hom.app V a) _
  rw [sectionAct_unit, sectionAct_unit]
  refine ULift.ext (Subtype.ext (ContinuousMap.ext fun z ↦ ?_))
  change a.down.1 _ * f.down.1 _ = a.down.1 _ * f.down.1 _
  congr 2
  change (pullback.fst V.unop.hom g ≫ V.unop.hom).base z = (pullback.snd V.unop.hom g ≫ g).base z
  rw [pullback.condition]
  rfl

/-- **`Rⁱg_*` carries the multiplication by `f ∘ g` to the multiplication by `f`**, for a global
section `f` of `ℚ̄_ℓ,Y`. -/
lemma rightDerived_adicLowerStar_map_globalSMul_pullbackGlobalSection (i : ℕ)
    (N : AdicSheaf l Z) :
    ((g)_*ᵃ[l].rightDerived i).map ((globalSMul (pullbackGlobalSection g f)).app N) =
      (globalSMul f).app (((g)_*ᵃ[l].rightDerived i).obj N) :=
  rightDerived_adicLowerStar_map_globalSMul_app g (sectionSheafHom_pullbackGlobalSection g f) i N

end Pullback

end AlgebraicGeometry.ProEtale.AdicSheaf
