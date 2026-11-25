/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.TorsionFree
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntModuleUpperStar

/-!
# Derived pushforward of `ℤ_ℓ`-modules and of `ℓ`-adic sheaves

For an arbitrary morphism of schemes `f : X ⟶ Y`, pulling back continuous functions along the
projections `V ×_Y X ⟶ V` is a morphism of ring objects `ℤ_ℓ,Y ⟶ f_* ℤ_ℓ,X`
(`AlgebraicGeometry.ProEtale.padicIntAbSheafToPushforward`), which defines the pushforward of
`ℤ_ℓ`-modules `AlgebraicGeometry.ProEtale.padicIntModPushforward` (the weakly étale case is
`AlgebraicGeometry.ProEtale.padicIntModLowerStar`). We compare its derived functor with the
derived pushforwards of abelian sheaves and of `ℓ`-adic sheaves:

* `Hᵠ(Rf_* M[0])_ab ≅ Hᵠ(Rf_* M_ab[0])` for a `ℤ_ℓ,X`-module `M`
  (`AlgebraicGeometry.ProEtale.forgetHomologyRightDerivedPadicIntModPushforwardIso`): the
  sections of `ℤ_ℓ,X` being torsion-free, `ℤ_ℓ,X` is a flat abelian sheaf
  (`CategoryTheory.Sheaf.preservesMonomorphisms_tensorLeft_of_flat`), so that underlying abelian
  sheaves of injective `ℤ_ℓ`-modules are injective;
* `res Hᵠ(Rf_* F[0]) ≅ Hᵠ(Rf_* (res F)[0])` for an `ℓ`-adic sheaf `F`, where `res` is the
  restriction of scalars `AlgebraicGeometry.ProEtale.AdicSheaf.restrictPadicInt` to
  `ℤ_ℓ`-modules (`AlgebraicGeometry.ProEtale.restrictPadicIntHomologyRightDerivedAdicLowerStarIso`):
  restriction of scalars commutes with the pushforwards
  (`AlgebraicGeometry.ProEtale.adicLowerStarRestrictPadicIntPushforwardIso`), and sends injective
  `ℓ`-adic sheaves to `f_*`-acyclic `ℤ_ℓ`-modules, their underlying abelian sheaves being
  injective (`WeilConjectures.SixFunctors.ProEtale.Adic.ForgetAbRightDerivedLowerStar`).

For a `ℤ_ℓ,X`-module `M` (for instance the limit of an `ℓ`-adic tower), this gives the
comparison `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ⟶ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`
(`AlgebraicGeometry.ProEtale.adicSheafExtendScalarsHomologyRightDerivedComparison`), and the
target is lisse as soon as the source is and the comparison is an isomorphism of underlying
abelian sheaves
(`isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_adicSheafExtendScalars`).
That the comparison is an isomorphism (extension of scalars `ℚ̄_ℓ,X ⊗_{ℤ_ℓ,X} -` commuting with
`Rf_*` for quasi-compact quasi-separated `f`) is not proved here.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

section ContinuousMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Type) [TopologicalSpace T] [Ring T]
  [IsTopologicalRing T]

/-- The comparison `C(-, T)_Y ⟶ f_* C(-, T)_X` of sheaves of rings on `Y_proét`: precomposition
with the projections `V ×_Y X ⟶ V`. -/
noncomputable def continuousMapRingSheafToPushforward :
    continuousMapRingSheaf Y T ⟶
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology Y) (ProEt.topology X)).obj (continuousMapRingSheaf X T) :=
  ⟨{ app V := RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        (((ContinuousMap.compRightAlgHom ℤ T (pullback.fst V.unop.hom f).base.hom).toRingHom).comp
          ULift.ringEquiv.toRingHom))
     naturality V₁ V₂ a := by
       ext x
       refine ULift.ext (ContinuousMap.ext fun y ↦ ?_)
       change x.down (a.unop.left (pullback.fst _ f y)) =
         x.down (pullback.fst _ f (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map
           a.unop).left y))
       have key : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).map a.unop).left ≫
           pullback.fst _ f = pullback.fst _ f ≫ a.unop.left :=
         pullback.lift_fst _ _ _
       rw [← Scheme.Hom.comp_apply, ← key]
       rfl }⟩

end ContinuousMap

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The comparison `ℤ_ℓ,Y ⟶ f_* ℤ_ℓ,X` of abelian sheaves, for any morphism `f : X ⟶ Y`: pulling
back continuous functions along the projections `V ×_Y X ⟶ V`. -/
noncomputable def padicIntAbSheafToPushforward :
    padicIntAbSheaf Y l ⟶ (f)_*[Ab.{u + 1}].obj (padicIntAbSheaf X l) :=
  (sheafCompose (ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafToPushforward f ℤ_[l])

/-- The comparison `ℤ_ℓ,Y ⟶ f_* ℤ_ℓ,X` is a morphism of ring objects. -/
instance isMonHom_padicIntAbSheafToPushforward :
    IsMonHom (padicIntAbSheafToPushforward l f) :=
  have : IsMonHom ((sheafCompose (ProEt.topology Y) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafToPushforward f ℤ_[l])) := inferInstance
  IsMonHom.of_eq (hf := this) _ rfl
    (Sheaf.monObjObj_sheafPushforwardContinuous_eq
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (padicIntSheaf X l)).symm

/-- The pushforward `f_*` of `ℤ_ℓ`-modules along any morphism `f : X ⟶ Y`: the pushforward of
the underlying abelian sheaf, a `ℤ_ℓ,Y`-module along `ℤ_ℓ,Y ⟶ f_* ℤ_ℓ,X`. -/
noncomputable def padicIntModPushforward :
    Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l) ⥤
      Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) (padicIntAbSheaf Y l) :=
  (upperStarLowerStarAdjunction Ab.{u + 1} f).modRight (padicIntAbSheafToPushforward l f)

instance : (padicIntModPushforward l f).Additive :=
  inferInstanceAs (Functor.mapMod _ _ ⋙ Mod.comap _).Additive

instance : PreservesFiniteLimits (padicIntModPushforward l f) :=
  have : PreservesFiniteLimits (padicIntModPushforward l f ⋙ Mod.forget _) :=
    inferInstanceAs (PreservesFiniteLimits (Mod.forget _ ⋙ (f)_*[Ab.{u + 1}]))
  preservesFiniteLimits_of_reflects_of_preserves _ (Mod.forget _)

/-- `ℤ_ℓ`-modules on `X_proét` form a Grothendieck abelian category. -/
instance (X : Scheme.{u}) : IsGrothendieckAbelian.{u + 1}
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) :=
  Mod.isGrothendieckAbelian _

/-- Continuous `ℓ`-adic functions form a torsion-free abelian group. -/
instance (T : Type*) [TopologicalSpace T] : IsAddTorsionFree (ULift.{u + 1} C(T, ℤ_[l])) :=
  Function.Injective.isAddTorsionFree
    ((ContinuousMap.coeFnAddMonoidHom).comp (AddEquiv.ulift (α := C(T, ℤ_[l]))).toAddMonoidHom)
    (DFunLike.coe_injective.comp ULift.down_injective)

/-- The sections of `ℤ_ℓ,X` are flat `ℤ`-modules, being torsion-free. -/
lemma flat_padicIntAbSheaf_obj_obj (X : Scheme.{u}) (U : X.ProEtᵒᵖ) :
    Module.Flat ℤ ((padicIntAbSheaf X l).obj.obj U) := by
  have : HasUniqueDiv (ULift.{u + 1} C(U.unop.left, ℤ_[l])) :=
    ⟨fun _ hn a b h ↦ eq_of_nsmul_eq_nsmul_of_addCommute hn (add_comm a b) h⟩
  have : Module.IsTorsionFree ℤ (ULift.{u + 1} C(U.unop.left, ℤ_[l])) :=
    Module.isTorsionFree_int_iff_hasUniqueDiv.mpr inferInstance
  exact inferInstanceAs (Module.Flat ℤ (ULift.{u + 1} C(U.unop.left, ℤ_[l])))

end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/-- **Tensoring with an abelian sheaf with flat sections preserves monomorphisms**: up to
isomorphism it is the sheafification of the sectionwise tensor product, which preserves
injections. -/
lemma preservesMonomorphisms_tensorLeft_of_flat (S : Sheaf J Ab.{u + 1})
    (hS : ∀ U, Module.Flat ℤ (S.obj.obj U)) : (tensorLeft S).PreservesMonomorphisms := by
  let P := S.obj
  have hP : (tensorLeft ((presheafToSheaf J Ab.{u + 1}).obj P)).PreservesMonomorphisms := by
    refine ⟨fun {M N} g _ ↦ ?_⟩
    have : Mono g.hom := (sheafToPresheaf J _).map_mono g
    have (U : Cᵒᵖ) : Mono ((P ◁ g.hom).app U) := by
      have hU : Mono (g.hom.app U) := inferInstance
      rw [AddCommGrpCat.mono_iff_injective] at hU ⊢
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := P.obj U)
        (g.hom.app U).hom.toIntLinearMap hU
    have : Mono (P ◁ g.hom) := NatTrans.mono_of_mono_app _
    let e := Sheaf.presheafToSheafCompTensorLeftIso (J := J) (A := Ab.{u + 1}) P
    have h₁ : (presheafToSheaf J _).obj P ◁ (presheafToSheaf J _).map g.hom =
        e.hom.app _ ≫ (presheafToSheaf J _).map (P ◁ g.hom) ≫ e.inv.app _ := by
      have hn := e.hom.naturality g.hom
      change _ ◁ _ ≫ _ = _ ≫ (presheafToSheaf J _).map (P ◁ g.hom) at hn
      rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    let ε := (sheafificationAdjunction J Ab.{u + 1}).counit
    have h₂ : g = inv (ε.app M) ≫ (presheafToSheaf J _).map g.hom ≫ ε.app N := by
      rw [IsIso.eq_inv_comp]
      exact (ε.naturality g).symm
    change Mono ((presheafToSheaf J _).obj P ◁ g)
    rw [h₂, MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp, h₁]
    infer_instance
  exact Functor.PreservesMonomorphisms.of_iso (F := tensorLeft ((presheafToSheaf J _).obj P))
    ((tensoringLeft _).mapIso (asIso ((sheafificationAdjunction J _).counit.app S)))

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

variable (l : ℕ) [Fact l.Prime] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The underlying abelian sheaf of an injective `ℤ_ℓ`-module is injective, `ℤ_ℓ,X` being flat. -/
instance preservesInjectiveObjects_padicIntModForget (X : Scheme.{u}) :
    (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicIntAbSheaf X l)).PreservesInjectiveObjects :=
  have := Sheaf.preservesMonomorphisms_tensorLeft_of_flat (ProEt.topology X)
    (padicIntAbSheaf X l) (flat_padicIntAbSheaf_obj_obj l X)
  Mod.preservesInjectiveObjects_forget _

/-- The pushforward of `ℤ_ℓ`-modules commutes with taking underlying abelian sheaves. -/
noncomputable def padicIntModPushforwardCompForgetIso :
    padicIntModPushforward l f ⋙ Mod.forget _ ≅ Mod.forget _ ⋙ (f)_*[Ab.{u + 1}] :=
  Iso.refl _

/-- The base change morphism `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` for `ℤ_ℓ`-modules. -/
noncomputable def rightDerivedPadicIntModPushforwardForget :
    (padicIntModPushforward l f).rightDerivedFunctorPlus ⋙
        (Mod.forget (D := Sheaf (ProEt.topology Y) Ab.{u + 1})
          (padicIntAbSheaf Y l)).mapDerivedCategoryPlus ⟶
      (Mod.forget (D := Sheaf (ProEt.topology X) Ab.{u + 1})
          (padicIntAbSheaf X l)).mapDerivedCategoryPlus ⋙
        ((f)_*[Ab.{u + 1}]).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (padicIntModPushforwardCompForgetIso l f).hom

/-- The comparison `(R⁺f_* K)_ab ⟶ R⁺f_*(K_ab)` for `ℤ_ℓ`-modules is an isomorphism. -/
instance isIso_rightDerivedPadicIntModPushforwardForget :
    IsIso (rightDerivedPadicIntModPushforwardForget l f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun _ _ ↦ Functor.rightAcyclic_of_injective _

/-- `(Rᵠf_* M)_ab ≅ Rᵠf_*(M_ab)` for `ℤ_ℓ`-modules `M`, for the classical right derived
functors. -/
noncomputable def rightDerivedPadicIntModPushforwardForgetIso (q : ℕ) :
    (padicIntModPushforward l f).rightDerived q ⋙ Mod.forget _ ≅
      Mod.forget _ ⋙ ((f)_*[Ab.{u + 1}]).rightDerived q :=
  have : IsIso
      (Functor.rightDerivedBaseChange (padicIntModPushforwardCompForgetIso l f).hom q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
        (padicIntModPushforwardCompForgetIso l f).hom) :=
      isIso_rightDerivedPadicIntModPushforwardForget l f
    infer_instance
  asIso (Functor.rightDerivedBaseChange (padicIntModPushforwardCompForgetIso l f).hom q)

/-! ### Restriction of scalars from `ℓ`-adic sheaves to `ℤ_ℓ`-modules -/

/-- The inclusions `ℤ_ℓ ⟶ ℚ̄_ℓ` on `Y` and on `X` are compatible with the comparisons
`ℤ_ℓ,Y ⟶ f_* ℤ_ℓ,X` and `ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X`. -/
lemma padicIntSheafToAdicConstantSheaf_comp_map_adicConstantSheafToLowerStar_eq :
    padicIntSheafToAdicConstantSheaf Y l ≫
        (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f) =
      padicIntAbSheafToPushforward l f ≫
        (f)_*[Ab.{u + 1}].map (padicIntSheafToAdicConstantSheaf X l) := by
  rw [padicIntSheafToAdicConstantSheaf_eq, padicIntSheafToAdicConstantSheaf_eq]
  ext U x
  rfl

/-- The pushforward of sheaves of `ℚ̄_ℓ`-modules along any morphism commutes with the forgetful
functor to abelian sheaves, strictly. -/
noncomputable abbrev pushforwardCompWeilCoefficientsForgetAbIso :
    (f)_*[WeilCoefficients.{u} l] ⋙ weilCoefficientsForgetAb l Y ≅
      weilCoefficientsForgetAb l X ⋙ (f)_*[Ab.{u + 1}] :=
  Iso.refl _

/-- The identification `f_* ⋙ forget = forget ⋙ f_*` is monoidal. -/
instance : NatTrans.IsMonoidal (pushforwardCompWeilCoefficientsForgetAbIso l f).hom :=
  Functor.isMonoidal_sheafPushforwardContinuousCompSheafComposeIso_hom
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f) (ProEt.topology Y) (ProEt.topology X)
    (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})

/-- The restriction of scalars to `ℤ_ℓ,Y` of the pushforward of an `ℓ`-adic sheaf, as the
`mapMod` of the composite `f_* ⋙ forget` followed by a restriction of scalars. -/
noncomputable def adicLowerStarCompRestrictPadicIntPushforwardIso :
    (f)_*ᵃ[l] ⋙ AdicSheaf.restrictPadicInt Y l ≅
      (weilCoefficientsForgetAb l X ⋙ (f)_*[Ab.{u + 1}]).mapMod (adicConstantSheaf l X) ⋙
        Mod.comap (padicIntSheafToAdicConstantSheaf Y l ≫
          (weilCoefficientsForgetAb l Y).map (adicConstantSheafToLowerStar l f) ≫
            Functor.compAlgHom (f)_*[WeilCoefficients.{u} l] (weilCoefficientsForgetAb l Y)
              (pushforwardCompWeilCoefficientsForgetAbIso l f).hom (adicConstantSheaf l X)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((weilCoefficientsForgetAb l Y).mapModComapIso (adicConstantSheafToLowerStar l f)) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso _ _
      (pushforwardCompWeilCoefficientsForgetAbIso l f).hom (adicConstantSheaf l X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)

/-- The pushforward of the restriction of scalars to `ℤ_ℓ,X` of an `ℓ`-adic sheaf, as the
`mapMod` of the composite `forget ⋙ f_*` followed by a restriction of scalars. -/
noncomputable def restrictPadicIntCompPadicIntModPushforwardIso :
    AdicSheaf.restrictPadicInt X l ⋙ padicIntModPushforward l f ≅
      (weilCoefficientsForgetAb l X ⋙ (f)_*[Ab.{u + 1}]).mapMod (adicConstantSheaf l X) ⋙
        Mod.comap (padicIntAbSheafToPushforward l f ≫
          (f)_*[Ab.{u + 1}].map (padicIntSheafToAdicConstantSheaf X l) ≫
            Functor.compAlgHom (weilCoefficientsForgetAb l X) (f)_*[Ab.{u + 1}]
              (𝟙 (weilCoefficientsForgetAb l X ⋙ (f)_*[Ab.{u + 1}])) (adicConstantSheaf l X)) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((f)_*[Ab.{u + 1}].mapModComapIso (padicIntSheafToAdicConstantSheaf X l)) _ ≪≫
      Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapModCompIso _ _
      (𝟙 (weilCoefficientsForgetAb l X ⋙ (f)_*[Ab.{u + 1}])) (adicConstantSheaf l X)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Mod.comapComp _ _).symm _ ≪≫ (Mod.comapComp _ _).symm)

/-- **Restriction of scalars commutes with the pushforward**: for any `f : X ⟶ Y`, restricting
the scalars of `f_* F` to `ℤ_ℓ,Y` is pushing forward `F` with its scalars restricted to
`ℤ_ℓ,X`. -/
noncomputable def adicLowerStarRestrictPadicIntPushforwardIso :
    (f)_*ᵃ[l] ⋙ AdicSheaf.restrictPadicInt Y l ≅
      AdicSheaf.restrictPadicInt X l ⋙ padicIntModPushforward l f :=
  adicLowerStarCompRestrictPadicIntPushforwardIso l f ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr (by
      simp only [Functor.compAlgHom, Iso.refl_hom, NatTrans.id_app]
      exact padicIntSheafToAdicConstantSheaf_comp_map_adicConstantSheafToLowerStar_eq l f)) ≪≫
    (restrictPadicIntCompPadicIntModPushforwardIso l f).symm

/-- An object of `ℤ_ℓ`-modules whose underlying abelian sheaf is zero is zero. -/
lemma isZero_of_isZero_padicIntModForget {X : Scheme.{u}}
    {N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)}
    (h : IsZero ((Mod.forget _).obj N)) : IsZero N := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  exact (Mod.forget _).map_injective (by rw [CategoryTheory.Functor.map_id, Functor.map_zero, h])

/-- The restriction of scalars of an injective `ℓ`-adic sheaf to `ℤ_ℓ,X` is acyclic for the
pushforward of `ℤ_ℓ`-modules: its higher direct images have zero underlying abelian sheaves,
since its underlying abelian sheaf is injective. -/
lemma rightAcyclic_padicIntModPushforward_restrictPadicInt_obj (I : AdicSheaf l X)
    [Injective I] :
    (padicIntModPushforward l f).rightAcyclic ((AdicSheaf.restrictPadicInt X l).obj I) :=
  fun n ↦ isZero_of_isZero_padicIntModForget l
    ((Functor.rightAcyclic_of_injective (F := (f)_*[Ab.{u + 1}])
      ((AdicSheaf.toAb l X).obj I) n).of_iso
      ((rightDerivedPadicIntModPushforwardForgetIso l f (n + 1)).app _))

/-- The base change morphism `res(R⁺f_* K) ⟶ R⁺f_*(res K)` comparing the derived pushforward of
`ℓ`-adic sheaves with that of `ℤ_ℓ`-modules, along restriction of scalars. -/
noncomputable def rightDerivedAdicLowerStarRestrictPadicInt :
    ((f)_*ᵃ[l]).rightDerivedFunctorPlus ⋙
        (AdicSheaf.restrictPadicInt Y l).mapDerivedCategoryPlus ⟶
      (AdicSheaf.restrictPadicInt X l).mapDerivedCategoryPlus ⋙
        (padicIntModPushforward l f).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (adicLowerStarRestrictPadicIntPushforwardIso l f).hom

/-- The comparison `res(R⁺f_* K) ⟶ R⁺f_*(res K)` is an isomorphism. -/
instance isIso_rightDerivedAdicLowerStarRestrictPadicInt :
    IsIso (rightDerivedAdicLowerStarRestrictPadicInt l f) :=
  Functor.isIso_rightDerivedFunctorPlusBaseChange_of_rightAcyclic _
    fun I _ ↦ rightAcyclic_padicIntModPushforward_restrictPadicInt_obj l f I

/-- `res(Rᵠf_* F) ≅ Rᵠf_*(res F)` for the classical right derived functors, where `res` is the
restriction of scalars from `ℓ`-adic sheaves to `ℤ_ℓ`-modules. -/
noncomputable def rightDerivedAdicLowerStarRestrictPadicIntIso (q : ℕ) :
    ((f)_*ᵃ[l]).rightDerived q ⋙ AdicSheaf.restrictPadicInt Y l ≅
      AdicSheaf.restrictPadicInt X l ⋙ (padicIntModPushforward l f).rightDerived q :=
  have : IsIso (Functor.rightDerivedBaseChange
      (adicLowerStarRestrictPadicIntPushforwardIso l f).hom q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro G
    rw [Functor.rightDerivedBaseChange_app]
    have : IsIso (Functor.rightDerivedFunctorPlusBaseChange
        (adicLowerStarRestrictPadicIntPushforwardIso l f).hom) :=
      isIso_rightDerivedAdicLowerStarRestrictPadicInt l f
    infer_instance
  asIso (Functor.rightDerivedBaseChange (adicLowerStarRestrictPadicIntPushforwardIso l f).hom q)

/-- **Cohomology sheaves of the derived pushforward of `ℓ`-adic sheaves, as `ℤ_ℓ`-modules**: for
an `ℓ`-adic sheaf `F` on `X_proét` and `q : ℕ`, the restriction of scalars to `ℤ_ℓ,Y` of
`Hᵠ(Rf_* F[0])`, computed in `D(AdicSheaf l Y)`, is `Hᵠ(Rf_* (res F)[0])`, computed in the derived
category of `ℤ_ℓ,Y`-modules. -/
noncomputable def restrictPadicIntHomologyRightDerivedAdicLowerStarIso (F : AdicSheaf l X)
    (q : ℕ) :
    (AdicSheaf.restrictPadicInt Y l).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((f)_*ᵃ[l].rightDerivedFunctor.obj ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj ((AdicSheaf.restrictPadicInt X l).obj F))) :=
  (AdicSheaf.restrictPadicInt Y l).mapIso
      (((f)_*ᵃ[l]).homologyRightDerivedFunctorObjSingleFunctorIso F q) ≪≫
    (rightDerivedAdicLowerStarRestrictPadicIntIso l f q).app F ≪≫
    ((padicIntModPushforward l f).homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm

/-- **Cohomology sheaves of the derived pushforward of `ℤ_ℓ`-modules, as abelian sheaves**: for a
`ℤ_ℓ,X`-module `M`, the underlying abelian sheaf of `Hᵠ(Rf_* M[0])`, computed in the derived
category of `ℤ_ℓ,Y`-modules, is `Hᵠ(Rf_* M_ab[0])`, computed for abelian sheaves. -/
noncomputable def forgetHomologyRightDerivedPadicIntModPushforwardIso
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ) :
    (Mod.forget _).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ≅
      (DerivedCategory.homologyFunctor _ q).obj (((f)_*[Ab.{u + 1}]).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Mod.forget _).obj M))) :=
  (Mod.forget _).mapIso
      ((padicIntModPushforward l f).homologyRightDerivedFunctorObjSingleFunctorIso M q) ≪≫
    (rightDerivedPadicIntModPushforwardForgetIso l f q).app M ≪≫
    (((f)_*[Ab.{u + 1}]).homologyRightDerivedFunctorObjSingleFunctorIso _ q).symm

/-! ### Extension of scalars and the derived pushforward -/

/-- The comparison `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ⟶ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])` for a `ℤ_ℓ,X`-module `M`, the
left hand side computed for `ℤ_ℓ`-modules and the right hand side for `ℓ`-adic sheaves: the
adjoint of the morphism `Hᵠ(Rf_* M[0]) ⟶ Hᵠ(Rf_* res(ℚ̄_ℓ ⊗ M)[0]) ≅ res Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])`
induced by the unit `M ⟶ res(ℚ̄_ℓ ⊗ M)`. -/
noncomputable def adicSheafExtendScalarsHomologyRightDerivedComparison
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ) :
    (adicSheafExtendScalars Y l).obj ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) ⟶
      (DerivedCategory.homologyFunctor _ q).obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafExtendScalars X l).obj M))) :=
  ((adicSheafExtendScalarsRestrictAdjunction Y l).homEquiv _ _).symm
    ((DerivedCategory.homologyFunctor _ q).map
        ((padicIntModPushforward l f).rightDerivedFunctor.map
          ((DerivedCategory.singleFunctor _ 0).map
            ((adicSheafExtendScalarsRestrictAdjunction X l).unit.app M))) ≫
      (restrictPadicIntHomologyRightDerivedAdicLowerStarIso l f _ q).inv)

/-- **Lisse direct images from the integral comparison**: if `ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0])` is lisse, the
right hand side computed for `ℤ_ℓ`-modules, and the comparison
`ℚ̄_ℓ ⊗ Hᵠ(Rf_* M[0]) ⟶ Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])` is an isomorphism of underlying abelian sheaves,
then `Hᵠ(Rf_* (ℚ̄_ℓ ⊗ M)[0])` is lisse. -/
theorem isAdicLisseSheaf_homology_rightDerivedFunctor_adicLowerStar_adicSheafExtendScalars
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicIntAbSheaf X l)) (q : ℕ)
    (hM : IsAdicLisseSheaf ((adicSheafExtendScalars Y l).obj
      ((DerivedCategory.homologyFunctor _ q).obj
        ((padicIntModPushforward l f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M)))))
    [IsIso ((AdicSheaf.toAb l Y).map
      (adicSheafExtendScalarsHomologyRightDerivedComparison l f M q))] :
    IsAdicLisseSheaf ((DerivedCategory.homologyFunctor _ q).obj ((f)_*ᵃ[l].rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj ((adicSheafExtendScalars X l).obj M)))) :=
  hM.of_isIso_toAb_map l (adicSheafExtendScalarsHomologyRightDerivedComparison l f M q)

end AlgebraicGeometry.ProEtale
