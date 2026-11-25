/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelEquivalenceFunctoriality
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.MatesUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence

/-!
# Composition of pullbacks in the two models of ℓ-adic sheaves

The comparison `adicUpperStarCompCondensedModIso` of the pullbacks of the two models is compatible
with the composition isomorphisms of the pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {X Y : Scheme.{u}}

/-- The pullback compatibility of the two models is the mate of the pushforward compatibility. -/
theorem mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom (f : Y ⟶ X) :
    (mateEquiv (adicUpperStarLowerStarAdjunction l f)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (adicUpperStarCompCondensedModIso l f).inv) =
      (adicLowerStarCompCondensedModIso l f).hom :=
  mateEquiv_eq_of_unit _ _ _ _ (fun a ↦
    (unit_app_comp_map_conjugateIsoEquiv_symm_inv_app _ _ _ _ _ _ (fun b ↦ by
      rw [condensedModInverseCompAdicLowerStarIso]
      exact inverseCompIso_hom_app _ _ _ b) a).symm)

variable {Z : Scheme.{u}}

/-- On underlying abelian sheaves, the composition isomorphism of pushforwards of sheaves of
`ℚ̄_ℓ`-modules is that of pushforwards of abelian sheaves. -/
lemma weilCoefficientsForgetAb_map_lowerStarComp_inv_app_eq (g : Z ⟶ Y) (f : Y ⟶ X)
    (N : Sheaf (Scheme.ProEt.topology Z) (WeilCoefficients.{u} l)) :
    (weilCoefficientsForgetAb l X).map ((lowerStarComp (WeilCoefficients.{u} l) g f).inv.app N) =
      (lowerStarComp Ab.{u + 1} g f).inv.app ((weilCoefficientsForgetAb l Z).obj N) := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ?_))
  rw [lowerStarComp_inv_app_hom_app]
  exact congrArg (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1}).map
    (lowerStarComp_inv_app_hom_app (WeilCoefficients.{u} l) g f N V)

/-- The pushforward compatibility of the two models is compatible with the composition
isomorphisms of the pushforwards. -/
lemma adicLowerStarCompCondensedModIso_hom_app_comp_lowerStarComp_inv_app (g : Z ⟶ Y)
    (f : Y ⟶ X) (c : AdicSheaf l Z) :
    (adicLowerStarCompCondensedModIso l (g ≫ f)).hom.app c ≫
        (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) g f).inv.app
          ((adicSheafEquivCondensedMod l Z).functor.obj c) =
      (adicSheafEquivCondensedMod l X).functor.map ((adicLowerStarComp l g f).inv.app c) ≫
        (adicLowerStarCompCondensedModIso l f).hom.app ((g)_*ᵃ[l].obj c) ≫
        (CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) f).map
          ((adicLowerStarCompCondensedModIso l g).hom.app c) := by
  apply Mod.hom_ext
  have hinv : ((CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) g f).inv.app
      ((adicSheafEquivCondensedMod l Z).functor.obj c)).hom =
      (lowerStarComp Ab.{u + 1} g f).inv.app ((adicSheafEquivCondensedMod l Z).functor.obj c).X :=
          by
    rw [← cancel_epi ((lowerStarComp Ab.{u + 1} g f).hom.app
      ((adicSheafEquivCondensedMod l Z).functor.obj c).X), Iso.hom_inv_id_app,
      ← CondensedRing.lowerStarComp_hom_app_hom, ← Mod.comp_hom', Iso.hom_inv_id_app]
    rfl
  rw [Mod.comp_hom', Mod.comp_hom', Mod.comp_hom', adicLowerStarCompCondensedModIso_hom_app_hom,
    adicLowerStarCompCondensedModIso_hom_app_hom, CondensedRing.lowerStar_map_hom,
    adicLowerStarCompCondensedModIso_hom_app_hom, hinv]
  rw [Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  exact (weilCoefficientsForgetAb_map_lowerStarComp_inv_app_eq g f c.X).symm

/-- **The pullback compatibility of the two models is compatible with composition**. -/
theorem adicUpperStarCompCondensedModIso_inv_app_comp_map_adicUpperStarComp_hom_app
    (g : Z ⟶ Y) (f : Y ⟶ X) (M : AdicSheaf l X) :
    (adicUpperStarCompCondensedModIso l (g ≫ f)).inv.app M ≫
        (adicSheafEquivCondensedMod l Z).functor.map ((adicUpperStarComp l g f).hom.app M) =
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g f).hom.app
          ((adicSheafEquivCondensedMod l X).functor.obj M) ≫
        (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).map
          ((adicUpperStarCompCondensedModIso l f).inv.app M) ≫
        (adicUpperStarCompCondensedModIso l g).inv.app ((f)^*ᵃ[l].obj M) := by
  refine app_comp_map_hom_app_of_mateEquiv (adicUpperStarLowerStarAdjunction l f)
    (adicUpperStarLowerStarAdjunction l g) (adicUpperStarLowerStarAdjunction l (g ≫ f))
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (g ≫ f))
    (adicUpperStarComp l g f) (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g f)
    _ _ _ (fun c ↦ ?_) M
  have h₁ := congrArg (fun α ↦ α.app c)
      (mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom (l := l) (g ≫ f))
  have h₂ := congrArg (fun α ↦ α.app ((g)_*ᵃ[l].obj c))
    (mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom (l := l) f)
  have h₃ := congrArg (fun α ↦ α.app c)
      (mateEquiv_adicUpperStarCompCondensedModIso_inv_eq_hom (l := l) g)
  have ho : conjugateIsoEquiv (adicUpperStarLowerStarAdjunction l (g ≫ f))
      ((adicUpperStarLowerStarAdjunction l f).comp (adicUpperStarLowerStarAdjunction l g))
      (adicUpperStarComp l g f).symm = (adicLowerStarComp l g f).symm := by
    rw [adicUpperStarComp, Iso.symm_symm_eq, Equiv.apply_symm_apply]
  have hn : conjugateIsoEquiv
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) (g ≫ f))
      ((CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f).comp
        (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) g))
      (CondensedRing.upperStarComp (Profinite.padicAlgClRingObj l) g f).symm =
      (CondensedRing.lowerStarComp (Profinite.padicAlgClRingObj l) g f).symm := by
    rw [CondensedRing.upperStarComp, Iso.symm_symm_eq, Equiv.apply_symm_apply]
  rw [h₁, h₂, h₃, ho, hn, Iso.symm_hom, Iso.symm_hom]
  exact adicLowerStarCompCondensedModIso_hom_app_comp_lowerStarComp_inv_app g f c

end AlgebraicGeometry.ProEtale
