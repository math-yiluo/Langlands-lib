/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposePushforwardMonoidal
public import WeilConjectures.SixFunctors.ProEtale.Adic.AdicSheafForgetAb
public import WeilConjectures.SixFunctors.ProEtale.Adic.PadicAlgClSheafIso

/-!
# The two models of `ℚ̄_ℓ,X` agree as ring objects

The comparison `padicAlgClSheaf X ℓ ⟶ adicConstantSheaf ℓ X` of abelian sheaves is a morphism of
ring objects, for the ring structure on the target induced by the lax monoidal forgetful functor
`weilCoefficientsForgetAb`
(`AlgebraicGeometry.ProEtale.isMonHom_padicAlgClSheafToAdicConstantSheaf`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits Opposite

open scoped Obj

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- For a monoidal adjunction `F ⊣ G`, the morphism `F.obj M ⟶ S` adjoint to a morphism of monoids
`M ⟶ G.obj S` is a morphism of monoids. -/
lemma isMonHom_homEquiv_symm {M : C} [MonObj M] {S : D} [MonObj S] (f : M ⟶ G.obj S)
    [IsMonHom f] : IsMonHom ((adj.homEquiv M S).symm f) := by
  have key : ((adj.mapMon.homEquiv (Mon.mk M) (Mon.mk S)).symm (Mon.Hom.mk f)).hom =
      (adj.homEquiv M S).symm f := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
    simp only [Adjunction.mapMon_counit, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
      Mon.comp_hom', Functor.mapMon_map_hom, Functor.mapMonCompIso_inv_app_hom,
      Functor.mapMonNatTrans_app_hom, Functor.mapMonIdIso_hom_app_hom]
    erw [Category.id_comp, Category.comp_id]
  exact key ▸ ((adj.mapMon.homEquiv (Mon.mk M) (Mon.mk S)).symm (Mon.Hom.mk f)).isMonHom_hom

end CategoryTheory.Adjunction

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]

attribute [local instance] monoidalCategory braidedCategory

/-- The morphism of sheaves adjoint to a morphism of monoids from a monoid presheaf `P` to the
underlying presheaf of a monoid sheaf `S` is a morphism of monoids, sheafification being a
monoidal left adjoint. -/
instance isMonHom_sheafificationAdjunction_homEquiv_symm {P : Cᵒᵖ ⥤ A} [MonObj P]
    {S : Sheaf J A} [MonObj S] (f : P ⟶ (sheafToPresheaf J A).obj S) [IsMonHom f] :
    IsMonHom (((sheafificationAdjunction J A).homEquiv P S).symm f) :=
  (sheafificationAdjunction J A).isMonHom_homEquiv_symm f

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.ProEtale

open Scheme Functor.LaxMonoidal

variable (X : Scheme.{u}) (l : ℕ) [Fact l.Prime]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The inclusion of the functions with values in a finite subextension into the locally finite
functions, as a morphism of monoid objects of abelian presheaves, for the pointwise ring
structure of the target. -/
noncomputable def padicAlgClPresheafToAdicConstantSheafMonHom :
    Mon.mk (padicAlgClRingPresheaf X l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ⟶
      ((Functor.whiskeringRight _ _ _).obj
        (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).mapMon.obj
          (Mon.mk (adicConstantSheaf l X).obj) :=
  Mon.Hom.mk' (padicAlgClPresheafToAdicConstantSheaf X l)
    (by
      ext U n
      refine ULift.ext (Subtype.ext (ContinuousMap.ext fun x ↦ ?_))
      exact (show ((ULift.down n : ℤ) : PadicAlgCl l) =
        (ULift.down n • (1 : ULift.{u + 1} (PadicAlgCl l))).down by simp))
    (by
      ext U : 2
      refine AddCommGrpCat.hom_ext_toIntLinearMap (TensorProduct.ext' fun a b ↦ ?_)
      rfl)

/-- The identity of the underlying presheaf of `ℚ̄_ℓ,X`, as a morphism of monoid objects from its
pointwise ring structure to the one induced by the lax monoidal functor `sheafToPresheaf`. -/
noncomputable def adicConstantSheafObjMonHom :
    Mon.mk (adicConstantSheaf l X).obj ⟶
      (sheafToPresheaf (ProEt.topology X) (WeilCoefficients.{u} l)).mapMon.obj
        (Mon.mk (adicConstantSheaf l X)) :=
  Mon.Hom.mk' (𝟙 _) ((Category.comp_id _).trans (adicConstantSheaf_ε_comp_map_one' X).symm)
    (by
      rw [Category.comp_id, id_tensorHom_id, Category.id_comp]
      exact (adicConstantSheaf_μ_comp_map_mul' X).symm)

/-- The inclusion of the functions with values in a finite subextension into the locally finite
functions, as a morphism of monoid objects of abelian presheaves into the underlying presheaf of
the image of `ℚ̄_ℓ,X` under the lax monoidal functor `weilCoefficientsForgetAb`. -/
noncomputable def padicAlgClPresheafToForgetAbMonHom :
    Mon.mk (padicAlgClRingPresheaf X l ⋙ forget₂ RingCat.{u + 1} Ab.{u + 1}) ⟶
      (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}).mapMon.obj
        ((weilCoefficientsForgetAb l X).mapMon.obj (Mon.mk (adicConstantSheaf l X))) :=
  padicAlgClPresheafToAdicConstantSheafMonHom X l ≫
    ((Functor.whiskeringRight _ _ _).obj
      (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).mapMon.map (adicConstantSheafObjMonHom X l) ≫
    Functor.mapMonCompIso.inv.app _ ≫
    (Functor.mapMonNatTrans (sheafToPresheafCompWhiskeringRightIsoSheafCompose
      (ProEt.topology X) (forget₂ (WeilCoefficients.{u} l) Ab.{u + 1})).hom).app _ ≫
    Functor.mapMonCompIso.hom.app _

/-- The underlying morphism of `padicAlgClPresheafToForgetAbMonHom` is the inclusion of the
functions with values in a finite subextension into the locally finite functions. -/
lemma padicAlgClPresheafToForgetAbMonHom_hom :
    (padicAlgClPresheafToForgetAbMonHom X l).hom = padicAlgClPresheafToAdicConstantSheaf X l := by
  simp only [padicAlgClPresheafToForgetAbMonHom, padicAlgClPresheafToAdicConstantSheafMonHom,
    adicConstantSheafObjMonHom, Mon.comp_hom', Functor.mapMon_map_hom,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_id', Functor.mapMonCompIso_inv_app_hom,
    ObjectProperty.ι_obj, Functor.whiskeringRight_obj_obj, Functor.mapMonNatTrans_app_hom,
    sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app, Functor.mapMonCompIso_hom_app_hom]
  rfl

/-- **The two models of `ℚ̄_ℓ,X` agree as ring objects**: the comparison
`padicAlgClSheaf X ℓ ⟶ adicConstantSheaf ℓ X` is a morphism of ring objects of abelian sheaves,
for the ring structure on the target induced by the lax monoidal functor
`weilCoefficientsForgetAb`. -/
instance isMonHom_padicAlgClSheafToAdicConstantSheaf :
    IsMonHom (padicAlgClSheafToAdicConstantSheaf X l) := by
  have := (padicAlgClPresheafToForgetAbMonHom X l).isMonHom_hom
  rw [padicAlgClPresheafToForgetAbMonHom_hom] at this
  exact Sheaf.isMonHom_sheafificationAdjunction_homEquiv_symm _ _

end AlgebraicGeometry.ProEtale
