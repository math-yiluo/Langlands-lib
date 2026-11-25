/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.NativePairCohomology.NativePairCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryHomologyNatIso

/-! # Exact forgetting computes the action on native cohomology

The private composition lemmas adapt the kernel/quotient proof in
`WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GoodTruncationNormalization` to every
degree.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.NativePairCohomology

open CategoryTheory.Limits CategoryTheory.Endofunctor DerivedCategory
section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem short_homology_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (S : ShortComplex C) :
    (S.mapHomologyIso (F ⋙ G)).hom =
      ((S.map F).mapHomologyIso G).hom ≫ G.map (S.mapHomologyIso F).hom := by
  let h := S.homologyData.left
  have hc : ((h.map F).map G).cyclesIso.hom = (h.map (F ⋙ G)).cyclesIso.hom := by
    apply (cancel_mono ((F ⋙ G).map h.i)).1
    change ((h.map F).map G).cyclesIso.hom ≫ ((h.map F).map G).i =
      (h.map (F ⋙ G)).cyclesIso.hom ≫ (h.map (F ⋙ G)).i
    rw [ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i]
    rfl
  have hh : ((h.map F).map G).homologyIso.hom = (h.map (F ⋙ G)).homologyIso.hom := by
    apply (cancel_epi ((S.map (F ⋙ G)).homologyπ)).1
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom,
      ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom, hc]
    rfl
  rw [h.mapHomologyIso_eq (F ⋙ G), (h.map F).mapHomologyIso_eq G,
    h.mapHomologyIso_eq F]
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
      CategoryTheory.Functor.map_comp]
  simp only [Category.assoc, ← G.map_comp, Iso.inv_hom_id_assoc]
  rw [hh]
  rfl

set_option backward.defeqAttrib.useBackward true in
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complex_homology_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (A : CochainComplex C ℤ) (n : ℤ) :
    ((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app A =
      (G.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj A) ≫
      G.map ((F.mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app A) := by
  rw [CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq,
    CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq,
    CategoryTheory.Functor.mapHomologicalComplexHomologyIso_hom_app_eq]
  exact short_homology_comp F G (A.sc n)

set_option backward.defeqAttrib.useBackward true in
private theorem derived_homology_factor (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (A : CochainComplex C ℤ) (n : ℤ) :
    (F.mapDerivedCategoryHomologyFunctorIso n).hom.app (Q.obj A) ≫
      (homologyFunctor D n).map (F.mapDerivedCategoryFactors.hom.app A) ≫
      (homologyFunctorFactors D n).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj A) =
    F.map ((homologyFunctorFactors C n).hom.app A) ≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) n).inv.app A := by
  rw [CategoryTheory.Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_Q]
  simp only [Category.assoc]
  erw [← (homologyFunctor D n).map_comp_assoc, Iso.inv_hom_id_app,
    (homologyFunctor D n).map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
private theorem derived_homology_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : DerivedCategory C) (n : ℤ) :
    ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom.app K ≫
        (homologyFunctor E n).map ((CategoryTheory.Functor.mapDerivedCategoryCompIso F G).inv.app K)
            =
      G.map ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app K) ≫
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app (F.mapDerivedCategory.obj K) := by
  let τ₁ := ((F ⋙ G).mapDerivedCategoryHomologyFunctorIso n).hom ≫
    CategoryTheory.Functor.whiskerRight (CategoryTheory.Functor.mapDerivedCategoryCompIso F G).inv
        (homologyFunctor E n)
  let τ₂ := CategoryTheory.Functor.whiskerRight (F.mapDerivedCategoryHomologyFunctorIso n).hom G ≫
    CategoryTheory.Functor.whiskerLeft F.mapDerivedCategory (G.mapDerivedCategoryHomologyFunctorIso
        n).hom
  have h : τ₁ = τ₂ := by
    apply Localization.natTrans_ext Q (HomologicalComplex.quasiIso C (.up ℤ))
    intro A
    dsimp only [τ₁, τ₂, NatTrans.comp_app, CategoryTheory.Functor.whiskerRight_app,
      CategoryTheory.Functor.whiskerLeft_app]
    apply (cancel_mono ((homologyFunctor E n).map
      (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app A)) ≫
      (homologyFunctor E n).map (G.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj A)) ≫
      (homologyFunctorFactors E n).hom.app
        ((G.mapHomologicalComplex (.up ℤ)).obj
          ((F.mapHomologicalComplex (.up ℤ)).obj A)))).mp
    have hfac := CategoryTheory.Functor.mapDerivedCategoryCompIso_fac F G A
    have hc : (CategoryTheory.Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G))
        (.up ℤ)).hom.app A = 𝟙 _ := rfl
    erw [hc, CategoryTheory.Functor.map_id, Category.comp_id] at hfac
    have hχ := (G.mapDerivedCategoryHomologyFunctorIso n).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app A)
    dsimp only [CategoryTheory.Functor.comp_map] at hχ
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      Category.assoc, hfac]
    erw [derived_homology_factor]
    erw [← reassoc_of% hχ, derived_homology_factor]
    erw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, derived_homology_factor]
    erw [G.map_comp, Category.assoc]
    congr 1
    apply (cancel_mono (((F ⋙ G).mapHomologicalComplexHomologyIso (.up ℤ) n).hom.app A)).mp
    erw [Iso.inv_hom_id_app, complex_homology_comp]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    erw [← G.map_comp, Iso.inv_hom_id_app, G.map_id]
    rfl
  exact congr_app h K

end

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (.of k₀))]

/-- Native cohomology agrees, including its action, with cohomology of the ordinary
derived pair obtained by exact forgetting.

Source: BBD 1.3.3; exact derived forgetting in the final exceptional-adjunction
paragraph of cor-coef-verdier-weil-equivariance.proof.md.
(blueprint: lem-sf-native-pair-homology-comparison)

Proof: let U forget a native sheaf's invertible Frobenius structure. The functor U
is exact. Its canonical cohomology comparison H^n(-) U = D(U) H^n(-) gives the
underlying sheaf isomorphism. On a complex of native sheaves, the action is the
termwise structure map U F -> U. Naturality of homology with respect to that map,
and compatibility of exact-functor homology comparisons with composition, say
precisely that this isomorphism intertwines the two Frobenius actions. Both the
action and the comparison descend through the same localization at quasi-isomorphisms,
so this equality holds for every derived object, not just objects of the heart.
Lift the sheaf isomorphism to IsoAlgebra using this equality. The argument is
degree-independent and includes acyclic complexes and the empty scheme. -/
theorem native_homology (K : WeilComplex k₀ l X) (n : ℤ) :
    Nonempty (((WeilComplex.homologySheaf n).obj K).obj ≅
      (homology k₀ l X n).obj ((native k₀ l X).obj K))  := by
  let F := WeilSheaf.frobeniusPullback k₀ l X
  let U := IsoAlgebra.forget F
  let H := DerivedCategory.homologyFunctor
    (ProEtale.AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber) n
  let χ := U.mapDerivedCategoryHomologyFunctorIso n
  refine ⟨ObjectProperty.isoMk _ (Algebra.isoMk (χ.app K.obj) ?_)⟩
  change F.map (χ.hom.app K.obj) ≫
      ((F.mapDerivedCategoryHomologyFunctorIso n).hom.app (U.mapDerivedCategory.obj K.obj) ≫
        H.map ((theta k₀ l X).hom.app K)) =
    (IsoAlgebra.strNatIso F).hom.app
        ((DerivedCategory.homologyFunctor _ n).obj K.obj) ≫ χ.hom.app K.obj
  have ht : (theta k₀ l X).hom.app K =
      (Functor.mapDerivedCategoryCompIso U F).hom.app K.obj ≫
        (Functor.mapDerivedCategoryNatIso (IsoAlgebra.strNatIso F)).hom.app K.obj := by
    simp only [theta, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
    erw [Category.id_comp]
    rfl
  rw [ht]
  have hc := derived_homology_comp U F K.obj n
  have hn := Functor.mapDerivedCategoryHomologyFunctorIso_hom_app_naturality
    (IsoAlgebra.strNatIso F) n K.obj
  erw [H.map_comp, ← Category.assoc, ← Category.assoc, ← hc]
  dsimp only [H]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc]
  exact hn.symm

end WeilConjectures.NativePairCohomology
