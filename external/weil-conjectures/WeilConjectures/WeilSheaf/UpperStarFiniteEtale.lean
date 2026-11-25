/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.FiniteEtaleCounit
public import WeilConjectures.WeilSheaf.UpperStarComp
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Pullbacks of Weil sheaves along composites and finite étale morphisms

The pullback of Weil sheaves along a composite is the iterated pullback
(`AlgebraicGeometry.WeilSheaf.nonempty_upperStar_comp_iso`), and for a finite étale morphism `g`
the counit `g^* g_* F ⟶ F` of Weil sheaves is an epimorphism
(`AlgebraicGeometry.WeilSheaf.epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale`): its
underlying morphism of `ℓ`-adic sheaves is the counit along the base change of `g` to the
geometric fibres, which is again finite étale.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y Z : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))]

variable (k₀ l) in
/-- The composition isomorphism `(φ ≫ ψ)^* ≅ ψ^* ⋙ φ^*` of pullbacks of Weil sheaves, after the
inclusion into pro-étale Weil sheaves, induced by
`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarCompIso`. -/
noncomputable def upperStarCompCompιIso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))] :
    upperStar (k₀ := k₀) (l := l) (φ ≫ ψ) ⋙ (WeilSheaf.objectProperty k₀ l X).ι ≅
      (upperStar ψ ⋙ upperStar φ) ⋙ (WeilSheaf.objectProperty k₀ l X).ι :=
  ObjectProperty.liftFullSubcategoryCompιIso (WeilSheaf.objectProperty k₀ l Z)
      (WeilSheaf.objectProperty k₀ l X) (ProEtaleWeilSheaf.upperStar k₀ l (φ ≫ ψ))
      (fun _ hF ↦ ProEtale.IsAdicConstructibleSheaf.upperStar _ hF) ≪≫
    Functor.isoWhiskerLeft _ (ProEtaleWeilSheaf.upperStarCompIso k₀ l φ ψ) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ObjectProperty.liftFullSubcategoryCompιIso
      (WeilSheaf.objectProperty k₀ l Z) (WeilSheaf.objectProperty k₀ l Y)
      (ProEtaleWeilSheaf.upperStar k₀ l ψ)
      (fun _ hF ↦ ProEtale.IsAdicConstructibleSheaf.upperStar _ hF)).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (ObjectProperty.liftFullSubcategoryCompιIso
      (WeilSheaf.objectProperty k₀ l Y) (WeilSheaf.objectProperty k₀ l X)
      (ProEtaleWeilSheaf.upperStar k₀ l φ)
      (fun _ hF ↦ ProEtale.IsAdicConstructibleSheaf.upperStar _ hF)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The pullback of Weil sheaves along a composite `φ ≫ ψ` is isomorphic to the iterated
pullback. -/
theorem nonempty_upperStar_comp_iso (φ : X ⟶ Y) (ψ : Y ⟶ Z)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [ψ.IsOver (Spec (CommRingCat.of k₀))]
    (F : WeilSheaf k₀ l Z) :
    Nonempty ((upperStar (φ ≫ ψ)).obj F ≅ (upperStar φ).obj ((upperStar ψ).obj F)) :=
  ⟨ObjectProperty.isoMk _ ((upperStarCompCompιIso k₀ l φ ψ).app F)⟩

/-- Pullbacks of Weil sheaves along equal morphisms agree. -/
theorem upperStar_congr {φ φ' : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') :
    upperStar (k₀ := k₀) (l := l) φ = upperStar φ' := by
  subst h
  rfl

/-- The pullbacks of a Weil sheaf along equal morphisms are isomorphic. -/
theorem nonempty_upperStar_congr_iso {φ φ' : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))]
    [φ'.IsOver (Spec (CommRingCat.of k₀))] (h : φ = φ') (F : WeilSheaf k₀ l Y) :
    Nonempty ((upperStar φ).obj F ≅ (upperStar φ').obj F) :=
  ⟨eqToIso (by rw [upperStar_congr h])⟩

/-- For a finite étale morphism `g` of `k₀`-schemes, the counit `g^* g_* F ⟶ F` of Weil sheaves
is an epimorphism: on underlying `ℓ`-adic sheaves it is the counit along the base change of `g`
to the geometric fibres, which is finite étale
(`AlgebraicGeometry.ProEtale.epi_adicUpperStarLowerStarAdjunction_counit_app`). -/
theorem epi_upperStarLowerStarAdjunction_counit_app_of_finite_etale (g : X ⟶ Y)
    [g.IsOver (Spec (CommRingCat.of k₀))] [IsFinite g] [Etale g]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l X) :
    Epi ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).counit.app F) := by
  have : IsFinite (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsFinite) g _ ‹_›
  have : Etale (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Etale) g _ ‹_›
  have h : Epi ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).counit.app F).hom.hom.f := by
    rw [upperStarLowerStarAdjunction_counit_app_hom_hom_f]
    exact ProEtale.epi_adicUpperStarLowerStarAdjunction_counit_app l _ _
  have : Epi ((Endofunctor.IsoAlgebra.forget _).map
      ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).counit.app F).hom) := h
  have : Epi ((upperStarLowerStarAdjunction (k₀ := k₀) (l := l) g).counit.app F).hom :=
    (Endofunctor.IsoAlgebra.forget _).epi_of_epi_map this
  exact (ObjectProperty.ι _).epi_of_epi_map this

end AlgebraicGeometry.WeilSheaf
