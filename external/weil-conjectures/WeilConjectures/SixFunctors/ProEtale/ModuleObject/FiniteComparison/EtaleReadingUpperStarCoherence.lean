/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.PullbackSquareComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.DerivedBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingUpperStar

/-!
# The pullback comparisons of the étale reading: composition and pullback squares

Write `ρ_X : Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ)` for the étale reading
(`ProEtale.CondensedRing.finiteEtaleReading`) and `Lf^* ⋙ ρ_Z ≅ ρ_Y ⋙ Lf^*_{ét}` for its pullback
comparison (`ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso`).

* `ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso_inv_app_comp`: the comparisons are
  compatible with the composition isomorphisms of the pullbacks; this is checked separately on
  the three layers of `ρ = Rν_* ∘ Φ ∘ ι` (`CategoryTheory.app_comp_map_comp_of_compCoherence`):
  the inclusion `ι` (by construction of `boundedConstructibleUpperStarComp`), the
  finite-coefficient comparison `Φ` (`ProEtale.finiteCoefficientDerivedUpperStarIso_compCoherence`)
  and `Rν_*` (`ProEtale.rightDerivedComparisonBaseChange_comp`);
* `ProEtale.CondensedRing.finiteEtaleReadingUpperStarIso_cube`: hence they are compatible with
  the pullback square comparisons of a commutative square, on the condensed side
  (`ProEtale.CondensedRing.boundedConstructiblePullbackSquareComparison`) and on the étale side
  (`Etale.derivedSquareUpperStarIso`). This is the hypothesis of the cube law of mates
  `CategoryTheory.mateEquiv_app_cube`.

This is the `ρ`-part of the compatibility of reduction modulo `ℓⁿ` with proper base change
(blueprint `proposition-compatibility-purity-base-change`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section Coherence

variable {X Y Z : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The compatibility of the inclusion of bounded constructible complexes with the derived
pullbacks is compatible with the composition isomorphisms `boundedConstructibleUpperStarComp`
(by construction of the latter). -/
lemma boundedConstructibleUpperStarCompatibility_inv_app_comp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (p : X ⟶ Y) (q : Y ⟶ Z) (M : Dᵇc(Z.left)⟦Λ⟧) :
    (boundedConstructibleUpperStarCompatibility Λ ℓ (p ≫ q)).inv.app M ≫
        (boundedConstructible _).ι.map ((boundedConstructibleUpperStarComp Λ ℓ p q).hom.app M) =
      (leftDerivedUpperStarComp Λ p.left q.left).hom.app M.obj ≫
        L((p.left)^*⟦Λ⟧).map ((boundedConstructibleUpperStarCompatibility Λ ℓ q).inv.app M) ≫
        (boundedConstructibleUpperStarCompatibility Λ ℓ p).inv.app
          ((boundedConstructibleUpperStar Λ ℓ q).obj M) := by
  simp [boundedConstructibleUpperStarComp]

/-- **The pullback comparisons of the étale reading are compatible with composition**: for
`p : X ⟶ Y` and `q : Y ⟶ Z`, the comparison for `p ≫ q` (as a 2-cell
`ρ_Z ⋙ L(p ≫ q)^* ⟶ L(p ≫ q)^* ⋙ ρ_X`) followed by the composition isomorphism of the condensed
pullbacks is the composition isomorphism of the étale pullbacks followed by the comparisons for
`q` and `p`. -/
theorem finiteEtaleReadingUpperStarIso_inv_app_comp (p : X ⟶ Y) (q : Y ⟶ Z)
    (M : Dᵇc(Z.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (finiteEtaleReadingUpperStarIso ℓ E n (p ≫ q)).inv.app M ≫
        (finiteEtaleReading ℓ E n X).map
          ((boundedConstructibleUpperStarComp (Profinite.integersModPowRingObj ℓ E n) ℓ p q).hom.app
            M) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left
          q.left).hom.app ((finiteEtaleReading ℓ E n Z).obj M) ≫
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) p.left).map
          ((finiteEtaleReadingUpperStarIso ℓ E n q).inv.app M) ≫
        (finiteEtaleReadingUpperStarIso ℓ E n p).inv.app
          ((boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ q).obj M) := by
  simp only [finiteEtaleReadingUpperStarIso_inv_app]
  let T := PadicAlgCl.integersModPow ℓ E n
  let A := ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)
  let Λ := Profinite.integersModPowRingObj ℓ E n
  -- the layer of the inclusions and of the finite-coefficient comparisons `Φ`
  have h₁ := app_comp_map_comp_of_compCoherence
    (boundedConstructibleUpperStarComp Λ ℓ p q) (leftDerivedUpperStarComp Λ p.left q.left)
    (ProEtale.leftDerivedUpperStarComp A p.left q.left)
    (boundedConstructibleUpperStarCompatibility Λ ℓ p).inv
    (boundedConstructibleUpperStarCompatibility Λ ℓ q).inv
    (boundedConstructibleUpperStarCompatibility Λ ℓ (p ≫ q)).inv
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso p.left T).inv
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso q.left T).inv
    (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso (p ≫ q).left T).inv
    (boundedConstructibleUpperStarCompatibility_inv_app_comp ℓ Λ p q)
    (CompCoherence.inv_app (finiteCoefficientDerivedUpperStarIso_compCoherence T p.left q.left))
  -- the layer of the comparisons `Rν_*`
  have h₂ := app_comp_map_comp_of_compCoherence
    (GX := (boundedConstructible _).ι ⋙ (finiteCoefficientDerivedEquivalence X.left T).functor)
    (GY := (boundedConstructible _).ι ⋙ (finiteCoefficientDerivedEquivalence Y.left T).functor)
    (GZ := (boundedConstructible _).ι ⋙ (finiteCoefficientDerivedEquivalence Z.left T).functor)
    (boundedConstructibleUpperStarComp Λ ℓ p q)
    (ProEtale.leftDerivedUpperStarComp A p.left q.left)
    (Etale.leftDerivedUpperStarComp A p.left q.left)
    (Functor.whiskerLeft (boundedConstructible _).ι
        (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso p.left T).inv ≫
      Functor.whiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ p).inv
        (finiteCoefficientDerivedEquivalence X.left T).functor)
    (Functor.whiskerLeft (boundedConstructible _).ι
        (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso q.left T).inv ≫
      Functor.whiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ q).inv
        (finiteCoefficientDerivedEquivalence Y.left T).functor)
    (Functor.whiskerLeft (boundedConstructible _).ι
        (leftDerivedUpperStarFiniteCoefficientDerivedEquivalenceIso (p ≫ q).left T).inv ≫
      Functor.whiskerRight (boundedConstructibleUpperStarCompatibility Λ ℓ (p ≫ q)).inv
        (finiteCoefficientDerivedEquivalence X.left T).functor)
    (rightDerivedComparisonBaseChange A p.left) (rightDerivedComparisonBaseChange A q.left)
    (rightDerivedComparisonBaseChange A (p ≫ q).left) h₁
    (rightDerivedComparisonBaseChange_comp A p.left q.left) M
  simpa [finiteEtaleReading] using h₂

/-- The pullback comparisons of the étale reading for equal morphisms `u = v` agree, up to the
transports along `u = v`. -/
lemma finiteEtaleReadingUpperStarIso_inv_app_eqToHom {u v : Z ⟶ Y} (e : u = v)
    (M : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    (finiteEtaleReadingUpperStarIso ℓ E n u).inv.app M ≫
        (finiteEtaleReading ℓ E n Z).map (eqToHom (by rw [e])) =
      eqToHom (by rw [e]) ≫ (finiteEtaleReadingUpperStarIso ℓ E n v).inv.app M := by
  subst e
  simp

end Coherence

/-- The composition isomorphism of derived étale pullbacks along a morphism `g₁₂` equal to
`g₁ ≫ g₂` is the one along `g₁ ≫ g₂`, up to the transport along `g₁₂ = g₁ ≫ g₂`. -/
lemma _root_.AlgebraicGeometry.Etale.leftDerivedUpperStarComp_inv_app_of_eq
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (g₁₂ : T ⟶ R) (h : g₁₂ = g₁ ≫ g₂)
    (K : DerivedCategory (Sheaf R.smallEtaleTopology A)) :
    (Etale.leftDerivedUpperStarComp A g₁ g₂ g₁₂ h).inv.app K =
      (Etale.leftDerivedUpperStarComp A g₁ g₂).inv.app K ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The components of the derived square isomorphism `Lg^* ⋙ Lf'^* ≅ Lf^* ⋙ Lg'^*` of a
commutative square `g' ≫ f = f' ≫ g` of schemes. -/
lemma _root_.AlgebraicGeometry.Etale.derivedSquareUpperStarIso_hom_app
    (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (Etale.derivedSquareUpperStarIso A sq).hom.app K =
      (Etale.leftDerivedUpperStarComp A f' g).inv.app K ≫ eqToHom (by rw [sq.w]) ≫
        (Etale.leftDerivedUpperStarComp A g' f).hom.app K := by
  rw [Etale.derivedSquareUpperStarIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Etale.leftDerivedUpperStarComp_inv_app_of_eq, Category.assoc]

/-- An abstract form of the cube of 2-cells of `finiteEtaleReadingUpperStarIso_cube`. -/
private lemma cube_aux {C D : Type*} [Category* C] [Category* D] (P : C ⥤ D)
    {R₀ R₀' R₁ R₂ : C} {K₁ K₂ S S' K₃ K₄ : D}
    (x₁ : K₁ ⟶ K₂) (x₂ : K₂ ⟶ P.obj R₁) (c₁ : R₀ ⟶ R₁) (c₁' : R₁ ⟶ R₀) (tρ : R₀ ⟶ R₀')
    (c₂ : R₀' ⟶ R₂) (A₁ : S ⟶ P.obj R₀) (A₂ : S' ⟶ P.obj R₀') (e₁ : S ⟶ K₁) (e₁' : K₁ ⟶ S)
    (t : S ⟶ S') (e₂ : S' ⟶ K₃) (y₁ : K₃ ⟶ K₄) (y₂ : K₄ ⟶ P.obj R₂)
    (hc : c₁ ≫ c₁' = 𝟙 R₀) (he : e₁' ≫ e₁ = 𝟙 K₁)
    (H₁ : A₁ ≫ P.map c₁ = e₁ ≫ x₁ ≫ x₂) (H₂ : A₂ ≫ P.map c₂ = e₂ ≫ y₁ ≫ y₂)
    (H₃ : A₁ ≫ P.map tρ = t ≫ A₂) :
    x₁ ≫ x₂ ≫ P.map (c₁' ≫ tρ ≫ c₂) = (e₁' ≫ t ≫ e₂) ≫ y₁ ≫ y₂ := by
  have h : x₁ ≫ x₂ = e₁' ≫ A₁ ≫ P.map c₁ := by
    rw [H₁, reassoc_of% he]
  rw [reassoc_of% h, ← P.map_comp, reassoc_of% hc, P.map_comp, reassoc_of% H₃, H₂]
  simp

section Cube

variable {X Y X' Y' : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The pullback comparisons of the étale reading and pullback squares**: for a commutative
square `g' ≫ f = f' ≫ g`, the comparisons `finiteEtaleReadingUpperStarIso` (as 2-cells
`ρ ⋙ Lh^*_{ét} ⟶ Lh^* ⋙ ρ`) are compatible with the pullback square comparisons
`Lf'^* Lg^* ≅ Lg'^* Lf^*` on bounded constructible condensed `𝒪_E ⧸ ℓⁿ`-complexes
(`boundedConstructiblePullbackSquareComparison`) and on étale complexes
(`Etale.derivedSquareUpperStarIso`). This is the hypothesis of the cube law of mates
`CategoryTheory.mateEquiv_app_cube` for the étale reading. -/
theorem finiteEtaleReadingUpperStarIso_cube (sq : CommSq g' f' f g)
    (M : Dᵇc(Y.left)⟦Profinite.integersModPowRingObj ℓ E n⟧) :
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f'.left).map
        ((finiteEtaleReadingUpperStarIso ℓ E n g).inv.app M) ≫
      (finiteEtaleReadingUpperStarIso ℓ E n f').inv.app
        ((boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ g).obj M) ≫
      (finiteEtaleReading ℓ E n X').map
        ((boundedConstructiblePullbackSquareComparison (Profinite.integersModPowRingObj ℓ E n) ℓ
          sq).hom.app M) =
    (Etale.derivedSquareUpperStarIso (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
        (⟨Over.left_comp_left_eq_of_comp_eq sq.w⟩ : CommSq g'.left f'.left f.left g.left)).hom.app
          ((finiteEtaleReading ℓ E n Y).obj M) ≫
      L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g'.left).map
        ((finiteEtaleReadingUpperStarIso ℓ E n f).inv.app M) ≫
      (finiteEtaleReadingUpperStarIso ℓ E n g').inv.app
        ((boundedConstructibleUpperStar (Profinite.integersModPowRingObj ℓ E n) ℓ f).obj M) := by
  have H₁ := finiteEtaleReadingUpperStarIso_inv_app_comp ℓ E n f' g M
  have H₂ := finiteEtaleReadingUpperStarIso_inv_app_comp ℓ E n g' f M
  have H₃ := finiteEtaleReadingUpperStarIso_inv_app_eqToHom ℓ E n sq.w.symm M
  have hc := (boundedConstructibleUpperStarComp (Profinite.integersModPowRingObj ℓ E n) ℓ f'
    g).hom_inv_id_app M
  have he := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))
    f'.left g.left).inv_hom_id_app ((finiteEtaleReading ℓ E n Y).obj M)
  rw [boundedConstructiblePullbackSquareComparison_hom_app,
    Etale.derivedSquareUpperStarIso_hom_app]
  exact cube_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc he H₁ H₂ H₃

end Cube

end AlgebraicGeometry.ProEtale.CondensedRing
